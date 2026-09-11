[CmdletBinding()]
param(
    [Parameter(Mandatory)]
    [ValidatePattern('^[a-z0-9-]+$')]
    [string] $Paper,

    [Parameter(Mandatory)]
    [string] $OutputDirectory,

    [Parameter(Mandatory)]
    [ValidatePattern('^[A-Za-z0-9._-]+$')]
    [string] $ReleaseTag,

    [string] $RepositoryRoot = '',

    [switch] $AllowDirty
)

$ErrorActionPreference = 'Stop'

# Windows PowerShell 5 does not always preload the assembly that exposes
# System.IO.Compression.ZipFile.  Loading it explicitly keeps local review-kit
# generation aligned with PowerShell 7 and the GitHub Actions runner.
Add-Type -AssemblyName System.IO.Compression.FileSystem

if (-not $RepositoryRoot) {
    $RepositoryRoot = Join-Path $PSScriptRoot '../..'
}
$RepositoryRoot = [IO.Path]::GetFullPath($RepositoryRoot)
$OutputDirectory = [IO.Path]::GetFullPath($OutputDirectory)

$metadataPath = Join-Path $RepositoryRoot "papers/$Paper/paper.json"
if (-not (Test-Path -LiteralPath $metadataPath -PathType Leaf)) {
    throw "Unknown paper manifest: $metadataPath"
}
$metadata = Get-Content -LiteralPath $metadataPath -Raw | ConvertFrom-Json
if ($metadata.schemaVersion -notin @(1, 2) -or $metadata.id -ne $Paper) {
    throw "Unsupported or mismatched paper manifest: $metadataPath"
}

$commonRequiredProperties = @(
    'canonicalName',
    'assetStem',
    'theoremIndexRowPrefix',
    'title',
    'author',
    'entryModule',
    'auditModules',
    'auditDirectory',
    'semanticStatus',
    'grade',
    'expectedAxioms'
)
foreach ($property in $commonRequiredProperties) {
    if ($metadata.PSObject.Properties.Name -notcontains $property) {
        throw "Paper manifest lacks required property '$property': $metadataPath"
    }
}
if ([string]::IsNullOrWhiteSpace([string] $metadata.theoremIndexRowPrefix) -or
    [string] $metadata.theoremIndexRowPrefix -match '[|\r\n]') {
    throw "Paper manifest has an invalid theoremIndexRowPrefix: $metadataPath"
}

if ($metadata.schemaVersion -eq 1) {
    $versionRequiredProperties = @('year', 'sourceUrl', 'sourceDescription', 'sourceSha256')
} else {
    $versionRequiredProperties = @(
        'workYear',
        'publicationYear',
        'citation',
        'doi',
        'authoritativeSource',
        'comparisonSources',
        'formalizedScope',
        'excludedScope'
    )
}
foreach ($property in $versionRequiredProperties) {
    if ($metadata.PSObject.Properties.Name -notcontains $property) {
        throw "Paper manifest lacks schema-$($metadata.schemaVersion) property '$property': $metadataPath"
    }
}

$paperYear = if ($metadata.schemaVersion -eq 1) {
    [int] $metadata.year
} else {
    [int] $metadata.publicationYear
}
$workYear = if ($metadata.schemaVersion -eq 1) {
    [int] $metadata.year
} else {
    [int] $metadata.workYear
}
$sourceUrl = if ($metadata.schemaVersion -eq 1) {
    [string] $metadata.sourceUrl
} else {
    [string] $metadata.authoritativeSource.url
}
$sourceDescription = if ($metadata.schemaVersion -eq 1) {
    [string] $metadata.sourceDescription
} else {
    [string] $metadata.authoritativeSource.description
}
$sourceSha256 = if ($metadata.schemaVersion -eq 1) {
    [string] $metadata.sourceSha256
} else {
    [string] $metadata.authoritativeSource.sha256
}

if ($metadata.schemaVersion -eq 2) {
    foreach ($property in @('url', 'description', 'sha256', 'authority', 'redistributable')) {
        if ($metadata.authoritativeSource.PSObject.Properties.Name -notcontains $property) {
            throw "Authoritative source lacks required property '$property': $metadataPath"
        }
    }
    if ($metadata.authoritativeSource.authority -ne $true) {
        throw "Schema-2 authoritativeSource.authority must be true: $metadataPath"
    }
    foreach ($comparison in @($metadata.comparisonSources)) {
        if ($comparison.authority -ne $false) {
            throw "Every schema-2 comparison source must have authority=false: $metadataPath"
        }
        if ($comparison.sha256 -notmatch '^[0-9A-F]{64}$') {
            throw "Comparison-source SHA-256 is invalid: $metadataPath"
        }
    }
}

if ($sourceSha256 -notmatch '^[0-9A-F]{64}$') {
    throw "Paper source SHA-256 is not an uppercase 64-digit hexadecimal value: $metadataPath"
}

$commitOutput = @(& git -C $RepositoryRoot rev-parse HEAD)
$commitExitCode = $LASTEXITCODE
$commit = if ($commitOutput.Count -gt 0) { ([string] $commitOutput[0]).Trim() } else { '' }
if ($commitExitCode -ne 0 -or $commit -notmatch '^[0-9a-f]{40}$') {
    throw "Cannot resolve the source commit for $RepositoryRoot"
}
$status = @(& git -C $RepositoryRoot status --porcelain)
if ($LASTEXITCODE -ne 0) {
    throw "Cannot inspect the source worktree for $RepositoryRoot"
}
$treeState = if ($status.Count -eq 0) { 'clean' } else { 'dirty' }
if ($treeState -eq 'dirty' -and -not $AllowDirty) {
    throw 'Refusing to publish a Review Kit from a dirty worktree. Use -AllowDirty only for local development.'
}

function Convert-ModuleToRelativePath {
    param([Parameter(Mandatory)][string] $Module)

    return $Module.Replace('.', [IO.Path]::DirectorySeparatorChar) + '.lean'
}

function Convert-ToForwardSlashPath {
    param([Parameter(Mandatory)][string] $Path)

    return $Path.Replace([IO.Path]::DirectorySeparatorChar, '/')
}

function Get-LocalImports {
    param([Parameter(Mandatory)][string] $SourcePath)

    $imports = [Collections.Generic.List[string]]::new()
    foreach ($line in Get-Content -LiteralPath $SourcePath) {
        $match = [regex]::Match($line, '^\s*import\s+(.+)$')
        if (-not $match.Success) {
            continue
        }
        $tail = ($match.Groups[1].Value -split '--', 2)[0].Trim()
        foreach ($token in ($tail -split '\s+')) {
            if (-not $token -or $token.StartsWith('/-')) {
                break
            }
            $imports.Add($token.Trim())
        }
    }
    return $imports
}

$pending = [Collections.Generic.Queue[string]]::new()
$seenModules = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
$sourceFiles = [Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)

$roots = @([string] $metadata.entryModule) + @($metadata.auditModules | ForEach-Object { [string] $_ })
$roots += 'BongTest.AxiomGate'
foreach ($root in $roots) {
    $pending.Enqueue($root)
}

while ($pending.Count -gt 0) {
    $module = $pending.Dequeue()
    if (-not $seenModules.Add($module)) {
        continue
    }
    $relativePath = Convert-ModuleToRelativePath $module
    $sourcePath = Join-Path $RepositoryRoot $relativePath
    if (-not (Test-Path -LiteralPath $sourcePath -PathType Leaf)) {
        if ($module -eq $metadata.entryModule -or
            @($metadata.auditModules) -contains $module -or
            $module.StartsWith('Bong.') -or
            $module.StartsWith('BongTest.')) {
            throw "Missing local Lean module '$module' at $sourcePath"
        }
        continue
    }
    $relativeForward = Convert-ToForwardSlashPath $relativePath
    [void] $sourceFiles.Add($relativeForward)
    foreach ($import in Get-LocalImports $sourcePath) {
        $pending.Enqueue($import)
    }
}

$assetBase = "BongTheory-$($metadata.assetStem)-$ReleaseTag-review-kit"
$stagingDirectory = Join-Path $OutputDirectory $assetBase
$archivePath = Join-Path $OutputDirectory ($assetBase + '.zip')
if (Test-Path -LiteralPath $stagingDirectory) {
    throw "Review Kit staging directory already exists: $stagingDirectory"
}
if (Test-Path -LiteralPath $archivePath) {
    throw "Review Kit archive already exists: $archivePath"
}
[void] (New-Item -ItemType Directory -Path $stagingDirectory -Force)

function Copy-RepositoryFile {
    param([Parameter(Mandatory)][string] $RelativePath)

    $normalized = $RelativePath.Replace('/', [IO.Path]::DirectorySeparatorChar)
    $source = [IO.Path]::GetFullPath((Join-Path $RepositoryRoot $normalized))
    $repositoryPrefix = $RepositoryRoot.TrimEnd([IO.Path]::DirectorySeparatorChar) +
        [IO.Path]::DirectorySeparatorChar
    if (-not $source.StartsWith($repositoryPrefix, [StringComparison]::OrdinalIgnoreCase)) {
        throw "Source path escapes repository: $RelativePath"
    }
    if (-not (Test-Path -LiteralPath $source -PathType Leaf)) {
        throw "Required Review Kit file is missing: $RelativePath"
    }
    $destination = Join-Path $stagingDirectory $normalized
    $parent = Split-Path -Parent $destination
    if ($parent) {
        [void] (New-Item -ItemType Directory -Path $parent -Force)
    }
    [IO.File]::Copy($source, $destination, $false)
}

foreach ($relativePath in @($sourceFiles | Sort-Object)) {
    if ($relativePath -in @('Bong.lean', 'BongTest.lean')) {
        continue
    }
    Copy-RepositoryFile $relativePath
}

$fixedFiles = @(
    'lean-toolchain',
    'lakefile.toml',
    'lake-manifest.json',
    'LICENSE',
    'papers/SCHEMA.md',
    "papers/$Paper/paper.json"
)
foreach ($relativePath in $fixedFiles) {
    Copy-RepositoryFile $relativePath
}

$verificationFiles = @()
if ($metadata.PSObject.Properties.Name -contains 'verificationFiles') {
    $verificationFiles = @($metadata.verificationFiles | ForEach-Object {
        [string] $_
    })
}
foreach ($relativePath in $verificationFiles) {
    if (-not $relativePath) {
        throw "Paper manifest contains an empty verificationFiles entry: $metadataPath"
    }
    Copy-RepositoryFile $relativePath
}

$verificationCommands = @()
if ($metadata.PSObject.Properties.Name -contains 'verificationCommands') {
    $verificationCommands = @($metadata.verificationCommands | ForEach-Object {
        [string] $_
    })
}

$auditRoot = [IO.Path]::GetFullPath((Join-Path $RepositoryRoot ([string] $metadata.auditDirectory)))
$repositoryPrefix = $RepositoryRoot.TrimEnd([IO.Path]::DirectorySeparatorChar) +
    [IO.Path]::DirectorySeparatorChar
if (-not $auditRoot.StartsWith($repositoryPrefix, [StringComparison]::OrdinalIgnoreCase) -or
    -not (Test-Path -LiteralPath $auditRoot -PathType Container)) {
    throw "Invalid audit directory: $auditRoot"
}
foreach ($file in Get-ChildItem -LiteralPath $auditRoot -File -Recurse) {
    if (($file.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0) {
        throw "Review Kit does not accept reparse-point audit files: $($file.FullName)"
    }
    $relativePath = $file.FullName.Substring($RepositoryRoot.Length).TrimStart('\', '/')
    Copy-RepositoryFile (Convert-ToForwardSlashPath $relativePath)
}

$encoding = [Text.UTF8Encoding]::new($false)

$theoremIndexRows = @(
    Get-Content -LiteralPath (Join-Path $RepositoryRoot 'THEOREM_INDEX.md') |
        Where-Object {
            $_.StartsWith(
                "| $($metadata.theoremIndexRowPrefix)",
                [StringComparison]::Ordinal
            )
        }
)
if ($theoremIndexRows.Count -eq 0) {
    throw "No public theorem-index row matches '$($metadata.theoremIndexRowPrefix)'"
}
$theoremIndex = @"
# Public theorem index: $($metadata.canonicalName)

This paper-specific table lists stable public entry points for this Review
Kit. Internal proof modules and the included fidelity audit provide the fuller
map. Rows for unrelated papers are intentionally excluded.

| Source result | Lean endpoint | Source file | Status |
| --- | --- | --- | --- |
$($theoremIndexRows -join "`n")

Successful compilation checks these encoded declarations; it does not by
itself establish semantic fidelity to the identified paper version.
"@
[IO.File]::WriteAllText(
    (Join-Path $stagingDirectory 'THEOREM_INDEX.md'),
    $theoremIndex,
    $encoding
)

$comparisonSourceText = if ($metadata.schemaVersion -eq 2 -and
    @($metadata.comparisonSources).Count -gt 0) {
    (@($metadata.comparisonSources | ForEach-Object {
        "- Comparison source (not authoritative): $($_.url)`n" +
        "  SHA-256: **$($_.sha256)**"
    }) -join "`n") + "`n"
} else {
    ''
}
$sourceAuthorityText = if ($metadata.schemaVersion -eq 2) {
    "- Citation: $($metadata.citation)`n" +
        "- DOI: $($metadata.doi)`n" +
        "- Authority: publisher version of record`n"
} else {
    "- Authority: frozen source identified by this manifest`n"
}
$sources = @"
# Audited mathematical source: $($metadata.canonicalName)

$sourceAuthorityText- Source: $sourceUrl
- Description: $sourceDescription
- SHA-256: **$sourceSha256**
$comparisonSourceText
The source PDF is not bundled. Reviewers must obtain it independently and
verify the hash before auditing statement fidelity. No source listed as a
comparison copy may silently override the authoritative source.
"@
[IO.File]::WriteAllText((Join-Path $stagingDirectory 'SOURCES.md'), $sources, $encoding)

$trust = @"
# Trust boundary: $($metadata.canonicalName)

This Review Kit separates three claims:

1. Lean kernel acceptance of the encoded declarations;
2. technical reproducibility from the pinned source and dependency closure;
3. semantic fidelity to the source identified in **SOURCES.md**.

The first two are mechanically checkable. The third also requires independent
mathematical and formalization review.

- Semantic status: **$($metadata.semanticStatus)**
- Coverage status: **$($metadata.coverageStatus)**
- Project grade: **$($metadata.grade)**
- Permitted foundational axioms: **$(@($metadata.expectedAxioms) -join ', ')**

The generated **BongTest/PaperAxiomGate.lean** checks the transitive axiom
dependencies of this paper's imported project-module closure and rejects any
dependency outside the stated allowance. It does not certify that the Lean
statements match the paper. Consult **paper-manifest.json** and the included
paper-specific audit directory for covered, excluded, conditional, and
refuted scope.
"@
[IO.File]::WriteAllText((Join-Path $stagingDirectory 'TRUST.md'), $trust, $encoding)

$reviewNoticeText = if ($metadata.PSObject.Properties.Name -contains 'reviewNotice') {
    "`n## Paper-specific notice`n`n$($metadata.reviewNotice)`n"
} else {
    ''
}
$reviewing = @"
# Independent review protocol: $($metadata.canonicalName)

The review is intentionally divided between mathematical and Lean roles. A
reviewer may fill both roles only when that overlap is disclosed.

## Mathematical reviewer

Obtain the source identified in **SOURCES.md**, verify its SHA-256, and read it
independently before using the theorem inventory and author review cards.
Check objects, hypotheses, normalizations, quantifier order, representation
direction, strict inequalities, rank conventions, and every boundary case.
Record disagreements rather than silently repairing the source.
$reviewNoticeText
## Lean formalization reviewer

Build this clean extraction, inspect declaration signatures rather than names
or comments, expand the underlying definitions, run every audit in
**paper-manifest.json**, and inspect the import closure for circularity or an
imported equivalent of a target theorem.

## Required evidence

Every signed review must identify the exact paper hash, repository commit and
tag, reviewer identity and role, files or theorem cards reviewed, commands and
exit results, decisions, reservations, exclusions, conflicts of interest, and
date. Use **docs/audit/IndependentReviewSignoff.md**. Project-generated or
AI-generated names are not independent sign-off.
"@
[IO.File]::WriteAllText((Join-Path $stagingDirectory 'REVIEWING.md'), $reviewing, $encoding)

$auditReadme = @"
# Formalization fidelity audit: $($metadata.canonicalName)

This directory contains only the audit package for **$($metadata.canonicalName)**.

- Audit directory: **$($metadata.auditDirectory)**
- Semantic status: **$($metadata.semanticStatus)**
- Coverage status: **$($metadata.coverageStatus)**
- Project grade: **$($metadata.grade)**

Start with the paper directory's executive summary, completion audit, theorem
correspondence, and author review cards. Kernel acceptance, reproducibility,
semantic fidelity, source mismatches, and human sign-off are separate gates.
"@
[IO.File]::WriteAllText(
    (Join-Path $stagingDirectory 'docs/audit/README.md'),
    $auditReadme,
    $encoding
)

$signoff = @"
# Independent review sign-off: $($metadata.canonicalName)

No independent human sign-off is created by this generated Review Kit.

## Paper author or domain expert

- Name:
- Affiliation or public profile:
- Role:
- Paper version and SHA-256:
- Repository full commit and tag:
- Review-card decisions:
- Reservations or exclusions:
- Conflict-of-interest disclosure:
- Date:
- Signature or immutable approval link:

## Lean formalization expert

- Name:
- Affiliation or public profile:
- Repository full commit and tag:
- Operating system and architecture:
- Lean and Lake versions:
- Commands executed and exit results:
- Trust-boundary decision:
- Semantic-scope decision:
- Reservations or exclusions:
- Conflict-of-interest disclosure:
- Date:
- Signature or immutable approval link:

An entry is valid only when completed by the named reviewer. Project-generated
or AI-generated names do not constitute independent review.
"@
[IO.File]::WriteAllText(
    (Join-Path $stagingDirectory 'docs/audit/IndependentReviewSignoff.md'),
    $signoff,
    $encoding
)

$citation = @"
cff-version: 1.2.0
message: "If you use this Review Kit, cite both this software artifact and the source paper identified in SOURCES.md."
title: "BongTheory Lean 4 Review Kit: $($metadata.canonicalName)"
type: software
version: "$ReleaseTag"
authors:
  - name: "BONG Theory contributors"
license: Apache-2.0
repository-code: "https://github.com/hzldew-git/BongTheory"
url: "https://github.com/hzldew-git/BongTheory"
keywords:
  - Lean 4
  - quadratic lattices
  - BONG
  - formalized mathematics
abstract: >-
  Paper-specific Lean 4 Review Kit for $($metadata.author),
  $($metadata.title) ($paperYear). The package records coverage and semantic
  status separately from kernel acceptance.
"@
[IO.File]::WriteAllText((Join-Path $stagingDirectory 'CITATION.cff'), $citation, $encoding)

$entryRootText = "import $($metadata.entryModule)`n"
[IO.File]::WriteAllText((Join-Path $stagingDirectory 'Bong.lean'), $entryRootText, $encoding)

$auditImports = @($metadata.auditModules | ForEach-Object { "import $_" }) -join "`n"
$gateModule = 'BongTest.PaperAxiomGate'
$gateText = "/-`nCopyright (c) 2026 BONG Theory contributors. All rights reserved.`n" +
    "Released under Apache 2.0 license as described in the file LICENSE.`n" +
    "Authors: BONG Theory contributors`n-/`n" +
    "import Bong`nimport BongTest.AxiomGate`n" + $auditImports + "`n`n" +
    "/-! Enforce the fixed foundational axiom allowance on this paper's closure. -/`n`n" +
    "set_option maxHeartbeats 0 in`n" +
    'run_cmd BongCI.checkAxioms #[`Bong, `BongTest]' + "`n"
[IO.File]::WriteAllText(
    (Join-Path $stagingDirectory 'BongTest/PaperAxiomGate.lean'), $gateText, $encoding
)
[IO.File]::WriteAllText(
    (Join-Path $stagingDirectory 'BongTest.lean'),
    $auditImports + "`nimport $gateModule`n",
    $encoding
)

$kitAuditModules = @($metadata.auditModules) + @($gateModule)
$auditCommands = @()
foreach ($auditModule in $kitAuditModules) {
    $auditPath = Convert-ToForwardSlashPath (Convert-ModuleToRelativePath ([string] $auditModule))
    $auditCommands += "lake env lean $auditPath"
}
$coverageLine = if ($metadata.PSObject.Properties.Name -contains 'coverageStatus') {
    "- Coverage status: **$($metadata.coverageStatus)**`n"
} else {
    ''
}
$notice = if ($metadata.PSObject.Properties.Name -contains 'reviewNotice') {
    "`n## Paper-specific review notice`n`n$($metadata.reviewNotice)`n"
} else {
    ''
}
$comparisonLines = if ($metadata.schemaVersion -eq 2 -and @($metadata.comparisonSources).Count -gt 0) {
    (@($metadata.comparisonSources | ForEach-Object {
        "- Non-authoritative comparison source: $($_.url) (SHA-256: $($_.sha256))"
    }) -join "`n") + "`n"
} else {
    ''
}
$authorityNotice = if ($metadata.schemaVersion -eq 2) {
    "- Semantic authority: **publisher version of record only**`n- DOI: $($metadata.doi)`n- Work year / publication year: **$workYear / $paperYear**`n"
} else {
    ''
}
$verificationSection = if ($verificationFiles.Count -gt 0) {
    $fileLines = ($verificationFiles | ForEach-Object { "- **$_**" }) -join "`n"
    $commandBlock = if ($verificationCommands.Count -gt 0) {
        "`nRun the available independent checks with:`n`n~~~text`n" +
            ($verificationCommands -join "`n") + "`n~~~`n"
    } else {
        ''
    }
    "`n## Independent computational cross-checks`n`n" +
        "The kit includes the following non-Lean verification material:`n`n" +
        $fileLines + "`n" + $commandBlock +
        "`nThese checks corroborate finite calculations but do not enlarge the " +
        "Lean trust boundary or replace semantic review.`n"
} else {
    ''
}
$readme = @"
# $($metadata.canonicalName) Lean 4 Review Kit

Paper: *$($metadata.title)* ($paperYear), $($metadata.author).

- Frozen source: $sourceUrl
- Frozen source SHA-256: **$sourceSha256**
$authorityNotice$comparisonLines- Canonical Lean entry: **$($metadata.entryModule)**
- Semantic status: **$($metadata.semanticStatus)**
- Project grade: **$($metadata.grade)**
$coverageLine
This source-only package contains the repository-local transitive import
closure of the paper entry and audit modules. It contains no compiled Lean
artifact, **.lake** directory, publisher PDF, Git history, or unrelated
**BongTest/M*.lean** milestone file.

## Fast verification

Set the environment variable **LEAN_NUM_THREADS=1** in the invoking shell
(`$env:LEAN_NUM_THREADS = '1'` in PowerShell), then run:

~~~text
lake exe cache get
lake build
$($auditCommands -join "`n")
~~~

## Source-build verification

In a fresh extraction, omit the cache command and run:

~~~text
lake --no-cache build
$($auditCommands -join "`n")
~~~

The one-thread setting is deliberate: the complete source closure contains
several memory-intensive shared modules, and unconstrained parallel builds can
exhaust a review machine even when every module compiles successfully.

Successful compilation establishes kernel acceptance of the encoded
statements. It does not by itself promote the semantic status to
**VERIFIED_MATCH**. Consult the included fidelity materials under
**$($metadata.auditDirectory)**.

The generated **BongTest/PaperAxiomGate.lean** additionally rejects any
declaration in this paper's imported project-module closure whose transitive
axiom dependencies exceed **propext, Classical.choice, Quot.sound**. It checks
module ownership as well as namespaces, including private helpers. This
enforcing check is separate from the human-readable axiom listings and does
not claim semantic equivalence to the paper.
$verificationSection
$notice
## Integrity

**FILES.sha256** covers every file in this archive other than itself. The GitHub
Release also publishes the SHA-256 of the complete ZIP archive.
"@
[IO.File]::WriteAllText((Join-Path $stagingDirectory 'README.md'), $readme, $encoding)

$paperManifest = if ($metadata.schemaVersion -eq 1) {
    [ordered]@{
        id = $metadata.id
        canonicalName = $metadata.canonicalName
        theoremIndexRowPrefix = $metadata.theoremIndexRowPrefix
        year = $metadata.year
        title = $metadata.title
        author = $metadata.author
        sourceUrl = $sourceUrl
        sourceDescription = $sourceDescription
        sourceSha256 = $sourceSha256
    }
} else {
    [ordered]@{
        id = $metadata.id
        canonicalName = $metadata.canonicalName
        theoremIndexRowPrefix = $metadata.theoremIndexRowPrefix
        workYear = $workYear
        publicationYear = $paperYear
        title = $metadata.title
        author = $metadata.author
        citation = $metadata.citation
        doi = $metadata.doi
        authoritativeSource = $metadata.authoritativeSource
        comparisonSources = @($metadata.comparisonSources)
    }
}
$manifest = [ordered]@{
    schemaVersion = $metadata.schemaVersion
    paper = $paperManifest
    formalization = [ordered]@{
        entryModule = $metadata.entryModule
        auditModules = $kitAuditModules
        enforcingAxiomGate = $gateModule
        auditDirectory = $metadata.auditDirectory
        coverageStatus = if ($metadata.PSObject.Properties.Name -contains 'coverageStatus') {
            $metadata.coverageStatus
        } else {
            $null
        }
        semanticStatus = $metadata.semanticStatus
        grade = $metadata.grade
        expectedAxioms = @($metadata.expectedAxioms)
        verificationFiles = $verificationFiles
        verificationCommands = $verificationCommands
        formalizedScope = if ($metadata.schemaVersion -eq 2) {
            @($metadata.formalizedScope)
        } else {
            $null
        }
        excludedScope = if ($metadata.schemaVersion -eq 2) {
            @($metadata.excludedScope)
        } else {
            $null
        }
        reviewNotice = if ($metadata.PSObject.Properties.Name -contains 'reviewNotice') {
            $metadata.reviewNotice
        } else {
            $null
        }
    }
    provenance = [ordered]@{
        repository = 'https://github.com/hzldew-git/BongTheory'
        releaseTag = $ReleaseTag
        sourceCommit = $commit
        sourceTreeState = $treeState
        generator = 'scripts/paper-kits/Build-PaperReviewKit.ps1'
    }
    package = [ordered]@{
        localLeanSourceCount = @($sourceFiles).Count
        excludesCompiledArtifacts = $true
        excludesPublisherPdf = $true
        excludesGitHistory = $true
    }
}
$manifestPath = Join-Path $stagingDirectory 'paper-manifest.json'
[IO.File]::WriteAllText(
    $manifestPath,
    ($manifest | ConvertTo-Json -Depth 10) + "`n",
    $encoding
)

$payloadFiles = @(
    Get-ChildItem -LiteralPath $stagingDirectory -File -Recurse |
        Where-Object { $_.Name -ne 'FILES.sha256' } |
        Sort-Object FullName
)
$checksumLines = foreach ($file in $payloadFiles) {
    $relative = $file.FullName.Substring($stagingDirectory.Length).TrimStart('\', '/')
    $relative = Convert-ToForwardSlashPath $relative
    $hash = (Get-FileHash -LiteralPath $file.FullName -Algorithm SHA256).Hash
    "$hash  $relative"
}
[IO.File]::WriteAllText(
    (Join-Path $stagingDirectory 'FILES.sha256'),
    ($checksumLines -join "`n") + "`n",
    $encoding
)

$forbidden = @(
    Get-ChildItem -LiteralPath $stagingDirectory -Force -Recurse |
        Where-Object {
            $_.Name -eq '.lake' -or
            $_.Extension -in @('.olean', '.ilean') -or
            $_.FullName -match '[\\/]BongTest[\\/]M\d+\.lean$'
        }
)
if ($forbidden.Count -gt 0) {
    throw "Forbidden Review Kit content: $($forbidden.FullName -join ', ')"
}

if (-not (Test-Path -LiteralPath $OutputDirectory -PathType Container)) {
    [void] (New-Item -ItemType Directory -Path $OutputDirectory -Force)
}
[IO.Compression.ZipFile]::CreateFromDirectory(
    $stagingDirectory,
    $archivePath,
    [IO.Compression.CompressionLevel]::Optimal,
    $false
)

$archive = Get-Item -LiteralPath $archivePath
[pscustomobject]@{
    paper = $Paper
    canonicalName = $metadata.canonicalName
    archive = $archive.FullName
    archiveBytes = $archive.Length
    archiveSha256 = (Get-FileHash -LiteralPath $archive.FullName -Algorithm SHA256).Hash
    stagingDirectory = $stagingDirectory
    sourceCommit = $commit
    sourceTreeState = $treeState
    localLeanSourceCount = @($sourceFiles).Count
    packagedFileCount = @($payloadFiles).Count + 1
} | ConvertTo-Json -Depth 5
