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
    'CITATION.cff',
    'SOURCES.md',
    'TRUST.md',
    'THEOREM_INDEX.md',
    'REVIEWING.md',
    'docs/audit/README.md',
    'docs/audit/IndependentReviewSignoff.md',
    'papers/SCHEMA.md',
    "papers/$Paper/paper.json"
)
foreach ($relativePath in $fixedFiles) {
    Copy-RepositoryFile $relativePath
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
