[CmdletBinding()]
param(
    [Parameter(Mandatory)]
    [string] $Archive,

    [Parameter(Mandatory)]
    [string] $ExtractionDirectory,

    [switch] $StructureOnly,

    [switch] $AllowDirtyKit,

    [string] $LogDirectory = '',

    [ValidateRange(1, 64)]
    [int] $LeanThreads = 1
)

$ErrorActionPreference = 'Stop'
$Archive = [IO.Path]::GetFullPath($Archive)
$ExtractionDirectory = [IO.Path]::GetFullPath($ExtractionDirectory)
if (-not (Test-Path -LiteralPath $Archive -PathType Leaf)) {
    throw "Review Kit archive does not exist: $Archive"
}
if (Test-Path -LiteralPath $ExtractionDirectory) {
    throw "Extraction directory already exists: $ExtractionDirectory"
}

Expand-Archive -LiteralPath $Archive -DestinationPath $ExtractionDirectory
$manifestPath = Join-Path $ExtractionDirectory 'paper-manifest.json'
$checksumsPath = Join-Path $ExtractionDirectory 'FILES.sha256'
if (-not (Test-Path -LiteralPath $manifestPath -PathType Leaf) -or
    -not (Test-Path -LiteralPath $checksumsPath -PathType Leaf)) {
    throw 'Review Kit lacks paper-manifest.json or FILES.sha256.'
}
$manifest = Get-Content -LiteralPath $manifestPath -Raw | ConvertFrom-Json
if ($manifest.schemaVersion -notin @(1, 2)) {
    throw 'Unsupported Review Kit manifest schema.'
}
$paperPrefix = [string] $manifest.paper.theoremIndexRowPrefix
if ([string]::IsNullOrWhiteSpace($paperPrefix) -or $paperPrefix -match '[|\r\n]') {
    throw 'Review Kit manifest lacks a valid paper-specific theorem-index prefix.'
}
if ($manifest.schemaVersion -eq 2) {
    if ($manifest.paper.authoritativeSource.authority -ne $true) {
        throw 'Schema-2 Review Kit lacks a unique authoritative publisher source.'
    }
    foreach ($comparison in @($manifest.paper.comparisonSources)) {
        if ($comparison.authority -ne $false) {
            throw 'Schema-2 comparison sources must be explicitly non-authoritative.'
        }
    }
    if ($manifest.formalization.PSObject.Properties.Name -notcontains 'formalizedScope' -or
        $manifest.formalization.PSObject.Properties.Name -notcontains 'excludedScope') {
        throw 'Schema-2 Review Kit lacks formalized/excluded scope accounting.'
    }
}
if ($manifest.provenance.sourceTreeState -ne 'clean' -and -not $AllowDirtyKit) {
    throw 'Review Kit was generated from a dirty source tree.'
}

$paperDirectory = Join-Path $ExtractionDirectory 'papers'
$packagedPaperDirectories = @(
    Get-ChildItem -LiteralPath $paperDirectory -Directory -ErrorAction Stop
)
if ($packagedPaperDirectories.Count -ne 1 -or
    $packagedPaperDirectories[0].Name -ne $manifest.paper.id) {
    throw 'Review Kit must contain exactly its own papers/<paper-id> directory.'
}
$auditDirectory = [IO.Path]::GetFullPath(
    (Join-Path $ExtractionDirectory ([string] $manifest.formalization.auditDirectory))
)
$packagedAuditDirectories = @(
    Get-ChildItem -LiteralPath (Join-Path $ExtractionDirectory 'docs/audit') `
        -Directory -ErrorAction Stop
)
if ($packagedAuditDirectories.Count -ne 1 -or
    $packagedAuditDirectories[0].FullName -ne $auditDirectory) {
    throw 'Review Kit must contain exactly its own paper-specific audit directory.'
}

foreach ($relativeReviewFile in @(
    'CITATION.cff',
    'SOURCES.md',
    'TRUST.md',
    'THEOREM_INDEX.md',
    'REVIEWING.md',
    'docs/audit/README.md',
    'docs/audit/IndependentReviewSignoff.md'
)) {
    if (-not (Test-Path -LiteralPath (Join-Path $ExtractionDirectory $relativeReviewFile) `
        -PathType Leaf)) {
        throw "Review Kit lacks paper-specific review material: $relativeReviewFile"
    }
}

$theoremIndexRows = @(
    Get-Content -LiteralPath (Join-Path $ExtractionDirectory 'THEOREM_INDEX.md') |
        Where-Object {
            $_ -match '^\| ' -and
            -not $_.StartsWith('| Source result', [StringComparison]::Ordinal) -and
            -not $_.StartsWith('| ---', [StringComparison]::Ordinal)
        }
)
if ($theoremIndexRows.Count -eq 0) {
    throw 'Paper-specific theorem index has no public entry rows.'
}
foreach ($row in $theoremIndexRows) {
    if (-not $row.StartsWith("| $paperPrefix", [StringComparison]::Ordinal)) {
        throw "Unrelated theorem-index row in paper-specific Review Kit: $row"
    }
}

$listed = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
foreach ($line in Get-Content -LiteralPath $checksumsPath) {
    if (-not $line) {
        continue
    }
    $match = [regex]::Match($line, '^([0-9A-F]{64})  (.+)$')
    if (-not $match.Success) {
        throw "Malformed FILES.sha256 line: $line"
    }
    $expected = $match.Groups[1].Value
    $relative = $match.Groups[2].Value
    if (-not $listed.Add($relative)) {
        throw "Duplicate checksum entry: $relative"
    }
    $candidate = [IO.Path]::GetFullPath((Join-Path $ExtractionDirectory $relative))
    $prefix = $ExtractionDirectory.TrimEnd([IO.Path]::DirectorySeparatorChar) +
        [IO.Path]::DirectorySeparatorChar
    if (-not $candidate.StartsWith($prefix, [StringComparison]::OrdinalIgnoreCase)) {
        throw "Checksum path escapes extraction directory: $relative"
    }
    if (-not (Test-Path -LiteralPath $candidate -PathType Leaf)) {
        throw "Checksummed file is missing: $relative"
    }
    $actual = (Get-FileHash -LiteralPath $candidate -Algorithm SHA256).Hash
    if ($actual -ne $expected) {
        throw "Checksum mismatch for $relative"
    }
}

$actualPayload = @(
    Get-ChildItem -LiteralPath $ExtractionDirectory -File -Recurse |
        Where-Object { $_.Name -ne 'FILES.sha256' }
)
if ($actualPayload.Count -ne $listed.Count) {
    throw "Checksum coverage mismatch: listed $($listed.Count), found $($actualPayload.Count)."
}

$forbidden = @(
    Get-ChildItem -LiteralPath $ExtractionDirectory -Force -Recurse |
        Where-Object {
            $_.Name -eq '.lake' -or
            $_.Name -eq '.git' -or
            $_.Extension -in @('.olean', '.ilean') -or
            $_.Extension -eq '.pdf' -or
            $_.FullName -match '[\\/]BongTest[\\/]M\d+\.lean$'
        }
)
if ($forbidden.Count -gt 0) {
    throw "Forbidden Review Kit content: $($forbidden.FullName -join ', ')"
}

if ($StructureOnly) {
    [pscustomobject]@{
        paper = $manifest.paper.id
        sourceCommit = $manifest.provenance.sourceCommit
        sourceTreeState = $manifest.provenance.sourceTreeState
        verifiedFileCount = $listed.Count
        structure = 'verified'
    } | ConvertTo-Json
    exit 0
}

if ($manifest.formalization.enforcingAxiomGate -ne 'BongTest.PaperAxiomGate' -or
    @($manifest.formalization.auditModules) -notcontains 'BongTest.PaperAxiomGate') {
    throw 'This older kit lacks the enforcing transitive axiom gate; regenerate it before full verification.'
}

$lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
$lake = if ($lakeCommand) { $lakeCommand.Source } else { $null }
if (-not $lake) {
    $runnerHome = if ($env:USERPROFILE) {
        $env:USERPROFILE
    } elseif ($env:HOME) {
        $env:HOME
    } else {
        throw 'Neither USERPROFILE nor HOME identifies the user home directory.'
    }
    $lakeName = if ($IsWindows) { 'lake.exe' } else { 'lake' }
    $lake = Join-Path (Join-Path $runnerHome '.elan/bin') $lakeName
}
if (-not (Test-Path -LiteralPath $lake)) {
    throw "Lake is unavailable: $lake"
}

if (-not $LogDirectory) {
    $LogDirectory = Join-Path (Split-Path -Parent $ExtractionDirectory) 'verification-logs'
}
$LogDirectory = [IO.Path]::GetFullPath($LogDirectory)
[void] (New-Item -ItemType Directory -Path $LogDirectory -Force)

$previousLeanNumThreads = [Environment]::GetEnvironmentVariable(
    'LEAN_NUM_THREADS',
    [EnvironmentVariableTarget]::Process
)
$env:LEAN_NUM_THREADS = [string] $LeanThreads
Push-Location $ExtractionDirectory
try {
    $buildLogPath = Join-Path $LogDirectory 'lake-build.log'
    & $lake build *> $buildLogPath
    if ($LASTEXITCODE -ne 0) {
        Get-Content -LiteralPath $buildLogPath -Tail 200
        throw "Review Kit Lake build failed with exit code $LASTEXITCODE."
    }
    foreach ($auditModule in @($manifest.formalization.auditModules)) {
        $auditPath = ([string] $auditModule).Replace('.', '/') + '.lean'
        $logPath = Join-Path $LogDirectory (([string] $auditModule).Replace('.', '-') + '.log')
        & $lake env lean $auditPath *> $logPath
        if ($LASTEXITCODE -ne 0) {
            Get-Content -LiteralPath $logPath -Tail 200
            throw "Review Kit audit failed for $auditModule with exit code $LASTEXITCODE."
        }
        if ($auditModule -eq $manifest.formalization.enforcingAxiomGate -and
            -not (Select-String -LiteralPath $logPath -SimpleMatch 'AXIOM_GATE_PASS:' -Quiet)) {
            throw 'The enforcing gate returned without its success marker.'
        }
    }
} finally {
    Pop-Location
    if ($null -eq $previousLeanNumThreads) {
        Remove-Item Env:LEAN_NUM_THREADS -ErrorAction SilentlyContinue
    } else {
        $env:LEAN_NUM_THREADS = $previousLeanNumThreads
    }
}

[pscustomobject]@{
    paper = $manifest.paper.id
    sourceCommit = $manifest.provenance.sourceCommit
    sourceTreeState = $manifest.provenance.sourceTreeState
    verifiedFileCount = $listed.Count
    structure = 'verified'
    build = 'passed'
    leanThreads = $LeanThreads
    buildLog = $buildLogPath
    audits = @($manifest.formalization.auditModules)
    enforcingAxiomGate = $manifest.formalization.enforcingAxiomGate
    logDirectory = $LogDirectory
} | ConvertTo-Json -Depth 5
