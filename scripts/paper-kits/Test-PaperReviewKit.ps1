[CmdletBinding()]
param(
    [Parameter(Mandatory)]
    [string] $Archive,

    [Parameter(Mandatory)]
    [string] $ExtractionDirectory,

    [switch] $StructureOnly,

    [switch] $AllowDirtyKit,

    [string] $LogDirectory = ''
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
if ($manifest.schemaVersion -ne 1) {
    throw 'Unsupported Review Kit manifest schema.'
}
if ($manifest.provenance.sourceTreeState -ne 'clean' -and -not $AllowDirtyKit) {
    throw 'Review Kit was generated from a dirty source tree.'
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
            $_.Extension -in @('.olean', '.ilean') -or
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

Push-Location $ExtractionDirectory
try {
    & $lake build
    if ($LASTEXITCODE -ne 0) {
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
    }
} finally {
    Pop-Location
}

[pscustomobject]@{
    paper = $manifest.paper.id
    sourceCommit = $manifest.provenance.sourceCommit
    sourceTreeState = $manifest.provenance.sourceTreeState
    verifiedFileCount = $listed.Count
    structure = 'verified'
    build = 'passed'
    audits = @($manifest.formalization.auditModules)
    logDirectory = $LogDirectory
} | ConvertTo-Json -Depth 5
