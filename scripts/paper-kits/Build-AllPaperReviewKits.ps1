[CmdletBinding()]
param(
    [Parameter(Mandatory)]
    [string] $OutputDirectory,

    [Parameter(Mandatory)]
    [ValidatePattern('^[A-Za-z0-9._-]+$')]
    [string] $ReleaseTag,

    [string] $RepositoryRoot = '',

    [switch] $AllowDirty
)

$ErrorActionPreference = 'Stop'
if (-not $RepositoryRoot) {
    $RepositoryRoot = Join-Path $PSScriptRoot '../..'
}
$RepositoryRoot = [IO.Path]::GetFullPath($RepositoryRoot)
$OutputDirectory = [IO.Path]::GetFullPath($OutputDirectory)
if (-not (Test-Path -LiteralPath $OutputDirectory -PathType Container)) {
    [void] (New-Item -ItemType Directory -Path $OutputDirectory -Force)
}

$manifests = @(
    Get-ChildItem -LiteralPath (Join-Path $RepositoryRoot 'papers') -Directory |
        Where-Object { Test-Path -LiteralPath (Join-Path $_.FullName 'paper.json') } |
        Sort-Object Name
)
if ($manifests.Count -eq 0) {
    throw 'No paper manifests were discovered.'
}

$results = @()
foreach ($directory in $manifests) {
    $arguments = @{
        Paper = $directory.Name
        OutputDirectory = $OutputDirectory
        ReleaseTag = $ReleaseTag
        RepositoryRoot = $RepositoryRoot
    }
    if ($AllowDirty) {
        $arguments.AllowDirty = $true
    }
    $json = & (Join-Path $PSScriptRoot 'Build-PaperReviewKit.ps1') @arguments
    if ($LASTEXITCODE -ne 0) {
        throw "Review Kit generation failed for $($directory.Name)."
    }
    $results += ($json | ConvertFrom-Json)
}

$checksumLines = foreach ($result in $results | Sort-Object archive) {
    "$($result.archiveSha256)  $([IO.Path]::GetFileName($result.archive))"
}
$checksumPath = Join-Path $OutputDirectory "BongTheory-$ReleaseTag-paper-review-kits-SHA256SUMS.txt"
[IO.File]::WriteAllText(
    $checksumPath,
    ($checksumLines -join "`n") + "`n",
    [Text.UTF8Encoding]::new($false)
)

[pscustomobject]@{
    releaseTag = $ReleaseTag
    sourceCommit = $results[0].sourceCommit
    sourceTreeState = $results[0].sourceTreeState
    papers = @($results)
    checksumFile = $checksumPath
    checksumFileSha256 = (Get-FileHash -LiteralPath $checksumPath -Algorithm SHA256).Hash
} | ConvertTo-Json -Depth 8
