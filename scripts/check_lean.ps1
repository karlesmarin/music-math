param(
    [Parameter(Mandatory = $true)][string]$DependencyRoot,
    [string]$LeanBinary = '',
    [string]$SourceDir = '',
    [string]$BuildDir = '',
    [string[]]$Modules = @()
)

# Recompile sources against an existing cache of the pinned Mathlib/dependencies.
# Reads the external cache; writes all project artifacts under BuildDir.
$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path $PSScriptRoot -Parent
if (-not $SourceDir) { $SourceDir = Join-Path $projectRoot 'lean' }
if (-not $BuildDir) { $BuildDir = Join-Path $projectRoot '.work/checked' }
$SourceDir = (Resolve-Path -LiteralPath $SourceDir).Path
$toolchainFile = Join-Path $projectRoot 'lean-toolchain'
if (-not (Test-Path -LiteralPath $toolchainFile)) {
    $toolchainFile = Join-Path $projectRoot 'release/lean-toolchain'
}
$toolchain = (Get-Content -LiteralPath $toolchainFile -Raw).Trim()
if (-not $LeanBinary) {
    $installedName = $toolchain.Replace('/', '--').Replace(':', '---')
    $LeanBinary = Join-Path $env:USERPROFILE ".elan/toolchains/$installedName/bin/lean.exe"
}
$depPaths = @(Get-ChildItem -LiteralPath $DependencyRoot -Directory | ForEach-Object {
    Join-Path $_.FullName '.lake/build/lib/lean'
})
New-Item -ItemType Directory -Path $BuildDir -Force | Out-Null
$BuildDir = (Resolve-Path -LiteralPath $BuildDir).Path
$env:LEAN_PATH = (@($BuildDir) + $depPaths) -join [IO.Path]::PathSeparator
$sources = @{}
Get-ChildItem -LiteralPath $SourceDir -Filter '*.lean' | Where-Object { $_.BaseName -ne 'Probe' } |
    ForEach-Object { $sources[$_.BaseName] = $_.FullName }
if ($Modules.Count -eq 0) { $Modules = @($sources.Keys | Sort-Object) }
$order = [Collections.Generic.List[string]]::new()
$visited = @{}
function Visit-Module([string]$moduleName) {
    if ($visited.ContainsKey($moduleName)) { return }
    if (-not $sources.ContainsKey($moduleName)) { throw "Unknown local module: $moduleName" }
    $visited[$moduleName] = $true
    $sourceText = Get-Content -LiteralPath $sources[$moduleName] -Raw
    foreach ($match in [regex]::Matches($sourceText, '(?m)^import\s+([^\r\n]+)')) {
        foreach ($dependency in ($match.Groups[1].Value -split '\s+')) {
            if ($sources.ContainsKey($dependency)) { Visit-Module $dependency }
        }
    }
    $order.Add($moduleName)
}
foreach ($moduleName in $Modules) { Visit-Module $moduleName }
$records = [Collections.Generic.List[object]]::new()
foreach ($moduleName in $order) {
    $sourceFile = $sources[$moduleName]
    $outputFile = Join-Path $BuildDir "$moduleName.olean"
    $logFile = Join-Path $BuildDir "$moduleName.log"
    $started = Get-Date
    $lines = @(& $LeanBinary "--root=$SourceDir" '-DautoImplicit=false' '-DrelaxedAutoImplicit=false' '-o' $outputFile $sourceFile 2>&1)
    $exitCode = $LASTEXITCODE
    $log = ($lines | ForEach-Object { $_.ToString() }) -join "`n"
    Set-Content -LiteralPath $logFile -Value $log -Encoding utf8
    $axioms = @([regex]::Matches($log, "(?s)'([^']+)' depends on axioms:\s*\[([^\]]*)\]") | ForEach-Object {
        [ordered]@{ declaration = $_.Groups[1].Value; axioms = @($_.Groups[2].Value -split ',' | ForEach-Object { $_.Trim() }) }
    })
    # Git can normalize CRLF to LF; retain both the actual compiler-input hash
    # and the hash of the same UTF-8 bytes with only CRLF replaced by LF.
    $sourceBytes = [IO.File]::ReadAllBytes($sourceFile)
    $lfBytes = [Text.Encoding]::UTF8.GetBytes(
        [Text.Encoding]::UTF8.GetString($sourceBytes).Replace("`r`n", "`n"))
    $hashAlgorithm = [Security.Cryptography.SHA256]::Create()
    $lfHash = [BitConverter]::ToString($hashAlgorithm.ComputeHash($lfBytes)).Replace('-', '').ToLowerInvariant()
    $hashAlgorithm.Dispose()
    $records.Add([ordered]@{
        module = $moduleName
        source_sha256 = (Get-FileHash -LiteralPath $sourceFile -Algorithm SHA256).Hash.ToLower()
        source_lf_sha256 = $lfHash
        exit_code = $exitCode
        seconds = [math]::Round(((Get-Date) - $started).TotalSeconds, 2)
        axiom_reports = $axioms
        log_file = "$moduleName.log"
    })
    Write-Output "$moduleName : exit $exitCode"
    if ($exitCode -ne 0 -or $log.Contains('sorryAx')) {
        Write-Output $log
        throw "Failed compilation or sorryAx: $moduleName"
    }
}
$mathlibDir = (Resolve-Path -LiteralPath (Join-Path $DependencyRoot 'mathlib')).Path
$mathlibRev = (& git -c "safe.directory=$mathlibDir" -C $mathlibDir rev-parse HEAD).Trim()
if ($LASTEXITCODE -ne 0) { throw 'Cannot record the dependency revision' }
$report = [ordered]@{
    generated_utc = [DateTime]::UtcNow.ToString('o')
    lean_toolchain = $toolchain
    mathlib_revision = $mathlibRev
    options = @('autoImplicit=false', 'relaxedAutoImplicit=false')
    method = 'Direct Lean compilation in dependency order using an existing external dependency cache; not a fresh Lake dependency download'
    source_hash_convention = 'source_sha256 hashes the exact compiler input; source_lf_sha256 normalizes CRLF to LF for comparison with Git blobs'
    modules = @($records.ToArray())
}
$report | ConvertTo-Json -Depth 12 | Set-Content -LiteralPath (Join-Path $BuildDir 'build_report.json') -Encoding utf8
Write-Output "Report: $(Join-Path $BuildDir 'build_report.json')"
