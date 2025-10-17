$ErrorActionPreference = 'Stop'

function Get-CoqcPath {
    param()
    if ($env:COQC) {
        $candidate = Resolve-Path -Path $env:COQC -ErrorAction SilentlyContinue
        if ($candidate) {
            return $candidate.Path
        }
        Write-Warning "COQC environment variable points to a missing executable: $($env:COQC)"
    }

    $coqc = Get-Command coqc -ErrorAction SilentlyContinue
    if ($null -ne $coqc) {
        return $coqc.Source
    }

    throw "Unable to locate coqc. Ensure Coq is installed and coqc is on PATH or set the COQC environment variable."
}

$coqcPath = Get-CoqcPath
$coqDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$repoRoot = Resolve-Path (Join-Path $coqDir "..")

# Discover the Coq standard library root using `coqc -where`
$coqStdlib = (& $coqcPath '-where').Trim()

$coqArgs = @('-q')
if ($coqStdlib) {
    $coqArgs += @('-R', $coqStdlib, 'Coq')
}

$coqArgs += @(
    '-R', (Join-Path $coqDir 'thielemachine/coqproofs'), 'ThieleMachine',
    '-R', (Join-Path $coqDir 'thieleuniversal/coqproofs'), 'ThieleUniversal',
    '-R', (Join-Path $coqDir 'catnet/coqproofs'), 'CatNet',
    '-R', (Join-Path $coqDir 'isomorphism/coqproofs'), 'Isomorphism',
    '-R', (Join-Path $coqDir 'p_equals_np_thiele'), 'P_equals_NP_Thiele',
    '-R', (Join-Path $coqDir 'project_cerberus/coqproofs'), 'ProjectCerberus',
    '-R', (Join-Path $coqDir 'test_vscoq/coqproofs'), 'TestVSCoq',
    '-R', (Join-Path $coqDir 'modular_proofs'), 'ThieleMachine.Modular_Proofs',
    '-R', (Join-Path $coqDir 'sandboxes'), 'Sandbox'
)

$target = Join-Path $coqDir 'thielemachine/coqproofs/Simulation.v'

Push-Location $coqDir
try {
    & $coqcPath @coqArgs $target
} finally {
    Pop-Location
}
