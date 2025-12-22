#!/usr/bin/env bash
set -euo pipefail

# One script to produce the thesis falsifiability dataset + supporting evidence.
#
# What it does:
# - (Optional) installs OS prerequisites (Ubuntu/Debian)
# - creates/uses .venv and installs Python requirements
# - checks for Intel RAPL counters (if ENERGY_MODE=rapl)
# - runs focused verification tests
# - runs equivalence bundle (cross-layer Python ↔ extracted ↔ RTL)
# - runs thermodynamic bridge experiment (energy vs μ)
# - runs analyzer and writes a timestamped results bundle
#
# Safe defaults:
# - ENERGY_MODE=rapl (fails fast if RAPL missing)
# - ENERGY_REPS=20000 (adjust upward if energy signal is noisy)
# - EVIDENCE_STRICT=1 (fail closed if any runner emits μ=0/None)

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

OUT_BASE="${OUT_BASE:-results/falsifiability_bundle}"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
OUT_DIR="$OUT_BASE/$STAMP"

ENERGY_MODE="${ENERGY_MODE:-rapl}"               # rapl|none
ENERGY_REPS="${ENERGY_REPS:-20000}"
EVIDENCE_STRICT="${EVIDENCE_STRICT:-1}"
ALLOW_MU_NORMALIZE="${ALLOW_MU_NORMALIZE:-0}"
THERMO_TEMPERATURE_K="${THERMO_TEMPERATURE_K:-300}"
CPU_PIN="${CPU_PIN:-0}"
INSTALL_OS_DEPS="${INSTALL_OS_DEPS:-0}"

mkdir -p "$OUT_DIR"

echo "[0/8] Bundle directory: $OUT_DIR"

echo "[1/8] Host snapshot"
uname -a | tee "$OUT_DIR/uname.txt"
( command -v lscpu >/dev/null 2>&1 && lscpu | tee "$OUT_DIR/lscpu.txt" ) || true
( command -v free  >/dev/null 2>&1 && free -h | tee "$OUT_DIR/mem.txt" ) || true

# Best-effort AWS IMDS probe (works only on EC2).
IMDS_BASE="http://169.254.169.254/latest"
if command -v curl >/dev/null 2>&1; then
  curl -fsS --max-time 1 "$IMDS_BASE/meta-data/instance-id" >"$OUT_DIR/aws_instance_id.txt" 2>/dev/null || true
  curl -fsS --max-time 1 "$IMDS_BASE/meta-data/instance-type" >"$OUT_DIR/aws_instance_type.txt" 2>/dev/null || true
  curl -fsS --max-time 1 "$IMDS_BASE/meta-data/placement/region" >"$OUT_DIR/aws_region.txt" 2>/dev/null || true
fi

echo "[2/8] (Optional) OS deps"
if [[ "$INSTALL_OS_DEPS" == "1" ]]; then
  if command -v apt-get >/dev/null 2>&1; then
    sudo apt-get update | tee "$OUT_DIR/apt_update.log"
    sudo apt-get install -y git python3-venv python3-dev build-essential iverilog yosys | tee "$OUT_DIR/apt_install.log"
  else
    echo "INSTALL_OS_DEPS=1 requested but apt-get not found" | tee "$OUT_DIR/os_deps_error.txt"
    exit 2
  fi
else
  echo "Skipping OS deps install (set INSTALL_OS_DEPS=1 to enable)." | tee "$OUT_DIR/os_deps_skipped.txt"
fi

echo "[3/8] Python venv + requirements"
if [[ ! -d .venv ]]; then
  python3 -m venv .venv
fi
# shellcheck disable=SC1091
source .venv/bin/activate
python -V | tee "$OUT_DIR/python_version.txt"
python -m pip install -U pip >/dev/null
python -m pip install -r requirements.txt | tee "$OUT_DIR/pip_install.log"

echo "[4/8] RAPL check"
if ls /sys/class/powercap/intel-rapl:*/energy_uj >/dev/null 2>&1; then
  ls -1 /sys/class/powercap/intel-rapl:*/energy_uj | tee "$OUT_DIR/rapl_paths.txt"
  cat /sys/class/powercap/intel-rapl:*/energy_uj | tee "$OUT_DIR/rapl_energy_before_uj.txt"
else
  echo "RAPL not present on this host" | tee "$OUT_DIR/rapl_missing.txt"
  if [[ "$ENERGY_MODE" == "rapl" ]]; then
    echo "ENERGY_MODE=rapl requested but RAPL missing; set ENERGY_MODE=none to continue (μ-only)." | tee "$OUT_DIR/error.txt"
    exit 3
  fi
fi

echo "[5/8] Focused verification tests"
python -m pytest -q tests/test_thermo_experiment.py | tee "$OUT_DIR/test_thermo_experiment.log"
python -m pytest -q tests/test_equivalence_bundle.py | tee "$OUT_DIR/test_equivalence_bundle.log" || true


echo "[6/8] Equivalence bundle (cross-layer CPU sanity)"
export EVIDENCE_STRICT="$EVIDENCE_STRICT"
export ALLOW_MU_NORMALIZE="$ALLOW_MU_NORMALIZE"
# Pinning helps reduce noise and makes energy runs steadier on shared hosts.
if command -v taskset >/dev/null 2>&1; then
  taskset -c "$CPU_PIN" python scripts/equivalence_bundle.py --out "$OUT_DIR/equivalence_bundle.json" | tee "$OUT_DIR/equivalence_bundle.log"
else
  python scripts/equivalence_bundle.py --out "$OUT_DIR/equivalence_bundle.json" | tee "$OUT_DIR/equivalence_bundle.log"
fi

echo "[7/8] Thermodynamic bridge dataset (energy vs μ)"
export THERMO_TEMPERATURE_K="$THERMO_TEMPERATURE_K"
if command -v taskset >/dev/null 2>&1; then
  taskset -c "$CPU_PIN" python scripts/thermo_experiment.py \
    --measure-energy "$ENERGY_MODE" \
    --energy-repetitions "$ENERGY_REPS" \
    --out "$OUT_DIR/thermo_energy.json" | tee "$OUT_DIR/thermo_run.log"
else
  python scripts/thermo_experiment.py \
    --measure-energy "$ENERGY_MODE" \
    --energy-repetitions "$ENERGY_REPS" \
    --out "$OUT_DIR/thermo_energy.json" | tee "$OUT_DIR/thermo_run.log"
fi
python scripts/analyze_thermo_energy.py "$OUT_DIR/thermo_energy.json" | tee "$OUT_DIR/analysis.txt"

echo "[8/8] Package bundle"
( cd "$OUT_BASE" && tar -czf "${STAMP}.tar.gz" "$STAMP" )
echo "Bundle directory: $OUT_DIR"
echo "Bundle archive:   $OUT_BASE/${STAMP}.tar.gz"

echo "Done. If this was an AWS instance, terminate it to stop costs."
