#!/usr/bin/env bash
set -euo pipefail

# One-command runner for the thesis thermodynamic falsifiability dataset.
# Intended for AWS EC2 with Session Manager (no SSH keys).

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

OUT_BASE="${OUT_BASE:-results/aws_falsifiability_bundle}"
STAMP="$(date -u +%Y%m%dT%H%M%SZ)"
OUT_DIR="$OUT_BASE/$STAMP"

ENERGY_MODE="${ENERGY_MODE:-rapl}"               # rapl|none
ENERGY_REPS="${ENERGY_REPS:-20000}"
EVIDENCE_STRICT="${EVIDENCE_STRICT:-1}"
THERMO_TEMPERATURE_K="${THERMO_TEMPERATURE_K:-300}"
RUN_EQUIVALENCE="${RUN_EQUIVALENCE:-0}"         # 1 to run cross-layer RTL sanity check
CPU_PIN="${CPU_PIN:-0}"                         # used if RUN_EQUIVALENCE=1 and taskset exists

mkdir -p "$OUT_DIR"

echo "[1/6] Environment"
uname -a | tee "$OUT_DIR/uname.txt"
( command -v lscpu >/dev/null 2>&1 && lscpu | tee "$OUT_DIR/lscpu.txt" ) || true

echo "[2/6] RAPL check (best-effort)"
if ls /sys/class/powercap/intel-rapl:*/energy_uj >/dev/null 2>&1; then
  ls -1 /sys/class/powercap/intel-rapl:*/energy_uj | tee "$OUT_DIR/rapl_paths.txt"
  cat /sys/class/powercap/intel-rapl:*/energy_uj | tee "$OUT_DIR/rapl_energy_before_uj.txt"
else
  echo "RAPL not present on this host" | tee "$OUT_DIR/rapl_missing.txt"
  if [[ "$ENERGY_MODE" == "rapl" ]]; then
    echo "ENERGY_MODE=rapl requested but RAPL missing; set ENERGY_MODE=none to continue." | tee "$OUT_DIR/error.txt"
    exit 2
  fi
fi

echo "[3/6] Python environment"
if [[ ! -d .venv ]]; then
  python3 -m venv .venv
fi
# shellcheck disable=SC1091
source .venv/bin/activate
python -V | tee "$OUT_DIR/python_version.txt"

echo "[4/6] Dependencies"
python -m pip install -U pip >/dev/null
python -m pip install -r requirements.txt | tee "$OUT_DIR/pip_install.log"

echo "[5/7] (Optional) Equivalence bundle (cross-layer CPU sanity)"
if [[ "$RUN_EQUIVALENCE" == "1" ]]; then
  export EVIDENCE_STRICT="$EVIDENCE_STRICT"
  if command -v taskset >/dev/null 2>&1; then
    taskset -c "$CPU_PIN" python scripts/equivalence_bundle.py --out "$OUT_DIR/equivalence_bundle.json" | tee "$OUT_DIR/equivalence_bundle.log"
  else
    python scripts/equivalence_bundle.py --out "$OUT_DIR/equivalence_bundle.json" | tee "$OUT_DIR/equivalence_bundle.log"
  fi
else
  echo "Skipping equivalence bundle (set RUN_EQUIVALENCE=1 to enable)." | tee "$OUT_DIR/equivalence_bundle_skipped.txt"
fi

echo "[6/7] Run thermo experiment"
export EVIDENCE_STRICT="$EVIDENCE_STRICT"
export THERMO_TEMPERATURE_K="$THERMO_TEMPERATURE_K"
python scripts/thermo_experiment.py \
  --measure-energy "$ENERGY_MODE" \
  --energy-repetitions "$ENERGY_REPS" \
  --out "$OUT_DIR/thermo_energy.json" | tee "$OUT_DIR/thermo_run.log"

echo "[7/7] Analyze"
python scripts/analyze_thermo_energy.py "$OUT_DIR/thermo_energy.json" | tee "$OUT_DIR/analysis.txt"

echo "Wrote bundle: $OUT_DIR"
