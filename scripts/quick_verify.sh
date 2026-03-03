#!/usr/bin/env bash
# Quick verification script for local development
# Runs Coq + Inquisitor + Python tests (proof + extraction layers only)
#
# Usage:
#   ./scripts/quick_verify.sh          # Run fast checks only
#   ./scripts/quick_verify.sh full     # Include hardware synthesis
#   ./scripts/quick_verify.sh hw-only  # Hardware synthesis only

set -euo pipefail

SCRIPT_PATH="$(readlink -f "${BASH_SOURCE[0]}")"
ROOT="$(cd "$(dirname "$SCRIPT_PATH")/.." && pwd)"

phase() {
  printf "\n[%s] %s\n" "$1" "$2"
}

die() {
  echo "error: $*" >&2
  exit 1
}

cd "$ROOT"

# Parse arguments
MODE="${1:-fast}"
if [[ ! "$MODE" =~ ^(fast|full|hw-only)$ ]]; then
  echo "Usage: $0 [fast|full|hw-only]"
  echo "  fast    - Coq + Inquisitor + Python tests (default)"
  echo "  full    - fast + hardware synthesis"
  echo "  hw-only - Hardware synthesis only (assumes fast checks already passed)"
  exit 1
fi

if [[ "$MODE" =~ ^(fast|full)$ ]]; then
  phase "COQBUILD" "Building Coq proof tree"
  cd coq
  if [ -f Makefile.coq ]; then
    make -j4 clean || true
  fi
  coq_makefile -f _CoqProject -o Makefile.coq 2>&1 | grep -v "Warning:" || true
  make -j4 -f Makefile.coq || die "Coq build failed"
  cd "$ROOT"

  phase "INQUISITOR" "Running proof audit"
  python3 scripts/inquisitor.py --report INQUISITOR_REPORT.md || die "Inquisitor found issues"

  phase "EXTRACT" "Extracting Coq to OCaml"
  make -C coq Extraction.vo || die "Extraction failed"
  ocamlfind ocamlc -I build -package str -linkpkg -o build/extracted_vm_runner \
    build/thiele_core.mli build/thiele_core.ml tools/extracted_vm_runner.ml || \
    die "OCaml compilation failed"

  phase "BISIM" "Running 3-layer bisimulation tests"
  bash scripts/parity_extracted_only.sh || die "3-layer bisimulation failed"

  phase "PYTEST" "Running Python tests"
  python3 -m pip install --quiet --upgrade pip
  pip install --quiet -r requirements.txt
  pip install --quiet -e . --no-deps
  python3 -m pytest tests/ -q -m "not coq" || die "Python tests failed"

  if [[ "$MODE" == "fast" ]]; then
    phase "SUCCESS" "Fast verification passed ✓"
    echo "To run full verification (including hardware): $0 full"
    exit 0
  fi
fi

if [[ "$MODE" =~ ^(full|hw-only)$ ]]; then
  phase "FORGE" "Running hardware forge pipeline"
  bash scripts/forge_artifact.sh || die "Forge pipeline failed"

  phase "SYNTHESIS" "Synthesizing with Yosys"
  yosys -p "read_verilog -sv -DSYNTHESIS thielecpu/hardware/rtl/thiele_cpu_kami.v; prep -top mkModule1; check; stat" > build/synthesis.log 2>&1 || \
    die "Yosys synthesis failed (see build/synthesis.log)"

  if ! grep -q "Number of cells:" build/synthesis.log; then
    die "Synthesis validation failed - no cell count in output"
  fi

  phase "SIMULATE" "Simulating hardware"
  vvp build/thiele_cpu_tb.out +VCD=build/thiele_cpu_tb.vcd > build/simulation.log 2>&1 || \
    die "Simulation failed (see build/simulation.log)"

  if ! grep -q "Test completed" build/simulation.log; then
    die "Simulation validation failed - no 'Test completed' marker"
  fi

  phase "ANALYZE" "Analyzing waveforms"
  python3 scripts/analyze_waveforms.py build/thiele_cpu_tb.vcd > build/waveform_analysis.txt || \
    die "Waveform analysis failed"

  phase "REPRO" "Reproducible synthesis gate"
  bash scripts/synthesis_repro_gate.sh || die "Reprodicible synthesis gate failed"

  phase "SUCCESS" "Full verification passed ✓"
  echo "Logs available in:"
  echo "  - build/synthesis.log"
  echo "  - build/simulation.log"
  echo "  - build/waveform_analysis.txt"
  exit 0
fi
