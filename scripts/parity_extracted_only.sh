#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

export OCAMLRUNPARAM="${OCAMLRUNPARAM:-l=64M}"

PARITY_TEST_FILES=(
  tests/test_extracted_vm_runner.py
  tests/test_bisimulation.py
  tests/test_bisimulation_complete.py
  tests/test_rtl_compute_isomorphism.py
  tests/test_property_bisimulation.py
)

echo "[parity] enforcing extracted-RTL-only references"
for f in "${PARITY_TEST_FILES[@]}"; do
  if grep -Eq 'thiele_cpu_unified\.v|thiele_cpu_tb\.v' "$f"; then
    echo "FAIL: unified RTL reference found in parity/equivalence gate file: $f"
    grep -En 'thiele_cpu_unified\.v|thiele_cpu_tb\.v' "$f"
    exit 1
  fi
done

echo "[parity] running extracted-only parity/equivalence suite"
pytest -q \
  tests/test_extracted_vm_runner.py \
  tests/test_bisimulation.py \
  tests/test_bisimulation_complete.py \
  tests/test_rtl_compute_isomorphism.py \
  tests/test_property_bisimulation.py \
  -x --maxfail=1

echo "[parity] PASS"
