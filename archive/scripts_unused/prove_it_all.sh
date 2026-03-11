#!/bin/bash
# Orchestrate the empirical → formal bridge for the graph-colouring demo.
set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)"
OUTPUT_DIR="${PROJECT_ROOT}/graph_demo_output"
ACT_DIR="${OUTPUT_DIR}/triadic_cascade/act_iii"
GENERATED_V="${PROJECT_ROOT}/coq/sandboxes/GeneratedProof.v"

printf '=== Integrated Verification Pipeline ===\n'
printf '[1/3] Running graph_coloring_demo.py to regenerate receipts...\n'
python "${PROJECT_ROOT}/scripts/graph_coloring_demo.py" --output-dir "${OUTPUT_DIR}" >/tmp/graph_demo.log
printf '    receipts written to %s\n' "$OUTPUT_DIR"

if [ ! -d "$ACT_DIR" ]; then
  printf 'FATAL: expected Act III receipts at %s\n' "$ACT_DIR" >&2
  exit 1
fi

printf '[2/3] Translating receipts into a Coq development...\n'
python "${PROJECT_ROOT}/scripts/translate_receipts_to_coq.py" "$ACT_DIR" --output "$GENERATED_V"

printf '[3/3] Mechanically verifying the generated proof...\n'
coqc -q -Q "${PROJECT_ROOT}/coq/sandboxes" Sandbox "${PROJECT_ROOT}/coq/sandboxes/VerifiedGraphSolver.v"
coqc -q -Q "${PROJECT_ROOT}/coq/sandboxes" Sandbox "$GENERATED_V"

printf '\nSUCCESS: Python execution and Coq microcosm are now linked.\n'
