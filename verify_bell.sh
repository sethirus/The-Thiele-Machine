#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$REPO_ROOT"

if ! command -v coqc >/dev/null 2>&1; then
  echo "Error: coqc not found. Install Coq 8.18 or newer and ensure it is on PATH." >&2
  exit 1
fi

if ! command -v coq_makefile >/dev/null 2>&1; then
  echo "Error: coq_makefile not found. Install Coq 8.18 or newer and ensure it is on PATH." >&2
  exit 1
fi

if ! command -v python >/dev/null 2>&1; then
  echo "Error: python interpreter not found. Install Python 3.9 or newer." >&2
  exit 1
fi

export PYTHONPATH="$REPO_ROOT${PYTHONPATH:+:$PYTHONPATH}"

printf '==> Compiling Coq development\n'
make -C "$REPO_ROOT/coq" thielemachine/coqproofs/BellInequality.vo

printf '\n==> Generating Tsirelson receipts\n'
python scripts/generate_tsirelson_receipts.py examples/tsirelson_step_receipts.json

printf '\n==> Running Python Bell inequality demo\n'
python examples/bell_inequality_demo.py

printf '\n==> Verifying receipts against Coq proof\n'
"$REPO_ROOT/scripts/verify_truth.sh" "$REPO_ROOT/examples/tsirelson_step_receipts.json"

printf '\n✅ SUCCESS: Verified Bell inequality artifact\n'
