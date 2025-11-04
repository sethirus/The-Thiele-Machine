#!/usr/bin/env bash
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

set -euo pipefail

# Navigate to the repository root
# This works whether the script is called directly or via symlink
SCRIPT_PATH="${BASH_SOURCE[0]}"
# Resolve symlinks to get the actual script location
while [ -L "$SCRIPT_PATH" ]; do
  SCRIPT_DIR="$(cd "$(dirname "$SCRIPT_PATH")" && pwd)"
  SCRIPT_PATH="$(readlink "$SCRIPT_PATH")"
  # If the symlink is relative, make it absolute
  [[ "$SCRIPT_PATH" != /* ]] && SCRIPT_PATH="$SCRIPT_DIR/$SCRIPT_PATH"
done
SCRIPT_DIR="$(cd "$(dirname "$SCRIPT_PATH")" && pwd)"
# The script is in scripts/verification/, so go up two levels
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
cd "$REPO_ROOT"

if [ -f "$REPO_ROOT/.coq-env" ]; then
  # shellcheck disable=SC1090
  source "$REPO_ROOT/.coq-env"
fi

if ! command -v coqc >/dev/null 2>&1; then
  echo "Coq compiler not found; installing via apt" >&2
  sudo apt-get update && sudo apt-get install -y coq
fi

if ! command -v coqc >/dev/null 2>&1; then
  echo "Error: coqc not found. Install Coq 8.18 or newer and ensure it is on PATH." >&2
  exit 1
fi

if ! command -v coq_makefile >/dev/null 2>&1; then
  echo "Error: coq_makefile not found. Ensure the Coq toolchain is installed (try scripts/setup_coq_toolchain.sh)." >&2
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
python demos/verification-demos/bell-inequality/bell_inequality_demo.py

printf '\n==> Verifying receipts against Coq proof\n'
"$REPO_ROOT/scripts/verify_truth.sh" "$REPO_ROOT/examples/tsirelson_step_receipts.json"

printf '\n✅ SUCCESS: Verified Bell inequality artifact\n'
