#!/usr/bin/env bash
# Canonical two-pillar verification for the Thiele subsumption claim.
set -euo pipefail
shopt -s inherit_errexit 2>/dev/null || true

script_dir="$(cd "$(dirname "$0")" && pwd)"

if ! command -v make >/dev/null 2>&1; then
  echo "[verify_subsumption] error: make not found on PATH" >&2
  exit 2
fi

if ! command -v coq_makefile >/dev/null 2>&1 || ! command -v coqc >/dev/null 2>&1; then
  echo "❌ FAILURE: Coq toolchain not found. Please install Coq (coq_makefile, coqc) and ensure it is on your PATH." >&2
  exit 2
fi

echo "=== CANONICAL SUBSUMPTION VERIFICATION ==="
echo "Building Coq project in $script_dir"

make -C "$script_dir" clean
make -C "$script_dir"

echo "✅ Coq project built successfully."
