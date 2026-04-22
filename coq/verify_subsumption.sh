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
echo "Building current subsumption/separation files in active tree"

(
  cd "$script_dir"
  make kernel/Subsumption.vo kernel/TuringStrictness.vo
)

echo "✅ Subsumption and strictness lemmas rebuilt successfully."
