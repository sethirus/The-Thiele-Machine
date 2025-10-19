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
echo "This workflow has been retired. The attempted universal proof now lives under" >&2
echo "archive/research/incomplete_subsumption_proof/ with a README explaining the" >&2
echo "type-mismatch barrier. The live formal artefacts are the sandbox microcosms" >&2
echo "(`ToyThieleMachine.v`, `VerifiedGraphSolver.v`) plus the receipts bridge" >&2
echo "emitted by scripts/prove_it_all.sh." >&2
exit 1
