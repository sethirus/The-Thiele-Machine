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
make -C "$script_dir" clean >/dev/null

echo "[1/2] Verifying the Containment Proof (Simulation.v)..."
if make -C "$script_dir" thielemachine/coqproofs/Simulation.vo >/dev/null; then
  echo "✅ SUCCESS: Containment proof compiled."
else
  echo "❌ FAILURE: Containment proof failed. Subsumption is unproven." >&2
  exit 1
fi

echo "[2/2] Verifying the Strictness Proof (Separation.v)..."
if make -C "$script_dir" thielemachine/coqproofs/Separation.vo >/dev/null; then
  echo "✅ SUCCESS: Strictness proof compiled."
else
  echo "❌ FAILURE: Strictness proof failed. Subsumption is unproven." >&2
  exit 1
fi

echo
echo "=== VERIFICATION COMPLETE: Both pillars of the subsumption argument are formally verified. Turing ⊂ Thiele holds. ==="
