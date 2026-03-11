#!/usr/bin/env bash
# Complete CI check suite for kernel proofs
# Run this before pushing to ensure clean architecture

set -euo pipefail

echo "======================================================================"
echo " Thiele Machine Kernel - CI Checks"
echo "======================================================================"
echo ""

FAILED=0

# Check 1: No global axioms
echo "[1/2] Checking for global axioms..."
if ./scripts/check_no_axioms.sh; then
  echo "    ✓ No global axioms"
else
  echo "    ✗ Found global axioms"
  FAILED=$((FAILED + 1))
fi
echo ""

# Check 2: INQUISITOR clean
echo "[2/2] Running INQUISITOR..."
if ./scripts/check_inquisitor_clean.sh; then
  echo "    ✓ INQUISITOR clean (HIGH: 0)"
else
  echo "    ✗ INQUISITOR found HIGH priority issues"
  FAILED=$((FAILED + 1))
fi
echo ""

# Summary
echo "======================================================================"
if [ "$FAILED" -eq 0 ]; then
  echo " ✅ ALL CHECKS PASSED"
  echo "======================================================================"
  exit 0
else
  echo " ❌ $FAILED CHECK(S) FAILED"
  echo "======================================================================"
  echo ""
  echo "Fix the issues above before pushing."
  echo "See PROOF_DEBT.md for proof status and priorities."
  exit 1
fi
