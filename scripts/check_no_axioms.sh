#!/usr/bin/env bash
# Check that kernel files contain no global Axiom/Parameter declarations
# (except in Module Type signatures, which are allowed)

set -euo pipefail

KERNEL_DIR="${1:-coq/kernel}"

echo "Checking for global axioms in $KERNEL_DIR..."

# Find all .v files
VFILES=$(find "$KERNEL_DIR" -name "*.v" -type f)

VIOLATIONS=0

for f in $VFILES; do
  # Skip the assumption interface files (these are SUPPOSED to have Parameters)
  if [[ "$f" == *"HardAssumptions.v" ]] || [[ "$f" == *"AssumptionBundle.v" ]]; then
    echo "  SKIP: $f (assumption interface)"
    continue
  fi

  # Look for global Axiom/Parameter outside Module Type
  # This is a heuristic check - catches most cases

  # Check if file has "Axiom" or "Parameter" outside Module Type or Section
  if grep -n "^Axiom\|^Parameter" "$f" 2>/dev/null; then
    echo "  ❌ FAIL: $f has global Axiom/Parameter"
    VIOLATIONS=$((VIOLATIONS + 1))
  else
    echo "  ✓ PASS: $f"
  fi
done

if [ "$VIOLATIONS" -gt 0 ]; then
  echo ""
  echo "❌ FAILED: Found $VIOLATIONS file(s) with global axioms"
  echo ""
  echo "All assumptions must be in Section/Context or Module Type."
  echo "See AssumptionBundle.v for the proper pattern."
  exit 1
fi

echo ""
echo "✅ PASSED: No global axioms found in $KERNEL_DIR"
exit 0
