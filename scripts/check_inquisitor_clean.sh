#!/usr/bin/env bash
# Verify INQUISITOR reports 0 HIGH priority issues

set -euo pipefail

echo "Running INQUISITOR..."
python3 scripts/inquisitor.py > INQUISITOR_REPORT.md 2>&1

# Extract HIGH count
HIGH_COUNT=$(grep "^- HIGH:" INQUISITOR_REPORT.md | awk '{print $3}')

echo "INQUISITOR Results:"
grep "^- HIGH:\|^- MEDIUM:\|^- LOW:" INQUISITOR_REPORT.md

if [ "$HIGH_COUNT" != "0" ]; then
  echo ""
  echo "❌ FAILED: INQUISITOR found $HIGH_COUNT HIGH priority issues"
  echo ""
  echo "HIGH priority issues are FORBIDDEN:"
  echo "  - Axiom/Parameter (must be in Section/Context)"
  echo "  - Admitted proofs"
  echo "  - admit tactics"
  echo "  - give_up tactics"
  echo ""
  echo "See INQUISITOR_REPORT.md for details."
  exit 1
fi

echo ""
echo "✅ PASSED: INQUISITOR clean (HIGH: 0)"
exit 0
