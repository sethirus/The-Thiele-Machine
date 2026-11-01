#!/usr/bin/env bash
# Verification script for active-tree assumption surfaces.

set -euo pipefail

echo "======================================"
echo " Active Coq Axiomatization Verification"
echo "======================================"
echo

cd "$(dirname "$0")"

echo "1. Building active proof tree..."
if make -j4 > /tmp/build.log 2>&1; then
    echo "   ✅ Build successful"
else
    echo "   ❌ Build failed"
    tail -20 /tmp/build.log
    exit 1
fi

echo
echo "2. Checking for admits in active Coq tree..."
ADMIT_COUNT=$( ( (grep -rnE '^\s*(Admitted\.|admit\.)' . --include='*.v' || true) | (grep -v '/patches/' || true) ) | wc -l | tr -d ' ')
if [ "$ADMIT_COUNT" -eq 0 ]; then
    echo "   ✅ No admits found"
else
    echo "   ❌ Found $ADMIT_COUNT admits"
    grep -rnE '^\s*(Admitted\.|admit\.)' . --include='*.v' | grep -v '/patches/' | head -20
    exit 1
fi

echo
echo "3. Checking explicit assumption surfaces (Axiom/Parameter/Hypothesis)..."
ASSUMPTION_COUNT=$( ( (grep -rnE "^\s*(Axiom|Parameter|Hypothesis)\s+[A-Za-z0-9_']+\s*:" . --include='*.v' || true) | (grep -v '/patches/' || true) ) | wc -l | tr -d ' ')
echo "   Found $ASSUMPTION_COUNT explicit assumption declarations"

if [ "$ASSUMPTION_COUNT" -eq 0 ]; then
    echo "   ✅ No explicit assumption declarations found"
else
    echo "   ⚠️  Non-zero assumption surface; first matches:"
    grep -rnE "^\s*(Axiom|Parameter|Hypothesis)\s+[A-Za-z0-9_']+\s*:" . --include='*.v' | grep -v '/patches/' | head -20
fi

echo
echo "======================================"
echo " Verification Complete"
echo "======================================"
echo
echo "Summary:"
echo "  - Build: ✅ Success"
echo "  - Admits: $ADMIT_COUNT (expected 0)"
echo "  - Assumption declarations: $ASSUMPTION_COUNT"
