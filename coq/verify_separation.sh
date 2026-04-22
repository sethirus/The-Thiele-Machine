#!/usr/bin/env bash
# Verification script for current Thiele/Turing separation claims.

set -euo pipefail

echo "=========================================="
echo " Thiele Machine Separation Verification"
echo "=========================================="
echo

cd "$(dirname "$0")"

echo "1. Building separation-related proof files..."
if make kernel/Subsumption.vo kernel/TuringStrictness.vo > /tmp/separation_build.log 2>&1; then
    echo "   ✅ Build successful"
else
    echo "   ❌ Build failed"
    tail -20 /tmp/separation_build.log
    exit 1
fi

echo
echo "2. Checking for admits in separation files..."
ADMIT_COUNT=$( (grep -nE '^\s*(Admitted\.|admit\.)' kernel/Subsumption.v kernel/TuringStrictness.v || true) | wc -l | tr -d ' ')
if [ "$ADMIT_COUNT" -eq 0 ]; then
    echo "   ✅ No admits found"
else
    echo "   ❌ Found $ADMIT_COUNT admits"
    grep -nE '^\s*(Admitted\.|admit\.)' kernel/Subsumption.v kernel/TuringStrictness.v
    exit 1
fi

echo
echo "3. Listing top-level theorem declarations..."
echo
grep -E "^Theorem " kernel/Subsumption.v kernel/TuringStrictness.v | while read line; do
    echo "   ✅ $line"
done

echo
echo "=========================================="
echo " Verification Complete"
echo "=========================================="
echo
echo "Summary:"
echo "  - Build: ✅ Success"
echo "  - Admits: $ADMIT_COUNT (none)"
echo "  - Main Result Files: ✅ kernel/Subsumption.v, kernel/TuringStrictness.v"
echo
echo "For broader status, run: make coq-gate"
