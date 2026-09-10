#!/usr/bin/env bash
# Verification script for current Thiele/Turing separation claims.

set -euo pipefail

echo "=========================================="
echo " Thiele Machine Separation Verification"
echo "=========================================="
echo

cd "$(dirname "$0")"

echo "1. Building separation-related proof files..."
if make kernel/foundation/Subsumption.vo kernel/foundation/TuringStrictness.vo > /tmp/separation_build.log 2>&1; then
    echo "   ✅ Build successful"
else
    echo "   ❌ Build failed"
    tail -20 /tmp/separation_build.log
    exit 1
fi

echo
echo "2. Checking for admits in separation files..."
# The files must exist before we can conclude anything from a grep over them.
# Without this guard `grep ... || true` swallows "No such file or directory",
# wc -l reports 0, and the script prints "No admits found". That is a green
# result produced by a grep that never ran, which is the exact failure mode
# this script exists to catch. Check existence explicitly and hard-fail.
SEPARATION_FILES=(kernel/foundation/Subsumption.v kernel/foundation/TuringStrictness.v)
for f in "${SEPARATION_FILES[@]}"; do
    if [ ! -f "$f" ]; then
        echo "   ❌ Expected separation source missing: $f"
        echo "      (Refusing to report 'no admits' from a grep over a file that does not exist.)"
        exit 1
    fi
done
ADMIT_COUNT=$( (grep -nE '^\s*(Admitted\.|admit\.)' "${SEPARATION_FILES[@]}" || true) | wc -l | tr -d ' ')
if [ "$ADMIT_COUNT" -eq 0 ]; then
    echo "   ✅ No admits found"
else
    echo "   ❌ Found $ADMIT_COUNT admits"
    grep -nE '^\s*(Admitted\.|admit\.)' "${SEPARATION_FILES[@]}"
    exit 1
fi

echo
echo "3. Listing top-level theorem declarations..."
echo
grep -E "^Theorem " "${SEPARATION_FILES[@]}" | while read line; do
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
echo "  - Main Result Files: ✅ ${SEPARATION_FILES[*]}"
echo
echo "For broader status, run: make coq-gate"
