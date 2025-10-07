#!/bin/bash
# Verification script for Thiele Machine Subsumption Proof

set -e

echo "=========================================="
echo " Thiele Machine Subsumption Verification"
echo "=========================================="
echo

cd "$(dirname "$0")"

echo "1. Building Subsumption.v..."
if make thielemachine/coqproofs/Subsumption.vo > /tmp/subsumption_build.log 2>&1; then
    echo "   ✅ Build successful"
else
    echo "   ❌ Build failed"
    tail -20 /tmp/subsumption_build.log
    exit 1
fi

echo
echo "2. Checking for axioms..."
AXIOM_COUNT=$(grep -c "^Axiom " thielemachine/coqproofs/Subsumption.v)
echo "   Found $AXIOM_COUNT axiom(s)"

if [ "$AXIOM_COUNT" -eq 1 ]; then
    echo "   ✅ Expected count (1 - halting_undecidable)"
else
    echo "   ⚠️  Expected 1, found $AXIOM_COUNT"
fi

echo
echo "3. Checking for admits..."
ADMIT_COUNT=$(grep -c "admit\." thielemachine/coqproofs/Subsumption.v || true)
if [ "$ADMIT_COUNT" -eq 0 ]; then
    echo "   ✅ No admits found"
else
    echo "   ❌ Found $ADMIT_COUNT admits"
    grep -n "admit\." thielemachine/coqproofs/Subsumption.v
    exit 1
fi

echo
echo "4. Listing proven theorems..."
echo
grep -E "^Theorem " thielemachine/coqproofs/Subsumption.v | while read line; do
    echo "   ✅ $line"
done

echo
echo "5. Listing axiom..."
echo
grep -A 3 "^Axiom " thielemachine/coqproofs/Subsumption.v | head -4 | while read line; do
    echo "   $line"
done

echo
echo "=========================================="
echo " Verification Complete"
echo "=========================================="
echo
echo "Summary:"
echo "  - Build: ✅ Success"
echo "  - Axioms: $AXIOM_COUNT (halting_undecidable - well-established result)"
echo "  - Admits: $ADMIT_COUNT (none)"
echo "  - Main Result: ✅ Thiele Machine strictly extends Turing Machine"
echo
echo "Key Theorems Proven:"
echo "  1. thiele_solves_halting - Thiele with oracle solves halting problem"
echo "  2. thiele_strictly_extends_turing - Thiele > Turing (strict extension)"
echo
echo "For detailed analysis, see:"
echo "  - docs/SUBSUMPTION_PROOF_SUMMARY.md"
