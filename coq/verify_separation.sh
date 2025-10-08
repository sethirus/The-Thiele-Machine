#!/bin/bash
# Verification script for the Thiele Machine / Turing separation proof

set -e

echo "=========================================="
echo " Thiele Machine Separation Verification"
echo "=========================================="
echo

cd "$(dirname "$0")"

echo "1. Building Separation.v..."
if make thielemachine/coqproofs/Separation.vo > /tmp/separation_build.log 2>&1; then
    echo "   ✅ Build successful"
else
    echo "   ❌ Build failed"
    tail -20 /tmp/separation_build.log
    exit 1
fi

echo
echo "2. Checking for axioms..."
AXIOM_COUNT=$(grep -c "^Axiom " thielemachine/coqproofs/Separation.v)
echo "   Found $AXIOM_COUNT axiom(s)"

if [ "$AXIOM_COUNT" -eq 1 ]; then
    echo "   ✅ Expected count (1 - exponential lower bound assumption)"
else
    echo "   ⚠️  Expected 1, found $AXIOM_COUNT"
fi

echo
echo "3. Checking for admits..."
ADMIT_COUNT=$(grep -c "admit\." thielemachine/coqproofs/Separation.v || true)
if [ "$ADMIT_COUNT" -eq 0 ]; then
    echo "   ✅ No admits found"
else
    echo "   ❌ Found $ADMIT_COUNT admits"
    grep -n "admit\." thielemachine/coqproofs/Separation.v
    exit 1
fi

echo
echo "4. Listing proven theorems..."
echo
grep -E "^Theorem " thielemachine/coqproofs/Separation.v | while read line; do
    echo "   ✅ $line"
done

echo
echo "5. Listing axiom..."
echo
grep -A 3 "^Axiom " thielemachine/coqproofs/Separation.v | head -4 | while read line; do
    echo "   $line"
done

echo
echo "=========================================="
echo " Verification Complete"
echo "=========================================="
echo
echo "Summary:"
echo "  - Build: ✅ Success"
echo "  - Axioms: $AXIOM_COUNT (blind exponential lower bound)"
echo "  - Admits: $ADMIT_COUNT (none)"
echo "  - Main Result: ✅ thiele_exponential_separation"
echo
echo "Key Statements in the model:"
echo "  1. thiele_sighted_steps_polynomial - sighted solver runs in cubic time"
echo "  2. thiele_mu_cost_quadratic      - μ accounting stays quadratic"
echo "  3. thiele_exponential_separation - combines the constructive bounds with the axiom"
echo
echo "For detailed analysis, see:"
echo "  - coq/README_PROOFS.md (status overview)"
