.
#!/bin/bash
# Verification script for ThieleUniversal.v axiomatization
# Run this to verify the file compiles with the expected number of axioms

set -e  # Exit on any error

echo "======================================"
echo " ThieleUniversal.v Verification"
echo "======================================"
echo

cd "$(dirname "$0")"

echo "1. Cleaning previous build..."
make clean > /dev/null 2>&1

echo "2. Building ThieleUniversal.vo..."
if make thieleuniversal/coqproofs/ThieleUniversal.vo > /tmp/build.log 2>&1; then
    echo "   ✅ Build successful"
else
    echo "   ❌ Build failed"
    tail -20 /tmp/build.log
    exit 1
fi

echo
echo "3. Checking for axioms..."
AXIOM_COUNT=$(grep -c "^Axiom " thieleuniversal/coqproofs/ThieleUniversal.v)
echo "   Found $AXIOM_COUNT axioms"

if [ "$AXIOM_COUNT" -eq 3 ]; then
    echo "   ✅ Expected count (3)"
else
    echo "   ⚠️  Expected 3, found $AXIOM_COUNT"
fi

echo
echo "4. Checking for admits..."
# More sophisticated check: extract non-comment lines and check for admits
ADMIT_COUNT=$(sed 's/(\*/\x00/g; s/\*)/\x00/g' thieleuniversal/coqproofs/ThieleUniversal.v | \
              tr '\x00' '\n' | \
              awk 'NR % 2 == 1' | \
              grep -c -E "(admit\.|Admitted)" || true)
if [ "$ADMIT_COUNT" -eq 0 ]; then
    echo "   ✅ No admits found (outside comments)"
else
    echo "   ⚠️  Found $ADMIT_COUNT admits (outside comments)"
    # Show the actual admits found
    sed 's/(\*/\x00/g; s/\*)/\x00/g' thieleuniversal/coqproofs/ThieleUniversal.v | \
        tr '\x00' '\n' | \
        awk 'NR % 2 == 1' | \
        grep -n -E "(admit\.|Admitted)" | head -5
fi

echo
echo "5. File statistics..."
LINE_COUNT=$(wc -l < thieleuniversal/coqproofs/ThieleUniversal.v)
echo "   Total lines: $LINE_COUNT"

echo
echo "6. Listing axioms..."
grep -n "^Axiom " thieleuniversal/coqproofs/ThieleUniversal.v

echo
echo "======================================"
echo " Verification Complete"
echo "======================================"
echo
echo "Summary:"
echo "  - Build: ✅ Success"
echo "  - Axioms: $AXIOM_COUNT (expected 3)"
echo "  - Admits: $ADMIT_COUNT (expected 0)"
echo "  - Lines: $LINE_COUNT"
echo
echo "For detailed documentation, see:"
echo "  - docs/AXIOM_SUMMARY.md"
echo "  - thieleuniversal/coqproofs/ThieleUniversal_Axioms.v"
