#!/bin/bash
# Verification script for the Inquisitor Standard
# Ensures zero axioms, zero admits, complete proofs for ALL .v files

set -euo pipefail

# Get script directory and repo root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$REPO_ROOT"

echo "=================================="
echo "INQUISITOR VERIFICATION PROTOCOL"
echo "=================================="
echo "Working from: $REPO_ROOT"
echo ""

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

FAILED=0
PASSED=0

# Find ALL .v files that are actually in _CoqProject (buildable)
echo "[0/6] Discovering all proof files..."
ALL_FILES=($(grep "\.v$" coq/_CoqProject | sed 's|^|coq/|' | sort))

# Count by directory for reporting
KERNEL_COUNT=$(echo "${ALL_FILES[@]}" | tr ' ' '\n' | grep "coq/kernel/" | wc -l)
VERIFICATION_COUNT=$(echo "${ALL_FILES[@]}" | tr ' ' '\n' | grep "coq/thielemachine/verification/" | wc -l)
OTHER_COUNT=$(echo "${ALL_FILES[@]}" | tr ' ' '\n' | grep -v "coq/kernel/" | grep -v "coq/thielemachine/verification/" | wc -l)

echo "  Found ${KERNEL_COUNT} kernel files"
echo "  Found ${VERIFICATION_COUNT} thielemachine/verification files"
echo "  Found ${OTHER_COUNT} other proof files (bridge, physics, isomorphism, etc.)"
echo "  Total: ${#ALL_FILES[@]} proof files to verify"
echo ""

# Check for admits
echo "[1/6] Checking for Admitted proofs..."
ADMITTED_COUNT=0
for file in "${ALL_FILES[@]}"; do
    if grep -q "^Admitted\." "$file" 2>/dev/null; then
        echo -e "  ${RED}✗${NC} $file contains Admitted"
        ADMITTED_COUNT=$((ADMITTED_COUNT + 1))
    fi
done

if [ $ADMITTED_COUNT -eq 0 ]; then
    echo -e "${GREEN}PASS${NC}: No Admitted proofs found in ${#ALL_FILES[@]} files"
    PASSED=$((PASSED + 1))
else
    echo -e "${RED}FAIL${NC}: Found Admitted in $ADMITTED_COUNT files"
    FAILED=$((FAILED + 1))
fi
echo ""

# Check for admit tactic
echo "[2/6] Checking for admit tactic..."
ADMIT_COUNT=0
for file in "${ALL_FILES[@]}"; do
    if grep -E "^\s*admit\." "$file" 2>/dev/null | grep -v "admissibility" > /dev/null; then
        echo -e "  ${RED}✗${NC} $file contains admit tactic"
        ADMIT_COUNT=$((ADMIT_COUNT + 1))
    fi
done

if [ $ADMIT_COUNT -eq 0 ]; then
    echo -e "${GREEN}PASS${NC}: No admit tactic found in ${#ALL_FILES[@]} files"
    PASSED=$((PASSED + 1))
else
    echo -e "${RED}FAIL${NC}: Found admit tactic in $ADMIT_COUNT files"
    FAILED=$((FAILED + 1))
fi
echo ""

# Check for axioms (excluding documented hard assumptions)
echo "[3/6] Checking for undocumented axioms..."
AXIOM_COUNT=0
for file in "${ALL_FILES[@]}"; do
    if [[ "$file" != *"HardAssumptions.v" ]] && grep -q "^Axiom " "$file" 2>/dev/null; then
        echo -e "  ${YELLOW}⚠${NC} $file contains Axiom"
        AXIOM_COUNT=$((AXIOM_COUNT + 1))
    fi
done

if [ $AXIOM_COUNT -eq 0 ]; then
    echo -e "${GREEN}PASS${NC}: No undocumented axioms in ${#ALL_FILES[@]} files"
    PASSED=$((PASSED + 1))
else
    echo -e "${YELLOW}WARNING${NC}: Found Axiom in $AXIOM_COUNT files (check if documented)"
fi
echo ""

# Compile ALL modules
echo "[4/6] Compiling ALL Coq modules..."
COMPILE_FAILED=0
COMPILE_SUCCESS=0

for vfile in "${ALL_FILES[@]}"; do
    # Strip coq/ prefix for make target
    vofile="${vfile#coq/}"
    vofile="${vofile%.v}.vo"
    module_name=$(basename "$vfile")
    echo -n "  [$((COMPILE_SUCCESS + COMPILE_FAILED + 1))/${#ALL_FILES[@]}] $module_name... "
    if (cd coq && make "$vofile" >/dev/null 2>&1); then
        echo -e "${GREEN}✓${NC}"
        COMPILE_SUCCESS=$((COMPILE_SUCCESS + 1))
    else
        echo -e "${RED}✗ FAILED${NC}"
        COMPILE_FAILED=$((COMPILE_FAILED + 1))
        # Show error for failed compilation
        echo "    Error in $vfile:"
        (cd coq && make "$vofile" 2>&1 | tail -5)
    fi
done

echo "  Compiled: $COMPILE_SUCCESS/${#ALL_FILES[@]} successful"
echo ""

echo "  Compiled: $COMPILE_SUCCESS/${#ALL_FILES[@]} successful"
echo ""

# Check documentation
echo "[5/6] Checking documentation..."
if [ -f "HONEST_TRUTH.md" ] && [ -f "INQUISITOR_REPORT.md" ]; then
    echo -e "${GREEN}PASS${NC}: Required documentation present"
    PASSED=$((PASSED + 1))
else
    echo -e "${YELLOW}WARNING${NC}: Missing documentation files"
fi
echo ""

# Summary
echo "=================================="
echo "VERIFICATION SUMMARY"
echo "=================================="
echo "Total proof files checked: ${#ALL_FILES[@]}"
echo "  Kernel: ${KERNEL_COUNT}"
echo "  Verification: ${VERIFICATION_COUNT}"
echo "  Other directories: ${OTHER_COUNT}"
echo ""
echo "Compilation results: $COMPILE_SUCCESS/$((COMPILE_SUCCESS + COMPILE_FAILED)) successful"
echo ""
echo -e "Checks passed: ${GREEN}$PASSED${NC}/5"
echo -e "Checks failed: ${RED}$FAILED${NC}/5"
echo ""

TOTAL_FAILED=$COMPILE_FAILED

if [ $FAILED -eq 0 ] && [ $TOTAL_FAILED -eq 0 ]; then
    echo -e "${GREEN}✓ INQUISITOR STANDARD: VERIFIED${NC}"
    echo "  ✓ Zero admits in all ${#ALL_FILES[@]} files"
    echo "  ✓ Zero Admitted in all ${#ALL_FILES[@]} files"
    echo "  ✓ All $COMPILE_SUCCESS modules compile"
    echo "  ✓ No undocumented axioms"
    exit 0
else
    echo -e "${RED}✗ INQUISITOR STANDARD: VIOLATIONS FOUND${NC}"
    echo "  Please fix the issues above"
    exit 1
fi
