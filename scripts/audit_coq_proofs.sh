#!/bin/bash
# Audit Coq proofs for correctness and completeness
# Checks for axioms, admits, opaque definitions, and proof obligations

set -e

COQ_DIR="/workspaces/The-Thiele-Machine/coq"
AUDIT_LOG="/tmp/coq_audit_$(date +%Y%m%d_%H%M%S).txt"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

echo -e "${CYAN}=========================================="
echo "COQ PROOF AUDIT"
echo "=========================================="
echo -e "Directory: ${YELLOW}$COQ_DIR${NC}"
echo -e "Report:    ${YELLOW}$AUDIT_LOG${NC}"
echo -e "Started:   ${GREEN}$(date)${NC}"
echo -e "==========================================${NC}\n"

# Initialize counters
TOTAL_FILES=0
TOTAL_LEMMAS=0
TOTAL_PROOFS=0
TOTAL_ADMITS=0
TOTAL_AXIOMS=0
TOTAL_OPAQUE=0

exec > >(tee "$AUDIT_LOG")

echo "=== 1. SCANNING FOR ADMITTED PROOFS ==="
echo ""
while IFS= read -r file; do
    # Use grep|wc so we always get a single numeric result (grep exits 1 on no matches).
    ADMITS=$(grep -o "Admitted\." "$file" 2>/dev/null | wc -l | tr -d ' ')
    if [ "$ADMITS" -gt 0 ]; then
        echo -e "${YELLOW}$file: $ADMITS admits${NC}"
        grep -B 3 "Admitted\." "$file" | grep -E "^Lemma|^Theorem" | sed 's/^/  /'
        TOTAL_ADMITS=$((TOTAL_ADMITS + ADMITS))
    fi
done < <(find "$COQ_DIR" -name "*.v" -type f)

echo ""
echo "=== 2. SCANNING FOR AXIOMS ==="
echo ""
while IFS= read -r file; do
    # Match both top-level and indented axioms.
    AXIOMS=$(grep -E -o "^[[:space:]]*Axiom[[:space:]]+" "$file" 2>/dev/null | wc -l | tr -d ' ')
    if [ "$AXIOMS" -gt 0 ]; then
        echo -e "${RED}$file: $AXIOMS axioms${NC}"
        grep -E "^[[:space:]]*Axiom[[:space:]]+" "$file" | sed 's/^/  /'
        TOTAL_AXIOMS=$((TOTAL_AXIOMS + AXIOMS))
    fi
done < <(find "$COQ_DIR" -name "*.v" -type f)

echo ""
echo "=== 3. SCANNING FOR OPAQUE DEFINITIONS ==="
echo ""
while IFS= read -r file; do
    OPAQUE=$(grep -E "Opaque|#\[global\] Opaque" "$file" 2>/dev/null | wc -l | tr -d ' ')
    if [ "$OPAQUE" -gt 0 ]; then
        echo -e "${CYAN}$file: $OPAQUE opaque${NC}"
        grep -E "Opaque|#\[global\] Opaque" "$file" | sed 's/^/  /'
        TOTAL_OPAQUE=$((TOTAL_OPAQUE + OPAQUE))
    fi
done < <(find "$COQ_DIR" -name "*.v" -type f)

echo ""
echo "=== 4. PROOF STATISTICS ==="
echo ""
while IFS= read -r file; do
    TOTAL_FILES=$((TOTAL_FILES + 1))
    LEMMAS=$(grep -E "^Lemma |^Theorem " "$file" 2>/dev/null | wc -l | tr -d ' ')
    PROOFS=$(grep -E "^(Qed\.|Defined\.)$" "$file" 2>/dev/null | wc -l | tr -d ' ')
    TOTAL_LEMMAS=$((TOTAL_LEMMAS + LEMMAS))
    TOTAL_PROOFS=$((TOTAL_PROOFS + PROOFS))
done < <(find "$COQ_DIR" -name "*.v" -type f)

echo "Total .v files: $TOTAL_FILES"
echo "Total lemmas/theorems: $TOTAL_LEMMAS"
echo "Total completed proofs: $TOTAL_PROOFS"

echo ""
echo "=== 5. SPECIFIC FILE AUDIT: BridgeDefinitions.v ==="
echo ""
BRIDGE_FILE="$COQ_DIR/thielemachine/verification/BridgeDefinitions.v"
if [ -f "$BRIDGE_FILE" ]; then
    echo "File: $BRIDGE_FILE"
    echo ""
    echo "Lemmas with proofs:"
    grep -E "^Lemma|^Theorem" "$BRIDGE_FILE" | while read -r line; do
        LEMMA_NAME=$(echo "$line" | awk '{print $2}')
        # Check if it has Qed or Admitted
        if awk "/^Lemma $LEMMA_NAME/,/^(Qed|Admitted)\./" "$BRIDGE_FILE" | grep -q "^Qed\."; then
            echo -e "  ${GREEN}✓ $LEMMA_NAME${NC} (proven)"
        elif awk "/^Lemma $LEMMA_NAME/,/^(Qed|Admitted)\./" "$BRIDGE_FILE" | grep -q "^Admitted\."; then
            echo -e "  ${YELLOW}⚠ $LEMMA_NAME${NC} (admitted)"
        else
            echo -e "  ${CYAN}? $LEMMA_NAME${NC} (status unclear)"
        fi
    done
    
    echo ""
    echo "Helper lemmas created today:"
    grep -E "^Lemma (setup_state_|tape_window_ok_)" "$BRIDGE_FILE" | awk '{print "  " $2}' | sed 's/:.*//'
fi

echo ""
echo "=== 6. VERIFICATION STATUS ==="
echo ""
cd "$COQ_DIR" && make --quiet core 2>&1 | grep -E "Error|Warning" || echo -e "${GREEN}✓ All core files compile successfully${NC}"

echo ""
echo -e "${CYAN}=========================================="
echo "AUDIT SUMMARY"
echo "==========================================${NC}"
echo -e "Files scanned:      ${CYAN}$TOTAL_FILES${NC}"
echo -e "Lemmas/Theorems:    ${CYAN}$TOTAL_LEMMAS${NC}"
echo -e "Completed proofs:   ${GREEN}$TOTAL_PROOFS${NC}"
echo -e "Admitted proofs:    ${YELLOW}$TOTAL_ADMITS${NC}"
echo -e "Axioms declared:    ${RED}$TOTAL_AXIOMS${NC}"
echo -e "Opaque defs:        ${CYAN}$TOTAL_OPAQUE${NC}"

if [ $TOTAL_ADMITS -eq 0 ] && [ $TOTAL_AXIOMS -eq 0 ]; then
    echo -e "\n${GREEN}✅ AUDIT PASSED: No admits or axioms found!${NC}"
elif [ $TOTAL_AXIOMS -gt 0 ]; then
    echo -e "\n${RED}⚠ WARNING: Axioms detected - review for soundness${NC}"
elif [ $TOTAL_ADMITS -gt 0 ]; then
    echo -e "\n${YELLOW}ℹ INFO: Some proofs admitted - see details above${NC}"
fi

echo -e "\n${CYAN}Full report: ${YELLOW}$AUDIT_LOG${NC}"
echo -e "${CYAN}==========================================${NC}"
