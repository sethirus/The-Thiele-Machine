#!/bin/bash
# Real-time Coq compilation monitor with detailed metrics
# Usage: ./coq_monitor.sh <target.vo> [verbose]

set -o pipefail

TARGET="${1:-thielemachine/verification/BridgeDefinitions.vo}"
VERBOSE="${2:-0}"
LOG_DIR="/tmp/coq_monitor_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$LOG_DIR"

MAIN_LOG="$LOG_DIR/build.log"
MEMORY_LOG="$LOG_DIR/memory.log"
TIMING_LOG="$LOG_DIR/timing.log"
ERROR_LOG="$LOG_DIR/errors.log"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

echo -e "${CYAN}=========================================="
echo "COQ REAL-TIME COMPILATION MONITOR"
echo "=========================================="
echo -e "Target:   ${YELLOW}$TARGET${NC}"
echo -e "Started:  ${GREEN}$(date)${NC}"
echo -e "Log Dir:  ${BLUE}$LOG_DIR${NC}"
echo "==========================================${NC}"
echo ""

# Counters
LEMMA_COUNT=0
PROOF_COUNT=0
ERROR_COUNT=0
START_TIME=$(date +%s)

# Track current file being compiled
CURRENT_FILE=""
FILE_START_TIME=0

# Memory tracking function
track_memory() {
    while true; do
        if ps aux | grep -E "coqc.*\.v" | grep -v grep > /dev/null; then
            TIMESTAMP=$(date +%H:%M:%S)
            MEM_KB=$(ps aux | grep -E "coqc.*\.v" | grep -v grep | awk '{sum+=$6} END {print sum}')
            if [ -n "$MEM_KB" ]; then
                MEM_MB=$((MEM_KB / 1024))
                CPU=$(ps aux | grep -E "coqc.*\.v" | grep -v grep | awk '{sum+=$3} END {print sum}')
                echo "$TIMESTAMP,$MEM_MB,$CPU" >> "$MEMORY_LOG"
                
                # Real-time display
                if [ "$MEM_MB" -gt 1000 ]; then
                    MEM_COLOR="$RED"
                elif [ "$MEM_MB" -gt 500 ]; then
                    MEM_COLOR="$YELLOW"
                else
                    MEM_COLOR="$GREEN"
                fi
                
                echo -ne "\r${CYAN}[$TIMESTAMP]${NC} Mem: ${MEM_COLOR}${MEM_MB}MB${NC} | CPU: ${BLUE}${CPU}%${NC}    "
            fi
        fi
        sleep 0.3
    done
}

# Start memory monitor in background
track_memory &
MONITOR_PID=$!
trap "kill $MONITOR_PID 2>/dev/null; exit" INT TERM EXIT

# Parse and display build output
cd /workspaces/The-Thiele-Machine/coq || exit 1

make "$TARGET" 2>&1 | tee "$MAIN_LOG" | while IFS= read -r line; do
    echo "$line"
    
    # Track files being compiled
    if echo "$line" | grep -q "COQC"; then
        if [ -n "$CURRENT_FILE" ] && [ "$FILE_START_TIME" -gt 0 ]; then
            FILE_END_TIME=$(date +%s)
            FILE_DURATION=$((FILE_END_TIME - FILE_START_TIME))
            echo "$CURRENT_FILE,$FILE_DURATION" >> "$TIMING_LOG"
        fi
        
        CURRENT_FILE=$(echo "$line" | sed 's/.*COQC //')
        FILE_START_TIME=$(date +%s)
        echo -e "\n${GREEN}▶ COMPILING:${NC} ${YELLOW}$CURRENT_FILE${NC}"
    fi
    
    # Track lemmas and definitions
    if echo "$line" | grep -qE "^Lemma|^Theorem|^Definition"; then
        LEMMA_NAME=$(echo "$line" | awk '{print $2}' | sed 's/:.*//')
        LEMMA_COUNT=$((LEMMA_COUNT + 1))
        echo -e "${CYAN}  📝 Lemma #$LEMMA_COUNT:${NC} $LEMMA_NAME"
    fi
    
    # Track proofs
    if echo "$line" | grep -qE "^Qed\.|^Defined\."; then
        PROOF_COUNT=$((PROOF_COUNT + 1))
        echo -e "${GREEN}  ✓ Proof #$PROOF_COUNT completed${NC}"
    fi
    
    # Track admits
    if echo "$line" | grep -q "Admitted\."; then
        echo -e "${YELLOW}  ⚠ ADMITTED (proof skipped)${NC}"
    fi
    
    # Track errors
    if echo "$line" | grep -q "Error:"; then
        ERROR_COUNT=$((ERROR_COUNT + 1))
        echo -e "\n${RED}❌ ERROR #$ERROR_COUNT${NC}"
        echo "=== Error at $(date) ===" >> "$ERROR_LOG"
        echo "$line" >> "$ERROR_LOG"
    fi
    
    # Track file and line info
    if echo "$line" | grep -qE "File.*line [0-9]+"; then
        LOCATION=$(echo "$line" | grep -oE 'File "[^"]*", line [0-9]+')
        echo -e "${BLUE}📍 $LOCATION${NC}"
        echo "$LOCATION" >> "$ERROR_LOG"
    fi
    
    # Show tactic execution if verbose
    if [ "$VERBOSE" = "1" ] && echo "$line" | grep -qE "^\s+(apply|rewrite|unfold|reflexivity|lia|assumption|exact)"; then
        TACTIC=$(echo "$line" | sed 's/^\s*//')
        echo -e "${CYAN}    → $TACTIC${NC}"
    fi
done

BUILD_EXIT=${PIPESTATUS[0]}

# Kill memory monitor
kill $MONITOR_PID 2>/dev/null

# Calculate total time
END_TIME=$(date +%s)
TOTAL_TIME=$((END_TIME - START_TIME))

# Generate summary
echo -e "\n\n${CYAN}=========================================="
echo "BUILD SUMMARY"
echo "==========================================${NC}"
echo -e "Target:        ${YELLOW}$TARGET${NC}"
echo -e "Duration:      ${GREEN}${TOTAL_TIME}s${NC}"
echo -e "Lemmas found:  ${CYAN}$LEMMA_COUNT${NC}"
echo -e "Proofs done:   ${GREEN}$PROOF_COUNT${NC}"
echo -e "Errors:        ${RED}$ERROR_COUNT${NC}"

# Memory statistics
if [ -f "$MEMORY_LOG" ]; then
    MAX_MEM=$(awk -F, '{print $2}' "$MEMORY_LOG" | sort -n | tail -1)
    AVG_MEM=$(awk -F, '{sum+=$2; count++} END {if(count>0) print int(sum/count); else print 0}' "$MEMORY_LOG")
    echo -e "Peak Memory:   ${YELLOW}${MAX_MEM}MB${NC}"
    echo -e "Avg Memory:    ${BLUE}${AVG_MEM}MB${NC}"
fi

# File timing statistics
if [ -f "$TIMING_LOG" ]; then
    echo -e "\n${CYAN}Slowest files:${NC}"
    sort -t, -k2 -rn "$TIMING_LOG" | head -5 | while IFS=, read -r file duration; do
        echo -e "  ${duration}s - ${YELLOW}$file${NC}"
    done
fi

# Show errors if any
if [ $BUILD_EXIT -ne 0 ]; then
    echo -e "\n${RED}❌ BUILD FAILED${NC}"
    if [ -f "$ERROR_LOG" ]; then
        echo -e "\n${RED}Last error details:${NC}"
        tail -30 "$ERROR_LOG"
    fi
else
    echo -e "\n${GREEN}✅ BUILD SUCCESSFUL${NC}"
fi

echo -e "\n${CYAN}Full logs:${NC}"
echo -e "  Main:   ${BLUE}$MAIN_LOG${NC}"
echo -e "  Memory: ${BLUE}$MEMORY_LOG${NC}"
echo -e "  Timing: ${BLUE}$TIMING_LOG${NC}"
echo -e "  Errors: ${BLUE}$ERROR_LOG${NC}"
echo -e "${CYAN}==========================================${NC}"

exit $BUILD_EXIT
