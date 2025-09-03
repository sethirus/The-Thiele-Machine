#!/bin/bash
# Project SIGHTLINE: Autonomous Recursive Solver

# --- Initial Strategy Configuration ---
export INITIAL_LOOKAHEAD=0
export MAX_LOOKAHEAD=10
ATTEMPT=1
LOG_FILE="logs/sightline_log.txt"

# --- Environment Setup ---
VENV_DIR="thiele_env"
if [ ! -d "$VENV_DIR" ]; then
    echo "Creating virtual environment: $VENV_DIR"
    python3 -m venv "$VENV_DIR"
fi

# --- The Unstoppable Loop ---
while true; do
    echo "==================================================" >> ${LOG_FILE}
    echo "SIGHTLINE ATTEMPT #${ATTEMPT}" >> ${LOG_FILE}
    echo "Strategy: Initial Lookahead=${INITIAL_LOOKAHEAD}, Max Lookahead=${MAX_LOOKAHEAD}" >> ${LOG_FILE}
    echo "==================================================" >> ${LOG_FILE}

    echo "=================================================="
    echo "SIGHTLINE ATTEMPT #${ATTEMPT}"
    echo "Strategy: Initial Lookahead=${INITIAL_LOOKAHEAD}, Max Lookahead=${MAX_LOOKAHEAD}"
    echo "Appending to log file: ${LOG_FILE}"
    echo "=================================================="

    # Activate environment and run the solver, appending all output to log
    source "$VENV_DIR/bin/activate" && python solvers/solve.py >> ${LOG_FILE} 2>&1
    EXIT_CODE=$?

    # --- Analysis and Adaptation ---
    if [ ${EXIT_CODE} -eq 0 ]; then
        echo ""
        echo "OBJECTIVE ACHIEVED. Factors found."
        echo "Final solution in ${LOG_FILE}."
        break # Mission accomplished
    fi

    # A "Genius Move": Analyze the failure and adjust the strategy
    LAST_LOG_LINE=$(tail -n 2 ${LOG_FILE})

    if [[ ${LAST_LOG_LINE} == *"Max lookahead"* ]]; then
        # Extract the bit number from the log
        BIT_FAILED=$(echo "${LAST_LOG_LINE}" | grep -oP 'bit \K\d+')
        echo "ANALYSIS: Failure at bit ${BIT_FAILED} due to max lookahead. Strategy requires more depth."
        # Smarter adaptation: increase more if early bits fail
        if [ ${BIT_FAILED} -lt 50 ]; then
            INCREASE=10
        elif [ ${BIT_FAILED} -lt 100 ]; then
            INCREASE=5
        else
            INCREASE=2
        fi
        export INITIAL_LOOKAHEAD=$((INITIAL_LOOKAHEAD + 1))
        export MAX_LOOKAHEAD=$((MAX_LOOKAHEAD + INCREASE))
        echo "ADAPTATION: New strategy -> Initial Lookahead=${INITIAL_LOOKAHEAD}, Max Lookahead=${MAX_LOOKAHEAD}"
    else
        echo "ANALYSIS: Unknown failure (Exit Code ${EXIT_CODE}). Retrying with baseline."
        # Default retry logic
    fi

    ATTEMPT=$((ATTEMPT + 1))

    # Safety check: don't run forever
    if [ ${ATTEMPT} -gt 100 ]; then
        echo "SAFETY: Maximum attempts reached. Aborting."
        break
    fi

    # Brief pause to prevent overwhelming the system
    sleep 1
done