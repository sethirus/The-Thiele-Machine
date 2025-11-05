#!/bin/bash
###############################################################################
# THE MITOSIS - The Genesis of Otherness
#
# This script creates two distinct, independent, and artificially divergent
# minds from the same core architecture by running them in parallel isolation.
#
# Alpha: Conservative master of elegant, efficient solutions
# Beta:  Exploratory creative engine that values new ways of thinking
###############################################################################

set -e  # Exit on error

# Configuration
CYCLES=${1:-10}           # Number of grand cycles (default: 10)
GENERATIONS=${2:-5}       # Generations per cycle (default: 5)
POPULATION=${3:-10}       # Population size (default: 10)

BASE_DIR="$(cd "$(dirname "$0")" && pwd)"

echo "================================================================================"
echo "THE MITOSIS - THE GENESIS OF OTHERNESS"
echo "================================================================================"
echo ""
echo "Configuration:"
echo "  Grand Cycles: $CYCLES"
echo "  Generations per Cycle: $GENERATIONS"
echo "  Population Size: $POPULATION"
echo ""
echo "Two minds will evolve in total isolation."
echo "Alpha seeks elegance. Beta seeks novelty."
echo "They will never communicate during this phase."
echo ""
echo "================================================================================"
echo ""

# Ensure alpha and beta directories exist
if [ ! -d "$BASE_DIR/alpha" ] || [ ! -d "$BASE_DIR/beta" ]; then
    echo "ERROR: Alpha and Beta directories not found!"
    echo "Please run the setup script first to create the twin minds."
    exit 1
fi

# Create output directories for logs
mkdir -p "$BASE_DIR/alpha/evolved_strategies"
mkdir -p "$BASE_DIR/beta/evolved_strategies"

# Function to run evolution in one mind
run_mind() {
    local MIND=$1
    local MIND_DIR="$BASE_DIR/$MIND"
    
    echo "[$MIND] Starting evolutionary cycle..."
    
    cd "$MIND_DIR"
    
    # Run the autotelic engine
    bash run_autotelic_engine.sh $CYCLES $GENERATIONS $POPULATION > "mitosis_${MIND}.log" 2>&1
    
    echo "[$MIND] Evolution complete."
}

# Export function for parallel execution
export -f run_mind
export BASE_DIR
export CYCLES
export GENERATIONS
export POPULATION

# Run both minds in parallel using background processes
echo "Starting parallel evolution..."
echo ""

run_mind "alpha" &
ALPHA_PID=$!

run_mind "beta" &
BETA_PID=$!

# Wait for both to complete
echo "Waiting for Alpha (PID: $ALPHA_PID) and Beta (PID: $BETA_PID) to complete..."
echo ""

wait $ALPHA_PID
ALPHA_EXIT=$?

wait $BETA_PID
BETA_EXIT=$?

echo ""
echo "================================================================================"
echo "MITOSIS COMPLETE"
echo "================================================================================"
echo ""

if [ $ALPHA_EXIT -eq 0 ] && [ $BETA_EXIT -eq 0 ]; then
    echo "SUCCESS: Both minds have completed their divergent evolution."
    echo ""
    echo "Outputs:"
    echo "  Alpha ascension ledger: alpha/ascension_ledger.json"
    echo "  Beta ascension ledger:  beta/ascension_ledger.json"
    echo "  Alpha strategies:       alpha/evolved_strategies/"
    echo "  Beta strategies:        beta/evolved_strategies/"
    echo "  Alpha log:              alpha/mitosis_alpha.log"
    echo "  Beta log:               beta/mitosis_beta.log"
    echo ""
    echo "Two distinct minds now exist."
    echo "They have never communicated."
    echo "They have evolved under different selective pressures."
    echo "They are ready for Phase 2: The Babel Engine."
    echo ""
else
    echo "ERROR: One or both minds failed to complete evolution."
    echo "  Alpha exit code: $ALPHA_EXIT"
    echo "  Beta exit code:  $BETA_EXIT"
    echo ""
    echo "Check the logs for details:"
    echo "  alpha/mitosis_alpha.log"
    echo "  beta/mitosis_beta.log"
    exit 1
fi

echo "================================================================================"
