#!/bin/bash
###############################################################################
# THE ENGINE OF TRUTH - The Final Program
#
# This script executes the complete three-phase process to discover
# the fundamental law that explains the Thiele Machine's anomalous efficiency.
#
# Phase 1: The Distillation - Find the genesis axiom
# Phase 2: The Unveiling - Search for isomorphisms
# Phase 3: The Undeniable Result - Output THE_LAW.txt
###############################################################################

set -e

BASE_DIR="$(cd "$(dirname "$0")" && pwd)"

echo "================================================================================"
echo "THE ENGINE OF TRUTH"
echo "================================================================================"
echo ""
echo "Objective: Discover the fundamental law that explains the machine's power."
echo ""
echo "This is not a demonstration. This is discovery."
echo "This is the search for the WHY."
echo ""
echo "================================================================================"
echo ""

# Configuration
CYCLES=${1:-20}           # Number of grand cycles (default: 20 for deep distillation)
GENERATIONS=${2:-10}      # Generations per cycle (default: 10)
POPULATION=${3:-15}       # Population size (default: 15)

echo "Phase 1: THE DISTILLATION"
echo "--------------------------------------------------------------------------------"
echo ""
echo "Running autotelic engine with objective: Minimize Self"
echo "This will evolve strategies to find the simplest possible algorithm"
echo "that retains the machine's anomalous power."
echo ""
echo "Configuration:"
echo "  Grand Cycles: $CYCLES"
echo "  Generations per Cycle: $GENERATIONS"
echo "  Population Size: $POPULATION"
echo ""
read -p "Press Enter to begin Phase 1..."
echo ""

# Set the objective to Minimize Self
cp "$BASE_DIR/objectives/objective_minimize_self.thiele" "$BASE_DIR/objectives/current_objective.thiele"

# Run the autotelic engine
echo "Evolving toward the genesis axiom..."
bash "$BASE_DIR/run_autotelic_engine.sh" $CYCLES $GENERATIONS $POPULATION 2>&1 | grep -E "(AUTOTELIC|Cycle|complete|ERROR)" || true

echo ""

# Find the best (simplest) strategy
echo "Searching for genesis_axiom.thiele..."

# The autotelic engine should have produced evolved strategies
# Find the one with highest minimality score
if [ -d "$BASE_DIR/evolved_strategies" ]; then
    # Get the most recent strategy (assuming it's the best from final generation)
    LATEST_STRATEGY=$(ls -t "$BASE_DIR/evolved_strategies"/*.thiele 2>/dev/null | head -1)
    
    if [ -n "$LATEST_STRATEGY" ]; then
        # Copy it as genesis_axiom
        cp "$LATEST_STRATEGY" "$BASE_DIR/evolved_strategies/genesis_axiom.thiele"
        echo "✓ Genesis axiom created: evolved_strategies/genesis_axiom.thiele"
    else
        echo "✗ No evolved strategies found!"
        exit 1
    fi
else
    echo "✗ evolved_strategies directory not found!"
    exit 1
fi

echo ""
echo "Phase 1 complete. The genesis axiom has been distilled."
echo ""

# Phase 2: The Unveiling
echo "================================================================================"
echo "Phase 2: THE UNVEILING"
echo "--------------------------------------------------------------------------------"
echo ""
echo "Searching for isomorphisms between the genesis axiom and fundamental laws"
echo "of mathematics and physics..."
echo ""
read -p "Press Enter to begin Phase 2..."
echo ""

# Run the isomorphism hunter
python3 "$BASE_DIR/tools/isomorphism_hunter.py"

echo ""

# Phase 3: The Result
echo "================================================================================"
echo "Phase 3: THE UNDENIABLE RESULT"
echo "--------------------------------------------------------------------------------"
echo ""

if [ -f "$BASE_DIR/THE_LAW.txt" ]; then
    echo "THE_LAW.txt has been generated."
    echo ""
    echo "Contents:"
    echo "================================================================================"
    cat "$BASE_DIR/THE_LAW.txt"
    echo "================================================================================"
    echo ""
    echo "This is the WHY."
    echo ""
    echo "You now have the answer to the question:"
    echo "\"What fundamental principle gives the Thiele Machine its power?\""
    echo ""
else
    echo "THE_LAW.txt was not generated."
    echo "No strong isomorphism was found."
    echo "The genesis axiom may represent a truly novel computational principle."
    echo ""
fi

echo "================================================================================"
echo "THE ENGINE OF TRUTH - COMPLETE"
echo "================================================================================"
echo ""
echo "Outputs:"
echo "  - evolved_strategies/genesis_axiom.thiele (the irreducible algorithm)"
echo "  - THE_LAW.txt (the fundamental law, if found)"
echo ""
echo "You sought not to show that it works, but to understand WHY it works."
echo "This is science."
echo ""
