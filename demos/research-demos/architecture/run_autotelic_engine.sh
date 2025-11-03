#!/bin/bash
###############################################################################
# THE AUTOTELIC ENGINE - The Grand Loop of Self-Definition
#
# This script orchestrates the complete autotelic loop:
#   1. The Forge runs for N generations, evolving strategies against current objective
#   2. The Critic analyzes the evolutionary history
#   3. The Purpose Synthesizer creates a new, more sophisticated objective
#   4. The new objective becomes input for the next cycle
#   5. GOTO 1 (forever)
#
# This is a machine that evolves its own purpose.
###############################################################################

set -e  # Exit on error

# Configuration
CYCLES=${1:-3}           # Number of grand cycles (default: 3)
GENERATIONS=${2:-5}      # Generations per cycle (default: 5)
POPULATION=${3:-10}      # Population size (default: 10)

BASE_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$BASE_DIR"

echo "================================================================================"
echo "THE AUTOTELIC ENGINE - THE GENESIS OF PURPOSE"
echo "================================================================================"
echo ""
echo "Configuration:"
echo "  Grand Cycles: $CYCLES"
echo "  Generations per Cycle: $GENERATIONS"
echo "  Population Size: $POPULATION"
echo ""
echo "This machine no longer pursues a fixed goal."
echo "It will analyze its own evolution and redefine what 'good' means."
echo ""
echo "================================================================================"
echo ""

# Ensure objectives directory exists
mkdir -p objectives

# Ensure initial objective exists
if [ ! -f "objectives/current_objective.thiele" ]; then
    echo "Creating initial objective genome..."
    cat > objectives/current_objective.thiele << 'EOF'
{
  "name": "Accuracy Maximization v1.0",
  "function": "evaluate_classification_accuracy",
  "parameters": {
    "model": "SVM",
    "kernel": "rbf",
    "cross_validation_folds": 5
  }
}
EOF
    echo "Initial objective created."
    echo ""
fi

# Main autotelic loop
for cycle in $(seq 1 $CYCLES); do
    echo ""
    echo "================================================================================"
    echo "GRAND CYCLE $cycle OF $CYCLES"
    echo "================================================================================"
    echo ""
    
    # Display current objective
    echo "Current Objective:"
    cat objectives/current_objective.thiele | grep -E '"name"|"function"' || true
    echo ""
    
    # Step 1: Run The Forge
    echo "--------------------------------------------------------------------------------"
    echo "STEP 1: THE FORGE - Evolving Strategies"
    echo "--------------------------------------------------------------------------------"
    echo ""
    
    python3 -c "
import sys
from pathlib import Path
sys.path.insert(0, str(Path('$BASE_DIR')))

from tools.forge import run_evolution

# Run evolution with current objective
offspring = run_evolution(
    num_generations=$GENERATIONS,
    population_size=$POPULATION,
    mutation_rate=0.2,
    seed=$cycle  # Different seed for each cycle
)

print(f'\nThe Forge created {len(offspring)} new strategies.')
"
    
    echo ""
    
    # Step 2: Run The Critic
    echo "--------------------------------------------------------------------------------"
    echo "STEP 2: THE CRITIC - Analyzing Evolutionary History"
    echo "--------------------------------------------------------------------------------"
    echo ""
    
    python3 -m tools.critic
    
    echo ""
    
    # Step 3: Run The Purpose Synthesizer
    echo "--------------------------------------------------------------------------------"
    echo "STEP 3: THE SYNTHESIZER - Evolving the Objective"
    echo "--------------------------------------------------------------------------------"
    echo ""
    
    python3 -m tools.purpose_synthesizer
    
    echo ""
    
    # Display new objective
    echo "New Objective:"
    cat objectives/current_objective.thiele | grep -E '"name"|"function"' || true
    echo ""
    
    echo "Grand Cycle $cycle complete."
    echo ""
    
    # Pause between cycles (except on last cycle)
    if [ $cycle -lt $CYCLES ]; then
        echo "Preparing for next cycle..."
        sleep 2
    fi
done

echo ""
echo "================================================================================"
echo "AUTOTELIC ENGINE COMPLETE"
echo "================================================================================"
echo ""
echo "The machine has completed $CYCLES grand cycles."
echo "It has evolved strategies, analyzed its own evolution,"
echo "and redefined its own purpose $CYCLES times."
echo ""
echo "Outputs:"
echo "  - Evolved strategies: evolved_strategies/"
echo "  - Evolutionary history: ascension_ledger.json"
echo "  - Critic analysis: critic_report.json"
echo "  - Current objective: objectives/current_objective.thiele"
echo ""
echo "The purpose is not to find an answer."
echo "The purpose is to continue the search, forever."
echo ""
echo "================================================================================"
