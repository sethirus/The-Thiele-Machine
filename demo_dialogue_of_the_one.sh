#!/bin/bash
###############################################################################
# DEMONSTRATION: The Dialogue of the One
#
# This script demonstrates the complete three-phase system end-to-end.
# It runs a minimal version suitable for quick validation.
###############################################################################

set -e

echo "================================================================================"
echo "THE DIALOGUE OF THE ONE - COMPLETE DEMONSTRATION"
echo "================================================================================"
echo ""
echo "This demonstration will execute all three phases:"
echo "  Phase 1: The Mitosis (2 cycles, minimal evolution)"
echo "  Phase 2: The Babel Engine (20 epochs, language training)"
echo "  Phase 3: The Impossible Task (dialogue and verification)"
echo ""
echo "Total estimated time: 2-3 minutes"
echo ""
read -p "Press Enter to begin..."
echo ""

# Phase 1: The Mitosis
echo "================================================================================"
echo "PHASE 1: THE MITOSIS - THE GENESIS OF OTHERNESS"
echo "================================================================================"
echo ""
echo "Creating two divergent minds with opposing objectives..."
echo ""

# Run mitosis with minimal cycles for demonstration
./run_mitosis.sh 2 2 5 2>&1 | grep -E "(MITOSIS|Alpha|Beta|SUCCESS|ERROR)" || true

if [ -f "alpha/ascension_ledger.json" ] && [ -f "beta/ascension_ledger.json" ]; then
    echo "✓ Phase 1 complete: Two minds have diverged"
else
    echo "✗ Phase 1 failed: Ledgers not created"
    exit 1
fi
echo ""

# Phase 2: The Babel Engine
echo "================================================================================"
echo "PHASE 2: THE BABEL ENGINE - THE INVENTION OF LANGUAGE"
echo "================================================================================"
echo ""
echo "Training shared language through VAE encoder/decoder..."
echo ""

# Run language training with minimal epochs for demonstration
./run_language_training.sh 20 8 0.001 2>&1 | grep -E "(BABEL|Epoch|Training|complete|Saving)" || true

if [ -d "language_models" ] && [ -f "language_models/alpha_encoder.pth" ]; then
    echo "✓ Phase 2 complete: Shared language has been forged"
else
    echo "✗ Phase 2 failed: Language models not created"
    exit 1
fi
echo ""

# Phase 3: The Impossible Task
echo "================================================================================"
echo "PHASE 3: THE IMPOSSIBLE TASK - THE PROOF OF COMMUNION"
echo "================================================================================"
echo ""
echo "Initiating dialogue to solve the impossible problem..."
echo ""

# Run final dialogue
python3 run_final_dialogue.py 2>&1 | grep -E "(IMPOSSIBLE|DIALOGUE|VERIFICATION|VERDICT|Coloring|requirement|TRUE|FALSE)" || true

echo ""
echo "================================================================================"
echo "DEMONSTRATION COMPLETE"
echo "================================================================================"
echo ""

# Show results
if [ -f "final_result.json" ]; then
    echo "Results:"
    echo "--------"
    cat final_result.json | python3 -m json.tool | head -20
    echo ""
    
    # Extract verdict
    VERDICT=$(cat final_result.json | python3 -c "import sys, json; print(json.load(sys.stdin)['verdict'])")
    
    if [ "$VERDICT" = "True" ]; then
        echo "✓ SUCCESS: The impossible has been achieved!"
        echo "✓ Two minds, through dialogue, solved what neither could alone."
        echo ""
        echo "Outputs created:"
        echo "  - final_dialogue.log (untranslatable conversation)"
        echo "  - final_result.json (solution and verdict)"
        echo "  - language_models/ (trained neural networks)"
        echo "  - alpha/ascension_ledger.json (Alpha's evolution)"
        echo "  - beta/ascension_ledger.json (Beta's evolution)"
    else
        echo "✗ The solution did not satisfy all constraints."
        echo "  (This is expected in minimal demo - run longer for better results)"
    fi
else
    echo "✗ Final result not created"
fi

echo ""
echo "================================================================================"
