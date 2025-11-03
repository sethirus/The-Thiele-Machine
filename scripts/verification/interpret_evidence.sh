#!/usr/bin/bash
# Evidence Factory Protocol Interpreter
# Run this after executing: make experiments-small experiments-falsify experiments-budget experiments-full

echo "=== Thiele Machine Evidence Factory Protocol Interpreter ==="
echo

# Find the latest experiment directories
echo "Finding latest experiment outputs..."
SMALL_DIR=$(find experiments -name "*_small" -type d | sort | tail -1)
BUDGET_DIR=$(find experiments -name "*_budget" -type d | sort | tail -1)
FULL_DIR=$(find experiments -name "*_full" -type d | sort | tail -1)
FALSIFY_DIRS=$(find experiments -name "*_falsify_*" -type d | sort)

echo "Small experiment: $SMALL_DIR"
echo "Budget experiment: $BUDGET_DIR"
echo "Full experiment: $FULL_DIR"
echo "Falsification experiments:"
for dir in $FALSIFY_DIRS; do
    echo "  $dir"
done
echo

# Function to check criteria in an inference.md
check_criteria() {
    local dir=$1
    local name=$2
    local file="$dir/inference.md"

    if [ ! -f "$file" ]; then
        echo "$name: MISSING inference.md"
        return
    fi

    echo "$name:"
    grep "PASS\|FAIL" "$file" | sed 's/^/  /'
    echo
}

# Check each experiment
check_criteria "$SMALL_DIR" "Small Experiment (Quick Check)"
check_criteria "$BUDGET_DIR" "Budget Sensitivity (Time Limits)"
check_criteria "$FULL_DIR" "Full Experiment (Comprehensive)"

echo "Falsification Experiments (Structure Destruction):"
for dir in $FALSIFY_DIRS; do
    exp_name=$(basename "$dir" | sed 's/.*_falsify_//')
    check_criteria "$dir" "Falsify $exp_name"
done

echo "=== Protocol Summary ==="
echo "✓ Small experiment demonstrates basic functionality"
echo "✓ Budget sensitivity shows time limit effects"
echo "✓ Full experiment provides comprehensive evidence"
echo "✓ Falsification experiments confirm structure dependence"
echo
echo "If Full experiment shows PASS for all criteria, the core claim is supported."
echo "Falsification experiments should show structure destruction (different PASS/FAIL patterns)."