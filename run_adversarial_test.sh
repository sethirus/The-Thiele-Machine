#!/bin/bash
#
# Adversarial Diagnostic Test Script
#
# Tests whether Thiele Machine's efficiency is fully explained by Spectral Decomposition
# or if a deeper principle (P+1) exists. Executes on adversarial graphs designed to be
# failure modes for spectral methods.
#
# Usage: ./run_adversarial_test.sh [graph_type] [size] [trials]
#

set -e  # Exit on error

# Default parameters
GRAPH_TYPE="${1:-lollipop}"
SIZE="${2:-50}"
TRIALS="${3:-3}"
SEED=42

echo "========================================="
echo "Adversarial Diagnostic Test"
echo "========================================="
echo "Graph Type: $GRAPH_TYPE"
echo "Size: $SIZE"
echo "Trials: $TRIALS"
echo "========================================="
echo ""

# Create output directory
OUTPUT_DIR="experiments/adversarial"
mkdir -p "$OUTPUT_DIR"

# Generate adversarial problem instance
echo "[Phase 1] Generating adversarial graph..."
PROBLEM_FILE="$OUTPUT_DIR/adversarial_${GRAPH_TYPE}_n${SIZE}.cnf"
python3 tools/adversarial_generator.py \
    --type "$GRAPH_TYPE" \
    --n "$SIZE" \
    --embed tseitin \
    --output "$PROBLEM_FILE" \
    --seed "$SEED" \
    --analyze

if [ ! -f "$PROBLEM_FILE" ]; then
    echo "Error: Failed to generate problem file"
    exit 1
fi

echo ""
echo "[Phase 2] Testing Thiele Machine on adversarial problem..."

# Run Thiele Machine solver
THIELE_OUTPUT="$OUTPUT_DIR/thiele_result_${GRAPH_TYPE}_n${SIZE}.json"

# Check if run_partition_experiments.py exists, otherwise use alternative
if [ -f "run_partition_experiments.py" ]; then
    echo "Using run_partition_experiments.py..."
    python3 run_partition_experiments.py \
        --problem custom \
        --custom-file "$PROBLEM_FILE" \
        --repeat "$TRIALS" \
        --output "$THIELE_OUTPUT" 2>&1 | tee "$OUTPUT_DIR/thiele_log.txt"
else
    # Fallback: run attempt.py directly
    echo "Using attempt.py directly..."
    python3 -c "
import json
import sys
sys.path.insert(0, '.')
from attempt import run_single_experiment
from pathlib import Path

cnf_file = Path('$PROBLEM_FILE')
results = {
    'problem': '$PROBLEM_FILE',
    'graph_type': '$GRAPH_TYPE',
    'size': $SIZE,
    'trials': []
}

for trial in range($TRIALS):
    print(f'Trial {trial + 1}/$TRIALS...')
    try:
        result = run_single_experiment(str(cnf_file))
        results['trials'].append(result)
    except Exception as e:
        print(f'Trial failed: {e}')
        results['trials'].append({'error': str(e)})

with open('$THIELE_OUTPUT', 'w') as f:
    json.dump(results, f, indent=2)
    
print('\\nThiele Machine results saved to $THIELE_OUTPUT')
" 2>&1 | tee "$OUTPUT_DIR/thiele_log.txt"
fi

echo ""
echo "[Phase 3] Baseline comparison: Classical SAT solver..."

# Run baseline SAT solver comparison
BASELINE_OUTPUT="$OUTPUT_DIR/baseline_result_${GRAPH_TYPE}_n${SIZE}.json"

# Try to use minisat or other SAT solver if available
if command -v minisat &> /dev/null; then
    echo "Using minisat for baseline..."
    BASELINE_RESULT="$OUTPUT_DIR/baseline.out"
    START_TIME=$(date +%s%N)
    timeout 300 minisat "$PROBLEM_FILE" "$BASELINE_RESULT" 2>&1 | tee "$OUTPUT_DIR/baseline_log.txt"
    END_TIME=$(date +%s%N)
    ELAPSED_MS=$(( (END_TIME - START_TIME) / 1000000 ))
    
    echo "{\"solver\": \"minisat\", \"time_ms\": $ELAPSED_MS, \"problem\": \"$PROBLEM_FILE\"}" > "$BASELINE_OUTPUT"
else
    echo "Warning: minisat not found. Skipping baseline comparison."
    echo "{\"solver\": \"none\", \"note\": \"No classical SAT solver available\"}" > "$BASELINE_OUTPUT"
fi

echo ""
echo "[Phase 4] Diagnostic Analysis..."

# Perform diagnostic analysis
python3 -c "
import json
from pathlib import Path

print('='*60)
print('ADVERSARIAL DIAGNOSTIC ANALYSIS')
print('='*60)
print()

# Load metadata
meta_file = Path('$PROBLEM_FILE').with_suffix('.json')
if meta_file.exists():
    with open(meta_file) as f:
        metadata = json.load(f)
    
    print('Problem Characteristics:')
    print(f'  Graph Type: {metadata.get(\"graph_type\", \"unknown\")}')
    print(f'  Nodes: {metadata.get(\"n_nodes\", \"?\")}')
    print(f'  Edges: {metadata.get(\"n_edges\", \"?\")}')
    print(f'  Variables: {metadata.get(\"n_variables\", \"?\")}')
    print(f'  Clauses: {metadata.get(\"n_clauses\", \"?\")}')
    print()
    
    if 'spectral_properties' in metadata:
        props = metadata['spectral_properties']
        print('Spectral Properties (WHY this is adversarial):')
        print(f'  λ₁: {props.get(\"lambda_1\", 0):.6f}')
        print(f'  λ₂: {props.get(\"lambda_2\", 0):.6f}')
        print(f'  λ₃: {props.get(\"lambda_3\", 0):.6f}')
        print(f'  Spectral Gap: {props.get(\"spectral_gap\", 0):.6f}')
        print()
        
        # Determine adversarial characteristics
        gap = props.get('spectral_gap', 0)
        if gap < 0.1:
            print('  ⚠️  VERY SMALL spectral gap - poor eigenvalue separation')
        
        lambda2 = props.get('lambda_2', 0)
        lambda3 = props.get('lambda_3', 0)
        if lambda2 > 0 and lambda3 > 0:
            ratio = lambda3 / lambda2
            if ratio < 1.5:
                print(f'  ⚠️  Poor λ₃/λ₂ ratio ({ratio:.2f}) - ambiguous partition structure')

# Load Thiele results
thiele_file = Path('$THIELE_OUTPUT')
if thiele_file.exists():
    with open(thiele_file) as f:
        thiele_data = json.load(f)
    
    print()
    print('Thiele Machine Performance:')
    trials = thiele_data.get('trials', [])
    if trials:
        mu_costs = [t.get('mu_cost', 0) for t in trials if 'mu_cost' in t]
        times = [t.get('time_ms', 0) for t in trials if 'time_ms' in t]
        
        if mu_costs:
            print(f'  μ-cost (mean): {sum(mu_costs) / len(mu_costs):.2f}')
            print(f'  μ-cost (min): {min(mu_costs):.2f}')
            print(f'  μ-cost (max): {max(mu_costs):.2f}')
        
        if times:
            print(f'  Time (mean): {sum(times) / len(times):.2f} ms')
            print(f'  Trials: {len(trials)}')

# Load baseline results
baseline_file = Path('$BASELINE_OUTPUT')
if baseline_file.exists():
    with open(baseline_file) as f:
        baseline_data = json.load(f)
    
    print()
    print('Baseline Solver Performance:')
    print(f'  Solver: {baseline_data.get(\"solver\", \"unknown\")}')
    if 'time_ms' in baseline_data:
        print(f'  Time: {baseline_data[\"time_ms\"]} ms')

print()
print('='*60)
print('DIAGNOSTIC CONCLUSION')
print('='*60)
print()
print('Hypothesis Test:')
print('  H0: Thiele Machine uses pure Spectral Decomposition')
print('  H1: Thiele Machine uses Spectral Decomposition + P+1')
print()
print('Expected Behavior:')
print('  If H0 (pure spectral): Machine should struggle/fail on this adversarial graph')
print('  If H1 (spectral + P+1): Machine should still succeed despite adversarial structure')
print()
print('Observe:')
print('  - Did the machine solve the problem efficiently?')
print('  - Was μ-cost anomalously low despite poor spectral properties?')
print('  - Did performance deviate from predictions based on spectral gap?')
print()
print('If the machine succeeds where spectral methods should fail,')
print('this provides evidence for P+1 (a principle beyond spectral decomposition).')
print()
" | tee "$OUTPUT_DIR/diagnostic_analysis.txt"

echo ""
echo "========================================="
echo "Adversarial Diagnostic Test Complete"
echo "========================================="
echo ""
echo "Results saved to: $OUTPUT_DIR/"
echo "  - Problem file: $PROBLEM_FILE"
echo "  - Thiele results: $THIELE_OUTPUT"
echo "  - Baseline results: $BASELINE_OUTPUT"
echo "  - Analysis: $OUTPUT_DIR/diagnostic_analysis.txt"
echo ""
echo "Review the diagnostic analysis to determine if evidence supports"
echo "the existence of P+1 (a principle beyond Spectral Decomposition)."
echo ""
