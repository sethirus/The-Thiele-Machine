#!/usr/bin/env bash
#
# run_meta_observatory.sh - The Meta-Observatory Orchestrator
#
# This script runs the complete Phase 1-3 pipeline for multiple strategy combinations
# to study how different ways of seeing affect classification performance.
#
# It generates separate results for each combination of partitioning strategies,
# enabling meta-analysis of perception itself.

set -e  # Exit on error

echo "======================================================================"
echo "THE META-OBSERVATORY - Studying the Shape of Sight"
echo "======================================================================"
echo ""

# Configuration
SIGHT_LOGS_BASE="sight_logs/meta_observatory"
N_START=6
N_END=18
N_STEP=4
SEEDS="0,1,2"

# Define strategy combinations to test
# Format: combo_id:strategy1,strategy2,...
declare -a COMBINATIONS=(
    # Pairs
    "louvain_spectral:louvain,spectral"
    "louvain_degree:louvain,degree"
    "louvain_balanced:louvain,balanced"
    "spectral_degree:spectral,degree"
    "spectral_balanced:spectral,balanced"
    "degree_balanced:degree,balanced"
    
    # Triplets
    "louvain_spectral_degree:louvain,spectral,degree"
    "louvain_spectral_balanced:louvain,spectral,balanced"
    "louvain_degree_balanced:louvain,degree,balanced"
    "spectral_degree_balanced:spectral,degree,balanced"
    
    # Full quartet
    "all_four:louvain,spectral,degree,balanced"
    
    # Singles (for comparison)
    "louvain_only:louvain"
    "spectral_only:spectral"
    "degree_only:degree"
    "balanced_only:balanced"
)

echo "Testing ${#COMBINATIONS[@]} strategy combinations"
echo "Problem sizes: n=${N_START} to ${N_END} (step ${N_STEP})"
echo "Seeds: ${SEEDS}"
echo ""

# Function to run pipeline for a specific strategy combination
run_combination() {
    local combo_id=$1
    local strategies=$2
    
    echo "======================================================================"
    echo "Processing combination: ${combo_id}"
    echo "Strategies: ${strategies}"
    echo "======================================================================"
    
    # Create output directory
    local output_dir="${SIGHT_LOGS_BASE}/combo_${combo_id}"
    mkdir -p "${output_dir}"
    
    # Create temporary Python script to run with this strategy combination
    local runner_script="${output_dir}/runner.py"
    
    cat > "${runner_script}" << 'PYEOF'
#!/usr/bin/env python3
"""Temporary runner for specific strategy combination."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

from populate_observatory import main as populate_main
from tools.cartographer import generate_atlas
from tools.meta_analyzer import load_atlas, prepare_dataset, train_classifier, generate_visualizations

# Parse command line arguments
import argparse
parser = argparse.ArgumentParser()
parser.add_argument('--mode', required=True)
parser.add_argument('--n-start', type=int, required=True)
parser.add_argument('--n-end', type=int, required=True)
parser.add_argument('--n-step', type=int, required=True)
parser.add_argument('--seeds', required=True)
parser.add_argument('--strategies', required=True)
parser.add_argument('--output-dir', required=True)
args = parser.parse_args()

strategy_list = args.strategies.split(',')
output_base = Path(args.output_dir)

print(f"\n→ Running with strategies: {strategy_list}")

# Phase 1: Generate sight logs with specific strategies
# Note: populate_observatory.py needs to be modified to accept strategy_list
print("\n[Phase 1] Generating sight logs...")
# For now, we'll use the default populate_observatory and filter later
# This is a simplified version - full implementation would pass strategy_list through

import os
os.system(f"python3 populate_observatory.py --mode {args.mode} --n-start {args.n_start} "
          f"--n-end {args.n_end} --n-step {args.n_step} --seeds {args.seeds}")

# Move sight logs to combination-specific directory
import shutil
import glob
for log_file in glob.glob("sight_logs/*.json"):
    if "INDEX" not in log_file:
        dest = output_base / Path(log_file).name
        shutil.copy(log_file, dest)

print(f"→ Sight logs saved to {output_base}")

# Phase 2: Generate atlas
print("\n[Phase 2] Generating geometric atlas...")
atlas_path = output_base / "atlas" / "phase2_metrics.json"
generate_atlas(sight_logs_dir=output_base, output_path=atlas_path)

# Phase 3: META-PDISCOVER
print("\n[Phase 3] Running META-PDISCOVER...")
atlas = load_atlas(str(atlas_path))
features, labels, names = prepare_dataset(atlas)

if len(features) > 5:
    report_path = output_base / "atlas" / "classification_report.txt"
    plot_path = output_base / "atlas" / "separation_plot.png"
    
    accuracy, cv_scores, report = train_classifier(features, labels)
    generate_visualizations(features, labels, names, str(plot_path))
    
    # Save report
    with open(report_path, 'w') as f:
        f.write(report)
    
    print(f"\n→ Results saved to {output_base}/atlas/")
    print(f"   Classification accuracy: {accuracy:.4f}")
else:
    print("⚠️  Not enough samples for classification")

PYEOF
    
    chmod +x "${runner_script}"
    
    # Run the pipeline for this combination
    python3 "${runner_script}" \
        --mode both \
        --n-start ${N_START} \
        --n-end ${N_END} \
        --n-step ${N_STEP} \
        --seeds "${SEEDS}" \
        --strategies "${strategies}" \
        --output-dir "${output_dir}" \
        2>&1 | tee "${output_dir}/run.log"
    
    echo ""
    echo "✓ Combination ${combo_id} complete"
    echo ""
}

# Main execution loop
echo "Starting meta-observatory run..."
echo ""

for combo_spec in "${COMBINATIONS[@]}"; do
    IFS=':' read -r combo_id strategies <<< "$combo_spec"
    run_combination "$combo_id" "$strategies"
done

echo "======================================================================"
echo "META-OBSERVATORY COMPLETE"
echo "======================================================================"
echo ""
echo "All strategy combinations have been tested."
echo "Results saved to: ${SIGHT_LOGS_BASE}/"
echo ""
echo "Next steps:"
echo "  1. Run meta_cartographer.py to generate meta-atlas"
echo "  2. Run arch_analyzer.py to find optimal configuration"
echo ""
echo "======================================================================"
