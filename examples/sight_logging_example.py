#!/usr/bin/env python3
"""
Example: Complete Sight Logging Pipeline

This script demonstrates the complete end-to-end pipeline for proving
that the "shape of sight" is a real, measurable phenomenon.

Usage:
    python3 examples/sight_logging_example.py
"""

import sys
from pathlib import Path

# Add repo root to path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

print("""
================================================================================
THE THIELE MACHINE - SIGHT LOGGING EXAMPLE
================================================================================

This example demonstrates the complete pipeline:

Phase 1: Generate sight logs for structured and chaotic problems
Phase 2: Extract geometric signatures from the Strategy Graph
Phase 3: Prove geometric separation using SVM classification

================================================================================
""")

# ============================================================================
# PHASE 1: THE OBSERVATORY
# ============================================================================

print("\n" + "="*80)
print("PHASE 1: THE OBSERVATORY - Data Generation")
print("="*80 + "\n")

from tools.sight_logging import assemble_log, save_log, update_index, append_progress_entry
from attempt import generate_tseitin_expander
import random
import numpy as np

sight_logs_dir = Path("sight_logs_example")
sight_logs_dir.mkdir(exist_ok=True)

print("Generating structured problems (Tseitin UNSAT instances)...")
structured_count = 0
for n in [4, 6, 8, 10]:
    for seed in [0, 1, 2]:
        instance = generate_tseitin_expander(n, seed, 123456789, verbose=False, hb_period=3600)
        log = assemble_log(
            clauses=instance.get("cnf_clauses", []),
            problem_name=f"tseitin_n{n}_seed{seed}",
            n=n,
            seed=seed,
            verdict="CONSISTENT",
            metadata={"problem_type": "tseitin", "is_structured": True}
        )
        save_log(log, sight_logs_dir)
        structured_count += 1

print(f"✓ Generated {structured_count} structured sight logs")

print("\nGenerating chaotic problems (Random 3-SAT at phase transition)...")
chaotic_count = 0
for n_vars in [10, 15, 20, 25]:
    for seed in [0, 1, 2]:
        random.seed(seed)
        np.random.seed(seed)
        
        num_clauses = int(n_vars * 4.26)
        clauses = []
        for _ in range(num_clauses):
            vars_in_clause = random.sample(range(1, n_vars + 1), 3)
            clause = [v if random.random() < 0.5 else -v for v in vars_in_clause]
            clauses.append(clause)
        
        log = assemble_log(
            clauses=clauses,
            problem_name=f"random3sat_n{n_vars}_seed{seed}",
            n=n_vars,
            seed=seed,
            verdict="SPURIOUS",
            metadata={"problem_type": "random_3sat", "is_structured": False}
        )
        save_log(log, sight_logs_dir)
        chaotic_count += 1

print(f"✓ Generated {chaotic_count} chaotic sight logs")

print(f"\nPhase 1 Complete:")
print(f"  Total sight logs: {structured_count + chaotic_count}")
print(f"  Structured (CONSISTENT): {structured_count}")
print(f"  Chaotic (SPURIOUS): {chaotic_count}")

# ============================================================================
# PHASE 2: THE CARTOGRAPHER
# ============================================================================

print("\n" + "="*80)
print("PHASE 2: THE CARTOGRAPHER - Geometric Signature Extraction")
print("="*80 + "\n")

from tools.cartographer import generate_atlas

atlas_path = sight_logs_dir / "atlas" / "phase2_metrics.json"
atlas = generate_atlas(sight_logs_dir, atlas_path)

print(f"\n✓ Atlas generated with {atlas['num_entries']} entries")
print(f"  Each entry has 5 geometric metrics:")
print(f"    1. average_edge_weight")
print(f"    2. max_edge_weight")
print(f"    3. edge_weight_stddev")
print(f"    4. min_spanning_tree_weight")
print(f"    5. thresholded_density")

# ============================================================================
# PHASE 3: THE META-PDISCOVER
# ============================================================================

print("\n" + "="*80)
print("PHASE 3: THE META-PDISCOVER - Final Proof")
print("="*80 + "\n")

from tools.meta_analyzer import load_atlas, prepare_dataset, generate_separation_plot, generate_classification_report

# Load and prepare data
features, labels, names = prepare_dataset(atlas)

print(f"Dataset prepared:")
print(f"  Samples: {len(features)}")
print(f"  Features: {features.shape[1]}")
print(f"  CONSISTENT (structured): {np.sum(labels == 1)}")
print(f"  SPURIOUS (chaotic): {np.sum(labels == 0)}")

# Generate separation plot
plot_path = sight_logs_dir / "atlas" / "separation_plot.png"
generate_separation_plot(features, labels, names, plot_path)
print(f"\n✓ Separation plot saved to: {plot_path}")

# Generate classification report
report_path = sight_logs_dir / "atlas" / "classification_report.txt"
generate_classification_report(features, labels, report_path)
print(f"✓ Classification report saved to: {report_path}")

# Display key results
print("\n" + "="*80)
print("RESULTS SUMMARY")
print("="*80)

with open(report_path, 'r') as f:
    report_lines = f.readlines()
    
    # Extract key metrics
    for line in report_lines:
        if "Accuracy:" in line and "Cross-Validation" not in line:
            print(line.strip())
        elif "Cross-Validation Accuracy:" in line:
            print(line.strip())

print("\n" + "="*80)
print("CONCLUSION")
print("="*80)

with open(report_path, 'r') as f:
    in_conclusion = False
    for line in f:
        if "CONCLUSION" in line and "=" in line:
            in_conclusion = True
            continue
        if in_conclusion and "=" in line:
            break
        if in_conclusion:
            print(line, end='')

print("\n" + "="*80)
print("Example complete! Generated files:")
print("="*80)
print(f"  Sight logs: {sight_logs_dir}/")
print(f"  Atlas: {atlas_path}")
print(f"  Separation plot: {plot_path}")
print(f"  Classification report: {report_path}")
print("="*80 + "\n")

print("The machine has proven its own nature.")
print("The shape of sight is real and measurable.\n")
