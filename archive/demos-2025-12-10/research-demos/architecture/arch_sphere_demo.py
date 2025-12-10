#!/usr/bin/env python3
"""
Demo: Arch-Sphere Concept
Demonstrates the meta-analysis framework with a small example.
"""

import json
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from tools.sight_logging import assemble_log
from tools.cartographer import build_strategy_graph, compute_geometric_metrics

print("="*70)
print("ARCH-SPHERE DEMONSTRATION")
print("="*70)
print()
print("This demo shows how different strategy combinations produce different")
print("geometric signatures from the same problem.")
print()

# Create a simple test problem (3-SAT clauses)
test_clauses = [
    [1, 2, 3],
    [-1, 2, 4],
    [-2, 3, 4],
    [1, -3, 4],
    [-1, -2, -3],
    [2, 3, -4]
]

# Test different strategy combinations
strategy_combinations = {
    "All Four": ["louvain", "spectral", "degree", "balanced"],
    "Pair 1": ["louvain", "spectral"],
    "Pair 2": ["degree", "balanced"],
    "Triplet": ["louvain", "degree", "balanced"],
    "Single": ["louvain"]
}

print("Testing strategy combinations on a 4-variable 3-SAT problem:")
print()

results = {}

for combo_name, strategies in strategy_combinations.items():
    print(f"→ {combo_name}: {', '.join(strategies)}")
    
    try:
        # Generate sight log with this combination
        log = assemble_log(
            clauses=test_clauses,
            problem_name=f"demo_{combo_name.replace(' ', '_')}",
            n=4,
            seed=42,
            verdict="CONSISTENT",
            strategy_list=strategies
        )
        
        # Extract VI matrix and compute metrics
        vi_matrix = log["consistency_analysis"]["vi_matrix"]
        
        if len(vi_matrix) > 1:  # Need at least 2 strategies for graph
            G = build_strategy_graph(vi_matrix)
            metrics = compute_geometric_metrics(G)
            
            results[combo_name] = {
                "num_strategies": len(strategies),
                "avg_vi": metrics["average_edge_weight"],
                "max_vi": metrics["max_edge_weight"],
                "std_vi": metrics["edge_weight_stddev"]
            }
            
            print(f"   Avg VI: {metrics['average_edge_weight']:.4f}")
            print(f"   Max VI: {metrics['max_edge_weight']:.4f}")
            print(f"   Std VI: {metrics['edge_weight_stddev']:.4f}")
        else:
            print(f"   (Single strategy - no VI matrix)")
            results[combo_name] = {"num_strategies": 1, "note": "single_strategy"}
        
    except Exception as e:
        print(f"   ✗ Error: {e}")
    
    print()

print("="*70)
print("INTERPRETATION")
print("="*70)
print()
print("Different combinations of strategies produce different geometric")
print("signatures. The Arch-Sphere analyzes which combination best")
print("distinguishes structured from chaotic problems.")
print()
print("In the full meta-observatory:")
print("  1. Each combination generates sight logs for many problems")
print("  2. Classification accuracy is measured for each combination")
print("  3. The optimal combination is identified")
print()
print("This answers: 'What is the best possible way to see?'")
print()
print("="*70)

# Save demo results
demo_output = Path("sight_logs/meta_atlas")
demo_output.mkdir(parents=True, exist_ok=True)

with open(demo_output / "demo_results.json", 'w') as f:
    json.dump(results, f, indent=2)

print(f"\n✓ Demo results saved to {demo_output}/demo_results.json\n")
