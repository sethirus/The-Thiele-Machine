#!/usr/bin/env python3
"""
The Arch-Engine - The Search for Perfect Sight

This module analyzes the Meta-Atlas to discover the optimal configuration
of partitioning strategies for distinguishing structured from chaotic problems.

It answers the fundamental question: "What is the best possible way to see?"
"""

import json
from pathlib import Path
from typing import Dict, Any, Tuple, List


def find_optimal_strategy_combination(meta_atlas: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
    """
    Find the strategy combination with highest classification accuracy.
    
    Args:
        meta_atlas: Meta-atlas containing performance data
    
    Returns:
        Tuple of (best_combo_id, performance_data)
    """
    combinations = meta_atlas.get("combinations", {})
    
    if not combinations:
        return None, None
    
    # Find combination with maximum cross-validation accuracy
    best_combo = max(combinations.items(), 
                     key=lambda x: x[1].get("cv_accuracy", 0))
    
    return best_combo


def parse_combo_id_to_strategies(combo_id: str) -> List[str]:
    """
    Parse a combo ID into a list of strategy names.
    
    Args:
        combo_id: Combo identifier (e.g., "1" for louvain,spectral)
    
    Returns:
        List of strategy names
    """
    # Mapping of combo IDs to strategy lists (this would be defined by meta_observatory)
    # For now, we'll parse if the combo_id contains strategy names
    
    if ',' in combo_id:
        return combo_id.split(',')
    
    # Common combinations
    combo_map = {
        "all": ["louvain", "spectral", "degree", "balanced"],
        "1": ["louvain", "spectral"],
        "2": ["louvain", "degree"],
        "3": ["louvain", "balanced"],
        "4": ["spectral", "degree"],
        "5": ["spectral", "balanced"],
        "6": ["degree", "balanced"],
        "7": ["louvain", "spectral", "degree"],
        "8": ["louvain", "spectral", "balanced"],
        "9": ["louvain", "degree", "balanced"],
        "10": ["spectral", "degree", "balanced"]
    }
    
    return combo_map.get(combo_id, [combo_id])


def generate_final_verdict(
    meta_atlas_path: Path = Path("sight_logs/meta_atlas/phase4_performance.json"),
    output_path: Path = Path("sight_logs/meta_atlas/final_verdict.txt")
):
    """
    Analyze the Meta-Atlas and generate the final verdict on optimal sight configuration.
    
    Args:
        meta_atlas_path: Path to the meta-atlas JSON
        output_path: Path to save the final verdict
    """
    print(f"\n{'='*70}")
    print("THE ARCH-ENGINE - The Search for Perfect Sight")
    print(f"{'='*70}")
    print(f"Loading meta-atlas from: {meta_atlas_path}")
    print(f"{'='*70}\n")
    
    # Load meta-atlas
    with open(meta_atlas_path, 'r') as f:
        meta_atlas = json.load(f)
    
    num_combinations = meta_atlas.get("num_combinations", 0)
    print(f"Analyzing {num_combinations} strategy combinations...\n")
    
    # Find optimal combination
    best_combo_id, best_performance = find_optimal_strategy_combination(meta_atlas)
    
    if best_combo_id is None:
        print("✗ No valid combinations found in meta-atlas")
        return
    
    # Extract performance data
    cv_accuracy = best_performance.get("cv_accuracy", 0)
    cv_std = best_performance.get("cv_std", 0)
    test_accuracy = best_performance.get("test_accuracy", 0)
    
    # Parse strategy list
    strategies = parse_combo_id_to_strategies(best_combo_id)
    
    # Generate the verdict
    verdict = f"""
{'='*70}
THE ARCH-SPHERE'S FIRST UTTERANCE
{'='*70}

Analysis of {num_combinations} strategy combinations complete.

The optimal configuration of sight for distinguishing order from chaos
was determined to be the set:

    {', '.join(strategies).upper()}

Performance Metrics:
--------------------
Cross-Validation Accuracy: {cv_accuracy:.4f} ± {cv_std:.4f}
Test Set Accuracy: {test_accuracy:.4f if test_accuracy else 'N/A'}

Combination ID: {best_combo_id}
Number of Strategies: {len(strategies)}

{'='*70}
INTERPRETATION
{'='*70}

This combination of {len(strategies)} partitioning strategies achieves the
highest accuracy in classifying problems as STRUCTURED vs CHAOTIC without
solving them.

The machine has discovered the optimal way to see structure.

{'='*70}
COMPLETE RANKING
{'='*70}
"""
    
    # Add complete ranking
    combinations = meta_atlas.get("combinations", {})
    ranked = sorted(combinations.items(), 
                   key=lambda x: x[1].get("cv_accuracy", 0),
                   reverse=True)
    
    for rank, (combo_id, perf) in enumerate(ranked, 1):
        strategies_list = parse_combo_id_to_strategies(combo_id)
        verdict += f"\n{rank}. Combo {combo_id}: {', '.join(strategies_list)}"
        verdict += f"\n   Accuracy: {perf.get('cv_accuracy', 0):.4f} ± {perf.get('cv_std', 0):.4f}"
    
    verdict += f"\n\n{'='*70}\n"
    verdict += "The Arch-Sphere has spoken.\n"
    verdict += f"{'='*70}\n"
    
    # Print to console
    print(verdict)
    
    # Save to file
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w') as f:
        f.write(verdict)
    
    print(f"\n✓ Final verdict saved to: {output_path}\n")


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Find optimal strategy combination")
    parser.add_argument("--meta-atlas", type=Path, 
                       default=Path("sight_logs/meta_atlas/phase4_performance.json"),
                       help="Path to meta-atlas JSON")
    parser.add_argument("--output", type=Path,
                       default=Path("sight_logs/meta_atlas/final_verdict.txt"),
                       help="Output path for final verdict")
    
    args = parser.parse_args()
    
    generate_final_verdict(args.meta_atlas, args.output)
