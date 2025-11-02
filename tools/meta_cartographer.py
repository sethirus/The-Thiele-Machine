#!/usr/bin/env python3
"""
The Meta-Cartographer - Atlas of Atlases

This module processes the classification reports from multiple strategy combinations
and extracts their performance metrics to create a meta-atlas that maps strategy
combinations to classification accuracy.

This enables meta-analysis: studying how different ways of seeing (strategy combinations)
affect the ability to distinguish structure from chaos.
"""

import json
import re
from pathlib import Path
from typing import Dict, Any, List


def parse_classification_report(report_path: Path) -> Dict[str, Any]:
    """
    Parse a classification report to extract key metrics.
    
    Args:
        report_path: Path to classification_report.txt
    
    Returns:
        Dictionary with parsed metrics
    """
    with open(report_path, 'r') as f:
        content = f.read()
    
    # Extract cross-validation accuracy
    cv_match = re.search(r'Cross-Validation Accuracy:\s*([\d.]+)\s*±\s*([\d.]+)', content)
    if cv_match:
        cv_accuracy = float(cv_match.group(1))
        cv_std = float(cv_match.group(2))
    else:
        cv_accuracy = None
        cv_std = None
    
    # Extract test accuracy
    acc_match = re.search(r'Accuracy:\s*([\d.]+)', content)
    if acc_match:
        test_accuracy = float(acc_match.group(1))
    else:
        test_accuracy = None
    
    return {
        "cross_validation_accuracy": cv_accuracy,
        "cross_validation_std": cv_std,
        "test_accuracy": test_accuracy
    }


def extract_strategy_combo_from_path(report_path: Path) -> str:
    """
    Extract strategy combination from report path.
    
    Expected format: classification_report_combo{name}.txt
    or from directory: .../combo{name}/...
    
    Args:
        report_path: Path to the report file
    
    Returns:
        Strategy combination identifier
    """
    # Try to extract from filename
    match = re.search(r'combo([^/\.]+)', str(report_path))
    if match:
        return match.group(1)
    
    # Fallback to parent directory name
    if 'combo' in report_path.parent.name:
        return report_path.parent.name.replace('combo', '')
    
    return "unknown"


def generate_meta_atlas(
    meta_observatory_dir: Path = Path("sight_logs/meta_observatory"),
    output_path: Path = Path("sight_logs/meta_atlas/phase4_performance.json")
):
    """
    Generate the Meta-Atlas by processing all classification reports.
    
    Args:
        meta_observatory_dir: Directory containing strategy combination results
        output_path: Path to save the meta-atlas
    """
    print(f"\n{'='*70}")
    print("THE META-CARTOGRAPHER - Generating Atlas of Atlases")
    print(f"{'='*70}")
    print(f"Input directory: {meta_observatory_dir}")
    print(f"Output path: {output_path}")
    print(f"{'='*70}\n")
    
    # Find all classification reports
    report_files = list(meta_observatory_dir.glob("**/classification_report*.txt"))
    
    if not report_files:
        print("⚠️ No classification reports found")
        return
    
    print(f"Found {len(report_files)} classification reports to process\n")
    
    performance_map = {}
    
    for i, report_path in enumerate(report_files, 1):
        combo_id = extract_strategy_combo_from_path(report_path)
        print(f"[{i}/{len(report_files)}] Processing combo {combo_id}...", end=" ")
        
        try:
            metrics = parse_classification_report(report_path)
            
            if metrics["cross_validation_accuracy"] is not None:
                performance_map[combo_id] = {
                    "cv_accuracy": metrics["cross_validation_accuracy"],
                    "cv_std": metrics["cross_validation_std"],
                    "test_accuracy": metrics["test_accuracy"],
                    "report_file": str(report_path)
                }
                print(f"✓ CV Accuracy: {metrics['cross_validation_accuracy']:.4f}")
            else:
                print("⚠️ Could not parse accuracy")
        except Exception as e:
            print(f"✗ Error: {e}")
    
    # Create meta-atlas
    meta_atlas = {
        "version": "1.0",
        "description": "Meta-atlas mapping strategy combinations to classification performance",
        "num_combinations": len(performance_map),
        "combinations": performance_map
    }
    
    # Save meta-atlas
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w') as f:
        json.dump(meta_atlas, f, indent=2)
    
    print(f"\n{'='*70}")
    print(f"✓ Meta-Atlas generated: {len(performance_map)} strategy combinations")
    print(f"✓ Saved to: {output_path}")
    print(f"{'='*70}\n")
    
    # Print summary
    if performance_map:
        accuracies = [v["cv_accuracy"] for v in performance_map.values()]
        print("Performance Summary:")
        print(f"  Min accuracy: {min(accuracies):.4f}")
        print(f"  Max accuracy: {max(accuracies):.4f}")
        print(f"  Mean accuracy: {sum(accuracies)/len(accuracies):.4f}")
        print()


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Generate Meta-Atlas from classification reports")
    parser.add_argument("--input-dir", type=Path, default=Path("sight_logs/meta_observatory"),
                       help="Directory containing strategy combination results")
    parser.add_argument("--output", type=Path, default=Path("sight_logs/meta_atlas/phase4_performance.json"),
                       help="Output path for meta-atlas")
    
    args = parser.parse_args()
    
    generate_meta_atlas(args.input_dir, args.output)
