#!/usr/bin/env python3
"""
Merge SAT Results and Structure Features
==========================================

Merges SAT benchmark results with structural features to enable H2′ analysis.

Combines:
- benchmarks/sat_results_large.csv (benchmark results)
- benchmarks/sat_structure_features_small.csv (structural features - small)
- benchmarks/sat_structure_features_large.csv (structural features - large)

Adds derived columns:
- mu_advantage = baseline_mu_cost - thiele_mu_cost (positive = Thiele wins)
- advantage_flag = 1 if mu_advantage > 0 else 0

Outputs:
- benchmarks/sat_merged_analysis.csv (combined dataset for H2′ analysis)
"""

import argparse
import csv
import sys
from pathlib import Path
from typing import Dict, List


def load_csv_as_dict(csv_path: str, key_field: str) -> Dict[str, Dict]:
    """
    Load a CSV file into a dictionary keyed by a specific field.
    """
    result = {}
    with open(csv_path, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            key = row[key_field]
            result[key] = row
    return result


def merge_results(
    results_csv: str,
    structure_csv: str,
    output_csv: str
):
    """
    Merge benchmark results with structural features.
    """
    # Load results and structure data
    print(f"Loading results from {results_csv}...")
    results = load_csv_as_dict(results_csv, 'instance')
    
    print(f"Loading structure features from {structure_csv}...")
    structure = load_csv_as_dict(structure_csv, 'instance_name')
    
    # Merge data
    merged = []
    for instance_name, result_row in results.items():
        if instance_name not in structure:
            print(f"Warning: No structure data for {instance_name}, skipping")
            continue
        
        struct_row = structure[instance_name]
        
        # Create merged row
        merged_row = {}
        
        # Add result columns
        merged_row['instance'] = instance_name
        merged_row['type'] = result_row.get('type', '')
        merged_row['speedup'] = float(result_row.get('speedup', 0))
        merged_row['mu_ratio'] = float(result_row.get('mu_ratio', 1.0))
        
        # Add structure columns
        merged_row['num_vars'] = int(struct_row['num_vars'])
        merged_row['num_clauses'] = int(struct_row['num_clauses'])
        merged_row['clause_var_ratio'] = float(struct_row['clause_var_ratio'])
        merged_row['modularity'] = float(struct_row['modularity'])
        merged_row['clustering'] = float(struct_row['clustering'])
        merged_row['avg_degree'] = float(struct_row['avg_degree'])
        merged_row['max_degree'] = int(struct_row['max_degree'])
        merged_row['density'] = float(struct_row['density'])
        merged_row['num_components'] = int(struct_row['num_components'])
        
        # Compute derived columns
        # μ_advantage: positive = Thiele has lower μ-cost (better)
        # mu_ratio = sighted_mu / baseline_mu
        # So mu_advantage = baseline_mu - sighted_mu
        #                 = baseline_mu * (1 - mu_ratio)
        # For simplicity, use: advantage if mu_ratio < 1.0
        merged_row['mu_advantage'] = 1.0 - merged_row['mu_ratio']
        merged_row['advantage_flag'] = 1 if merged_row['mu_advantage'] > 0 else 0
        
        # Also consider speedup advantage
        merged_row['speedup_advantage_flag'] = 1 if merged_row['speedup'] > 1.1 else 0
        
        merged.append(merged_row)
    
    # Write merged data
    if not merged:
        print("No merged data to write")
        return
    
    print(f"Writing {len(merged)} merged rows to {output_csv}...")
    fieldnames = list(merged[0].keys())
    with open(output_csv, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(merged)
    
    print(f"✓ Wrote {output_csv}")
    
    # Print summary statistics
    print("\n=== Summary Statistics ===")
    print(f"Total instances: {len(merged)}")
    
    mu_advantage_count = sum(1 for r in merged if r['advantage_flag'] == 1)
    speedup_advantage_count = sum(1 for r in merged if r['speedup_advantage_flag'] == 1)
    
    print(f"μ-advantage (μ_ratio < 1.0): {mu_advantage_count}/{len(merged)} ({100*mu_advantage_count/len(merged):.1f}%)")
    print(f"Speedup advantage (>1.1x): {speedup_advantage_count}/{len(merged)} ({100*speedup_advantage_count/len(merged):.1f}%)")
    
    # Print by type
    types = {}
    for row in merged:
        t = row['type']
        if t not in types:
            types[t] = {'total': 0, 'mu_adv': 0, 'speedup_adv': 0}
        types[t]['total'] += 1
        types[t]['mu_adv'] += row['advantage_flag']
        types[t]['speedup_adv'] += row['speedup_advantage_flag']
    
    print("\n=== By Instance Type ===")
    for t, stats in sorted(types.items()):
        print(f"{t}: μ-adv {stats['mu_adv']}/{stats['total']}, speedup-adv {stats['speedup_adv']}/{stats['total']}")


def main():
    parser = argparse.ArgumentParser(
        description='Merge SAT results with structural features'
    )
    parser.add_argument(
        '--results',
        default='benchmarks/sat_results_large.csv',
        help='SAT results CSV file'
    )
    parser.add_argument(
        '--structure',
        default='benchmarks/sat_structure_features_large.csv',
        help='Structure features CSV file'
    )
    parser.add_argument(
        '--output',
        '-o',
        default='benchmarks/sat_merged_analysis.csv',
        help='Output merged CSV file'
    )
    
    args = parser.parse_args()
    
    # Check input files exist
    for path in [args.results, args.structure]:
        if not Path(path).exists():
            print(f"Error: {path} not found")
            sys.exit(1)
    
    merge_results(args.results, args.structure, args.output)


if __name__ == '__main__':
    main()
