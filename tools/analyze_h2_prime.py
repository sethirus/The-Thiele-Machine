#!/usr/bin/env python3
"""
H2′ (Restricted Structural Advantage) Analysis
===============================================

Analyzes whether structural features predict μ-advantage in SAT solving.

H2′ Hypothesis: For SAT instances with strong modular structure (high modularity),
μ-guided partition-aware search will more often achieve lower μ-cost than baseline.

This script:
1. Bins instances by structural metrics (modularity, clustering, etc.)
2. Computes advantage rate per bin
3. Tests whether high-structure bins show higher advantage rates
"""

import argparse
import csv
import sys
from pathlib import Path
from typing import Dict, List, Tuple
import statistics


def load_merged_data(csv_path: str) -> List[Dict]:
    """Load the merged SAT analysis data."""
    with open(csv_path, 'r') as f:
        reader = csv.DictReader(f)
        return list(reader)


def bin_by_metric(
    data: List[Dict],
    metric_name: str,
    num_bins: int = 4
) -> List[Tuple[Tuple[float, float], List[Dict]]]:
    """
    Bin instances by a structural metric.
    
    Returns list of (bin_range, instances_in_bin) tuples.
    """
    # Extract metric values
    values = [float(row[metric_name]) for row in data]
    
    if not values:
        return []
    
    # Determine bin edges
    min_val = min(values)
    max_val = max(values)
    
    if min_val == max_val:
        return [((min_val, max_val), data)]
    
    bin_width = (max_val - min_val) / num_bins
    bins = []
    
    for i in range(num_bins):
        bin_start = min_val + i * bin_width
        bin_end = min_val + (i + 1) * bin_width
        
        # Include instances in this bin
        if i == num_bins - 1:
            # Last bin includes max value
            instances = [
                row for row in data
                if bin_start <= float(row[metric_name]) <= bin_end
            ]
        else:
            instances = [
                row for row in data
                if bin_start <= float(row[metric_name]) < bin_end
            ]
        
        if instances:
            bins.append(((bin_start, bin_end), instances))
    
    return bins


def analyze_bins(bins: List[Tuple[Tuple[float, float], List[Dict]]], metric_name: str):
    """Analyze and print advantage rates per bin."""
    print(f"\n{'='*70}")
    print(f"Analysis by {metric_name.upper()}")
    print(f"{'='*70}")
    print(f"{'Bin Range':<20} {'Count':<8} {'μ-Adv Rate':<15} {'Speedup-Adv Rate'}")
    print("-" * 70)
    
    bin_advantage_rates = []
    
    for (bin_start, bin_end), instances in bins:
        count = len(instances)
        mu_adv_count = sum(1 for r in instances if int(r['advantage_flag']) == 1)
        speedup_adv_count = sum(1 for r in instances if int(r['speedup_advantage_flag']) == 1)
        
        mu_adv_rate = mu_adv_count / count if count > 0 else 0
        speedup_adv_rate = speedup_adv_count / count if count > 0 else 0
        
        bin_advantage_rates.append(((bin_start + bin_end) / 2, mu_adv_rate))
        
        print(f"[{bin_start:.3f}, {bin_end:.3f})  {count:<8} {mu_adv_rate:.1%}             {speedup_adv_rate:.1%}")
    
    # Check for correlation
    if len(bin_advantage_rates) >= 2:
        bin_centers = [x[0] for x in bin_advantage_rates]
        rates = [x[1] for x in bin_advantage_rates]
        
        # Simple correlation check: does advantage rate increase with metric?
        if rates[-1] > rates[0]:
            print(f"\n✓ Positive trend: Advantage rate increases with {metric_name}")
        elif rates[-1] < rates[0]:
            print(f"\n✗ Negative trend: Advantage rate decreases with {metric_name}")
        else:
            print(f"\n~ Flat trend: No clear relationship with {metric_name}")


def analyze_by_type(data: List[Dict]):
    """Analyze advantage rates by instance type."""
    print(f"\n{'='*70}")
    print("Analysis by INSTANCE TYPE")
    print(f"{'='*70}")
    print(f"{'Type':<15} {'Count':<8} {'μ-Adv Rate':<15} {'Speedup-Adv Rate'}")
    print("-" * 70)
    
    types = {}
    for row in data:
        t = row['type']
        if t not in types:
            types[t] = []
        types[t].append(row)
    
    for t, instances in sorted(types.items()):
        count = len(instances)
        mu_adv_count = sum(1 for r in instances if int(r['advantage_flag']) == 1)
        speedup_adv_count = sum(1 for r in instances if int(r['speedup_advantage_flag']) == 1)
        
        mu_adv_rate = mu_adv_count / count if count > 0 else 0
        speedup_adv_rate = speedup_adv_count / count if count > 0 else 0
        
        print(f"{t:<15} {count:<8} {mu_adv_rate:.1%}             {speedup_adv_rate:.1%}")


def print_summary_statistics(data: List[Dict]):
    """Print overall summary statistics."""
    print(f"\n{'='*70}")
    print("OVERALL SUMMARY")
    print(f"{'='*70}")
    
    count = len(data)
    mu_adv = sum(1 for r in data if int(r['advantage_flag']) == 1)
    speedup_adv = sum(1 for r in data if int(r['speedup_advantage_flag']) == 1)
    
    print(f"Total instances: {count}")
    print(f"μ-advantage rate: {mu_adv}/{count} ({100*mu_adv/count:.1f}%)")
    print(f"Speedup advantage rate (>1.1x): {speedup_adv}/{count} ({100*speedup_adv/count:.1f}%)")
    
    # Compute average structural features
    avg_modularity = statistics.mean(float(r['modularity']) for r in data)
    avg_clustering = statistics.mean(float(r['clustering']) for r in data)
    
    print(f"\nAverage structural features:")
    print(f"  Modularity: {avg_modularity:.3f}")
    print(f"  Clustering: {avg_clustering:.3f}")


def h2_prime_conclusion(data: List[Dict]):
    """Draw conclusions about H2′ hypothesis."""
    print(f"\n{'='*70}")
    print("H2′ HYPOTHESIS EVALUATION")
    print(f"{'='*70}")
    
    # Split by modularity (high vs low)
    median_modularity = statistics.median(float(r['modularity']) for r in data)
    
    high_mod = [r for r in data if float(r['modularity']) >= median_modularity]
    low_mod = [r for r in data if float(r['modularity']) < median_modularity]
    
    high_mod_adv_rate = sum(1 for r in high_mod if int(r['advantage_flag']) == 1) / len(high_mod) if high_mod else 0
    low_mod_adv_rate = sum(1 for r in low_mod if int(r['advantage_flag']) == 1) / len(low_mod) if low_mod else 0
    
    print(f"H2′: 'High modularity instances show higher μ-advantage rate'")
    print(f"\nMedian modularity: {median_modularity:.3f}")
    print(f"High modularity (≥{median_modularity:.3f}): {high_mod_adv_rate:.1%} advantage rate ({len(high_mod)} instances)")
    print(f"Low modularity (<{median_modularity:.3f}): {low_mod_adv_rate:.1%} advantage rate ({len(low_mod)} instances)")
    
    if high_mod_adv_rate > low_mod_adv_rate + 0.1:  # At least 10% higher
        print(f"\n✓ H2′ SUPPORTED: High modularity shows {(high_mod_adv_rate - low_mod_adv_rate)*100:.1f}pp higher advantage rate")
    elif abs(high_mod_adv_rate - low_mod_adv_rate) < 0.1:
        print(f"\n~ H2′ INCONCLUSIVE: Advantage rates are similar regardless of modularity")
    else:
        print(f"\n✗ H2′ NOT SUPPORTED: Low modularity shows higher advantage rate")
    
    # Overall verdict
    overall_adv_rate = sum(1 for r in data if int(r['advantage_flag']) == 1) / len(data)
    
    print(f"\n{'='*70}")
    print("FINAL VERDICT")
    print(f"{'='*70}")
    
    if overall_adv_rate < 0.3:
        print("❌ Original H2 (structural advantage on generic SAT) is FALSIFIED")
        print(f"   Only {overall_adv_rate:.1%} of instances show μ-advantage")
        
        if high_mod_adv_rate > 0.5:
            print("\n✓ H2′ (restricted to high-modularity) shows promise")
            print(f"   {high_mod_adv_rate:.1%} advantage rate on high-modularity instances")
        else:
            print("\n❌ H2′ (restricted to high-modularity) is also not strongly supported")
            print(f"   {high_mod_adv_rate:.1%} advantage rate on high-modularity instances")
    else:
        print("✓ H2 shows moderate support on tested instances")


def main():
    parser = argparse.ArgumentParser(
        description='Analyze H2′ hypothesis: structural features vs μ-advantage'
    )
    parser.add_argument(
        '--input',
        default='benchmarks/sat_merged_analysis.csv',
        help='Merged analysis CSV file'
    )
    parser.add_argument(
        '--bins',
        type=int,
        default=4,
        help='Number of bins for metric analysis (default: 4)'
    )
    
    args = parser.parse_args()
    
    if not Path(args.input).exists():
        print(f"Error: {args.input} not found")
        sys.exit(1)
    
    # Load data
    print(f"Loading data from {args.input}...")
    data = load_merged_data(args.input)
    
    if not data:
        print("No data loaded")
        sys.exit(1)
    
    print(f"Loaded {len(data)} instances")
    
    # Print summary
    print_summary_statistics(data)
    
    # Analyze by type
    analyze_by_type(data)
    
    # Analyze by structural metrics
    for metric in ['modularity', 'clustering', 'density']:
        bins = bin_by_metric(data, metric, args.bins)
        if bins:
            analyze_bins(bins, metric)
    
    # Draw H2′ conclusions
    h2_prime_conclusion(data)


if __name__ == '__main__':
    main()
