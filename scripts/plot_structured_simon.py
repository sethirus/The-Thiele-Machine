#!/usr/bin/env python3
"""
Thiele Machine: Plot Structured Simon Experiment Results

This script generates publication-quality plots from the CSV results
of demonstrate_structured_oracle.py, showing the exponential scaling
differences between classical and partition-native approaches.
"""

import os
import csv
import math
import matplotlib.pyplot as plt
import argparse

def load_csv(path):
    """Load CSV data into list of dicts."""
    with open(path, "r") as f:
        return list(csv.DictReader(f))

def plot_experiment1(csv_data, output_path):
    """Plot Experiment 1: Fixed k=8, growing n."""
    ns = [int(row["n"]) for row in csv_data]
    classical_medians = [int(row["classical_median"]) for row in csv_data]
    partitioned_medians = [int(row["partitioned_median"]) for row in csv_data]
    classical_expected = [float(row["classical_expected_median"]) for row in csv_data]
    partitioned_expected = [float(row["partitioned_expected_median"]) for row in csv_data]

    plt.figure(figsize=(10, 6))
    plt.loglog(ns, classical_medians, 'o-', label='Classical (measured)', color='blue', markersize=8)
    plt.loglog(ns, partitioned_medians, 's-', label='Partitioned (measured)', color='red', markersize=8)
    plt.loglog(ns, classical_expected, '--', label='Classical (expected)', color='blue', alpha=0.7)
    plt.loglog(ns, partitioned_expected, '--', label='Partitioned (expected)', color='red', alpha=0.7)

    plt.xlabel('Problem Size n (bits)')
    plt.ylabel('Queries to Solution (median)')
    plt.title('Experiment 1: Fixed Locality k=8, Growing Problem Size n\nClassical scales as 2^(n/2); Partitioned flat at 2^(k/2)')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    print(f"Saved plot to {output_path}")

def plot_experiment2(csv_data, output_path):
    """Plot Experiment 2: Fixed n=24, growing k."""
    ks = [int(row["k"]) for row in csv_data]
    classical_medians = [int(row["classical_median"]) for row in csv_data]
    partitioned_medians = [int(row["partitioned_median"]) for row in csv_data]
    classical_expected = [float(row["classical_expected_median"]) for row in csv_data]
    partitioned_expected = [float(row["partitioned_expected_median"]) for row in csv_data]

    plt.figure(figsize=(10, 6))
    plt.loglog(ks, classical_medians, 'o-', label='Classical (measured)', color='blue', markersize=8)
    plt.loglog(ks, partitioned_medians, 's-', label='Partitioned (measured)', color='red', markersize=8)
    plt.loglog(ks, classical_expected, '--', label='Classical (expected)', color='blue', alpha=0.7)
    plt.loglog(ks, partitioned_expected, '--', label='Partitioned (expected)', color='red', alpha=0.7)

    plt.xlabel('Locality k (bits)')
    plt.ylabel('Queries to Solution (median)')
    plt.title('Experiment 2: Fixed Problem Size n=24, Growing Locality k\nClassical flat at 2^(n/2); Partitioned scales as 2^(k/2)')
    plt.legend()
    plt.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(output_path, dpi=300, bbox_inches='tight')
    plt.close()
    print(f"Saved plot to {output_path}")

def main():
    parser = argparse.ArgumentParser(description="Plot structured Simon experiment results")
    parser.add_argument("--results-dir", default="results", help="Directory containing CSV files")
    parser.add_argument("--output-dir", default="figures", help="Directory to save plots")
    args = parser.parse_args()

    os.makedirs(args.output_dir, exist_ok=True)

    csv1_path = os.path.join(args.results_dir, "fixed_k_grow_n.csv")
    csv2_path = os.path.join(args.results_dir, "fixed_n_grow_k.csv")

    if not os.path.exists(csv1_path) or not os.path.exists(csv2_path):
        print(f"Error: CSV files not found in {args.results_dir}")
        return

    data1 = load_csv(csv1_path)
    data2 = load_csv(csv2_path)

    plot_experiment1(data1, os.path.join(args.output_dir, "experiment1_scaling.png"))
    plot_experiment2(data2, os.path.join(args.output_dir, "experiment2_scaling.png"))

    print("Plotting complete.")

if __name__ == "__main__":
    main()