#!/usr/bin/env python3
"""
SAT Structure Analyzer
======================

Analyzes structural features of SAT instances (CNF files) to support H2′ testing.

For each CNF instance, computes:
- Number of variables and clauses
- Clause-to-variable ratio
- Graph structure metrics (modularity, clustering, degree distribution)
- Community structure

Outputs a CSV file with structural features for each instance.
"""

import argparse
import csv
import os
import sys
from pathlib import Path
from typing import Dict, List, Tuple

import networkx as nx
from networkx.algorithms import community


def parse_cnf(cnf_path: str) -> Tuple[int, int, List[List[int]]]:
    """
    Parse a DIMACS CNF file.
    
    Returns:
        (num_vars, num_clauses, clauses)
    """
    num_vars = 0
    num_clauses = 0
    clauses = []
    
    with open(cnf_path, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c'):
                continue
            if line.startswith('p'):
                parts = line.split()
                num_vars = int(parts[2])
                num_clauses = int(parts[3])
            else:
                clause = [int(x) for x in line.split() if int(x) != 0]
                clauses.append(clause)
    
    return num_vars, num_clauses, clauses


def build_variable_graph(num_vars: int, clauses: List[List[int]]) -> nx.Graph:
    """
    Build a variable co-occurrence graph.
    
    Two variables are connected if they appear together in at least one clause.
    Edge weight = number of co-occurrences.
    """
    G = nx.Graph()
    
    # Add all variables as nodes
    for v in range(1, num_vars + 1):
        G.add_node(v)
    
    # Add edges for co-occurrences
    for clause in clauses:
        abs_vars = [abs(lit) for lit in clause]
        # Add edge between each pair of variables in the clause
        for i, v1 in enumerate(abs_vars):
            for v2 in abs_vars[i+1:]:
                if G.has_edge(v1, v2):
                    G[v1][v2]['weight'] += 1
                else:
                    G.add_edge(v1, v2, weight=1)
    
    return G


def compute_modularity(G: nx.Graph) -> float:
    """
    Compute modularity using Louvain community detection.
    
    Returns modularity score (0.0 = random, 1.0 = perfect communities).
    """
    if G.number_of_edges() == 0:
        return 0.0
    
    try:
        # Use Louvain method for community detection
        communities = community.greedy_modularity_communities(G)
        mod = community.modularity(G, communities)
        return mod
    except Exception:
        return 0.0


def compute_clustering_coefficient(G: nx.Graph) -> float:
    """
    Compute average clustering coefficient.
    
    Measures how much nodes tend to cluster together.
    """
    if G.number_of_nodes() == 0:
        return 0.0
    
    try:
        return nx.average_clustering(G)
    except Exception:
        return 0.0


def compute_degree_stats(G: nx.Graph) -> Dict[str, float]:
    """
    Compute degree distribution statistics.
    """
    if G.number_of_nodes() == 0:
        return {'avg_degree': 0.0, 'max_degree': 0, 'min_degree': 0}
    
    degrees = [d for n, d in G.degree()]
    return {
        'avg_degree': sum(degrees) / len(degrees) if degrees else 0.0,
        'max_degree': max(degrees) if degrees else 0,
        'min_degree': min(degrees) if degrees else 0,
    }


def analyze_cnf_structure(cnf_path: str) -> Dict[str, float]:
    """
    Analyze structural features of a single CNF file.
    
    Returns a dictionary of features.
    """
    num_vars, num_clauses, clauses = parse_cnf(cnf_path)
    
    # Basic features
    features = {
        'instance_name': Path(cnf_path).stem,
        'num_vars': num_vars,
        'num_clauses': num_clauses,
        'clause_var_ratio': num_clauses / num_vars if num_vars > 0 else 0.0,
    }
    
    # Build variable co-occurrence graph
    G = build_variable_graph(num_vars, clauses)
    
    # Graph structure features
    features['modularity'] = compute_modularity(G)
    features['clustering'] = compute_clustering_coefficient(G)
    
    degree_stats = compute_degree_stats(G)
    features.update(degree_stats)
    
    # Connectivity features
    features['num_edges'] = G.number_of_edges()
    features['density'] = nx.density(G)
    features['num_components'] = nx.number_connected_components(G)
    
    return features


def analyze_directory(input_dir: str, output_csv: str):
    """
    Analyze all CNF files in a directory and write features to CSV.
    """
    cnf_files = sorted(Path(input_dir).glob('*.cnf'))
    
    if not cnf_files:
        print(f"No CNF files found in {input_dir}")
        return
    
    print(f"Found {len(cnf_files)} CNF files in {input_dir}")
    
    all_features = []
    for cnf_file in cnf_files:
        print(f"Analyzing {cnf_file.name}...", end=' ')
        try:
            features = analyze_cnf_structure(str(cnf_file))
            all_features.append(features)
            print("✓")
        except Exception as e:
            print(f"✗ Error: {e}")
    
    # Write to CSV
    if all_features:
        fieldnames = list(all_features[0].keys())
        with open(output_csv, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(all_features)
        
        print(f"\nWrote {len(all_features)} feature rows to {output_csv}")
    else:
        print("No features extracted")


def main():
    parser = argparse.ArgumentParser(
        description='Analyze structural features of SAT instances'
    )
    parser.add_argument(
        'input_dir',
        help='Directory containing CNF files'
    )
    parser.add_argument(
        '--output',
        '-o',
        default='sat_structure_features.csv',
        help='Output CSV file (default: sat_structure_features.csv)'
    )
    
    args = parser.parse_args()
    
    if not os.path.isdir(args.input_dir):
        print(f"Error: {args.input_dir} is not a directory")
        sys.exit(1)
    
    analyze_directory(args.input_dir, args.output)


if __name__ == '__main__':
    main()
