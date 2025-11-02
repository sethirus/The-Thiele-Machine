#!/usr/bin/env python3
"""
The Cartographer - Geometric Signature Extraction

This module reads sight logs and extracts geometric signatures from the
Strategy Graph (4-node graph where nodes are partitioning strategies and
edges are weighted by Variation of Information).

It computes five key geometric metrics that distinguish structured from chaotic problems:
1. average_edge_weight: Mean VI across all strategy pairs
2. max_edge_weight: Maximum VI between any two strategies
3. edge_weight_stddev: Standard deviation of VI (dispersion metric)
4. min_spanning_tree_weight: Sum of weights in MST (connectivity measure)
5. thresholded_density: Density of edges above a threshold (structural measure)
"""

import json
import time
from pathlib import Path
from typing import Dict, Any, List
import numpy as np
import networkx as nx


def build_strategy_graph(vi_matrix: Dict[str, Dict[str, float]]) -> nx.Graph:
    """
    Build the Strategy Graph from a Variation of Information matrix.
    
    Args:
        vi_matrix: Dictionary mapping strategy pairs to VI distance
    
    Returns:
        NetworkX graph with 4 nodes (strategies) and weighted edges
    """
    G = nx.Graph()
    
    strategies = list(vi_matrix.keys())
    G.add_nodes_from(strategies)
    
    # Add edges with VI as weight
    for s1 in strategies:
        for s2 in strategies:
            if s1 < s2:  # Only add each edge once (undirected)
                weight = vi_matrix[s1][s2]
                G.add_edge(s1, s2, weight=weight)
    
    return G


def compute_geometric_metrics(G: nx.Graph) -> Dict[str, float]:
    """
    Compute the five key geometric metrics from a Strategy Graph.
    
    Args:
        G: Strategy Graph (4 nodes, weighted edges)
    
    Returns:
        Dictionary of geometric metrics
    """
    # Get all edge weights
    edge_weights = [data['weight'] for u, v, data in G.edges(data=True)]
    
    if not edge_weights:
        return {
            "average_edge_weight": 0.0,
            "max_edge_weight": 0.0,
            "edge_weight_stddev": 0.0,
            "min_spanning_tree_weight": 0.0,
            "thresholded_density": 0.0
        }
    
    # 1. Average edge weight
    avg_edge_weight = np.mean(edge_weights)
    
    # 2. Max edge weight
    max_edge_weight = np.max(edge_weights)
    
    # 3. Edge weight standard deviation (dispersion)
    edge_weight_stddev = np.std(edge_weights)
    
    # 4. Minimum spanning tree weight
    # Sum of weights in the MST (minimum total VI to connect all strategies)
    try:
        mst = nx.minimum_spanning_tree(G, weight='weight')
        mst_weight = sum(data['weight'] for u, v, data in mst.edges(data=True))
    except (nx.NetworkXError, ValueError):
        mst_weight = 0.0
    
    # 5. Thresholded density
    # Fraction of edges with weight above median (structural measure)
    threshold = np.median(edge_weights)
    high_weight_edges = sum(1 for w in edge_weights if w > threshold)
    total_edges = len(edge_weights)
    thresholded_density = high_weight_edges / total_edges if total_edges > 0 else 0.0
    
    return {
        "average_edge_weight": float(avg_edge_weight),
        "max_edge_weight": float(max_edge_weight),
        "edge_weight_stddev": float(edge_weight_stddev),
        "min_spanning_tree_weight": float(mst_weight),
        "thresholded_density": float(thresholded_density)
    }


def extract_metrics_from_log(log_path: Path) -> Dict[str, Any]:
    """
    Extract geometric metrics from a single sight log.
    
    Args:
        log_path: Path to the sight log JSON file
    
    Returns:
        Dictionary with problem info and geometric metrics
    """
    with open(log_path, 'r') as f:
        log = json.load(f)
    
    # Extract VI matrix
    vi_matrix = log.get("consistency_analysis", {}).get("vi_matrix", {})
    
    if not vi_matrix:
        return None
    
    # Build strategy graph
    G = build_strategy_graph(vi_matrix)
    
    # Compute geometric metrics
    metrics = compute_geometric_metrics(G)
    
    # Assemble result
    result = {
        "problem_name": log.get("problem_name", "unknown"),
        "n": log.get("n", 0),
        "seed": log.get("seed", 0),
        "verdict": log.get("consistency_analysis", {}).get("ground_truth_verdict", "UNKNOWN"),
        "source_file": log_path.name,
        "geometric_metrics": metrics,
        "metadata": log.get("metadata", {})
    }
    
    return result


def generate_atlas(
    sight_logs_dir: Path = Path("sight_logs"),
    output_path: Path = Path("sight_logs/atlas/phase2_metrics.json")
):
    """
    Generate the complete Atlas by processing all sight logs.
    
    Args:
        sight_logs_dir: Directory containing sight logs
        output_path: Path to save the atlas
    """
    print(f"\n{'='*60}")
    print("THE CARTOGRAPHER - Generating Geometric Atlas")
    print(f"{'='*60}")
    print(f"Input directory: {sight_logs_dir}")
    print(f"Output path: {output_path}")
    print(f"{'='*60}\n")
    
    # Find all sight log files
    log_files = list(sight_logs_dir.glob("*.json"))
    # Exclude INDEX.json
    log_files = [f for f in log_files if f.name != "INDEX.json"]
    
    print(f"Found {len(log_files)} sight logs to process")
    
    atlas_entries = []
    
    for i, log_path in enumerate(log_files, 1):
        print(f"[{i}/{len(log_files)}] Processing {log_path.name}...", end=" ")
        
        try:
            result = extract_metrics_from_log(log_path)
            if result:
                atlas_entries.append(result)
                print("✓")
            else:
                print("⚠️ No VI matrix found")
        except Exception as e:
            print(f"✗ Error: {e}")
    
    # Create atlas
    atlas = {
        "version": "1.0",
        "created": time.time(),
        "num_entries": len(atlas_entries),
        "entries": atlas_entries
    }
    
    # Save atlas
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w') as f:
        json.dump(atlas, f, indent=2)
    
    print(f"\n✓ Atlas generated: {len(atlas_entries)} entries")
    print(f"✓ Saved to: {output_path}")
    
    # Print summary statistics
    if atlas_entries:
        verdicts = [e["verdict"] for e in atlas_entries]
        consistent_count = sum(1 for v in verdicts if v == "CONSISTENT")
        spurious_count = sum(1 for v in verdicts if v == "SPURIOUS")
        
        print(f"\n{'='*60}")
        print("ATLAS SUMMARY")
        print(f"{'='*60}")
        print(f"Total entries: {len(atlas_entries)}")
        print(f"CONSISTENT (structured): {consistent_count}")
        print(f"SPURIOUS (chaotic): {spurious_count}")
        print(f"{'='*60}\n")
    
    return atlas


def main():
    """Main entry point for the cartographer."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Generate geometric atlas from sight logs"
    )
    parser.add_argument(
        "--input-dir",
        type=str,
        default="sight_logs",
        help="Directory containing sight logs"
    )
    parser.add_argument(
        "--output",
        type=str,
        default="sight_logs/atlas/phase2_metrics.json",
        help="Output path for atlas"
    )
    
    args = parser.parse_args()
    
    sight_logs_dir = Path(args.input_dir)
    output_path = Path(args.output)
    
    atlas = generate_atlas(sight_logs_dir, output_path)
    
    print("✓ Cartographer complete\n")


if __name__ == "__main__":
    main()
