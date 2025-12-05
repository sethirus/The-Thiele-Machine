#!/usr/bin/env python3
"""
Graph Clustering via Thiele Machine Partition Discovery

This module applies the Thiele Machine's partition discovery to graph clustering
and compares it with standard clustering methods (spectral clustering, Louvain).

The goal is to validate H2 (Structural Advantage) in the graph clustering domain
by showing that μ-minimization discovers meaningful community structure.

Metrics:
- Modularity: Quality of community structure
- NMI (Normalized Mutual Information): Similarity to ground truth
- μ-cost: Information-theoretic cost of discovery

Copyright 2025 Devon Thiele
Licensed under the Apache License, Version 2.0
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

import networkx as nx
import numpy as np
from sklearn.metrics import normalized_mutual_info_score

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from thielecpu.discovery import Problem, EfficientPartitionDiscovery
from thielecpu.mu import question_cost_bits


@dataclass
class ClusteringResult:
    """Result of a clustering algorithm."""
    method: str
    clusters: List[Set[int]]
    modularity: float
    nmi: Optional[float]  # NMI vs ground truth (if available)
    mu_cost: float
    runtime: float
    num_clusters: int
    
    def to_dict(self) -> Dict:
        """Convert to dictionary for CSV export."""
        return {
            'method': self.method,
            'num_clusters': self.num_clusters,
            'modularity': self.modularity,
            'nmi': self.nmi if self.nmi is not None else float('nan'),
            'mu_cost': self.mu_cost,
            'runtime': self.runtime
        }


def compute_modularity(G: nx.Graph, clusters: List[Set[int]]) -> float:
    """
    Compute modularity Q of a clustering.
    
    Q = (1/2m) Σ [A_ij - k_i*k_j/(2m)] δ(c_i, c_j)
    
    where:
    - m = number of edges
    - A_ij = adjacency matrix
    - k_i = degree of node i
    - δ(c_i, c_j) = 1 if nodes i,j in same cluster, 0 otherwise
    """
    m = G.number_of_edges()
    if m == 0:
        return 0.0
    
    # Build cluster membership
    node_to_cluster = {}
    for cluster_id, cluster in enumerate(clusters):
        for node in cluster:
            node_to_cluster[node] = cluster_id
    
    Q = 0.0
    for i in G.nodes():
        for j in G.nodes():
            if node_to_cluster.get(i) == node_to_cluster.get(j):
                A_ij = 1.0 if G.has_edge(i, j) else 0.0
                k_i = G.degree(i)
                k_j = G.degree(j)
                Q += A_ij - (k_i * k_j) / (2.0 * m)
    
    return Q / (2.0 * m)


def compute_mu_cost_clustering(
    G: nx.Graph,
    clusters: List[Set[int]]
) -> float:
    """
    Compute μ-cost for a clustering.
    
    μ_cost = μ_discovery + μ_encoding
    
    μ_discovery: cost of finding the clustering
    μ_encoding: cost of encoding cluster assignments
    """
    n = G.number_of_nodes()
    k = len(clusters)
    
    # Discovery cost: log₂(n choose k) + k parameters
    if k > 0 and k <= n:
        # Binomial coefficient approximation
        mu_discovery = k * math.log2(n / k + 1) + k * 10  # 10 bits per cluster parameter
    else:
        mu_discovery = 0.0
    
    # Encoding cost: log₂(k) per node + description of cluster structure
    mu_encoding = n * math.log2(k + 1) if k > 0 else 0.0
    
    # Boundary cost: encoding edges between clusters
    boundary_edges = 0
    node_to_cluster = {}
    for cluster_id, cluster in enumerate(clusters):
        for node in cluster:
            node_to_cluster[node] = cluster_id
    
    for u, v in G.edges():
        if node_to_cluster.get(u) != node_to_cluster.get(v):
            boundary_edges += 1
    
    mu_boundary = boundary_edges * math.log2(k + 1) if k > 1 else 0.0
    
    return mu_discovery + mu_encoding + mu_boundary


def cluster_thiele(
    G: nx.Graph,
    ground_truth: Optional[List[Set[int]]] = None
) -> ClusteringResult:
    """
    Cluster graph using Thiele Machine partition discovery.
    """
    import time
    start_time = time.time()
    
    # Convert graph to Problem using 1-indexed variable IDs expected by discovery
    node_list = list(G.nodes())
    node_to_var = {node: i + 1 for i, node in enumerate(node_list)}
    interactions = [(node_to_var[u], node_to_var[v]) for u, v in G.edges()]
    problem = Problem(
        num_variables=len(node_list),
        interactions=interactions,
        name=f"graph_n{G.number_of_nodes()}_m{G.number_of_edges()}"
    )
    
    # Discover partition with adaptive max clusters based on graph size
    max_clusters = min(100, max(10, G.number_of_nodes() // 10))
    discovery = EfficientPartitionDiscovery(max_clusters=max_clusters, use_refinement=True, seed=42)
    candidate = discovery.discover_partition(problem, max_mu_budget=1000.0)
    # Debug: print discovery metadata to help understand clustering behavior
    try:
        print(f"Discovery method: {candidate.method}, modules: {len(candidate.modules)}, mdl={candidate.mdl_cost:.3f}, discovery_mu={candidate.discovery_cost_mu:.3f}")
        if 'eigengap' in candidate.metadata:
            print(f"Eigengap metadata: {candidate.metadata.get('eigengap', '')}")
    except Exception:
        pass
    
    # Convert modules (1-indexed variable IDs) back to graph node labels
    clusters = [set(node_list[var - 1] for var in module) for module in candidate.modules]
    
    runtime = time.time() - start_time
    
    # Compute metrics
    modularity = compute_modularity(G, clusters)
    mu_cost = candidate.mdl_cost + candidate.discovery_cost_mu
    nmi = None
    if ground_truth is not None:
        # Convert to labels for NMI
        node_list = list(G.nodes())
        labels_pred = np.zeros(len(node_list), dtype=int)
        for cluster_id, cluster in enumerate(clusters):
            for node in cluster:
                if node in node_list:
                    idx = node_list.index(node)
                    labels_pred[idx] = cluster_id
        
        labels_true = np.zeros(len(node_list), dtype=int)
        for cluster_id, cluster in enumerate(ground_truth):
            for node in cluster:
                if node in node_list:
                    idx = node_list.index(node)
                    labels_true[idx] = cluster_id
        
        nmi = normalized_mutual_info_score(labels_true, labels_pred)
    
    return ClusteringResult(
        method='thiele',
        clusters=clusters,
        modularity=modularity,
        nmi=nmi,
        mu_cost=mu_cost,
        runtime=runtime,
        num_clusters=len(clusters)
    )


def cluster_spectral(
    G: nx.Graph,
    num_clusters: int,
    ground_truth: Optional[List[Set[int]]] = None
) -> ClusteringResult:
    """
    Cluster graph using spectral clustering (baseline).
    """
    import time
    from sklearn.cluster import SpectralClustering
    
    start_time = time.time()
    
    # Get adjacency matrix
    adj_matrix = nx.adjacency_matrix(G).toarray()
    
    # Run spectral clustering
    clustering = SpectralClustering(
        n_clusters=num_clusters,
        affinity='precomputed',
        random_state=42
    )
    labels = clustering.fit_predict(adj_matrix)
    
    # Convert labels to clusters
    clusters = [set() for _ in range(num_clusters)]
    for node, label in enumerate(labels):
        clusters[label].add(node)
    
    # Remove empty clusters
    clusters = [c for c in clusters if len(c) > 0]
    
    runtime = time.time() - start_time
    
    # Compute metrics
    modularity = compute_modularity(G, clusters)
    mu_cost = compute_mu_cost_clustering(G, clusters)
    nmi = None
    if ground_truth is not None:
        node_list = list(G.nodes())
        labels_true = np.zeros(len(node_list), dtype=int)
        for cluster_id, cluster in enumerate(ground_truth):
            for node in cluster:
                if node in node_list:
                    idx = node_list.index(node)
                    labels_true[idx] = cluster_id
        nmi = normalized_mutual_info_score(labels_true, labels)
    
    return ClusteringResult(
        method='spectral',
        clusters=clusters,
        modularity=modularity,
        nmi=nmi,
        mu_cost=mu_cost,
        runtime=runtime,
        num_clusters=len(clusters)
    )


def cluster_louvain(
    G: nx.Graph,
    ground_truth: Optional[List[Set[int]]] = None
) -> ClusteringResult:
    """
    Cluster graph using Louvain method (baseline).
    """
    import time
    
    start_time = time.time()
    
    # Run Louvain
    try:
        communities = nx.community.louvain_communities(G, seed=42)
        clusters = [set(c) for c in communities]
    except AttributeError:
        # Fallback if louvain not available
        print("Warning: Louvain method not available, using greedy modularity")
        communities = nx.community.greedy_modularity_communities(G)
        clusters = [set(c) for c in communities]
    
    runtime = time.time() - start_time
    
    # Compute metrics
    modularity = compute_modularity(G, clusters)
    mu_cost = compute_mu_cost_clustering(G, clusters)
    nmi = None
    if ground_truth is not None:
        node_list = list(G.nodes())
        labels_pred = np.zeros(len(node_list), dtype=int)
        for cluster_id, cluster in enumerate(clusters):
            for node in cluster:
                if node in node_list:
                    idx = node_list.index(node)
                    labels_pred[idx] = cluster_id
        
        labels_true = np.zeros(len(node_list), dtype=int)
        for cluster_id, cluster in enumerate(ground_truth):
            for node in cluster:
                if node in node_list:
                    idx = node_list.index(node)
                    labels_true[idx] = cluster_id
        
        nmi = normalized_mutual_info_score(labels_true, labels_pred)
    
    return ClusteringResult(
        method='louvain',
        clusters=clusters,
        modularity=modularity,
        nmi=nmi,
        mu_cost=mu_cost,
        runtime=runtime,
        num_clusters=len(clusters)
    )


def generate_benchmark_graphs() -> List[Tuple[nx.Graph, Optional[List[Set[int]]], str]]:
    """
    Generate benchmark graphs with known community structure.
    
    Returns:
        List of (graph, ground_truth_clusters, name) tuples
    """
    graphs = []
    
    # 1. Karate Club (classic benchmark)
    G = nx.karate_club_graph()
    # Ground truth: two factions
    ground_truth = [
        set(range(0, 17)),  # Mr. Hi's faction
        set(range(17, 34))  # Officer's faction
    ]
    graphs.append((G, ground_truth, "karate_club"))
    
    # 2. Small modular graph (planted partition)
    sizes = [15, 15, 15]
    p_in = 0.3  # Within-community edge probability
    p_out = 0.05  # Between-community edge probability
    G = nx.planted_partition_graph(len(sizes), sizes[0], p_in, p_out, seed=42)
    ground_truth = []
    offset = 0
    for size in sizes:
        ground_truth.append(set(range(offset, offset + size)))
        offset += size
    graphs.append((G, ground_truth, "planted_3communities"))
    
    # 3. Ring of cliques
    num_cliques = 4
    clique_size = 10
    G = nx.ring_of_cliques(num_cliques, clique_size)
    ground_truth = []
    for i in range(num_cliques):
        ground_truth.append(set(range(i * clique_size, (i + 1) * clique_size)))
    graphs.append((G, ground_truth, "ring_of_cliques_4x10"))
    
    # 4. Barbell graph (two cliques connected by a path)
    clique_size = 15
    G = nx.barbell_graph(clique_size, 5)
    ground_truth = [
        set(range(0, clique_size)),
        set(range(clique_size + 5, 2 * clique_size + 5))
    ]
    graphs.append((G, ground_truth, "barbell_15_5_15"))
    
    # 5. Random graph (no structure - negative control)
    n = 50
    p = 0.1
    G = nx.erdos_renyi_graph(n, p, seed=42)
    graphs.append((G, None, "random_n50_p0.1"))
    
    return graphs


def run_benchmarks(output_file: Path):
    """
    Run graph clustering benchmarks comparing Thiele vs baselines.
    """
    print("="*60)
    print("GRAPH CLUSTERING BENCHMARKS")
    print("="*60)
    
    graphs = generate_benchmark_graphs()
    results = []
    
    for G, ground_truth, name in graphs:
        print(f"\n{'='*60}")
        print(f"Graph: {name}")
        print(f"Nodes: {G.number_of_nodes()}, Edges: {G.number_of_edges()}")
        print(f"{'='*60}")
        
        # Run Thiele clustering
        print("\n1. Thiele Machine Clustering...")
        thiele_result = cluster_thiele(G, ground_truth)
        print(f"   Clusters: {thiele_result.num_clusters}")
        print(f"   Modularity: {thiele_result.modularity:.4f}")
        print(f"   NMI: {thiele_result.nmi:.4f}" if thiele_result.nmi is not None else "   NMI: N/A")
        print(f"   μ-cost: {thiele_result.mu_cost:.2f} bits")
        print(f"   Runtime: {thiele_result.runtime:.4f}s")
        
        # Run spectral clustering (if ground truth available)
        if ground_truth is not None:
            print("\n2. Spectral Clustering...")
            spectral_result = cluster_spectral(G, len(ground_truth), ground_truth)
            print(f"   Clusters: {spectral_result.num_clusters}")
            print(f"   Modularity: {spectral_result.modularity:.4f}")
            print(f"   NMI: {spectral_result.nmi:.4f}" if spectral_result.nmi is not None else "   NMI: N/A")
            print(f"   μ-cost: {spectral_result.mu_cost:.2f} bits")
            print(f"   Runtime: {spectral_result.runtime:.4f}s")
            results.append({**spectral_result.to_dict(), 'graph': name})
        
        # Run Louvain clustering
        print("\n3. Louvain Clustering...")
        louvain_result = cluster_louvain(G, ground_truth)
        print(f"   Clusters: {louvain_result.num_clusters}")
        print(f"   Modularity: {louvain_result.modularity:.4f}")
        print(f"   NMI: {louvain_result.nmi:.4f}" if louvain_result.nmi is not None else "   NMI: N/A")
        print(f"   μ-cost: {louvain_result.mu_cost:.2f} bits")
        print(f"   Runtime: {louvain_result.runtime:.4f}s")
        
        # Add to results
        results.append({**thiele_result.to_dict(), 'graph': name})
        results.append({**louvain_result.to_dict(), 'graph': name})
    
    # Save results
    output_file.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, 'w', newline='') as f:
        fieldnames = ['graph', 'method', 'num_clusters', 'modularity', 'nmi', 'mu_cost', 'runtime']
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(results)
    
    print(f"\n{'='*60}")
    print(f"Results saved to: {output_file}")
    print(f"{'='*60}")
    
    # Summary statistics
    print("\nSUMMARY STATISTICS")
    print("="*60)
    
    thiele_results = [r for r in results if r['method'] == 'thiele']
    if thiele_results:
        avg_modularity = np.mean([r['modularity'] for r in thiele_results])
        avg_nmi = np.nanmean([r['nmi'] for r in thiele_results])
        avg_mu = np.mean([r['mu_cost'] for r in thiele_results])
        
        print(f"Thiele Machine:")
        print(f"  Average Modularity: {avg_modularity:.4f}")
        print(f"  Average NMI: {avg_nmi:.4f}")
        print(f"  Average μ-cost: {avg_mu:.2f} bits")
    
    louvain_results = [r for r in results if r['method'] == 'louvain']
    if louvain_results:
        avg_modularity = np.mean([r['modularity'] for r in louvain_results])
        avg_nmi = np.nanmean([r['nmi'] for r in louvain_results])
        avg_mu = np.mean([r['mu_cost'] for r in louvain_results])
        
        print(f"\nLouvain:")
        print(f"  Average Modularity: {avg_modularity:.4f}")
        print(f"  Average NMI: {avg_nmi:.4f}")
        print(f"  Average μ-cost: {avg_mu:.2f} bits")


def main():
    parser = argparse.ArgumentParser(description='Graph clustering benchmarks')
    parser.add_argument(
        '--output',
        type=Path,
        default=Path('benchmarks/graph_results.csv'),
        help='Output CSV file for results'
    )
    
    args = parser.parse_args()
    
    run_benchmarks(args.output)


if __name__ == '__main__':
    main()
