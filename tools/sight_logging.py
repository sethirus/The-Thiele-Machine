#!/usr/bin/env python3
"""
Sight Logging Module for The Thiele Machine

This module generates comprehensive "sight logs" for SAT problem instances,
analyzing how different graph partitioning strategies reveal structure.

The core hypothesis: Structured problems exhibit consistent partition signatures
across different strategies, while chaotic problems show high variation.
"""

import json
import hashlib
import time
from pathlib import Path
from typing import List, Dict, Any, Tuple, Optional
import numpy as np
import networkx as nx
from sklearn.cluster import SpectralClustering


def build_clause_graph(clauses: List[List[int]]) -> nx.Graph:
    """
    Build a variable interaction graph from CNF clauses.
    
    Each variable is a node, edges connect variables appearing in the same clause.
    
    Args:
        clauses: List of CNF clauses (each clause is a list of literals)
    
    Returns:
        NetworkX graph where nodes are variables
    """
    G = nx.Graph()
    
    # Extract all variables
    variables = set()
    for clause in clauses:
        for lit in clause:
            variables.add(abs(lit))
    
    # Add nodes for all variables
    G.add_nodes_from(sorted(variables))
    
    # Add edges between variables in the same clause
    for clause in clauses:
        vars_in_clause = [abs(lit) for lit in clause]
        # Connect all pairs of variables in this clause
        for i in range(len(vars_in_clause)):
            for j in range(i + 1, len(vars_in_clause)):
                v1, v2 = vars_in_clause[i], vars_in_clause[j]
                if G.has_edge(v1, v2):
                    G[v1][v2]['weight'] = G[v1][v2].get('weight', 0) + 1
                else:
                    G.add_edge(v1, v2, weight=1)
    
    return G


def _run_louvain(G: nx.Graph, seed: int = 42) -> Dict[int, int]:
    """
    Run Louvain community detection algorithm.
    
    Args:
        G: NetworkX graph
        seed: Random seed for reproducibility
    
    Returns:
        Dictionary mapping node -> partition_id
    """
    try:
        # Use networkx's community detection (greedy modularity)
        from networkx.algorithms import community
        communities = community.greedy_modularity_communities(G, weight='weight', resolution=1.0)
        
        # Convert to node -> partition_id mapping
        partition = {}
        for partition_id, comm in enumerate(communities):
            for node in comm:
                partition[node] = partition_id
        
        return partition
    except (ImportError, AttributeError):
        # Fallback to single partition if algorithm not available
        return {node: 0 for node in G.nodes()}


def _run_spectral(G: nx.Graph, n_clusters: int = 4, seed: int = 42) -> Dict[int, int]:
    """
    Run spectral clustering on the graph Laplacian.
    
    Args:
        G: NetworkX graph
        n_clusters: Number of clusters to find
        seed: Random seed for reproducibility
    
    Returns:
        Dictionary mapping node -> partition_id
    """
    if len(G.nodes()) < n_clusters:
        # Not enough nodes for requested clusters
        return {node: i for i, node in enumerate(G.nodes())}
    
    try:
        # Get adjacency matrix
        nodes = sorted(G.nodes())
        adj_matrix = nx.to_numpy_array(G, nodelist=nodes, weight='weight')
        
        # Run spectral clustering
        clustering = SpectralClustering(
            n_clusters=min(n_clusters, len(nodes)),
            affinity='precomputed',
            random_state=seed,
            n_init=10
        )
        labels = clustering.fit_predict(adj_matrix)
        
        # Convert to dictionary
        partition = {node: int(label) for node, label in zip(nodes, labels)}
        return partition
    except (ValueError, RuntimeError):
        # Fallback to degree-based if spectral fails
        return _run_degree(G, n_clusters)


def _run_degree(G: nx.Graph, n_clusters: int = 4) -> Dict[int, int]:
    """
    Partition based on node degree (simple heuristic).
    
    Nodes are sorted by degree and assigned to partitions round-robin.
    
    Args:
        G: NetworkX graph
        n_clusters: Number of partitions to create
    
    Returns:
        Dictionary mapping node -> partition_id
    """
    # Sort nodes by degree (descending)
    nodes_by_degree = sorted(G.nodes(), key=lambda n: G.degree(n, weight='weight'), reverse=True)
    
    # Assign to partitions round-robin
    partition = {}
    for i, node in enumerate(nodes_by_degree):
        partition[node] = i % n_clusters
    
    return partition


def _run_balanced(G: nx.Graph, n_clusters: int = 4) -> Dict[int, int]:
    """
    Create balanced partitions (equal size).
    
    Nodes are sorted by ID and distributed evenly across partitions.
    
    Args:
        G: NetworkX graph
        n_clusters: Number of partitions to create
    
    Returns:
        Dictionary mapping node -> partition_id
    """
    nodes = sorted(G.nodes())
    partition = {}
    for i, node in enumerate(nodes):
        partition[node] = i % n_clusters
    
    return partition


def _variation_of_information(partition1: Dict[int, int], partition2: Dict[int, int]) -> float:
    """
    Calculate Variation of Information (VI) distance between two partitions.
    
    VI is a true metric on the space of clusterings, measuring the information
    theoretic distance between two partitionings.
    
    VI(X, Y) = H(X) + H(Y) - 2 * I(X, Y)
    
    where H is entropy and I is mutual information.
    
    Args:
        partition1: First partition (node -> cluster_id)
        partition2: Second partition (node -> cluster_id)
    
    Returns:
        Variation of information distance (higher = more different)
    """
    # Get common nodes
    nodes = set(partition1.keys()) & set(partition2.keys())
    if len(nodes) == 0:
        return 0.0
    
    # Build contingency table
    labels1 = [partition1[n] for n in sorted(nodes)]
    labels2 = [partition2[n] for n in sorted(nodes)]
    
    # Count co-occurrences
    n_samples = len(nodes)
    clusters1 = set(labels1)
    clusters2 = set(labels2)
    
    # Build contingency matrix
    contingency = {}
    for c1 in clusters1:
        contingency[c1] = {}
        for c2 in clusters2:
            contingency[c1][c2] = 0
    
    for l1, l2 in zip(labels1, labels2):
        contingency[l1][l2] += 1
    
    # Calculate entropies and mutual information
    # P(X=i) = n_i / n
    p1 = {}
    for c1 in clusters1:
        count = sum(1 for l in labels1 if l == c1)
        p1[c1] = count / n_samples
    
    p2 = {}
    for c2 in clusters2:
        count = sum(1 for l in labels2 if l == c2)
        p2[c2] = count / n_samples
    
    # H(X) = -sum(p(x) * log(p(x)))
    h1 = -sum(p * np.log2(p) if p > 0 else 0 for p in p1.values())
    h2 = -sum(p * np.log2(p) if p > 0 else 0 for p in p2.values())
    
    # Mutual information: I(X, Y) = sum(p(x,y) * log(p(x,y) / (p(x)*p(y))))
    mi = 0.0
    for c1 in clusters1:
        for c2 in clusters2:
            p_joint = contingency[c1][c2] / n_samples
            if p_joint > 0:
                mi += p_joint * np.log2(p_joint / (p1[c1] * p2[c2]))
    
    # VI = H(X) + H(Y) - 2*I(X,Y)
    vi = h1 + h2 - 2 * mi
    
    return max(0.0, vi)  # Ensure non-negative due to numerical errors


def assemble_log(
    clauses: List[List[int]],
    problem_name: str,
    n: int,
    seed: int,
    verdict: str = "UNKNOWN",
    metadata: Optional[Dict[str, Any]] = None,
    strategy_list: Optional[List[str]] = None
) -> Dict[str, Any]:
    """
    Assemble a complete sight log for a problem instance.
    
    This is the master function that:
    1. Builds the clause graph
    2. Runs specified partitioning strategies (or all four by default)
    3. Computes pairwise Variation of Information
    4. Determines consistency (CONSISTENT vs SPURIOUS paradox)
    5. Returns the complete JSON-serializable log
    
    Args:
        clauses: CNF clauses of the problem
        problem_name: Identifier for the problem (e.g., "tseitin_n10_seed42")
        n: Problem size parameter
        seed: Random seed used for problem generation
        verdict: Ground truth verdict ("CONSISTENT" or "SPURIOUS")
        metadata: Optional additional metadata
        strategy_list: List of strategy names to use (default: all four)
    
    Returns:
        Complete sight log as a dictionary
    """
    # Default to all four strategies if not specified
    if strategy_list is None:
        strategy_list = ["louvain", "spectral", "degree", "balanced"]
    
    # Build graph from clauses
    G = build_clause_graph(clauses)
    
    # Calculate graph metrics
    num_nodes = G.number_of_nodes()
    num_edges = G.number_of_edges()
    avg_degree = np.mean([d for n, d in G.degree()]) if num_nodes > 0 else 0
    density = nx.density(G)
    
    # Run specified partitioning strategies
    n_clusters = min(4, max(2, num_nodes // 10))  # Adaptive cluster count
    
    # Strategy function mapping
    strategy_functions = {
        "louvain": lambda: _run_louvain(G, seed=seed),
        "spectral": lambda: _run_spectral(G, n_clusters=n_clusters, seed=seed),
        "degree": lambda: _run_degree(G, n_clusters=n_clusters),
        "balanced": lambda: _run_balanced(G, n_clusters=n_clusters)
    }
    
    # Run only the requested strategies
    partitions = {}
    for strategy in strategy_list:
        if strategy in strategy_functions:
            partitions[strategy] = strategy_functions[strategy]()
        else:
            raise ValueError(f"Unknown strategy: {strategy}")
    
    # Compute pairwise Variation of Information
    strategies = strategy_list
    vi_matrix = {s: {} for s in strategies}
    
    for i, s1 in enumerate(strategies):
        for j, s2 in enumerate(strategies):
            if i <= j:  # Symmetric, only compute upper triangle
                vi = _variation_of_information(partitions[s1], partitions[s2])
                vi_matrix[s1][s2] = vi
                if i != j:  # Don't duplicate diagonal
                    vi_matrix[s2][s1] = vi  # Symmetry
    
    # Compute consistency metrics
    # Average VI between different strategies
    vi_values = []
    for i, s1 in enumerate(strategies):
        for j, s2 in enumerate(strategies):
            if i < j:  # Only unique pairs
                vi_values.append(vi_matrix[s1][s2])
    
    avg_vi = np.mean(vi_values) if vi_values else 0.0
    max_vi = np.max(vi_values) if vi_values else 0.0
    std_vi = np.std(vi_values) if vi_values else 0.0
    
    # Determine consistency verdict based on VI statistics
    # Low VI = strategies agree = CONSISTENT (structured)
    # High VI = strategies disagree = SPURIOUS (chaotic)
    consistency_threshold = 0.5  # Empirical threshold
    computed_verdict = "CONSISTENT" if avg_vi < consistency_threshold else "SPURIOUS"
    
    # Assemble the complete log
    log = {
        "problem_name": problem_name,
        "n": n,
        "seed": seed,
        "timestamp": time.time(),
        "input": {
            "num_clauses": len(clauses),
            "num_variables": num_nodes,
        },
        "graph_metrics": {
            "num_nodes": num_nodes,
            "num_edges": num_edges,
            "avg_degree": float(avg_degree),
            "density": float(density)
        },
        "partitions": {
            strategy: {
                "num_clusters": len(set(partition.values())),
                "assignment": {str(k): v for k, v in partition.items()}  # JSON needs string keys
            }
            for strategy, partition in partitions.items()
        },
        "consistency_analysis": {
            "vi_matrix": {
                s1: {s2: float(vi_matrix[s1][s2]) for s2 in strategies}
                for s1 in strategies
            },
            "avg_vi": float(avg_vi),
            "max_vi": float(max_vi),
            "std_vi": float(std_vi),
            "computed_verdict": computed_verdict,
            "ground_truth_verdict": verdict
        },
        "metadata": metadata or {}
    }
    
    return log


def save_log(log: Dict[str, Any], output_dir: Path = Path("sight_logs")) -> Path:
    """
    Save a sight log to disk with a unique filename.
    
    Args:
        log: The sight log dictionary
        output_dir: Directory to save the log
    
    Returns:
        Path to the saved log file
    """
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Generate unique filename based on content hash
    content_str = json.dumps(log, sort_keys=True)
    content_hash = hashlib.sha256(content_str.encode()).hexdigest()[:12]
    
    problem_name = log.get("problem_name", "unknown")
    timestamp = int(log.get("timestamp", time.time()))
    
    filename = f"{problem_name}_{timestamp}_{content_hash}.json"
    filepath = output_dir / filename
    
    with open(filepath, 'w') as f:
        json.dump(log, f, indent=2)
    
    return filepath


def update_index(log_path: Path, index_path: Path = Path("sight_logs/INDEX.json")):
    """
    Update the INDEX.json file with a new sight log entry.
    
    Args:
        log_path: Path to the newly created log file
        index_path: Path to the INDEX.json file
    """
    # Load existing index or create new
    if index_path.exists():
        with open(index_path, 'r') as f:
            index = json.load(f)
    else:
        index = {
            "version": "1.0",
            "created": time.time(),
            "entries": []
        }
    
    # Load the log to extract metadata
    with open(log_path, 'r') as f:
        log = json.load(f)
    
    # Add entry to index
    entry = {
        "filename": log_path.name,
        "problem_name": log.get("problem_name", "unknown"),
        "n": log.get("n", 0),
        "seed": log.get("seed", 0),
        "timestamp": log.get("timestamp", time.time()),
        "verdict": log.get("consistency_analysis", {}).get("ground_truth_verdict", "UNKNOWN"),
        "avg_vi": log.get("consistency_analysis", {}).get("avg_vi", 0.0)
    }
    
    index["entries"].append(entry)
    index["last_updated"] = time.time()
    
    # Save updated index
    index_path.parent.mkdir(parents=True, exist_ok=True)
    with open(index_path, 'w') as f:
        json.dump(index, f, indent=2)


def append_progress_entry(
    message: str,
    progress_path: Path = Path("sight_logs/PROGRESS.md")
):
    """
    Append a progress entry to the PROGRESS.md file.
    
    Args:
        message: Progress message to append
        progress_path: Path to the PROGRESS.md file
    """
    progress_path.parent.mkdir(parents=True, exist_ok=True)
    
    timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
    entry = f"[{timestamp}] {message}\n"
    
    with open(progress_path, 'a') as f:
        f.write(entry)


# Main execution guard for testing
if __name__ == "__main__":
    # Simple test with a small problem
    test_clauses = [
        [1, 2, 3],
        [-1, 2],
        [-2, 3],
        [-1, -3],
        [1, -2, -3]
    ]
    
    log = assemble_log(
        clauses=test_clauses,
        problem_name="test_example",
        n=3,
        seed=0,
        verdict="CONSISTENT",
        metadata={"test": True}
    )
    
    print(json.dumps(log, indent=2))
    
    # Save the log
    log_path = save_log(log)
    print(f"\nLog saved to: {log_path}")
    
    # Update index
    update_index(log_path)
    print("Index updated")
    
    # Append progress
    append_progress_entry("Test sight log created successfully")
    print("Progress logged")
