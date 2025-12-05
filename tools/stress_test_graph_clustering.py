#!/usr/bin/env python3
"""
Comprehensive Stress Tests for Graph Clustering

Tests graph clustering under extreme conditions:
1. Large graphs (1000+ nodes)
2. Dense graphs (high edge density)
3. Sparse graphs (very low density)
4. Extreme community structures (many small/few large)
5. Scale-free networks
6. Complete graphs and stars

Copyright 2025 Devon Thiele
Licensed under the Apache License, Version 2.0
"""

import sys
import time
from pathlib import Path

import networkx as nx
import numpy as np

sys.path.insert(0, str(Path(__file__).parent.parent))

from tools.graph_clustering import (
    cluster_thiele, cluster_spectral, cluster_louvain,
    compute_modularity
)


def test_large_graph():
    """Test on large graph with 1000 nodes."""
    print("\n" + "="*60)
    print("TEST 1: Large Graph (N=1000)")
    print("="*60)
    
    # Create planted partition with 1000 nodes, 10 communities
    n_communities = 10
    size_per_community = 100
    p_in = 0.1  # Within-community edge probability
    p_out = 0.01  # Between-community edge probability
    
    G = nx.planted_partition_graph(
        l=n_communities,
        k=size_per_community,
        p_in=p_in,
        p_out=p_out,
        seed=42
    )
    
    print(f"Nodes: {G.number_of_nodes()}")
    print(f"Edges: {G.number_of_edges()}")
    print(f"Communities: {n_communities}")
    
    # Ground truth
    ground_truth = []
    for i in range(n_communities):
        ground_truth.append(set(range(i * size_per_community, (i+1) * size_per_community)))
    
    # Test Thiele clustering
    start = time.time()
    result_thiele = cluster_thiele(G, ground_truth)
    thiele_time = time.time() - start
    
    # Test spectral clustering
    start = time.time()
    result_spectral = cluster_spectral(G, num_clusters=n_communities, ground_truth=ground_truth)
    spectral_time = time.time() - start
    
    # Test Louvain clustering
    start = time.time()
    result_louvain = cluster_louvain(G, ground_truth)
    louvain_time = time.time() - start
    
    print(f"\nThiele:   modularity={result_thiele.modularity:.3f}, NMI={result_thiele.nmi:.3f}, time={thiele_time:.2f}s")
    print(f"Spectral: modularity={result_spectral.modularity:.3f}, NMI={result_spectral.nmi:.3f}, time={spectral_time:.2f}s")
    print(f"Louvain:  modularity={result_louvain.modularity:.3f}, NMI={result_louvain.nmi:.3f}, time={louvain_time:.2f}s")
    
    # Validation: All methods should finish in reasonable time (<60s)
    assert thiele_time < 60, f"Thiele too slow: {thiele_time:.1f}s"
    assert spectral_time < 60, f"Spectral too slow: {spectral_time:.1f}s"
    assert louvain_time < 60, f"Louvain too slow: {louvain_time:.1f}s"
    
    # All should have positive modularity
    assert result_thiele.modularity > 0, "Thiele modularity negative"
    assert result_spectral.modularity > 0, "Spectral modularity negative"
    assert result_louvain.modularity > 0, "Louvain modularity negative"
    
    print("\n✓ PASSED: Large graph test")


def test_dense_graph():
    """Test on dense graph (high edge probability)."""
    print("\n" + "="*60)
    print("TEST 2: Dense Graph (p=0.5)")
    print("="*60)
    
    # Dense Erdős-Rényi graph
    n = 100
    p = 0.5  # Very dense
    G = nx.erdos_renyi_graph(n, p, seed=42)
    
    print(f"Nodes: {G.number_of_nodes()}")
    print(f"Edges: {G.number_of_edges()}")
    print(f"Density: {nx.density(G):.3f}")
    
    # Test clustering (no ground truth for random graph)
    result_thiele = cluster_thiele(G, None)
    result_spectral = cluster_spectral(G, num_clusters=3, ground_truth=None)
    result_louvain = cluster_louvain(G, None)
    
    print(f"\nThiele:   modularity={result_thiele.modularity:.3f}, clusters={result_thiele.num_clusters}")
    print(f"Spectral: modularity={result_spectral.modularity:.3f}, clusters={result_spectral.num_clusters}")
    print(f"Louvain:  modularity={result_louvain.modularity:.3f}, clusters={result_louvain.num_clusters}")
    
    # Dense random graphs should have low modularity (no clear structure)
    # But methods should still return valid results
    assert result_thiele.num_clusters >= 1, "Thiele found no clusters"
    assert result_spectral.num_clusters >= 1, "Spectral found no clusters"
    assert result_louvain.num_clusters >= 1, "Louvain found no clusters"
    
    print("\n✓ PASSED: Dense graph test")


def test_sparse_graph():
    """Test on very sparse graph."""
    print("\n" + "="*60)
    print("TEST 3: Sparse Graph (p=0.01)")
    print("="*60)
    
    # Sparse Erdős-Rényi graph
    n = 200
    p = 0.01  # Very sparse
    G = nx.erdos_renyi_graph(n, p, seed=42)
    
    # Ensure connected
    if not nx.is_connected(G):
        G = G.subgraph(max(nx.connected_components(G), key=len)).copy()
    
    print(f"Nodes: {G.number_of_nodes()}")
    print(f"Edges: {G.number_of_edges()}")
    print(f"Density: {nx.density(G):.4f}")
    
    # Test clustering
    result_thiele = cluster_thiele(G, None)
    result_spectral = cluster_spectral(G, num_clusters=3, ground_truth=None)
    result_louvain = cluster_louvain(G, None)
    
    print(f"\nThiele:   modularity={result_thiele.modularity:.3f}, clusters={result_thiele.num_clusters}")
    print(f"Spectral: modularity={result_spectral.modularity:.3f}, clusters={result_spectral.num_clusters}")
    print(f"Louvain:  modularity={result_louvain.modularity:.3f}, clusters={result_louvain.num_clusters}")
    
    # Sparse graphs should still be clusterable
    assert result_thiele.num_clusters >= 1, "Thiele found no clusters"
    assert result_spectral.num_clusters >= 1, "Spectral found no clusters"
    assert result_louvain.num_clusters >= 1, "Louvain found no clusters"
    
    print("\n✓ PASSED: Sparse graph test")


def test_scale_free_network():
    """Test on scale-free (Barabási-Albert) network."""
    print("\n" + "="*60)
    print("TEST 4: Scale-Free Network (BA model)")
    print("="*60)
    
    # Barabási-Albert preferential attachment
    n = 500
    m = 3  # Edges to attach from new node
    G = nx.barabasi_albert_graph(n, m, seed=42)
    
    print(f"Nodes: {G.number_of_nodes()}")
    print(f"Edges: {G.number_of_edges()}")
    
    # Compute degree distribution
    degrees = [G.degree(n) for n in G.nodes()]
    print(f"Degree: mean={np.mean(degrees):.1f}, max={max(degrees)}")
    
    # Test clustering
    result_thiele = cluster_thiele(G, None)
    result_spectral = cluster_spectral(G, num_clusters=5, ground_truth=None)
    result_louvain = cluster_louvain(G, None)
    
    print(f"\nThiele:   modularity={result_thiele.modularity:.3f}, clusters={result_thiele.num_clusters}")
    print(f"Spectral: modularity={result_spectral.modularity:.3f}, clusters={result_spectral.num_clusters}")
    print(f"Louvain:  modularity={result_louvain.modularity:.3f}, clusters={result_louvain.num_clusters}")
    
    # Scale-free networks should have reasonable modularity
    assert result_thiele.modularity >= -0.5, "Thiele modularity too negative"
    assert result_spectral.modularity >= -0.5, "Spectral modularity too negative"
    assert result_louvain.modularity >= -0.5, "Louvain modularity too negative"
    
    print("\n✓ PASSED: Scale-free network test")


def test_extreme_structures():
    """Test on graphs with extreme community structures."""
    print("\n" + "="*60)
    print("TEST 5: Extreme Structures (star + complete)")
    print("="*60)
    
    # Star graph: one central node connected to all others
    G_star = nx.star_graph(50)
    print(f"\nStar graph: {G_star.number_of_nodes()} nodes, {G_star.number_of_edges()} edges")
    
    result_star_thiele = cluster_thiele(G_star, None)
    result_star_louvain = cluster_louvain(G_star, None)
    
    print(f"Star - Thiele: modularity={result_star_thiele.modularity:.3f}, clusters={result_star_thiele.num_clusters}")
    print(f"Star - Louvain: modularity={result_star_louvain.modularity:.3f}, clusters={result_star_louvain.num_clusters}")
    
    # Complete graph: all nodes connected
    G_complete = nx.complete_graph(50)
    print(f"\nComplete graph: {G_complete.number_of_nodes()} nodes, {G_complete.number_of_edges()} edges")
    
    result_complete_thiele = cluster_thiele(G_complete, None)
    result_complete_louvain = cluster_louvain(G_complete, None)
    
    print(f"Complete - Thiele: modularity={result_complete_thiele.modularity:.3f}, clusters={result_complete_thiele.num_clusters}")
    print(f"Complete - Louvain: modularity={result_complete_louvain.modularity:.3f}, clusters={result_complete_louvain.num_clusters}")
    
    # Star should have low modularity (no good clustering)
    # Complete should also have low/zero modularity (all nodes equivalent)
    # But methods should handle these edge cases
    assert result_star_thiele.num_clusters >= 1, "Star: Thiele found no clusters"
    assert result_complete_thiele.num_clusters >= 1, "Complete: Thiele found no clusters"
    
    print("\n✓ PASSED: Extreme structures test")


def test_many_small_communities():
    """Test with many small communities."""
    print("\n" + "="*60)
    print("TEST 6: Many Small Communities (50 communities of 10)")
    print("="*60)
    
    # 50 communities of 10 nodes each
    n_communities = 50
    size_per_community = 10
    p_in = 0.7
    p_out = 0.02
    
    G = nx.planted_partition_graph(
        l=n_communities,
        k=size_per_community,
        p_in=p_in,
        p_out=p_out,
        seed=42
    )
    
    print(f"Nodes: {G.number_of_nodes()}")
    print(f"Edges: {G.number_of_edges()}")
    print(f"Communities: {n_communities} × {size_per_community}")
    
    # Test clustering
    result_thiele = cluster_thiele(G, None)
    result_louvain = cluster_louvain(G, None)
    
    print(f"\nThiele:   modularity={result_thiele.modularity:.3f}, clusters={result_thiele.num_clusters}")
    print(f"Louvain:  modularity={result_louvain.modularity:.3f}, clusters={result_louvain.num_clusters}")
    
    # With many clear communities, methods should find high modularity
    assert result_thiele.modularity > 0.3, "Thiele low modularity on structured graph"
    assert result_louvain.modularity > 0.3, "Louvain low modularity on structured graph"
    
    # Should find multiple clusters
    assert result_thiele.num_clusters > 10, "Thiele found too few clusters"
    assert result_louvain.num_clusters > 10, "Louvain found too few clusters"
    
    print("\n✓ PASSED: Many small communities test")


def main():
    """Run all stress tests."""
    print("\n" + "="*60)
    print("GRAPH CLUSTERING STRESS TEST SUITE")
    print("="*60)
    
    tests = [
        test_large_graph,
        test_dense_graph,
        test_sparse_graph,
        test_scale_free_network,
        test_extreme_structures,
        test_many_small_communities
    ]
    
    passed = 0
    failed = 0
    
    for test in tests:
        try:
            test()
            passed += 1
        except AssertionError as e:
            print(f"\n✗ FAILED: {e}")
            failed += 1
        except Exception as e:
            print(f"\n✗ ERROR: {e}")
            failed += 1
    
    print("\n" + "="*60)
    print(f"RESULTS: {passed}/{len(tests)} tests passed")
    if failed > 0:
        print(f"         {failed}/{len(tests)} tests failed")
    print("="*60)
    
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
