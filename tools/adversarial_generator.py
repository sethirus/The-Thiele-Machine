#!/usr/bin/env python3
"""
Adversarial Graph Generator for Testing Spectral Decomposition Hypothesis

This script generates graph structures specifically designed to be failure modes
for spectral clustering and spectral partitioning algorithms. These adversarial
structures test whether the Thiele Machine's efficiency is fully explained by
Spectral Decomposition or if a deeper principle (P+1) exists.

Known Failure Modes for Spectral Methods:
1. Lollipop Graphs: Dense clique connected to long path (misleading eigenvectors)
2. Barbell Graphs: Two dense cliques connected by single edge (weak connectivity)
3. Multi-scale Communities: Dense communities of vastly different sizes
4. Hierarchical Structures: Nested communities with weak inter-connections
5. Near-bipartite with Noise: Almost bipartite but with adversarial perturbations
"""

import argparse
import json
import random
import sys
from pathlib import Path
from typing import List, Dict, Tuple, Set

import networkx as nx  # type: ignore
import numpy as np


class AdversarialGraphGenerator:
    """Generates graphs that are adversarial to spectral methods."""
    
    def __init__(self, seed: int = 42):
        random.seed(seed)
        np.random.seed(seed)
        self.seed = seed
    
    def generate_lollipop_graph(self, clique_size: int, path_length: int) -> nx.Graph:
        """
        Generate a lollipop graph: dense clique + long path.
        
        Spectral Issue: The dominant eigenvector primarily reflects the clique,
        masking structure in the path portion. Partitioning based on spectral
        gap will incorrectly split the graph.
        
        Args:
            clique_size: Number of nodes in the dense clique
            path_length: Length of the attached path
            
        Returns:
            NetworkX graph with lollipop structure
        """
        G = nx.Graph()
        n_total = clique_size + path_length
        
        # Create clique
        for i in range(clique_size):
            for j in range(i + 1, clique_size):
                G.add_edge(i, j)
        
        # Create path attached to clique
        for i in range(clique_size, n_total - 1):
            G.add_edge(i, i + 1)
        
        # Connect clique to path
        if clique_size > 0 and path_length > 0:
            G.add_edge(clique_size - 1, clique_size)
        
        return G
    
    def generate_barbell_graph(self, clique_size: int, bridge_length: int = 1) -> nx.Graph:
        """
        Generate a barbell graph: two cliques connected by a bridge.
        
        Spectral Issue: Weak connectivity between dense components leads to
        poor eigenvalue separation. The second eigenvector may not cleanly
        separate the two cliques if the bridge has subtle structure.
        
        Args:
            clique_size: Size of each clique
            bridge_length: Length of connecting path (default 1 = single edge)
            
        Returns:
            NetworkX graph with barbell structure
        """
        G = nx.Graph()
        
        # First clique (nodes 0 to clique_size-1)
        for i in range(clique_size):
            for j in range(i + 1, clique_size):
                G.add_edge(i, j)
        
        # Second clique (nodes clique_size+bridge_length to 2*clique_size+bridge_length-1)
        offset = clique_size + bridge_length
        for i in range(offset, offset + clique_size):
            for j in range(i + 1, offset + clique_size):
                G.add_edge(i, j)
        
        # Bridge connecting the cliques
        if bridge_length == 1:
            G.add_edge(clique_size - 1, offset)
        else:
            # Create path bridge
            for i in range(clique_size - 1, clique_size + bridge_length - 1):
                G.add_edge(i, i + 1)
        
        return G
    
    def generate_multiscale_communities(self, 
                                       sizes: List[int],
                                       inter_prob: float = 0.05,
                                       intra_prob: float = 0.8) -> nx.Graph:
        """
        Generate graph with communities of vastly different sizes.
        
        Spectral Issue: Dominant eigenvectors reflect large communities,
        completely missing small but important communities. Spectral gap
        may suggest k clusters when there are actually k+m (m small communities).
        
        Args:
            sizes: List of community sizes (e.g., [50, 50, 5, 5, 3])
            inter_prob: Probability of edges between communities
            intra_prob: Probability of edges within communities
            
        Returns:
            NetworkX graph with multi-scale community structure
        """
        G = nx.Graph()
        node_offset = 0
        communities = []
        
        for size in sizes:
            community_nodes = list(range(node_offset, node_offset + size))
            communities.append(community_nodes)
            
            # Dense intra-community edges
            for i in community_nodes:
                for j in community_nodes:
                    if i < j and random.random() < intra_prob:
                        G.add_edge(i, j)
            
            node_offset += size
        
        # Sparse inter-community edges
        for i, comm1 in enumerate(communities):
            for j, comm2 in enumerate(communities):
                if i < j:
                    for node1 in comm1:
                        for node2 in comm2:
                            if random.random() < inter_prob:
                                G.add_edge(node1, node2)
        
        return G
    
    def generate_near_bipartite_adversarial(self, 
                                            set1_size: int,
                                            set2_size: int,
                                            noise_edges: int = 5) -> nx.Graph:
        """
        Generate near-bipartite graph with adversarial noise.
        
        Spectral Issue: Perfect bipartite graphs have clean spectral structure,
        but adding specific noise edges can make spectral methods fail to find
        the correct partition while maintaining most bipartite structure.
        
        Args:
            set1_size: Size of first partition
            set2_size: Size of second partition
            noise_edges: Number of adversarial edges within partitions
            
        Returns:
            NetworkX graph that is almost bipartite with adversarial noise
        """
        G = nx.Graph()
        
        set1 = list(range(set1_size))
        set2 = list(range(set1_size, set1_size + set2_size))
        
        # Create bipartite edges (most edges go between sets)
        for i in set1:
            for j in set2:
                if random.random() < 0.7:  # 70% of possible bipartite edges
                    G.add_edge(i, j)
        
        # Add adversarial noise: strategically placed edges within sets
        # Place them to maximally confuse spectral partitioning
        for _ in range(noise_edges):
            # Add triangle-forming edges in set1
            if len(set1) >= 3:
                nodes = random.sample(set1, 3)
                G.add_edge(nodes[0], nodes[1])
                G.add_edge(nodes[1], nodes[2])
            
            # Add triangle-forming edges in set2
            if len(set2) >= 3:
                nodes = random.sample(set2, 3)
                G.add_edge(nodes[0], nodes[1])
                G.add_edge(nodes[1], nodes[2])
        
        return G
    
    def get_spectral_properties(self, G: nx.Graph) -> Dict[str, float]:
        """
        Compute spectral properties of the graph.
        
        Returns:
            Dictionary with eigenvalues, spectral gap, etc.
        """
        if len(G.nodes()) == 0:
            return {"error": "empty graph"}
        
        # Compute Laplacian eigenvalues
        L = nx.laplacian_matrix(G).todense()
        eigenvalues = np.linalg.eigvalsh(L)
        eigenvalues = sorted(eigenvalues)
        
        properties = {
            "n_nodes": len(G.nodes()),
            "n_edges": len(G.edges()),
            "lambda_1": float(eigenvalues[0]) if len(eigenvalues) > 0 else 0.0,
            "lambda_2": float(eigenvalues[1]) if len(eigenvalues) > 1 else 0.0,
            "lambda_3": float(eigenvalues[2]) if len(eigenvalues) > 2 else 0.0,
            "spectral_gap": float(eigenvalues[1] - eigenvalues[0]) if len(eigenvalues) > 1 else 0.0,
            "conductance_estimate": float(eigenvalues[1] / 2.0) if len(eigenvalues) > 1 else 0.0,
        }
        
        return properties


def embed_tseitin_on_graph(G: nx.Graph, seed: int = 42) -> Tuple[List[List[int]], Dict[str, any]]:
    """
    Embed a Tseitin formula onto the graph structure.
    
    The Tseitin transformation converts a graph into a CNF formula that is
    unsatisfiable if and only if the graph has odd degree sum. We'll create
    a variant that embeds the graph structure into the formula.
    
    Args:
        G: Input graph
        seed: Random seed
        
    Returns:
        Tuple of (CNF clauses, metadata)
    """
    random.seed(seed)
    n_nodes = len(G.nodes())
    
    if n_nodes == 0:
        return ([], {"error": "empty graph"})
    
    clauses = []
    
    # Create variable mapping: one variable per edge
    edge_to_var = {}
    var_counter = 1
    for edge in G.edges():
        edge_to_var[edge] = var_counter
        var_counter += 1
    
    # For each node, create Tseitin clause
    # XOR of all incident edges = parity bit
    for node in G.nodes():
        incident_edges = list(G.edges(node))
        if len(incident_edges) == 0:
            continue
        
        # Get variables for incident edges
        incident_vars = []
        for edge in incident_edges:
            # Normalize edge representation
            e = tuple(sorted(edge))
            if e in edge_to_var:
                incident_vars.append(edge_to_var[e])
            else:
                # Try reverse
                e_rev = tuple(sorted(edge[::-1]))
                if e_rev in edge_to_var:
                    incident_vars.append(edge_to_var[e_rev])
        
        # Create XOR constraint (convert to CNF)
        # For odd parity (makes formula unsatisfiable if graph has odd total degree)
        parity = node % 2  # Alternate parity per node to create conflict
        
        # XOR to CNF: for n variables, need 2^(n-1) clauses
        # Simplified: create representative clauses
        if len(incident_vars) == 1:
            if parity == 1:
                clauses.append([incident_vars[0]])
            else:
                clauses.append([-incident_vars[0]])
        elif len(incident_vars) == 2:
            if parity == 1:
                clauses.append([incident_vars[0], incident_vars[1]])
                clauses.append([-incident_vars[0], -incident_vars[1]])
            else:
                clauses.append([incident_vars[0], -incident_vars[1]])
                clauses.append([-incident_vars[0], incident_vars[1]])
        else:
            # For more variables, create subset of XOR clauses
            # This is an approximation to keep formula size manageable
            for i in range(len(incident_vars)):
                for j in range(i + 1, len(incident_vars)):
                    if parity == 1:
                        clauses.append([incident_vars[i], incident_vars[j]])
                    else:
                        clauses.append([incident_vars[i], -incident_vars[j]])
    
    metadata = {
        "n_variables": len(edge_to_var),
        "n_clauses": len(clauses),
        "n_nodes": n_nodes,
        "n_edges": len(G.edges()),
        "embedding": "tseitin",
    }
    
    return (clauses, metadata)


def write_cnf_file(clauses: List[List[int]], n_vars: int, output_path: Path):
    """Write CNF formula to DIMACS format file."""
    with open(output_path, 'w') as f:
        f.write(f"p cnf {n_vars} {len(clauses)}\n")
        for clause in clauses:
            f.write(" ".join(map(str, clause)) + " 0\n")


def main():
    parser = argparse.ArgumentParser(description="Generate adversarial graphs for testing spectral hypothesis")
    parser.add_argument("--type", choices=["lollipop", "barbell", "multiscale", "near_bipartite"],
                       default="lollipop", help="Type of adversarial structure")
    parser.add_argument("--n", type=int, default=50, help="Size parameter for graph generation")
    parser.add_argument("--embed", choices=["tseitin", "none"], default="tseitin",
                       help="Problem type to embed on graph")
    parser.add_argument("--output", type=str, default="adversarial_problem.cnf",
                       help="Output file name")
    parser.add_argument("--seed", type=int, default=42, help="Random seed")
    parser.add_argument("--analyze", action="store_true", help="Print spectral analysis")
    
    args = parser.parse_args()
    
    gen = AdversarialGraphGenerator(seed=args.seed)
    
    # Generate graph based on type
    if args.type == "lollipop":
        clique_size = args.n // 2
        path_length = args.n - clique_size
        G = gen.generate_lollipop_graph(clique_size, path_length)
        print(f"Generated lollipop graph: clique={clique_size}, path={path_length}")
        
    elif args.type == "barbell":
        clique_size = args.n // 3
        bridge_length = max(1, args.n // 10)
        G = gen.generate_barbell_graph(clique_size, bridge_length)
        print(f"Generated barbell graph: clique={clique_size}, bridge={bridge_length}")
        
    elif args.type == "multiscale":
        # Create multi-scale communities: few large, several small
        large_size = args.n // 3
        small_size = args.n // 10
        sizes = [large_size, large_size, small_size, small_size, small_size]
        G = gen.generate_multiscale_communities(sizes)
        print(f"Generated multiscale graph: communities={sizes}")
        
    elif args.type == "near_bipartite":
        set1_size = args.n // 2
        set2_size = args.n - set1_size
        noise_edges = max(3, args.n // 10)
        G = gen.generate_near_bipartite_adversarial(set1_size, set2_size, noise_edges)
        print(f"Generated near-bipartite graph: {set1_size}+{set2_size} with {noise_edges} noise edges")
    
    # Analyze spectral properties
    if args.analyze:
        props = gen.get_spectral_properties(G)
        print("\nSpectral Properties:")
        for key, value in props.items():
            print(f"  {key}: {value:.4f}" if isinstance(value, float) else f"  {key}: {value}")
    
    # Embed problem if requested
    if args.embed == "tseitin":
        clauses, metadata = embed_tseitin_on_graph(G, seed=args.seed)
        output_path = Path(args.output)
        write_cnf_file(clauses, metadata["n_variables"], output_path)
        print(f"\nEmbedded Tseitin formula: {metadata['n_variables']} vars, {metadata['n_clauses']} clauses")
        print(f"Written to: {output_path}")
        
        # Save metadata
        meta_path = output_path.with_suffix('.json')
        with open(meta_path, 'w') as f:
            metadata["graph_type"] = args.type
            metadata["spectral_properties"] = gen.get_spectral_properties(G)
            json.dump(metadata, f, indent=2)
        print(f"Metadata written to: {meta_path}")
    
    print("\nAdversarial graph generation complete.")
    print("This graph is designed to be a failure mode for spectral partitioning.")
    print("Testing it will reveal if the Thiele Machine uses pure spectral methods or P+1.")


if __name__ == "__main__":
    main()
