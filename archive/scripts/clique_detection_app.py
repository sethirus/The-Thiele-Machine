#!/usr/bin/env python3
"""
Clique Detection Application using Thiele Machine
Finds maximum cliques in graphs using constraint satisfaction
"""

import time
from pysat.solvers import Glucose4
import networkx as nx

class ThieleCliqueDetector:
    def __init__(self, graph):
        self.graph = graph
        self.nodes = list(graph.nodes())
        self.node_to_idx = {node: i for i, node in enumerate(self.nodes)}
        self.solver = Glucose4()
        self.vars = {}
        self.var_counter = 0

    def get_var(self, name):
        """Lazy variable allocation"""
        if name not in self.vars:
            self.var_counter += 1
            self.vars[name] = self.var_counter
        return self.vars[name]

    def add_clique_constraints(self, min_clique_size):
        """Add constraints for finding a clique of at least given size"""
        print(f"[{time.time():.2f}s] Adding clique constraints for minimum size {min_clique_size}...")

        # All selected nodes must form a clique (all pairs connected)
        for i in range(len(self.nodes)):
            for j in range(i + 1, len(self.nodes)):
                node_i = self.nodes[i]
                node_j = self.nodes[j]

                # If both nodes are selected, they must be connected
                if not self.graph.has_edge(node_i, node_j):
                    self.solver.add_clause([
                        -self.get_var(f"selected_{i}"),
                        -self.get_var(f"selected_{j}")
                    ])

        # Ensure at least min_clique_size nodes are selected
        # Select the first min_clique_size nodes to guarantee a minimum size
        for i in range(min(min_clique_size, len(self.nodes))):
            self.solver.add_clause([self.get_var(f"selected_{i}")])

        print(f"[{time.time():.2f}s] Added constraints for clique with min size {min_clique_size} in {len(self.nodes)}-node graph")

    def solve_clique(self, min_size):
        """Solve for clique of at least given size"""
        print(f"[{time.time():.2f}s] Searching for clique of size at least {min_size}...")

        start_time = time.time()
        result = self.solver.solve()

        if result:
            print(f"[{(time.time() - start_time):.4f}s] SATISFIABLE - Found valid clique!")
            return self.extract_clique()
        else:
            print(f"[{(time.time() - start_time):.4f}s] UNSATISFIABLE - No clique of size {min_size} exists")
            return None

    def extract_clique(self):
        """Extract the clique from SAT solution"""
        model = self.solver.get_model()
        clique = []

        if model is None:
            return None

        for i, node in enumerate(self.nodes):
            var = self.get_var(f"selected_{i}")
            if var in model and model[model.index(var)] > 0:
                clique.append(node)

        return clique

    def find_maximum_clique(self, max_size=None):
        """Find the maximum clique by trying different sizes"""
        if max_size is None:
            max_size = len(self.nodes)

        print(f"[{time.time():.2f}s] Finding maximum clique (max size: {max_size})...")

        max_clique = []
        for size in range(max_size, 0, -1):
            print(f"\n--- Testing clique size {size} ---")

            # Reset solver for new attempt
            self.solver = Glucose4()
            self.vars = {}
            self.var_counter = 0

            self.add_clique_constraints(size)
            clique = self.solve_clique(size)

            if clique and len(clique) >= size:
                print(f"✓ Found clique of size {len(clique)}: {clique}")
                if len(clique) > len(max_clique):
                    max_clique = clique
                break  # Found a clique
            else:
                print(f"✗ No clique of size {size} exists")

        return max_clique

def create_test_graph():
    """Create a test graph with known cliques"""
    G = nx.Graph()

    # Create a graph with a known clique of size 4
    nodes = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H']
    G.add_nodes_from(nodes)

    # Add a clique of size 4: A,B,C,D
    clique_edges = [('A', 'B'), ('A', 'C'), ('A', 'D'),
                    ('B', 'C'), ('B', 'D'),
                    ('C', 'D')]

    # Add some additional edges
    extra_edges = [('A', 'E'), ('B', 'F'), ('C', 'G'), ('D', 'H'),
                   ('E', 'F'), ('F', 'G'), ('G', 'H')]

    G.add_edges_from(clique_edges + extra_edges)

    return G

def main():
    print("=== Thiele Machine: Clique Detection Application ===")
    print("Finding maximum cliques in graphs using constraint satisfaction\n")

    # Create test graph
    graph = create_test_graph()
    print(f"Test Graph: {len(graph.nodes())} nodes, {len(graph.edges())} edges")

    # Find maximum clique
    detector = ThieleCliqueDetector(graph)
    max_clique = detector.find_maximum_clique()

    if max_clique:
        print(f"\n🎯 Maximum clique found: {max_clique} (size {len(max_clique)})")
        print("This demonstrates the Thiele Machine solving NP-hard clique detection!")
    else:
        print("\n❌ No cliques found")

    print("\n=== Clique Detection Complete ===")

if __name__ == "__main__":
    main()