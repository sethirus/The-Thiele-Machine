# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""
Graph Coloring Application using Thiele Machine
Demonstrates NP-hard problem solving with constraint satisfaction
"""

import time
from pysat.solvers import Glucose4
import networkx as nx
import matplotlib
matplotlib.use('Agg')  # Use non-interactive backend
import matplotlib.pyplot as plt

class ThieleGraphColoring:
    def __init__(self, graph, num_colors):
        self.graph = graph
        self.num_colors = num_colors
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

    def add_coloring_constraints(self):
        """Add constraints for valid graph coloring"""
        print(f"[{time.time():.2f}s] Adding graph coloring constraints...")

        # Each node must have exactly one color
        for node in self.nodes:
            node_idx = self.node_to_idx[node]
            # At least one color
            color_vars = [self.get_var(f"node_{node_idx}_color_{c}") for c in range(self.num_colors)]
            self.solver.add_clause(color_vars)

            # At most one color (pairwise exclusions)
            for c1 in range(self.num_colors):
                for c2 in range(c1 + 1, self.num_colors):
                    self.solver.add_clause([
                        -self.get_var(f"node_{node_idx}_color_{c1}"),
                        -self.get_var(f"node_{node_idx}_color_{c2}")
                    ])

        # Adjacent nodes cannot have the same color
        for edge in self.graph.edges():
            node1_idx = self.node_to_idx[edge[0]]
            node2_idx = self.node_to_idx[edge[1]]

            for c in range(self.num_colors):
                self.solver.add_clause([
                    -self.get_var(f"node_{node1_idx}_color_{c}"),
                    -self.get_var(f"node_{node2_idx}_color_{c}")
                ])

        print(f"[{time.time():.2f}s] Added {len(self.nodes)} node constraints and {len(self.graph.edges())} edge constraints")

    def solve_coloring(self):
        """Solve the graph coloring problem"""
        print(f"[{time.time():.2f}s] Solving {len(self.nodes)}-node graph with {self.num_colors} colors...")

        start_time = time.time()
        result = self.solver.solve()
        solve_time = time.time() - start_time

        if result:
            print(f"[{(time.time() - start_time):.4f}s] SATISFIABLE - Found valid {self.num_colors}-coloring!")
            return self.extract_coloring()
        else:
            print(f"[{(time.time() - start_time):.4f}s] UNSATISFIABLE - Cannot color with {self.num_colors} colors")
            return None

    def extract_coloring(self):
        """Extract the coloring assignment from SAT solution"""
        model = self.solver.get_model()
        coloring = {}

        if model is None:
            return None

        for node in self.nodes:
            node_idx = self.node_to_idx[node]
            for c in range(self.num_colors):
                var = self.get_var(f"node_{node_idx}_color_{c}")
                if var in model and model[model.index(var)] > 0:
                    coloring[node] = c
                    break

        return coloring

    def visualize_coloring(self, coloring, title="Graph Coloring Solution"):
        """Visualize the colored graph"""
        if coloring is None:
            print("No valid coloring found to visualize")
            return

        colors = ['red', 'blue', 'green', 'yellow', 'purple', 'orange', 'pink', 'brown']
        node_colors = [colors[coloring[node] % len(colors)] for node in self.nodes]

        plt.figure(figsize=(10, 8))
        pos = nx.spring_layout(self.graph)

        nx.draw(self.graph, pos, with_labels=True, node_color=node_colors,
                node_size=500, font_size=16, font_weight='bold')

        plt.title(title)
        plt.axis('off')
        plt.tight_layout()
        plt.savefig('graph_coloring_solution.png', dpi=300, bbox_inches='tight')
        plt.close()  # Close the figure to free memory
        print(f"✓ Graph coloring visualization saved as 'graph_coloring_solution.png'")

def create_test_graph():
    """Create a test graph for demonstration"""
    # Create a graph with known chromatic number
    G = nx.Graph()

    # Add nodes
    nodes = ['A', 'B', 'C', 'D', 'E', 'F', 'G']
    G.add_nodes_from(nodes)

    # Add edges to create a graph that requires 3 colors
    edges = [('A', 'B'), ('A', 'C'), ('A', 'D'),
             ('B', 'C'), ('B', 'E'),
             ('C', 'D'), ('C', 'E'), ('C', 'F'),
             ('D', 'F'), ('D', 'G'),
             ('E', 'F'), ('E', 'G'),
             ('F', 'G')]
    G.add_edges_from(edges)

    return G

def main():
    print("=== Thiele Machine: Graph Coloring Application ===")
    print("Solving NP-hard graph coloring problems with constraint satisfaction\n")

    # Create test graph
    graph = create_test_graph()
    print(f"Test Graph: {len(graph.nodes())} nodes, {len(graph.edges())} edges")

    # Try with different numbers of colors
    for num_colors in [2, 3, 4]:
        print(f"\n--- Attempting {num_colors}-coloring ---")

        colorer = ThieleGraphColoring(graph, num_colors)
        colorer.add_coloring_constraints()
        coloring = colorer.solve_coloring()

        if coloring:
            print(f"✓ Successfully colored with {num_colors} colors!")
            print("Color assignment:", coloring)

            # Visualize the solution
            colorer.visualize_coloring(coloring, f"{num_colors}-Color Graph Coloring")
            break
        else:
            print(f"✗ Cannot color with {num_colors} colors")

    print("\n=== Graph Coloring Complete ===")

if __name__ == "__main__":
    main()