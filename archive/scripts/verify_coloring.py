# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""
Verification script for Graph Coloring Solution
Confirms that the Thiele Machine's coloring assignment is valid
"""

import networkx as nx

def create_test_graph():
    """Recreate the exact same test graph"""
    G = nx.Graph()
    nodes = ['A', 'B', 'C', 'D', 'E', 'F', 'G']
    G.add_nodes_from(nodes)

    edges = [('A', 'B'), ('A', 'C'), ('A', 'D'),
             ('B', 'C'), ('B', 'E'),
             ('C', 'D'), ('C', 'E'), ('C', 'F'),
             ('D', 'F'), ('D', 'G'),
             ('E', 'F'), ('E', 'G'),
             ('F', 'G')]
    G.add_edges_from(edges)
    return G

def verify_coloring(graph, coloring):
    """Verify that a coloring assignment is valid"""
    print("🔍 Verifying Graph Coloring Solution")
    print(f"Graph: {len(graph.nodes())} nodes, {len(graph.edges())} edges")
    print(f"Coloring: {coloring}")

    conflicts = []

    for edge in graph.edges():
        node1, node2 = edge
        color1 = coloring.get(node1)
        color2 = coloring.get(node2)

        if color1 == color2:
            conflicts.append((node1, node2, color1))
            print(f"❌ CONFLICT: {node1} and {node2} both have color {color1}")
        else:
            print(f"✓ OK: {node1} (color {color1}) ≠ {node2} (color {color2})")

    if conflicts:
        print(f"\n🚨 INVALID COLORING: Found {len(conflicts)} conflicts")
        return False
    else:
        print("\n🎉 VALID COLORING: No conflicts found!")
        print(f"✓ All {len(graph.edges())} edges have different colors on their endpoints")
        return True

def analyze_color_usage(coloring):
    """Analyze how colors are used"""
    colors_used = set(coloring.values())
    print(f"\n📊 Color Analysis:")
    print(f"Colors used: {sorted(colors_used)}")
    print(f"Total colors: {len(colors_used)}")

    color_counts = {}
    for node, color in coloring.items():
        color_counts[color] = color_counts.get(color, 0) + 1

    print("Color distribution:")
    for color in sorted(color_counts.keys()):
        print(f"  Color {color}: {color_counts[color]} nodes")

def main():
    print("=== Graph Coloring Verification ===")

    # Recreate the exact graph
    graph = create_test_graph()

    # The coloring assignment from Thiele Machine
    coloring = {'A': 3, 'B': 1, 'C': 0, 'D': 2, 'E': 2, 'F': 1, 'G': 0}

    # Verify the coloring
    is_valid = verify_coloring(graph, coloring)

    if is_valid:
        analyze_color_usage(coloring)
        print("\n✅ VERIFICATION COMPLETE: Thiele Machine produced a valid 4-coloring!")
    else:
        print("\n❌ VERIFICATION FAILED: Invalid coloring detected!")

    print("\n=== Verification Complete ===")

if __name__ == "__main__":
    main()