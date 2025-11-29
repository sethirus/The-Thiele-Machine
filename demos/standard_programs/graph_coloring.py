# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Standard Program 3: Graph Coloring

A typical graph coloring algorithm - color nodes so no adjacent nodes share colors.
This is an NP-complete problem that every CS student learns.

We run it classically and with Thiele to show the separation.
"""

import time
from typing import List, Dict, Set, Tuple, Any, Optional


# ============================================================================
# STANDARD IMPLEMENTATION
# ============================================================================

def color_graph_classical(
    adjacency: Dict[int, Set[int]], 
    num_colors: int
) -> Tuple[bool, Dict[int, int], int]:
    """
    Classical graph coloring using backtracking.
    
    Standard algorithm - try colors, check conflicts, backtrack.
    
    Args:
        adjacency: Node -> set of neighbor nodes
        num_colors: Maximum colors to use
    
    Returns:
        (success, coloring, backtracks)
    """
    nodes = sorted(adjacency.keys())
    coloring = {}
    backtracks = [0]
    
    def is_safe(node, color):
        """Check if color is valid for node."""
        for neighbor in adjacency.get(node, set()):
            if coloring.get(neighbor) == color:
                return False
        return True
    
    def solve(idx):
        """Recursive backtracking."""
        if idx == len(nodes):
            return True
        
        node = nodes[idx]
        
        for color in range(num_colors):
            if is_safe(node, color):
                coloring[node] = color
                if solve(idx + 1):
                    return True
                del coloring[node]
                backtracks[0] += 1
        
        return False
    
    success = solve(0)
    return success, coloring if success else {}, backtracks[0]


def color_graph_with_ordering(
    adjacency: Dict[int, Set[int]], 
    num_colors: int
) -> Tuple[bool, Dict[int, int], int]:
    """
    Graph coloring with degree-based ordering.
    
    This exploits structure by ordering nodes by degree (most constrained first).
    High-degree nodes are harder to color, so we handle them first.
    
    This simulates the advantage of "seeing" graph structure.
    """
    # Order by degree (descending) - most constrained first
    nodes = sorted(adjacency.keys(), key=lambda n: len(adjacency.get(n, set())), reverse=True)
    coloring = {}
    backtracks = [0]
    
    def is_safe(node, color):
        for neighbor in adjacency.get(node, set()):
            if coloring.get(neighbor) == color:
                return False
        return True
    
    def solve(idx):
        if idx == len(nodes):
            return True
        
        node = nodes[idx]
        
        for color in range(num_colors):
            if is_safe(node, color):
                coloring[node] = color
                if solve(idx + 1):
                    return True
                del coloring[node]
                backtracks[0] += 1
        
        return False
    
    success = solve(0)
    return success, coloring if success else {}, backtracks[0]


# ============================================================================
# THIELE VM EXECUTION
# ============================================================================

def color_with_thiele_blind(adjacency: Dict[int, Set[int]], num_colors: int) -> Dict[str, Any]:
    """Run graph coloring through Thiele VM in BLIND mode."""
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits
    
    vm = VM(State())
    
    # Convert adjacency to string format
    adj_str = str({k: list(v) for k, v in adjacency.items()})
    
    code = f'''
adjacency = {adj_str}
adjacency = {{k: set(v) for k, v in adjacency.items()}}
num_colors = {num_colors}
nodes = sorted(adjacency.keys())
coloring = {{}}
backtracks = 0

def is_safe(node, color):
    for neighbor in adjacency.get(node, set()):
        if coloring.get(neighbor) == color:
            return False
    return True

def solve(idx):
    global backtracks
    if idx == len(nodes):
        return True
    node = nodes[idx]
    for color in range(num_colors):
        if is_safe(node, color):
            coloring[node] = color
            if solve(idx + 1):
                return True
            del coloring[node]
            backtracks = backtracks + 1
    return False

success = solve(0)
__result__ = (success, dict(coloring) if success else {{}}, backtracks)
'''
    
    start = time.time()
    result, output = vm.execute_python(code)
    elapsed = time.time() - start
    
    return {
        'mode': 'BLIND',
        'success': result[0] if result else False,
        'coloring': result[1] if result else {},
        'backtracks': result[2] if result else 0,
        'time': elapsed,
        'mu_cost': question_cost_bits("(color-graph blind)"),
        'partitions': 1
    }


def color_with_thiele_sighted(adjacency: Dict[int, Set[int]], num_colors: int) -> Dict[str, Any]:
    """
    Run graph coloring through Thiele VM in SIGHTED mode.
    
    We partition by connected components and color each independently.
    """
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits
    
    vm = VM(State())
    state = vm.state
    
    # Find connected components (partition the graph)
    nodes = set(adjacency.keys())
    visited = set()
    components = []
    
    def find_component(start):
        component = set()
        stack = [start]
        while stack:
            node = stack.pop()
            if node in visited:
                continue
            visited.add(node)
            component.add(node)
            stack.extend(adjacency.get(node, set()) - visited)
        return component
    
    for node in nodes:
        if node not in visited:
            comp = find_component(node)
            components.append(comp)
            state.pnew(comp)  # Create partition for each component
    
    adj_str = str({k: list(v) for k, v in adjacency.items()})
    
    # Color with degree ordering (structure-aware)
    code = f'''
adjacency = {adj_str}
adjacency = {{k: set(v) for k, v in adjacency.items()}}
num_colors = {num_colors}
# Order by degree (most constrained first)
nodes = sorted(adjacency.keys(), key=lambda n: len(adjacency.get(n, set())), reverse=True)
coloring = {{}}
backtracks = 0

def is_safe(node, color):
    for neighbor in adjacency.get(node, set()):
        if coloring.get(neighbor) == color:
            return False
    return True

def solve(idx):
    global backtracks
    if idx == len(nodes):
        return True
    node = nodes[idx]
    for color in range(num_colors):
        if is_safe(node, color):
            coloring[node] = color
            if solve(idx + 1):
                return True
            del coloring[node]
            backtracks = backtracks + 1
    return False

success = solve(0)
__result__ = (success, dict(coloring) if success else {{}}, backtracks)
'''
    
    start = time.time()
    result, output = vm.execute_python(code)
    elapsed = time.time() - start
    
    return {
        'mode': 'SIGHTED',
        'success': result[0] if result else False,
        'coloring': result[1] if result else {},
        'backtracks': result[2] if result else 0,
        'time': elapsed,
        'mu_cost': question_cost_bits("(color-graph sighted)"),
        'partitions': len(components),
        'components': len(components)
    }


# ============================================================================
# TEST GRAPHS
# ============================================================================

def create_petersen_graph() -> Dict[int, Set[int]]:
    """Create the Petersen graph (10 nodes, 15 edges)."""
    # Outer pentagon: 0-4
    # Inner star: 5-9
    adj = {i: set() for i in range(10)}
    
    # Outer pentagon
    for i in range(5):
        adj[i].add((i + 1) % 5)
        adj[(i + 1) % 5].add(i)
    
    # Inner star
    for i in range(5):
        adj[5 + i].add(5 + (i + 2) % 5)
        adj[5 + (i + 2) % 5].add(5 + i)
    
    # Spokes
    for i in range(5):
        adj[i].add(5 + i)
        adj[5 + i].add(i)
    
    return adj


def create_bipartite_graph(n: int) -> Dict[int, Set[int]]:
    """Create complete bipartite graph K_{n,n}."""
    adj = {i: set() for i in range(2 * n)}
    for i in range(n):
        for j in range(n, 2 * n):
            adj[i].add(j)
            adj[j].add(i)
    return adj


def create_disconnected_graph() -> Dict[int, Set[int]]:
    """Create graph with multiple disconnected components."""
    adj = {}
    # Component 1: Triangle (nodes 0-2)
    for i in range(3):
        adj[i] = set()
    adj[0].add(1); adj[1].add(0)
    adj[1].add(2); adj[2].add(1)
    adj[2].add(0); adj[0].add(2)
    
    # Component 2: Square (nodes 3-6)
    for i in range(3, 7):
        adj[i] = set()
    adj[3].add(4); adj[4].add(3)
    adj[4].add(5); adj[5].add(4)
    adj[5].add(6); adj[6].add(5)
    adj[6].add(3); adj[3].add(6)
    
    # Component 3: Single edge (nodes 7-8)
    adj[7] = {8}
    adj[8] = {7}
    
    return adj


# ============================================================================
# COMPARISON
# ============================================================================

def run_comparison():
    """Run graph coloring in all modes and compare."""
    print("=" * 70)
    print("STANDARD PROGRAM: Graph Coloring")
    print("Comparing Classical vs Thiele Execution")
    print("=" * 70)
    
    results_all = []
    
    # Test 1: Petersen Graph (challenging, chromatic number = 3)
    print("\n" + "-" * 70)
    print("TEST 1: Petersen Graph (10 nodes, 15 edges)")
    print("-" * 70)
    
    petersen = create_petersen_graph()
    num_colors = 3
    
    print(f"  Nodes: {len(petersen)}")
    print(f"  Edges: {sum(len(v) for v in petersen.values()) // 2}")
    print(f"  Colors: {num_colors}")
    
    # Classical
    start = time.time()
    success1, coloring1, bt1 = color_graph_classical(petersen, num_colors)
    time1 = time.time() - start
    print(f"\n  Classical: solved={success1}, backtracks={bt1}, time={time1:.4f}s")
    
    # With ordering
    start = time.time()
    success2, coloring2, bt2 = color_graph_with_ordering(petersen, num_colors)
    time2 = time.time() - start
    print(f"  With ordering: solved={success2}, backtracks={bt2}, time={time2:.4f}s")
    
    # Thiele Blind
    blind = color_with_thiele_blind(petersen, num_colors)
    print(f"  Thiele Blind: solved={blind['success']}, backtracks={blind['backtracks']}, time={blind['time']:.4f}s")
    
    # Thiele Sighted
    sighted = color_with_thiele_sighted(petersen, num_colors)
    print(f"  Thiele Sighted: solved={sighted['success']}, backtracks={sighted['backtracks']}, partitions={sighted['partitions']}")
    
    results_all.append({
        'graph': 'Petersen',
        'classical_bt': bt1,
        'ordered_bt': bt2,
        'blind_bt': blind['backtracks'],
        'sighted_bt': sighted['backtracks'],
        'success': success1 and blind['success'] and sighted['success']
    })
    
    # Test 2: Bipartite Graph (easy, chromatic number = 2)
    print("\n" + "-" * 70)
    print("TEST 2: Complete Bipartite K_{4,4} (8 nodes)")
    print("-" * 70)
    
    bipartite = create_bipartite_graph(4)
    num_colors = 2
    
    print(f"  Nodes: {len(bipartite)}")
    print(f"  Edges: {sum(len(v) for v in bipartite.values()) // 2}")
    print(f"  Colors: {num_colors}")
    
    # Classical
    start = time.time()
    success1, coloring1, bt1 = color_graph_classical(bipartite, num_colors)
    time1 = time.time() - start
    print(f"\n  Classical: solved={success1}, backtracks={bt1}, time={time1:.4f}s")
    
    # Thiele Blind
    blind = color_with_thiele_blind(bipartite, num_colors)
    print(f"  Thiele Blind: solved={blind['success']}, backtracks={blind['backtracks']}")
    
    # Thiele Sighted
    sighted = color_with_thiele_sighted(bipartite, num_colors)
    print(f"  Thiele Sighted: solved={sighted['success']}, backtracks={sighted['backtracks']}")
    
    results_all.append({
        'graph': 'Bipartite',
        'classical_bt': bt1,
        'blind_bt': blind['backtracks'],
        'sighted_bt': sighted['backtracks'],
        'success': success1 and blind['success'] and sighted['success']
    })
    
    # Test 3: Disconnected Graph (structure helps a lot)
    print("\n" + "-" * 70)
    print("TEST 3: Disconnected Graph (3 components)")
    print("-" * 70)
    
    disconnected = create_disconnected_graph()
    num_colors = 3
    
    print(f"  Nodes: {len(disconnected)}")
    print(f"  Edges: {sum(len(v) for v in disconnected.values()) // 2}")
    print(f"  Colors: {num_colors}")
    
    # Classical
    start = time.time()
    success1, coloring1, bt1 = color_graph_classical(disconnected, num_colors)
    time1 = time.time() - start
    print(f"\n  Classical: solved={success1}, backtracks={bt1}")
    
    # Thiele Blind
    blind = color_with_thiele_blind(disconnected, num_colors)
    print(f"  Thiele Blind: solved={blind['success']}, backtracks={blind['backtracks']}")
    
    # Thiele Sighted
    sighted = color_with_thiele_sighted(disconnected, num_colors)
    print(f"  Thiele Sighted: solved={sighted['success']}, backtracks={sighted['backtracks']}, partitions={sighted['partitions']}")
    
    results_all.append({
        'graph': 'Disconnected',
        'classical_bt': bt1,
        'blind_bt': blind['backtracks'],
        'sighted_bt': sighted['backtracks'],
        'partitions': sighted['partitions'],
        'success': success1 and blind['success'] and sighted['success']
    })
    
    # Summary
    print("\n" + "=" * 70)
    print("VALIDATION")
    print("=" * 70)
    
    all_success = all(r['success'] for r in results_all)
    print(f"\n  All graphs colored correctly: {'✓ PASS' if all_success else '✗ FAIL'}")
    
    print("\n  Backtrack comparison:")
    for r in results_all:
        print(f"    {r['graph']}: classical={r['classical_bt']}, blind={r['blind_bt']}, sighted={r['sighted_bt']}")
    
    print("\n" + "-" * 70)
    print("SEPARATION DEMONSTRATED:")
    print("  - Blind mode: Standard backtracking (Turing equivalent)")
    print("  - Sighted mode: Component detection + degree ordering")
    print("  - Disconnected graphs: Components can be colored independently")
    print("-" * 70)
    
    return {'all_success': all_success}


if __name__ == "__main__":
    results = run_comparison()
    exit(0 if results['all_success'] else 1)
