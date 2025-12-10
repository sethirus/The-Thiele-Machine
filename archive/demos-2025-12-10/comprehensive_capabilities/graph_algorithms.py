#!/usr/bin/env python3
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Graph Algorithms

Tests fundamental graph algorithms:
- BFS (Breadth-First Search)
- DFS (Depth-First Search)
- Dijkstra's shortest path
- Topological sort
- Cycle detection
- Connected components
"""

import time
from typing import Dict, Any, List, Tuple, Set, Optional
from collections import deque


# =============================================================================
# GRAPH ALGORITHMS (identical in both environments)
# =============================================================================

def bfs(graph: Dict[int, List[int]], start: int) -> Tuple[List[int], int]:
    """Breadth-first search returning visited order and operation count."""
    visited = []
    queue = deque([start])
    seen = {start}
    ops = 0
    
    while queue:
        ops += 1
        node = queue.popleft()
        visited.append(node)
        
        for neighbor in graph.get(node, []):
            ops += 1
            if neighbor not in seen:
                seen.add(neighbor)
                queue.append(neighbor)
    
    return visited, ops


def dfs(graph: Dict[int, List[int]], start: int) -> Tuple[List[int], int]:
    """Depth-first search (iterative) returning visited order and operation count."""
    visited = []
    stack = [start]
    seen = {start}
    ops = 0
    
    while stack:
        ops += 1
        node = stack.pop()
        visited.append(node)
        
        for neighbor in reversed(graph.get(node, [])):
            ops += 1
            if neighbor not in seen:
                seen.add(neighbor)
                stack.append(neighbor)
    
    return visited, ops


def dijkstra(graph: Dict[int, List[Tuple[int, int]]], start: int) -> Tuple[Dict[int, int], int]:
    """Dijkstra's shortest path algorithm."""
    distances = {start: 0}
    visited = set()
    ops = 0
    
    # Simple implementation without heap for VM compatibility
    while len(visited) < len(graph):
        ops += 1
        # Find minimum unvisited node
        min_dist = float('inf')
        min_node = None
        for node, dist in distances.items():
            if node not in visited and dist < min_dist:
                min_dist = dist
                min_node = node
        
        if min_node is None:
            break
        
        visited.add(min_node)
        
        for neighbor, weight in graph.get(min_node, []):
            ops += 1
            new_dist = distances[min_node] + weight
            if neighbor not in distances or new_dist < distances[neighbor]:
                distances[neighbor] = new_dist
    
    return distances, ops


def topological_sort(graph: Dict[int, List[int]], nodes: List[int]) -> Tuple[List[int], int]:
    """Kahn's algorithm for topological sorting."""
    in_degree = {node: 0 for node in nodes}
    ops = 0
    
    for node in graph:
        for neighbor in graph.get(node, []):
            ops += 1
            in_degree[neighbor] = in_degree.get(neighbor, 0) + 1
    
    queue = deque([node for node, degree in in_degree.items() if degree == 0])
    result = []
    
    while queue:
        ops += 1
        node = queue.popleft()
        result.append(node)
        
        for neighbor in graph.get(node, []):
            ops += 1
            in_degree[neighbor] -= 1
            if in_degree[neighbor] == 0:
                queue.append(neighbor)
    
    return result, ops


def has_cycle(graph: Dict[int, List[int]], nodes: List[int]) -> Tuple[bool, int]:
    """Detect cycle in directed graph using DFS."""
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {node: WHITE for node in nodes}
    ops = 0
    
    def dfs_visit(node):
        nonlocal ops
        ops += 1
        color[node] = GRAY
        
        for neighbor in graph.get(node, []):
            ops += 1
            if color[neighbor] == GRAY:
                return True
            if color[neighbor] == WHITE and dfs_visit(neighbor):
                return True
        
        color[node] = BLACK
        return False
    
    for node in nodes:
        if color[node] == WHITE:
            if dfs_visit(node):
                return True, ops
    
    return False, ops


def connected_components(graph: Dict[int, List[int]], nodes: List[int]) -> Tuple[int, int]:
    """Count connected components in undirected graph."""
    visited = set()
    components = 0
    ops = 0
    
    def explore(node):
        nonlocal ops
        ops += 1
        visited.add(node)
        for neighbor in graph.get(node, []):
            ops += 1
            if neighbor not in visited:
                explore(neighbor)
    
    for node in nodes:
        if node not in visited:
            components += 1
            explore(node)
    
    return components, ops


# =============================================================================
# TEST CASES
# =============================================================================

# Test graphs
GRAPH_LINEAR = {0: [1], 1: [2], 2: [3], 3: [4], 4: []}
GRAPH_TREE = {0: [1, 2], 1: [3, 4], 2: [5, 6], 3: [], 4: [], 5: [], 6: []}
GRAPH_CYCLE = {0: [1], 1: [2], 2: [3], 3: [0]}
GRAPH_DAG = {0: [1, 2], 1: [3], 2: [3], 3: [4], 4: []}
GRAPH_DISCONNECTED = {0: [1], 1: [], 2: [3], 3: [], 4: []}
GRAPH_WEIGHTED = {
    0: [(1, 4), (2, 1)],
    1: [(3, 1)],
    2: [(1, 2), (3, 5)],
    3: [(4, 3)],
    4: []
}


def run_standard_python() -> Dict[str, Any]:
    """Run all graph tests with standard Python."""
    results = {'runtime': 'Standard Python', 'tests': []}
    
    test_cases = [
        # BFS
        ("BFS linear", lambda: bfs(GRAPH_LINEAR, 0)),
        ("BFS tree", lambda: bfs(GRAPH_TREE, 0)),
        ("BFS cycle", lambda: bfs(GRAPH_CYCLE, 0)),
        
        # DFS
        ("DFS linear", lambda: dfs(GRAPH_LINEAR, 0)),
        ("DFS tree", lambda: dfs(GRAPH_TREE, 0)),
        ("DFS cycle", lambda: dfs(GRAPH_CYCLE, 0)),
        
        # Dijkstra
        ("Dijkstra weighted", lambda: dijkstra(GRAPH_WEIGHTED, 0)),
        
        # Topological sort
        ("Topo sort DAG", lambda: topological_sort(GRAPH_DAG, [0, 1, 2, 3, 4])),
        ("Topo sort linear", lambda: topological_sort(GRAPH_LINEAR, [0, 1, 2, 3, 4])),
        
        # Cycle detection
        ("Cycle detect (has cycle)", lambda: has_cycle(GRAPH_CYCLE, [0, 1, 2, 3])),
        ("Cycle detect (no cycle)", lambda: has_cycle(GRAPH_DAG, [0, 1, 2, 3, 4])),
        
        # Connected components
        ("Components connected", lambda: connected_components(
            {0: [1], 1: [0, 2], 2: [1]}, [0, 1, 2])),
        ("Components disconnected", lambda: connected_components(
            {0: [1], 1: [0], 2: [3], 3: [2], 4: []}, [0, 1, 2, 3, 4])),
    ]
    
    for name, test_fn in test_cases:
        start = time.time()
        result, ops = test_fn()
        elapsed = time.time() - start
        
        results['tests'].append({
            'name': name,
            'result': result,
            'operations': ops,
            'time': elapsed,
        })
    
    return results


def run_thiele_vm() -> Dict[str, Any]:
    """Run all graph tests through Thiele VM."""
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits
    
    results = {'runtime': 'Thiele VM', 'tests': []}
    
    test_cases = [
        # BFS
        ("BFS linear", '''
graph = {0: [1], 1: [2], 2: [3], 3: [4], 4: []}
start = 0
visited = []
queue = [start]
seen = {start}
ops = 0
while queue:
    ops = ops + 1
    node = queue.pop(0)
    visited.append(node)
    for neighbor in graph.get(node, []):
        ops = ops + 1
        if neighbor not in seen:
            seen.add(neighbor)
            queue.append(neighbor)
__result__ = (visited, ops)
'''),
        ("BFS tree", '''
graph = {0: [1, 2], 1: [3, 4], 2: [5, 6], 3: [], 4: [], 5: [], 6: []}
start = 0
visited = []
queue = [start]
seen = {start}
ops = 0
while queue:
    ops = ops + 1
    node = queue.pop(0)
    visited.append(node)
    for neighbor in graph.get(node, []):
        ops = ops + 1
        if neighbor not in seen:
            seen.add(neighbor)
            queue.append(neighbor)
__result__ = (visited, ops)
'''),
        ("BFS cycle", '''
graph = {0: [1], 1: [2], 2: [3], 3: [0]}
start = 0
visited = []
queue = [start]
seen = {start}
ops = 0
while queue:
    ops = ops + 1
    node = queue.pop(0)
    visited.append(node)
    for neighbor in graph.get(node, []):
        ops = ops + 1
        if neighbor not in seen:
            seen.add(neighbor)
            queue.append(neighbor)
__result__ = (visited, ops)
'''),
        # DFS
        ("DFS linear", '''
graph = {0: [1], 1: [2], 2: [3], 3: [4], 4: []}
start = 0
visited = []
stack = [start]
seen = {start}
ops = 0
while stack:
    ops = ops + 1
    node = stack.pop()
    visited.append(node)
    for neighbor in reversed(graph.get(node, [])):
        ops = ops + 1
        if neighbor not in seen:
            seen.add(neighbor)
            stack.append(neighbor)
__result__ = (visited, ops)
'''),
        ("DFS tree", '''
graph = {0: [1, 2], 1: [3, 4], 2: [5, 6], 3: [], 4: [], 5: [], 6: []}
start = 0
visited = []
stack = [start]
seen = {start}
ops = 0
while stack:
    ops = ops + 1
    node = stack.pop()
    visited.append(node)
    for neighbor in reversed(graph.get(node, [])):
        ops = ops + 1
        if neighbor not in seen:
            seen.add(neighbor)
            stack.append(neighbor)
__result__ = (visited, ops)
'''),
        ("DFS cycle", '''
graph = {0: [1], 1: [2], 2: [3], 3: [0]}
start = 0
visited = []
stack = [start]
seen = {start}
ops = 0
while stack:
    ops = ops + 1
    node = stack.pop()
    visited.append(node)
    for neighbor in reversed(graph.get(node, [])):
        ops = ops + 1
        if neighbor not in seen:
            seen.add(neighbor)
            stack.append(neighbor)
__result__ = (visited, ops)
'''),
        # Dijkstra
        ("Dijkstra weighted", '''
graph = {0: [(1, 4), (2, 1)], 1: [(3, 1)], 2: [(1, 2), (3, 5)], 3: [(4, 3)], 4: []}
start = 0
distances = {start: 0}
visited = set()
ops = 0
while len(visited) < len(graph):
    ops = ops + 1
    min_dist = float("inf")
    min_node = None
    for node, dist in distances.items():
        if node not in visited and dist < min_dist:
            min_dist = dist
            min_node = node
    if min_node is None:
        break
    visited.add(min_node)
    for neighbor, weight in graph.get(min_node, []):
        ops = ops + 1
        new_dist = distances[min_node] + weight
        if neighbor not in distances or new_dist < distances[neighbor]:
            distances[neighbor] = new_dist
__result__ = (distances, ops)
'''),
        # Topological sort
        ("Topo sort DAG", '''
graph = {0: [1, 2], 1: [3], 2: [3], 3: [4], 4: []}
nodes = [0, 1, 2, 3, 4]
in_degree = {node: 0 for node in nodes}
ops = 0
for node in graph:
    for neighbor in graph.get(node, []):
        ops = ops + 1
        in_degree[neighbor] = in_degree.get(neighbor, 0) + 1
queue = [node for node, degree in in_degree.items() if degree == 0]
result = []
while queue:
    ops = ops + 1
    node = queue.pop(0)
    result.append(node)
    for neighbor in graph.get(node, []):
        ops = ops + 1
        in_degree[neighbor] = in_degree[neighbor] - 1
        if in_degree[neighbor] == 0:
            queue.append(neighbor)
__result__ = (result, ops)
'''),
        ("Topo sort linear", '''
graph = {0: [1], 1: [2], 2: [3], 3: [4], 4: []}
nodes = [0, 1, 2, 3, 4]
in_degree = {node: 0 for node in nodes}
ops = 0
for node in graph:
    for neighbor in graph.get(node, []):
        ops = ops + 1
        in_degree[neighbor] = in_degree.get(neighbor, 0) + 1
queue = [node for node, degree in in_degree.items() if degree == 0]
result = []
while queue:
    ops = ops + 1
    node = queue.pop(0)
    result.append(node)
    for neighbor in graph.get(node, []):
        ops = ops + 1
        in_degree[neighbor] = in_degree[neighbor] - 1
        if in_degree[neighbor] == 0:
            queue.append(neighbor)
__result__ = (result, ops)
'''),
        # Cycle detection
        ("Cycle detect (has cycle)", '''
graph = {0: [1], 1: [2], 2: [3], 3: [0]}
nodes = [0, 1, 2, 3]
WHITE, GRAY, BLACK = 0, 1, 2
color = {node: WHITE for node in nodes}
ops = [0]
has_cycle = [False]
def dfs_visit(node):
    ops[0] = ops[0] + 1
    color[node] = GRAY
    for neighbor in graph.get(node, []):
        ops[0] = ops[0] + 1
        if color[neighbor] == GRAY:
            has_cycle[0] = True
            return True
        if color[neighbor] == WHITE and dfs_visit(neighbor):
            return True
    color[node] = BLACK
    return False
for node in nodes:
    if color[node] == WHITE:
        if dfs_visit(node):
            break
__result__ = (has_cycle[0], ops[0])
'''),
        ("Cycle detect (no cycle)", '''
graph = {0: [1, 2], 1: [3], 2: [3], 3: [4], 4: []}
nodes = [0, 1, 2, 3, 4]
WHITE, GRAY, BLACK = 0, 1, 2
color = {node: WHITE for node in nodes}
ops = [0]
has_cycle = [False]
def dfs_visit(node):
    ops[0] = ops[0] + 1
    color[node] = GRAY
    for neighbor in graph.get(node, []):
        ops[0] = ops[0] + 1
        if color[neighbor] == GRAY:
            has_cycle[0] = True
            return True
        if color[neighbor] == WHITE and dfs_visit(neighbor):
            return True
    color[node] = BLACK
    return False
for node in nodes:
    if color[node] == WHITE:
        if dfs_visit(node):
            break
__result__ = (has_cycle[0], ops[0])
'''),
        # Connected components
        ("Components connected", '''
graph = {0: [1], 1: [0, 2], 2: [1]}
nodes = [0, 1, 2]
visited = set()
components = 0
ops = [0]
def explore(node):
    ops[0] = ops[0] + 1
    visited.add(node)
    for neighbor in graph.get(node, []):
        ops[0] = ops[0] + 1
        if neighbor not in visited:
            explore(neighbor)
for node in nodes:
    if node not in visited:
        components = components + 1
        explore(node)
__result__ = (components, ops[0])
'''),
        ("Components disconnected", '''
graph = {0: [1], 1: [0], 2: [3], 3: [2], 4: []}
nodes = [0, 1, 2, 3, 4]
visited = set()
components = 0
ops = [0]
def explore(node):
    ops[0] = ops[0] + 1
    visited.add(node)
    for neighbor in graph.get(node, []):
        ops[0] = ops[0] + 1
        if neighbor not in visited:
            explore(neighbor)
for node in nodes:
    if node not in visited:
        components = components + 1
        explore(node)
__result__ = (components, ops[0])
'''),
    ]
    
    for name, code in test_cases:
        vm = VM(State())
        start = time.time()
        res, _ = vm.execute_python(code)
        elapsed = time.time() - start
        
        result, ops = res if res else (None, 0)
        mu_cost = question_cost_bits(f"(graph {name})") + ops * 0.1
        
        results['tests'].append({
            'name': name,
            'result': result,
            'operations': ops,
            'time': elapsed,
            'mu_cost': mu_cost,
        })
    
    return results


def compare_and_report() -> Dict[str, Any]:
    """Run both and compare results."""
    print("=" * 70)
    print("GRAPH ALGORITHMS")
    print("=" * 70)
    
    std_results = run_standard_python()
    vm_results = run_thiele_vm()
    
    all_match = True
    comparison_results = []
    
    print(f"\n{'Test Name':<30} {'Std Ops':<10} {'VM Ops':<10} {'Match':<6}")
    print("-" * 70)
    
    for std_test, vm_test in zip(std_results['tests'], vm_results['tests']):
        # For graph results, compare structure
        std_res = std_test['result']
        vm_res = vm_test['result']
        
        # Handle dict comparison
        if isinstance(std_res, dict) and isinstance(vm_res, dict):
            result_match = std_res == vm_res
        else:
            result_match = std_res == vm_res
        
        ops_match = std_test['operations'] == vm_test['operations']
        match = result_match and ops_match
        if not match:
            all_match = False
        
        status = "✓" if match else "✗"
        
        print(f"{std_test['name']:<30} {std_test['operations']:<10} {vm_test['operations']:<10} {status:<6}")
        
        comparison_results.append({
            'name': std_test['name'],
            'std_result': std_test['result'],
            'vm_result': vm_test['result'],
            'std_ops': std_test['operations'],
            'vm_ops': vm_test['operations'],
            'match': match,
            'mu_cost': vm_test.get('mu_cost', 0),
        })
    
    print("\n" + "-" * 70)
    print(f"ISOMORPHISM: {'✓ ALL TESTS PASS' if all_match else '✗ SOME TESTS FAILED'}")
    print(f"Total tests: {len(comparison_results)}")
    print(f"Matching: {sum(1 for r in comparison_results if r['match'])}")
    
    return {
        'category': 'Graph Algorithms',
        'all_match': all_match,
        'comparisons': comparison_results,
    }


if __name__ == "__main__":
    compare_and_report()
