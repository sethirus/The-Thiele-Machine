"""Standard Program: Graph Coloring

A typical backtracking graph coloring program, with Thiele VM wrappers.
"""

from __future__ import annotations

import time
from typing import Any, Dict, Set, Tuple


def color_graph_classical(adjacency: Dict[int, Set[int]], num_colors: int) -> Tuple[bool, Dict[int, int], int]:
    nodes = sorted(adjacency.keys())
    coloring: Dict[int, int] = {}
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


def color_graph_with_ordering(adjacency: Dict[int, Set[int]], num_colors: int) -> Tuple[bool, Dict[int, int], int]:
    nodes = sorted(adjacency.keys(), key=lambda n: len(adjacency.get(n, set())), reverse=True)
    coloring: Dict[int, int] = {}
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


def color_with_thiele_blind(adjacency: Dict[int, Set[int]], num_colors: int) -> Dict[str, Any]:
    from thielecpu.mu import question_cost_bits
    from thielecpu.state import State
    from thielecpu.vm import VM

    vm = VM(State())
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
    result, _ = vm.execute_python(code)
    elapsed = time.time() - start

    return {
        "mode": "BLIND",
        "success": result[0] if result else False,
        "coloring": result[1] if result else {},
        "backtracks": result[2] if result else 0,
        "time": elapsed,
        "mu_cost": question_cost_bits("(color-graph blind)"),
        "partitions": 1,
    }


def color_with_thiele_sighted(adjacency: Dict[int, Set[int]], num_colors: int) -> Dict[str, Any]:
    from thielecpu.mu import question_cost_bits
    from thielecpu.state import State
    from thielecpu.vm import VM

    vm = VM(State())
    state = vm.state

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
            state.pnew(comp)

    adj_str = str({k: list(v) for k, v in adjacency.items()})

    code = f'''
adjacency = {adj_str}
adjacency = {{k: set(v) for k, v in adjacency.items()}}
num_colors = {num_colors}
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
    result, _ = vm.execute_python(code)
    elapsed = time.time() - start

    return {
        "mode": "SIGHTED",
        "success": result[0] if result else False,
        "coloring": result[1] if result else {},
        "backtracks": result[2] if result else 0,
        "time": elapsed,
        "mu_cost": question_cost_bits("(color-graph sighted)"),
        "partitions": len(components),
        "components": len(components),
    }


def create_petersen_graph() -> Dict[int, Set[int]]:
    """Create the Petersen graph (10 nodes, 15 edges)."""
    adj: Dict[int, Set[int]] = {i: set() for i in range(10)}

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
    adj: Dict[int, Set[int]] = {i: set() for i in range(2 * n)}
    for i in range(n):
        for j in range(n, 2 * n):
            adj[i].add(j)
            adj[j].add(i)
    return adj


def create_disconnected_graph() -> Dict[int, Set[int]]:
    """Create a graph with multiple disconnected components."""
    adj: Dict[int, Set[int]] = {}

    # Component 1: Triangle (0-2)
    for i in range(3):
        adj[i] = set()
    adj[0].add(1)
    adj[1].add(0)
    adj[1].add(2)
    adj[2].add(1)
    adj[2].add(0)
    adj[0].add(2)

    # Component 2: Square (3-6)
    for i in range(3, 7):
        adj[i] = set()
    adj[3].add(4)
    adj[4].add(3)
    adj[4].add(5)
    adj[5].add(4)
    adj[5].add(6)
    adj[6].add(5)
    adj[6].add(3)
    adj[3].add(6)

    # Component 3: Single edge (7-8)
    adj[7] = {8}
    adj[8] = {7}

    return adj
