#!/usr/bin/env python3
"""Graph Algorithms

Restored from the archived demo set.
"""

import time
from collections import deque
from typing import Any, Dict, List, Tuple


def bfs(graph: Dict[int, List[int]], start: int) -> Tuple[List[int], int]:
    visited: List[int] = []
    queue: deque[int] = deque([start])
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
    visited: List[int] = []
    stack: List[int] = [start]
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
    distances: Dict[int, int] = {start: 0}
    visited = set()
    ops = 0

    while len(visited) < len(graph):
        ops += 1
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
            ops += 1
            new_dist = distances[min_node] + weight
            if neighbor not in distances or new_dist < distances[neighbor]:
                distances[neighbor] = int(new_dist)

    return distances, ops


def topological_sort(graph: Dict[int, List[int]], nodes: List[int]) -> Tuple[List[int], int]:
    in_degree: Dict[int, int] = {node: 0 for node in nodes}
    ops = 0

    for node in graph:
        for neighbor in graph.get(node, []):
            ops += 1
            in_degree[neighbor] = in_degree.get(neighbor, 0) + 1

    queue: deque[int] = deque([node for node, degree in in_degree.items() if degree == 0])
    result: List[int] = []

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


GRAPH_LINEAR = {0: [1], 1: [2], 2: [3], 3: [4], 4: []}
GRAPH_TREE = {0: [1, 2], 1: [3, 4], 2: [5, 6], 3: [], 4: [], 5: [], 6: []}
GRAPH_CYCLE = {0: [1], 1: [2], 2: [3], 3: [0]}
GRAPH_DAG = {0: [1, 2], 1: [3], 2: [3], 3: [4], 4: []}
GRAPH_WEIGHTED = {
    0: [(1, 4), (2, 1)],
    1: [(3, 1)],
    2: [(1, 2), (3, 5)],
    3: [(4, 3)],
    4: [],
}


def run_standard_python() -> Dict[str, Any]:
    results: Dict[str, Any] = {"runtime": "Standard Python", "tests": []}

    test_cases = [
        ("BFS linear", lambda: bfs(GRAPH_LINEAR, 0)),
        ("BFS tree", lambda: bfs(GRAPH_TREE, 0)),
        ("BFS cycle", lambda: bfs(GRAPH_CYCLE, 0)),
        ("DFS linear", lambda: dfs(GRAPH_LINEAR, 0)),
        ("DFS tree", lambda: dfs(GRAPH_TREE, 0)),
        ("DFS cycle", lambda: dfs(GRAPH_CYCLE, 0)),
        ("Dijkstra weighted", lambda: dijkstra(GRAPH_WEIGHTED, 0)),
        ("Topo sort DAG", lambda: topological_sort(GRAPH_DAG, [0, 1, 2, 3, 4])),
        ("Topo sort linear", lambda: topological_sort(GRAPH_LINEAR, [0, 1, 2, 3, 4])),
        ("Cycle detect (has cycle)", lambda: has_cycle(GRAPH_CYCLE, [0, 1, 2, 3])),
        ("Cycle detect (no cycle)", lambda: has_cycle(GRAPH_DAG, [0, 1, 2, 3, 4])),
        (
            "Components connected",
            lambda: connected_components({0: [1], 1: [0, 2], 2: [1]}, [0, 1, 2]),
        ),
        (
            "Components disconnected",
            lambda: connected_components({0: [1], 1: [0], 2: [3], 3: [2], 4: []}, [0, 1, 2, 3, 4]),
        ),
    ]

    for name, fn in test_cases:
        start = time.time()
        result, ops = fn()
        elapsed = time.time() - start
        results["tests"].append({"name": name, "result": result, "operations": ops, "time": elapsed})

    return results


def run_thiele_vm() -> Dict[str, Any]:
    from thielecpu.mu import question_cost_bits
    from thielecpu.state import State
    from thielecpu.vm import VM

    results: Dict[str, Any] = {"runtime": "Thiele VM", "tests": []}

    test_cases = [
        (
            "BFS linear",
            """
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
""",
        ),
        (
            "BFS tree",
            """
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
""",
        ),
        (
            "BFS cycle",
            """
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
""",
        ),
        (
            "DFS linear",
            """
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
""",
        ),
        (
            "DFS tree",
            """
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
""",
        ),
        (
            "DFS cycle",
            """
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
""",
        ),
        (
            "Dijkstra weighted",
            """
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
""",
        ),
        (
            "Topo sort DAG",
            """
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
""",
        ),
        (
            "Topo sort linear",
            """
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
""",
        ),
        (
            "Cycle detect (has cycle)",
            """
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
""",
        ),
        (
            "Cycle detect (no cycle)",
            """
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
""",
        ),
        (
            "Components connected",
            """
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
""",
        ),
        (
            "Components disconnected",
            """
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
""",
        ),
    ]

    for name, code in test_cases:
        vm = VM(State())
        start = time.time()
        res, _ = vm.execute_python(code)
        elapsed = time.time() - start
        value, ops = res if res else (None, 0)
        mu_cost = question_cost_bits(f"(graph {name})") + ops * 0.1
        results["tests"].append(
            {"name": name, "result": value, "operations": ops, "time": elapsed, "mu_cost": mu_cost}
        )

    return results


def compare_and_report() -> Dict[str, Any]:
    std_results = run_standard_python()
    vm_results = run_thiele_vm()

    all_match = True
    comparisons = []

    for std_test, vm_test in zip(std_results["tests"], vm_results["tests"]):
        match = std_test["result"] == vm_test["result"] and std_test["operations"] == vm_test["operations"]
        all_match = all_match and match
        comparisons.append(
            {
                "name": std_test["name"],
                "std_result": std_test["result"],
                "vm_result": vm_test["result"],
                "std_ops": std_test["operations"],
                "vm_ops": vm_test["operations"],
                "match": match,
                "mu_cost": vm_test.get("mu_cost", 0),
            }
        )

    return {"category": "Graph Algorithms", "all_match": all_match, "comparisons": comparisons}


if __name__ == "__main__":
    compare_and_report()
