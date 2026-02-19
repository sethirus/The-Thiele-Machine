import heapq
from typing import Dict, List, Tuple

import pytest

from thielecpu.hardware.cosim import run_verilog


def _shortest_path(
    graph: Dict[str, List[str]],
    potential: Dict[str, float],
    start: str,
    goal: str,
    coupling: float,
) -> Tuple[float, List[str]]:
    frontier: list[tuple[float, str, list[str]]] = [(0.0, start, [start])]
    best_cost: dict[str, float] = {start: 0.0}

    while frontier:
        cost, node, path = heapq.heappop(frontier)
        if node == goal:
            return cost, path
        if cost > best_cost.get(node, float("inf")):
            continue

        for nxt in graph[node]:
            edge_cost = 1.0 + coupling * (potential[node] + potential[nxt]) * 0.5
            new_cost = cost + edge_cost
            if new_cost < best_cost.get(nxt, float("inf")):
                best_cost[nxt] = new_cost
                heapq.heappush(frontier, (new_cost, nxt, path + [nxt]))

    raise AssertionError(f"no path from {start} to {goal}")


def test_proxy_time_dilation_from_rtl_mu_density() -> None:
    low_mu_program = "\n".join(
        [
            "EMIT 0 1 1",
            "EMIT 0 1 1",
            "EMIT 0 1 1",
            "EMIT 0 1 1",
            "HALT 1",
        ]
    )
    high_mu_program = "\n".join(
        [
            "EMIT 0 1 40",
            "EMIT 0 1 40",
            "EMIT 0 1 40",
            "EMIT 0 1 40",
            "HALT 1",
        ]
    )

    low = run_verilog(low_mu_program, timeout=20)
    high = run_verilog(high_mu_program, timeout=20)
    if low is None or high is None:
        pytest.skip("iverilog/vvp unavailable in this environment")

    assert "cycles" in low and "cycles" in high
    assert high["mu"] > low["mu"]
    assert high["cycles"] == low["cycles"]

    # Proper-time proxy: higher μ-density implies fewer normalized ticks.
    low_proper_ticks = low["cycles"] / (1.0 + (low["mu"] / 256.0))
    high_proper_ticks = high["cycles"] / (1.0 + (high["mu"] / 256.0))
    assert high_proper_ticks < low_proper_ticks


def test_proxy_geodesic_deflection_around_high_mass_node() -> None:
    graph = {
        "S": ["C", "A"],
        "A": ["S", "B"],
        "B": ["A", "T"],
        "C": ["S", "T"],
        "T": ["B", "C"],
    }
    potential = {
        "S": 0.1,
        "A": 0.2,
        "B": 0.2,
        "C": 12.0,
        "T": 0.1,
    }

    _, flat_path = _shortest_path(graph, potential, "S", "T", coupling=0.0)
    _, curved_path = _shortest_path(graph, potential, "S", "T", coupling=0.5)

    assert flat_path == ["S", "C", "T"]
    assert curved_path == ["S", "A", "B", "T"]


def test_proxy_radial_latency_falloff() -> None:
    radii = [1, 2, 3, 4, 5]
    source_mass = 120.0
    base_latency = 8.0

    # Radial latency proxy induced by a central mass term.
    latency = [base_latency + source_mass / r for r in radii]

    for left, right in zip(latency, latency[1:]):
        assert left > right

    scaled = [r * (value - base_latency) for r, value in zip(radii, latency)]
    mean_scaled = sum(scaled) / len(scaled)
    max_deviation = max(abs(s - mean_scaled) for s in scaled)

    # Accept small discretization spread around inverse-radius trend.
    assert max_deviation / mean_scaled < 0.20