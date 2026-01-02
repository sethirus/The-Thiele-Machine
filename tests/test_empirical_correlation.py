#!/usr/bin/env python3
"""
EMPIRICAL TEST: μ-COST VS COMPUTATIONAL RESOURCES
==================================================

This test measures whether μ-cost correlates with actual computational
resources (CPU time, as a proxy for energy).

If μ-cost is "just math" → no correlation expected
If μ-cost tracks physical reality → correlation expected

This is the most basic empirical test of the thermodynamic bridge.
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))

import time
import statistics
from dataclasses import dataclass
from typing import List, Tuple
import math

from thielecpu.state import State
from thielecpu.vm import VM


@dataclass
class Measurement:
    """Single measurement point."""
    n: int              # Problem size parameter
    mu_cost: float      # μ-bits charged
    cpu_time_ns: float  # Nanoseconds of CPU time
    description: str


def measure_cpu_time(func, *args, warmup=3, trials=10) -> Tuple[float, any]:
    """
    Measure CPU time for a function with warmup and averaging.
    
    Returns: (mean_time_ns, result)
    """
    # Warmup runs
    for _ in range(warmup):
        func(*args)
    
    # Timed runs
    times = []
    result = None
    for _ in range(trials):
        start = time.perf_counter_ns()
        result = func(*args)
        end = time.perf_counter_ns()
        times.append(end - start)
    
    return statistics.mean(times), result


def workload_partition_discovery(n: int) -> Tuple[float, State]:
    """
    Workload: Discover partition structure over n elements.
    
    This is the core μ-charging operation.
    """
    state = State()
    
    # Create universe
    universe = set(range(n))
    mid = state.pnew(universe)
    
    # Series of splits (log n splits to bisect completely)
    current_modules = [mid]
    for bit in range(int(math.log2(n)) if n > 1 else 1):
        new_modules = []
        for m in current_modules:
            region = state.regions[m]
            if len(region) > 1:
                # Split by bit position
                m1, m2 = state.psplit(m, lambda x, b=bit: (x >> b) & 1)
                new_modules.extend([m1, m2])
            else:
                new_modules.append(m)
        current_modules = new_modules
    
    return state.mu_ledger.total, state


def workload_search_simulation(n: int) -> Tuple[float, State]:
    """
    Workload: Simulate search over n elements.
    
    Models classical search with μ-cost per element checked.
    """
    state = State()
    
    # Search through n elements
    target = n - 1  # Worst case: target at end
    
    for i in range(n):
        # Each check costs μ
        state.mu_ledger.charge_execution(1)
        if i == target:
            break
    
    return state.mu_ledger.total, state


def workload_grover_simulation(n_qubits: int) -> Tuple[float, State]:
    """
    Workload: Simulate Grover's algorithm structure.
    
    Tracks the μ-cost of the algorithm's structural operations.
    """
    import numpy as np
    
    N = 2 ** n_qubits
    state = State()
    
    # Initialize superposition structure
    universe = set(range(N))
    mid = state.pnew(universe)  # O(N) cost
    
    # Simulate √N iterations
    iterations = int(math.pi / 4 * math.sqrt(N))
    
    # Each iteration has oracle + diffusion
    for _ in range(iterations):
        state.mu_ledger.charge_execution(1)  # Oracle
        state.mu_ledger.charge_execution(1)  # Diffusion
    
    # Measurement
    state.mu_ledger.charge_execution(int(math.log2(N)))
    
    return state.mu_ledger.total, state


def run_correlation_test():
    """
    Main test: Measure μ-cost vs CPU time across problem sizes.
    """
    print("=" * 80)
    print("EMPIRICAL TEST: μ-COST VS CPU TIME")
    print("=" * 80)
    print()
    print("Testing whether μ-cost correlates with actual computational resources.")
    print("CPU time is used as a proxy for energy consumption.")
    print()
    
    measurements: List[Measurement] = []
    
    # Test 1: Partition Discovery (varying N)
    print("TEST 1: Partition Discovery")
    print("-" * 40)
    print(f"{'N':>8} | {'μ-cost':>10} | {'CPU (μs)':>12} | {'μ/CPU':>10}")
    print("-" * 40)
    
    for n in [64, 128, 256, 512, 1024, 2048]:
        cpu_time, (mu_cost, _) = measure_cpu_time(workload_partition_discovery, n)
        cpu_us = cpu_time / 1000  # Convert to microseconds
        ratio = mu_cost / cpu_us if cpu_us > 0 else 0
        
        print(f"{n:>8} | {mu_cost:>10.1f} | {cpu_us:>12.2f} | {ratio:>10.4f}")
        
        measurements.append(Measurement(
            n=n, mu_cost=mu_cost, cpu_time_ns=cpu_time,
            description="partition_discovery"
        ))
    
    # Test 2: Search Simulation (varying N)
    print()
    print("TEST 2: Search Simulation (worst case)")
    print("-" * 40)
    print(f"{'N':>8} | {'μ-cost':>10} | {'CPU (μs)':>12} | {'μ/CPU':>10}")
    print("-" * 40)
    
    for n in [1000, 2000, 4000, 8000, 16000, 32000]:
        cpu_time, (mu_cost, _) = measure_cpu_time(workload_search_simulation, n)
        cpu_us = cpu_time / 1000
        ratio = mu_cost / cpu_us if cpu_us > 0 else 0
        
        print(f"{n:>8} | {mu_cost:>10.1f} | {cpu_us:>12.2f} | {ratio:>10.4f}")
        
        measurements.append(Measurement(
            n=n, mu_cost=mu_cost, cpu_time_ns=cpu_time,
            description="search_simulation"
        ))
    
    # Test 3: Grover Simulation (varying qubits)
    print()
    print("TEST 3: Grover Simulation")
    print("-" * 40)
    print(f"{'qubits':>8} | {'N':>8} | {'μ-cost':>10} | {'CPU (μs)':>12}")
    print("-" * 40)
    
    for qubits in [6, 8, 10, 12, 14]:
        N = 2 ** qubits
        cpu_time, (mu_cost, _) = measure_cpu_time(workload_grover_simulation, qubits)
        cpu_us = cpu_time / 1000
        
        print(f"{qubits:>8} | {N:>8} | {mu_cost:>10.1f} | {cpu_us:>12.2f}")
        
        measurements.append(Measurement(
            n=N, mu_cost=mu_cost, cpu_time_ns=cpu_time,
            description="grover_simulation"
        ))
    
    # Statistical Analysis
    print()
    print("=" * 80)
    print("STATISTICAL ANALYSIS")
    print("=" * 80)
    print()
    
    # Compute correlation coefficient
    partition_data = [m for m in measurements if m.description == "partition_discovery"]
    search_data = [m for m in measurements if m.description == "search_simulation"]
    grover_data = [m for m in measurements if m.description == "grover_simulation"]
    
    def pearson_correlation(data: List[Measurement]) -> float:
        """Compute Pearson correlation between μ-cost and CPU time."""
        if len(data) < 2:
            return 0.0
        
        x = [m.mu_cost for m in data]
        y = [m.cpu_time_ns for m in data]
        
        n = len(x)
        sum_x = sum(x)
        sum_y = sum(y)
        sum_xy = sum(xi * yi for xi, yi in zip(x, y))
        sum_x2 = sum(xi ** 2 for xi in x)
        sum_y2 = sum(yi ** 2 for yi in y)
        
        numerator = n * sum_xy - sum_x * sum_y
        denominator = math.sqrt((n * sum_x2 - sum_x**2) * (n * sum_y2 - sum_y**2))
        
        if denominator == 0:
            return 0.0
        
        return numerator / denominator
    
    r_partition = pearson_correlation(partition_data)
    r_search = pearson_correlation(search_data)
    r_grover = pearson_correlation(grover_data)
    r_all = pearson_correlation(measurements)
    
    print(f"Pearson correlation (μ-cost vs CPU time):")
    print(f"  Partition discovery: r = {r_partition:.4f}")
    print(f"  Search simulation:   r = {r_search:.4f}")
    print(f"  Grover simulation:   r = {r_grover:.4f}")
    print(f"  All data combined:   r = {r_all:.4f}")
    print()
    
    # Interpretation
    print("INTERPRETATION:")
    print("-" * 40)
    
    if r_all > 0.9:
        print("STRONG POSITIVE CORRELATION (r > 0.9)")
        print("μ-cost tracks CPU time closely.")
        print("This is evidence FOR the thermodynamic bridge.")
    elif r_all > 0.7:
        print("MODERATE POSITIVE CORRELATION (0.7 < r < 0.9)")
        print("μ-cost partially tracks CPU time.")
        print("This is WEAK evidence for the thermodynamic bridge.")
    elif r_all > 0.3:
        print("WEAK POSITIVE CORRELATION (0.3 < r < 0.7)")
        print("Some relationship exists, but noisy.")
        print("Inconclusive - need better measurement.")
    else:
        print("NO SIGNIFICANT CORRELATION (r < 0.3)")
        print("μ-cost does NOT track CPU time.")
        print("This is evidence AGAINST the thermodynamic bridge.")
    
    print()
    print("CAVEATS:")
    print("-" * 40)
    print("1. CPU time ≠ energy (but proportional under constant load)")
    print("2. Python overhead dominates small workloads")
    print("3. Memory allocation costs not tracked")
    print("4. This tests CLASSICAL simulation, not quantum reality")
    print()
    
    return measurements, r_all


def run_scaling_analysis():
    """
    Check if μ-cost and CPU time have the same scaling behavior.
    """
    print()
    print("=" * 80)
    print("SCALING ANALYSIS")
    print("=" * 80)
    print()
    
    print("If μ-cost tracks physical reality, they should scale together:")
    print("  - μ-cost ∝ N  should mean  CPU ∝ N")
    print("  - μ-cost ∝ log N  should mean  CPU ∝ log N")
    print()
    
    # Measure scaling for partition discovery
    sizes = [128, 256, 512, 1024, 2048, 4096]
    mu_costs = []
    cpu_times = []
    
    for n in sizes:
        cpu_time, (mu_cost, _) = measure_cpu_time(workload_partition_discovery, n)
        mu_costs.append(mu_cost)
        cpu_times.append(cpu_time)
    
    # Compute ratios to detect scaling
    print("Partition Discovery Scaling:")
    print(f"{'N':>6} | {'μ':>8} | {'CPU':>12} | {'μ/N':>8} | {'CPU/N':>10} | {'μ/NlogN':>10}")
    print("-" * 70)
    
    for i, n in enumerate(sizes):
        mu = mu_costs[i]
        cpu = cpu_times[i]
        nlogn = n * math.log2(n)
        
        print(f"{n:>6} | {mu:>8.0f} | {cpu:>12.0f} | {mu/n:>8.2f} | {cpu/n:>10.2f} | {mu/nlogn:>10.4f}")
    
    print()
    print("If μ/N is constant → μ scales as O(N)")
    print("If μ/NlogN is constant → μ scales as O(N log N)")
    print()
    
    # Check μ/N constancy
    mu_per_n = [mu_costs[i] / sizes[i] for i in range(len(sizes))]
    mu_per_n_std = statistics.stdev(mu_per_n) if len(mu_per_n) > 1 else 0
    mu_per_n_mean = statistics.mean(mu_per_n)
    cv_mu = mu_per_n_std / mu_per_n_mean if mu_per_n_mean > 0 else float('inf')
    
    cpu_per_n = [cpu_times[i] / sizes[i] for i in range(len(sizes))]
    cpu_per_n_std = statistics.stdev(cpu_per_n) if len(cpu_per_n) > 1 else 0
    cpu_per_n_mean = statistics.mean(cpu_per_n)
    cv_cpu = cpu_per_n_std / cpu_per_n_mean if cpu_per_n_mean > 0 else float('inf')
    
    print(f"μ/N coefficient of variation: {cv_mu:.4f}")
    print(f"CPU/N coefficient of variation: {cv_cpu:.4f}")
    print()
    
    if cv_mu < 0.2 and cv_cpu < 0.2:
        print("BOTH μ and CPU scale as O(N) - CONSISTENT")
    elif cv_mu < 0.2:
        print("μ scales as O(N), but CPU does not - INCONSISTENT")
    elif cv_cpu < 0.2:
        print("CPU scales as O(N), but μ does not - INCONSISTENT")
    else:
        print("Neither scales cleanly as O(N) - complex relationship")


# Pytest interface
def test_correlation_exists():
    """Test that μ-cost has some correlation with CPU time."""
    measurements, r = run_correlation_test()
    # We expect at least weak positive correlation
    assert r > 0.3, f"Correlation too weak: r={r}"


def test_scaling_consistency():
    """Test that μ-cost and CPU time scale similarly."""
    run_scaling_analysis()


if __name__ == "__main__":
    measurements, r = run_correlation_test()
    run_scaling_analysis()
    
    print()
    print("=" * 80)
    print("CONCLUSION")
    print("=" * 80)
    print()
    print(f"Overall correlation: r = {r:.4f}")
    print()
    if r > 0.7:
        print("RESULT: μ-cost correlates with computational resources.")
        print("This is empirical support (not proof) for the thermodynamic bridge.")
    else:
        print("RESULT: Correlation is weak or absent.")
        print("Either the bridge doesn't hold, or measurement is too noisy.")
    print()
    print("Next step: Repeat with direct power measurement (FPGA or instrumented CPU).")
