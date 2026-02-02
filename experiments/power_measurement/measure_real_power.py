#!/usr/bin/env python3
"""
REAL POWER MEASUREMENT: μ-COST VS ACTUAL ENERGY
================================================

This script measures ACTUAL energy consumption using Intel RAPL
and correlates it with μ-cost from the Thiele Machine.

Requirements:
- Linux with Intel CPU (Haswell or newer)
- RAPL access (bare metal or privileged VM)
- Run test_rapl_local.py first to verify support

This is the DEFINITIVE empirical test of the thermodynamic bridge.
"""

import sys
import time
import json
import math
import statistics
from pathlib import Path
from dataclasses import dataclass
from typing import List, Tuple, Optional

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

from thielecpu.state import State


@dataclass
class PowerMeasurement:
    """Single measurement with both μ-cost and real energy."""
    test_name: str
    n: int
    mu_cost: float
    energy_joules: float
    duration_seconds: float
    
    @property
    def mu_per_joule(self) -> float:
        return self.mu_cost / self.energy_joules if self.energy_joules > 0 else 0
    
    @property
    def joules_per_mu(self) -> float:
        return self.energy_joules / self.mu_cost if self.mu_cost > 0 else 0


class RAPLReader:
    """Read energy from Intel RAPL interface."""
    
    RAPL_PATHS = [
        "/sys/class/powercap/intel-rapl/intel-rapl:0/energy_uj",
        "/sys/devices/virtual/powercap/intel-rapl/intel-rapl:0/energy_uj",
        "/sys/class/powercap/amd-rapl/amd-rapl:0/energy_uj",
    ]
    
    def __init__(self):
        self.path = self._find_rapl_path()
        if not self.path:
            raise RuntimeError(
                "RAPL not available. Run test_rapl_local.py to diagnose.\n"
                "Need bare-metal Intel Linux or AWS c6i.metal instance."
            )
        
        # Get max energy value for wraparound detection
        max_path = self.path.parent / "max_energy_range_uj"
        if max_path.exists():
            self.max_energy = int(max_path.read_text().strip())
        else:
            self.max_energy = 2**32  # Default assumption
    
    def _find_rapl_path(self) -> Optional[Path]:
        for path_str in self.RAPL_PATHS:
            path = Path(path_str)
            if path.exists():
                try:
                    # Verify we can read it
                    int(path.read_text().strip())
                    return path
                except:
                    continue
        return None
    
    def read_energy_uj(self) -> int:
        """Read current energy counter in microjoules."""
        return int(self.path.read_text().strip())
    
    def read_energy_j(self) -> float:
        """Read current energy counter in joules."""
        return self.read_energy_uj() / 1_000_000
    
    def measure_workload(self, func, *args) -> Tuple[float, float, any]:
        """
        Measure energy consumption of a workload.
        
        Returns: (energy_joules, duration_seconds, result)
        """
        # Sync and settle
        time.sleep(0.01)
        
        # Read start
        energy_start = self.read_energy_uj()
        time_start = time.perf_counter()
        
        # Execute workload
        result = func(*args)
        
        # Read end
        time_end = time.perf_counter()
        energy_end = self.read_energy_uj()
        
        # Handle counter wraparound
        if energy_end < energy_start:
            energy_uj = (self.max_energy - energy_start) + energy_end
        else:
            energy_uj = energy_end - energy_start
        
        energy_j = energy_uj / 1_000_000
        duration_s = time_end - time_start
        
        return energy_j, duration_s, result


# ============================================================================
# WORKLOADS
# ============================================================================

def workload_partition_discovery(n: int) -> float:
    """
    Core μ-charging workload: partition discovery.
    
    Creates partition structure over n elements with binary splits.
    """
    state = State()
    
    universe = set(range(n))
    mid = state.pnew(universe)
    
    # Binary partition tree (log n levels)
    current = [mid]
    for bit in range(int(math.log2(n)) if n > 1 else 1):
        new_mods = []
        for m in current:
            region = state.regions[m]
            if len(region) > 1:
                m1, m2 = state.psplit(m, lambda x, b=bit: (x >> b) & 1)
                new_mods.extend([m1, m2])
            else:
                new_mods.append(m)
        current = new_mods
    
    return state.mu_ledger.total


def workload_search(n: int) -> float:
    """
    Sequential search workload.
    
    Charges 1 μ-bit per element checked.
    """
    state = State()
    
    for i in range(n):
        state.mu_ledger.charge_execution(1)
    
    return state.mu_ledger.total


def workload_grover_structure(n_qubits: int) -> float:
    """
    Grover algorithm structure (classical simulation).
    
    Models the μ-cost of Grover's algorithm components.
    """
    N = 2 ** n_qubits
    state = State()
    
    # Initialize superposition structure - O(N) cost
    universe = set(range(N))
    mid = state.pnew(universe)
    
    # √N iterations
    iterations = int(math.pi / 4 * math.sqrt(N))
    
    for _ in range(iterations):
        state.mu_ledger.charge_execution(1)  # Oracle
        state.mu_ledger.charge_execution(1)  # Diffusion
    
    # Measurement
    state.mu_ledger.charge_execution(n_qubits)
    
    return state.mu_ledger.total


def workload_baseline(n: int) -> float:
    """
    Baseline workload with known μ-cost.
    
    Just charges n μ-bits directly.
    """
    state = State()
    state.mu_ledger.charge_execution(n)
    return state.mu_ledger.total


# ============================================================================
# MAIN EXPERIMENT
# ============================================================================

def run_power_experiment():
    """Run complete power measurement experiment."""
    
    print("=" * 70)
    print("REAL POWER MEASUREMENT: μ-COST vs ACTUAL ENERGY")
    print("=" * 70)
    print()
    
    # Initialize RAPL reader
    try:
        rapl = RAPLReader()
        print(f"✓ RAPL initialized: {rapl.path}")
    except RuntimeError as e:
        print(f"✗ {e}")
        return None
    
    print()
    measurements: List[PowerMeasurement] = []
    
    # ========================================================================
    # Test 1: Partition Discovery
    # ========================================================================
    print("TEST 1: Partition Discovery")
    print("-" * 70)
    print(f"{'N':>8} | {'μ-cost':>10} | {'Energy (J)':>12} | {'μ/J':>12} | {'J/μ':>14}")
    print("-" * 70)
    
    for n in [256, 512, 1024, 2048, 4096, 8192]:
        # Multiple trials for averaging
        energies = []
        mu_cost = 0
        for _ in range(5):
            energy_j, duration_s, mu = rapl.measure_workload(workload_partition_discovery, n)
            energies.append(energy_j)
            mu_cost = mu  # Same every time
        
        avg_energy = statistics.mean(energies)
        
        m = PowerMeasurement(
            test_name="partition_discovery",
            n=n,
            mu_cost=mu_cost,
            energy_joules=avg_energy,
            duration_seconds=duration_s
        )
        measurements.append(m)
        
        print(f"{n:>8} | {m.mu_cost:>10.1f} | {m.energy_joules:>12.6f} | "
              f"{m.mu_per_joule:>12.2f} | {m.joules_per_mu:>14.2e}")
    
    # ========================================================================
    # Test 2: Sequential Search
    # ========================================================================
    print()
    print("TEST 2: Sequential Search")
    print("-" * 70)
    print(f"{'N':>8} | {'μ-cost':>10} | {'Energy (J)':>12} | {'μ/J':>12} | {'J/μ':>14}")
    print("-" * 70)
    
    for n in [1000, 2000, 4000, 8000, 16000, 32000]:
        energies = []
        mu_cost = 0
        for _ in range(5):
            energy_j, duration_s, mu = rapl.measure_workload(workload_search, n)
            energies.append(energy_j)
            mu_cost = mu
        
        avg_energy = statistics.mean(energies)
        
        m = PowerMeasurement(
            test_name="search",
            n=n,
            mu_cost=mu_cost,
            energy_joules=avg_energy,
            duration_seconds=duration_s
        )
        measurements.append(m)
        
        print(f"{n:>8} | {m.mu_cost:>10.1f} | {m.energy_joules:>12.6f} | "
              f"{m.mu_per_joule:>12.2f} | {m.joules_per_mu:>14.2e}")
    
    # ========================================================================
    # Test 3: Grover Structure
    # ========================================================================
    print()
    print("TEST 3: Grover Algorithm Structure")
    print("-" * 70)
    print(f"{'qubits':>8} | {'N':>8} | {'μ-cost':>10} | {'Energy (J)':>12}")
    print("-" * 70)
    
    for qubits in [6, 8, 10, 12, 14]:
        N = 2 ** qubits
        energies = []
        mu_cost = 0
        for _ in range(5):
            energy_j, duration_s, mu = rapl.measure_workload(workload_grover_structure, qubits)
            energies.append(energy_j)
            mu_cost = mu
        
        avg_energy = statistics.mean(energies)
        
        m = PowerMeasurement(
            test_name="grover",
            n=N,
            mu_cost=mu_cost,
            energy_joules=avg_energy,
            duration_seconds=duration_s
        )
        measurements.append(m)
        
        print(f"{qubits:>8} | {N:>8} | {m.mu_cost:>10.1f} | {m.energy_joules:>12.6f}")
    
    # ========================================================================
    # Statistical Analysis
    # ========================================================================
    print()
    print("=" * 70)
    print("STATISTICAL ANALYSIS")
    print("=" * 70)
    print()
    
    # Pearson correlation
    mu_costs = [m.mu_cost for m in measurements]
    energies = [m.energy_joules for m in measurements]
    
    n = len(mu_costs)
    sum_mu = sum(mu_costs)
    sum_e = sum(energies)
    sum_mu_e = sum(mu * e for mu, e in zip(mu_costs, energies))
    sum_mu2 = sum(mu**2 for mu in mu_costs)
    sum_e2 = sum(e**2 for e in energies)
    
    numerator = n * sum_mu_e - sum_mu * sum_e
    denominator = ((n * sum_mu2 - sum_mu**2) * (n * sum_e2 - sum_e**2)) ** 0.5
    
    r = numerator / denominator if denominator > 0 else 0
    
    print(f"Pearson correlation (μ-cost vs Energy): r = {r:.4f}")
    print()
    
    # By-test correlations
    for test_name in ["partition_discovery", "search", "grover"]:
        test_data = [m for m in measurements if m.test_name == test_name]
        if len(test_data) >= 2:
            x = [m.mu_cost for m in test_data]
            y = [m.energy_joules for m in test_data]
            n_t = len(x)
            sum_x = sum(x)
            sum_y = sum(y)
            sum_xy = sum(xi * yi for xi, yi in zip(x, y))
            sum_x2 = sum(xi**2 for xi in x)
            sum_y2 = sum(yi**2 for yi in y)
            num = n_t * sum_xy - sum_x * sum_y
            den = ((n_t * sum_x2 - sum_x**2) * (n_t * sum_y2 - sum_y**2)) ** 0.5
            r_t = num / den if den > 0 else 0
            print(f"  {test_name}: r = {r_t:.4f}")
    
    # ========================================================================
    # Landauer Limit Comparison
    # ========================================================================
    print()
    print("=" * 70)
    print("LANDAUER LIMIT COMPARISON")
    print("=" * 70)
    print()
    
    kB = 1.380649e-23  # Boltzmann constant (J/K)
    T = 300            # Room temperature (K)
    ln2 = math.log(2)
    E_landauer = kB * T * ln2  # ~2.87e-21 J per bit erasure
    
    print(f"Landauer limit: E = kT ln(2) = {E_landauer:.2e} J/bit")
    print()
    
    # Average energy per μ-bit
    avg_j_per_mu = statistics.mean([m.joules_per_mu for m in measurements])
    overhead = avg_j_per_mu / E_landauer
    
    print(f"Average energy per μ-bit: {avg_j_per_mu:.2e} J")
    print(f"Overhead above Landauer:  {overhead:.2e}× (expected ~10^6 to 10^12)")
    print()
    
    if 1e3 < overhead < 1e15:
        print("✓ Overhead is in physically plausible range")
    elif overhead < 1:
        print("✗ ERROR: Below Landauer limit - check measurement!")
    else:
        print("⚠ Overhead unusually large - check for noise")
    
    # ========================================================================
    # Save Results
    # ========================================================================
    results = {
        'measurements': [
            {
                'test': m.test_name,
                'n': m.n,
                'mu_cost': m.mu_cost,
                'energy_joules': m.energy_joules,
                'duration_seconds': m.duration_seconds,
                'mu_per_joule': m.mu_per_joule,
                'joules_per_mu': m.joules_per_mu
            }
            for m in measurements
        ],
        'correlation': r,
        'avg_joules_per_mu': avg_j_per_mu,
        'landauer_limit': E_landauer,
        'overhead_factor': overhead,
        'timestamp': time.time()
    }
    
    output_path = Path(__file__).parent / "power_results.json"
    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2)
    
    print()
    print(f"Results saved to: {output_path}")
    
    # ========================================================================
    # Conclusion
    # ========================================================================
    print()
    print("=" * 70)
    print("CONCLUSION")
    print("=" * 70)
    print()
    
    if r > 0.9:
        print("✓ STRONG CORRELATION (r > 0.9)")
        print("  μ-cost correlates strongly with actual energy consumption.")
        print("  This is evidence FOR the thermodynamic bridge.")
    elif r > 0.7:
        print("⚠ MODERATE CORRELATION (0.7 < r < 0.9)")
        print("  μ-cost partially tracks energy.")
        print("  Suggestive but not definitive.")
    elif r > 0.3:
        print("⚠ WEAK CORRELATION (0.3 < r < 0.7)")
        print("  Some relationship exists but noisy.")
        print("  Inconclusive - need more data.")
    else:
        print("✗ NO SIGNIFICANT CORRELATION (r < 0.3)")
        print("  μ-cost does NOT track actual energy.")
        print("  This is evidence AGAINST the thermodynamic bridge.")
    
    print()
    print(f"Final correlation: r = {r:.4f}")
    print(f"Energy efficiency: {avg_j_per_mu:.2e} J/μ-bit")
    print(f"Landauer overhead: {overhead:.2e}×")
    
    return results


# Pytest interface
def test_power_correlation():
    """Test that μ-cost correlates with actual power."""
    results = run_power_experiment()
    if results is None:
        import pytest
        pytest.skip("RAPL not available on this machine")
    
    assert results['correlation'] > 0.3, f"Correlation too weak: r={results['correlation']}"


if __name__ == "__main__":
    run_power_experiment()
