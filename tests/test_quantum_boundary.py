#!/usr/bin/env python3
"""
GROVER'S ALGORITHM: μ-COST SIMULATION
======================================

Classical simulation of Grover's algorithm with μ-cost tracking.

This tracks what μ-costs the model charges at each stage.
It is a SIMULATION, not a claim about real quantum hardware.
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))

import math
import numpy as np
from typing import List, Dict, Any, Tuple
from dataclasses import dataclass
from thielecpu.state import State
from thielecpu.vm import VM


@dataclass
class MuCostLog:
    """Track μ-costs at each stage."""
    stage: str
    mu_before: float
    mu_after: float
    description: str
    
    @property
    def cost(self) -> float:
        return self.mu_after - self.mu_before


class GroverSimulator:
    """
    Classical simulation of Grover's algorithm with μ-cost tracking.
    """
    
    def __init__(self, n_qubits: int, marked_state: int):
        self.n = n_qubits
        self.N = 2 ** n_qubits
        self.marked = marked_state
        self.amplitudes = np.zeros(self.N, dtype=complex)
        self.state = State()
        self.vm = VM(self.state)
        self.costs: List[MuCostLog] = []
        
    def log_cost(self, stage: str, mu_before: float, description: str):
        self.costs.append(MuCostLog(
            stage=stage,
            mu_before=mu_before,
            mu_after=self.state.mu_ledger.total,
            description=description
        ))
    
    def initialize_superposition(self):
        """Initialize uniform superposition."""
        mu_before = self.state.mu_ledger.total
        self.amplitudes = np.ones(self.N, dtype=complex) / np.sqrt(self.N)
        
        # Creating partition over N elements
        universe = set(range(self.N))
        mid = self.state.pnew(universe)
        
        self.log_cost("INIT_SUPERPOSITION", mu_before, 
                      f"Create superposition over {self.N} states")
        return mid
    
    def oracle_query(self, module_id: int):
        """Apply oracle: flip phase of marked state."""
        mu_before = self.state.mu_ledger.total
        self.amplitudes[self.marked] *= -1
        self.state.mu_ledger.charge_execution(1)
        self.log_cost("ORACLE_QUERY", mu_before, 
                      f"Query oracle (flip phase of |{self.marked}⟩)")
    
    def diffusion_operator(self, module_id: int):
        """Apply Grover diffusion."""
        mu_before = self.state.mu_ledger.total
        mean_amplitude = np.mean(self.amplitudes)
        self.amplitudes = 2 * mean_amplitude - self.amplitudes
        self.state.mu_ledger.charge_execution(1)
        self.log_cost("DIFFUSION", mu_before, 
                      "Apply diffusion operator")
    
    def measure(self) -> Tuple[int, float]:
        """Measure the quantum state."""
        mu_before = self.state.mu_ledger.total
        probs = np.abs(self.amplitudes) ** 2
        result = np.random.choice(self.N, p=probs)
        prob_result = probs[result]
        
        info_revealed = math.log2(self.N)
        self.state.mu_ledger.charge_execution(int(info_revealed))
        
        self.log_cost("MEASUREMENT", mu_before,
                      f"Collapse to |{result}⟩ (prob={prob_result:.4f})")
        return result, prob_result
    
    def run_grover(self) -> Dict[str, Any]:
        """Run full Grover's algorithm."""
        optimal_iterations = int(math.pi / 4 * math.sqrt(self.N))
        
        results = {
            "n_qubits": self.n,
            "search_space": self.N,
            "marked_state": self.marked,
            "optimal_iterations": optimal_iterations,
            "costs": [],
            "total_mu": 0,
            "success": False,
            "found": None
        }
        
        mid = self.initialize_superposition()
        
        for _ in range(optimal_iterations):
            self.oracle_query(mid)
            self.diffusion_operator(mid)
        
        result, prob = self.measure()
        
        results["costs"] = self.costs
        results["total_mu"] = self.state.mu_ledger.total
        results["success"] = (result == self.marked)
        results["found"] = result
        results["final_prob"] = prob
        
        return results


def classical_search(N: int, marked: int, state: State) -> Dict[str, Any]:
    """Classical exhaustive search for comparison."""
    results = {
        "search_space": N,
        "marked_state": marked,
        "queries": 0,
        "total_mu": 0,
        "success": False,
        "found": None
    }
    
    initial_mu = state.mu_ledger.total
    
    for x in range(N):
        state.mu_ledger.charge_execution(1)
        results["queries"] += 1
        
        if x == marked:
            results["success"] = True
            results["found"] = x
            break
    
    results["total_mu"] = state.mu_ledger.total - initial_mu
    return results


def run_comparison():
    """Compare Grover vs Classical μ-costs in simulation."""
    print("=" * 70)
    print("GROVER vs CLASSICAL μ-COST COMPARISON (SIMULATION)")
    print("=" * 70)
    print()
    
    test_cases = [
        (4, 7),
        (6, 42),
        (8, 179),
        (10, 512),
    ]
    
    print(f"{'n':>4} | {'N':>8} | {'√N':>6} | {'Grover μ':>10} | {'Classical μ':>12}")
    print("-" * 50)
    
    for n, marked in test_cases:
        N = 2 ** n
        sqrt_N = int(math.sqrt(N))
        
        grover = GroverSimulator(n, marked)
        g_result = grover.run_grover()
        
        c_state = State()
        c_result = classical_search(N, marked, c_state)
        
        print(f"{n:>4} | {N:>8} | {sqrt_N:>6} | {g_result['total_mu']:>10.1f} | {c_result['total_mu']:>12.1f}")
    
    print()
    print("Note: This is a classical simulation. μ-costs reflect")
    print("model assumptions, not measured quantum hardware behavior.")


# Pytest interface
def test_grover_simulation_runs():
    """Test that Grover simulation executes without error."""
    grover = GroverSimulator(6, 42)
    result = grover.run_grover()
    assert result["total_mu"] > 0
    assert result["search_space"] == 64


def test_classical_search():
    """Test classical search μ-cost tracking."""
    state = State()
    result = classical_search(100, 50, state)
    assert result["success"]
    assert result["found"] == 50
    assert result["total_mu"] == 51  # 0..50 inclusive


def test_amortization():
    """Test that reusing structures doesn't re-charge discovery cost."""
    state = State()
    
    universe = set(range(100))
    mid = state.pnew(universe)
    m1, m2 = state.psplit(mid, lambda x: x % 2 == 0)
    discovery_mu = state.mu_ledger.total
    
    for _ in range(100):
        _ = 50 in state.regions[m1]
    
    query_mu = state.mu_ledger.total - discovery_mu
    assert query_mu == 0, f"Queries added {query_mu} μ-cost"


if __name__ == "__main__":
    run_comparison()
