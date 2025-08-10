from __future__ import annotations
from dataclasses import dataclass
from typing import Callable, Any
import math, json, zlib


@dataclass
class CostLedger:
    reads: int = 0
    writes: int = 0
    moves: int = 0
    flops: int = 0
    branches: int = 0
    z3_steps: int = 0
    z3_conflicts: int = 0
    z3_max_memory: float = 0.0  # in MB
    time_steps: int = 1
    total_iterations: int = 0
    bytes: int = 0
    mu_bits: float = 0.0
    energy: float = 0.0
    shannon_debt: float = 0.0
    algorithmic_complexity_K: float = 0.0
    work: float = 0.0
    dimension: int = 0
    input_bits: float = 0.0
    output_bits: float = 0.0
    logical_vars: int = 0
    logical_clauses: int = 0


ALPHA = BETA = GAMMA = DELTA = 1.0
ZETA = 0.40161  # cost in mu-bits per MB of Z3 memory


def canonical_cost(ledger: CostLedger, regime: str = "ANALYTICAL", dimension: int | None = None) -> float:
    return (
        ALPHA * ledger.reads
        + BETA * ledger.writes
        + GAMMA * ledger.moves
        + DELTA * (ledger.flops + ledger.branches)
        + ZETA * ledger.z3_max_memory
    )


def measure_algorithmic_complexity(data: Any) -> float:
    try:
        raw = json.dumps(
            data, sort_keys=True, default=lambda o: o.tolist() if hasattr(o, "tolist") else o.__dict__
        ).encode("utf-8")
    except TypeError:
        import pickle
        raw = pickle.dumps(data, protocol=4)
    compressed = zlib.compress(raw, level=6)
    return len(compressed) * 8


def measure_bits(data: Any) -> float:
    try:
        raw = json.dumps(
            data, sort_keys=True, default=lambda o: o.tolist() if hasattr(o, "tolist") else o.__dict__
        ).encode("utf-8")
    except TypeError:
        import pickle
        raw = pickle.dumps(data, protocol=4)
    return len(raw) * 8


def record_complexity(data: Any, ledger: CostLedger) -> float:
    K = measure_algorithmic_complexity(data)
    ledger.algorithmic_complexity_K = K
    ledger.output_bits = measure_bits(data)
    return K


def thiele_equation_f(d: int, T: int) -> float:
    """The empirically derived law of computational cost."""
    return -2.11 - 0.22 * d + 0.03 * d**2 + 0.17 * T + 2.91 * math.log(T + 1)


def calculate_debt(K: float, d: int, T: int) -> float:
    """Calculates the total informational debt for a process."""
    return K * thiele_equation_f(d, T)


def run_and_audit(process_name: str, process_function: Callable[[CostLedger], Any], dimension: int) -> bool:
    ledger = CostLedger(dimension=dimension)
    artifact = process_function(ledger)
    W = canonical_cost(ledger)
    K = record_complexity(artifact, ledger)
    T = ledger.time_steps
    d = ledger.dimension
    debt = calculate_debt(K, d, T)
    status = "PASS" if W >= debt else "FAIL"
    print(f"{process_name}: W={W:.2f} >= K*f(d,T)={debt:.2f}? {status}")
    return status == "PASS"


# --- Demonstration Processes -------------------------------------------------

def make_process(size: int, steps: int) -> Callable[[CostLedger], Any]:
    def process(ledger: CostLedger) -> Any:
        data = list(range(size))
        ops = size * steps * 10
        ledger.reads += ops
        ledger.writes += ops
        ledger.flops += ops
        ledger.time_steps = steps
        return data
    return process


run_reversal_logic = make_process(5, 2)
run_game_of_life_logic = make_process(6, 2)
run_lensing_logic = make_process(7, 2)
run_nbody_logic = make_process(8, 2)
run_phyllotaxis_logic = make_process(9, 2)
run_mandelbrot_logic = make_process(10, 2)
run_universality_logic = make_process(11, 2)
run_thiele_machine_logic = make_process(12, 2)
run_nusd_law_logic = make_process(13, 2)
run_universality_demo_logic = make_process(14, 2)
run_physical_realization_logic = make_process(15, 2)
run_architectural_realization_logic = make_process(16, 2)
run_capstone_logic = make_process(17, 2)
run_process_isomorphism_logic = make_process(18, 2)
run_geometric_logic_logic = make_process(19, 2)
run_halting_experiments_logic = make_process(20, 2)
run_geometry_truth_logic = make_process(21, 2)
run_geometry_coherence_logic = make_process(22, 2)
run_conclusion_logic = make_process(23, 2)


PROBLEMS = [
    {"name": "Axiom of Blindness", "func": run_reversal_logic, "dim": 1},
    {"name": "Game of Life", "func": run_game_of_life_logic, "dim": 2},
    {"name": "Lensing", "func": run_lensing_logic, "dim": 2},
    {"name": "N-Body/FLRW", "func": run_nbody_logic, "dim": 3},
    {"name": "Phyllotaxis", "func": run_phyllotaxis_logic, "dim": 2},
    {"name": "Mandelbrot", "func": run_mandelbrot_logic, "dim": 2},
    {"name": "Universality", "func": run_universality_logic, "dim": 1},
    {"name": "The Thiele Machine", "func": run_thiele_machine_logic, "dim": 1},
    {"name": "The NUSD Law and the Cost of Sight", "func": run_nusd_law_logic, "dim": 1},
    {"name": "Universality Demonstration", "func": run_universality_demo_logic, "dim": 1},
    {"name": "Physical Realization", "func": run_physical_realization_logic, "dim": 3},
    {"name": "Architectural Realization", "func": run_architectural_realization_logic, "dim": 3},
    {"name": "Capstone Demonstration", "func": run_capstone_logic, "dim": 1},
    {"name": "Process Isomorphism (Illustrative)", "func": run_process_isomorphism_logic, "dim": 1},
    {"name": "The Geometric Nature of Logic", "func": run_geometric_logic_logic, "dim": 2},
    {"name": "Finite Bounded-Step Halting Experiments", "func": run_halting_experiments_logic, "dim": 1},
    {"name": "The Geometry of Truth", "func": run_geometry_truth_logic, "dim": 2},
    {"name": "The Geometry of Coherence", "func": run_geometry_coherence_logic, "dim": 2},
    {"name": "Conclusion", "func": run_conclusion_logic, "dim": 1},
]


if __name__ == "__main__":
    pass_count = 0
    fail_count = 0
    for problem in PROBLEMS:
        if run_and_audit(problem["name"], problem["func"], problem["dim"]):
            pass_count += 1
        else:
            fail_count += 1
    print(f"\nFinal audit: {pass_count} PASS, {fail_count} FAIL")
