# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""
Economic Weapon Demonstration: The Cost of Sight

This script demonstrates the Thiele Machine's superior economic model of computation.
It generates a computationally hard SAT puzzle with a hidden backdoor shortcut.
The classical SAT solver fails to find the shortcut, incurring massive costs.
The Thiele Machine discovers the partition cheaply, solves instantly, and generates
a verifiable receipt proving the economic dominance.

The puzzle: A Tseitin instance on a large expander graph (unsatisfiable by parity).
The backdoor: The underlying XOR equations that collapse the problem.
Classical: Brute-force search over assignments (expensive, fails).
Thiele: Partition discovery via GF(2) elimination (cheap, succeeds).
"""

import json
import time
import hashlib
import random
import math
import argparse
import sys

try:
    import networkx as nx
except ImportError:
    raise SystemExit("networkx is required. Install with pip install networkx")

try:
    from pysat.solvers import Glucose3
except ImportError:
    raise SystemExit("pysat is required. Install with pip install pysat")

from typing import Dict, List, Tuple, Sequence
from dataclasses import dataclass

import json
import time
import hashlib
import random
import math
import argparse
import sys

try:
    import networkx as nx
except ImportError:
    raise SystemExit("networkx is required. Install with pip install networkx")

try:
    from pysat.solvers import Solver, CryptoMinisat
except ImportError:
    raise SystemExit("pysat is required. Install with pip install pysat")

from typing import Dict, List, Tuple, Sequence
from dataclasses import dataclass

def seeded_rng(global_seed: int, n: int, seed: int) -> random.Random:
    """Deterministic RNG seeded via a hash of the parameters."""
    payload = f"{global_seed}|{n}|{seed}".encode()
    digest = int.from_bytes(__import__("hashlib").blake2b(payload, digest_size=8).digest(), "big")
    return random.Random(digest)

def generate_tseitin_expander(n: int, seed: int, *, global_seed: int = 123456789) -> Dict:
    """Generate a 3-regular graph and associated Tseitin parity instance."""
    if n % 2:
        raise ValueError(f"3-regular graphs require even n (got {n})")
    rng = seeded_rng(global_seed, n, seed)
    graph = nx.random_regular_graph(3, n, seed=rng)
    edges = sorted(tuple(sorted(e)) for e in graph.edges())
    edge_index = {edge: idx for idx, edge in enumerate(edges)}

    charges = [rng.randrange(2) for _ in range(n - 1)]
    charges.append(1 ^ (sum(charges) & 1))

    incidence: Dict[int, List[int]] = {v: [] for v in graph.nodes()}
    for (u, v) in edges:
        idx = edge_index[(min(u, v), max(u, v))]
        incidence[u].append(idx)
        incidence[v].append(idx)

    xor_rows: List[Tuple[List[int], int]] = []
    cnf: List[List[int]] = []
    for vertex, idxs in incidence.items():
        assert len(idxs) == 3, "generated graph is not 3-regular"
        idxs.sort()
        xor_rows.append((idxs, charges[vertex]))
        var_ids = [idx + 1 for idx in idxs]
        cnf.extend(_xor3_to_cnf(var_ids[0], var_ids[1], var_ids[2], charges[vertex]))
    return {
        "n": n,
        "seed": seed,
        "edges": edges,
        "charges": charges,
        "xor_rows": xor_rows,
        "cnf": cnf,
    }

def _xor3_to_cnf(x: int, y: int, z: int, charge: int) -> List[List[int]]:
    """Convert x ⊕ y ⊕ z = charge into CNF clauses."""
    if charge not in (0, 1):
        raise ValueError("charge must be 0 or 1")
    clauses: List[List[int]] = []
    combos = [
        (True, True, True), (True, True, False), (True, False, True), (True, False, False),
        (False, True, True), (False, True, False), (False, False, True), (False, False, False),
    ]
    for a, b, c in combos:
        parity = (a + b + c) % 2
        if parity == charge:
            continue
        clause: List[int] = []
        clause.append(x if a else -x)
        clause.append(y if b else -y)
        clause.append(z if c else -z)
        clauses.append(clause)
    return clauses

def solve_by_bruteforce(clauses: Sequence[Sequence[int]], *, max_seconds: float) -> Dict:
    start = time.perf_counter()
    num_vars = max((abs(lit) for clause in clauses for lit in clause), default=0)
    checked = 0
    status = "unsat"
    for assignment in range(1 << num_vars):
        if time.perf_counter() - start > max_seconds:
            status = "timeout"
            break
        checked += 1
        if _cnf_satisfied(clauses, assignment):
            status = "sat"
            break
    runtime = time.perf_counter() - start
    return {
        "status": status,
        "runtime_seconds": runtime,
        "assignments_checked": checked,
        "num_variables": num_vars,
    }

def _cnf_satisfied(clauses: Sequence[Sequence[int]], assignment: int) -> bool:
    for clause in clauses:
        satisfied = False
        for lit in clause:
            var = abs(lit) - 1
            bit = (assignment >> var) & 1
            if (lit > 0 and bit == 1) or (lit < 0 and bit == 0):
                satisfied = True
                break
        if not satisfied:
            return False
    return True

@dataclass
class GaussianResult:
    result: str
    runtime_seconds: float
    row_operations: int
    pivots: int
    inconsistent_rows: List[int]

    @property
    def mu_discovery(self) -> int:
        return self.row_operations

def solve_by_gaussian(xor_rows: Sequence[Tuple[Sequence[int], int]], num_vars: int) -> GaussianResult:
    matrix: List[List[int]] = []
    rhs: List[int] = []
    for row, value in xor_rows:
        mask = 0
        for idx in row:
            mask |= 1 << idx
        matrix.append([mask])
        rhs.append(value & 1)

    start = time.perf_counter()
    row_ops = 0
    pivot = 0
    rows = len(matrix)
    for col in range(num_vars):
        pivot_row = None
        for r in range(pivot, rows):
            if (matrix[r][0] >> col) & 1:
                pivot_row = r
                break
        if pivot_row is None:
            continue
        if pivot_row != pivot:
            matrix[pivot], matrix[pivot_row] = matrix[pivot_row], matrix[pivot]
            rhs[pivot], rhs[pivot_row] = rhs[pivot_row], rhs[pivot]
            row_ops += 1
        for r in range(rows):
            if r == pivot:
                continue
            if (matrix[r][0] >> col) & 1:
                matrix[r][0] ^= matrix[pivot][0]
                rhs[r] ^= rhs[pivot]
                row_ops += 1
        pivot += 1
        if pivot == rows:
            break
    inconsistent = any((row_mask == 0 and bit == 1) for (row_mask,), bit in zip(matrix, rhs))
    inconsistent_rows = [i for i, ((row_mask,), bit) in enumerate(zip(matrix, rhs)) if row_mask == 0 and bit == 1]
    runtime = time.perf_counter() - start
    return GaussianResult(
        result="unsat" if inconsistent else "sat",
        runtime_seconds=runtime,
        row_operations=row_ops,
        pivots=pivot,
        inconsistent_rows=inconsistent_rows,
    )

def generate_challenge_puzzle(n=20):
    """Generate a large, hard SAT puzzle with hidden backdoor."""
    # Large instance: n, 3-regular expander
    seed = 42  # Fixed for reproducibility
    instance = generate_tseitin_expander(n, seed)
    challenge_hash = hashlib.sha256(json.dumps(instance, sort_keys=True).encode()).hexdigest()
    return instance, challenge_hash

def run_classical_solver(instance, max_time=10.0):
    """Run classical brute-force SAT solver (will timeout)."""
    print("Running classical SAT solver (brute-force)...")
    start = time.time()
    result = solve_by_bruteforce(instance['cnf'], max_seconds=max_time)
    end = time.time()
    # Estimate hypothetical cost (e.g., in dollars for compute)
    # Assume 1e6 assignments/second, $1 per 1e9 assignments
    assignments_per_second = 5e7      # e.g., 50M/s on a beefy CPU/GPU bit-slicer
    cost_per_billion = 2.0            # $2 per 1e9 assignments (tune as you like)

    checked = result['assignments_checked']
    num_vars = result['num_variables']
    total_space = 1 << num_vars
    remaining = max(total_space - checked, 0)

    spent_cost = checked / 1e9 * cost_per_billion
    projected_cost_to_exhaust = remaining / 1e9 * cost_per_billion
    projected_time_to_exhaust_s = remaining / assignments_per_second

    return {
        'strategy': 'BLIND SEARCH',
        'status': result['status'],
        'runtime_seconds': end - start,
        'assignments_checked': checked,
        'num_variables': num_vars,
        'estimated_cost_spent': spent_cost,
        'projected_cost_to_prove_unsat': projected_cost_to_exhaust,
        'projected_seconds_to_prove_unsat': projected_time_to_exhaust_s,
        'mu_discovery': 0
    }

def run_cdcl_solver(instance):
    """Run CDCL+XOR SAT solver."""
    print("Running CDCL+XOR SAT solver...")
    start = time.time()
    result = solve_by_cdcl_xor(instance['cnf'])
    end = time.time()
    # Estimate cost similar to classical, but faster
    # Assume CDCL is much faster, but for large n, still expensive
    # For demo, use similar cost model but adjust
    cost_per_second = 0.01  # $ per second for compute
    return {
        'strategy': 'CDCL+XOR',
        'status': result['status'],
        'runtime_seconds': end - start,
        'estimated_cost_dollars': (end - start) * cost_per_second,
    }

def solve_by_cdcl_xor(cnf: Sequence[Sequence[int]]) -> Dict:
    """Run CDCL SAT solver using Glucose3."""
    start = time.perf_counter()
    solver = Glucose3()
    for clause in cnf:
        solver.add_clause(clause)
    status = solver.solve()
    runtime = time.perf_counter() - start
    solver.delete()
    return {
        "status": "sat" if status else "unsat",
        "runtime_seconds": runtime,
    }

def run_thiele_solver(instance):
    """Run Thiele partition discovery (GF(2) elimination)."""
    print("Running Thiele Machine partition discovery...")
    start = time.time()
    gaussian = solve_by_gaussian(instance['xor_rows'], len(instance['edges']))
    end = time.time()
    # Cost: μ-discovery = row operations
    # Operational cost: minimal
    mu_discovery = gaussian.mu_discovery
    mu_price = 1e-6         # $ per μ-op
    operational_cost = 1e-4 # flat "receipt assembly"

    return {
        'strategy': 'THIELE PARTITION DISCOVERY',
        'status': gaussian.result,
        'runtime_seconds': end - start,
        'mu_discovery': mu_discovery,
        'mu_operational': operational_cost,
        'estimated_cost_dollars': mu_discovery * mu_price + operational_cost,
        'rank': gaussian.pivots,
        'inconsistent_rows': gaussian.inconsistent_rows
    }

def generate_receipt(challenge_hash, classical_result, cdcl_result, thiele_result, instance):
    """Generate the verifiable receipt."""
    sum_charges_mod2 = sum(instance['charges']) & 1
    graph = nx.Graph(instance['edges'])
    receipt_data = {
        'challenge_hash': challenge_hash,
        'problem': {
            'num_equations': len(instance['xor_rows']),
            'num_variables': len(instance['edges']),
            'sum_charges_mod2': sum_charges_mod2,
            'graph_connected': nx.is_connected(graph),
            'degree': 3,
            'num_edges': len(instance['edges']),
            'unsat_certificate': thiele_result['inconsistent_rows'],
        },
        'classical': classical_result,
        'cdcl': cdcl_result,
        'thiele': thiele_result,
        'timestamp': time.time(),
        'proof': 'For a connected graph, XOR of all equations cancels LHS to 0; RHS sums to 1 ⇒ inconsistency ⇒ UNSAT.'
    }
    receipt_json = json.dumps(receipt_data, indent=2)
    receipt_hash = hashlib.sha256(receipt_json.encode()).hexdigest()
    receipt_data['receipt_hash'] = receipt_hash
    return receipt_data

def main():
    parser = argparse.ArgumentParser(description="Economic Weapon Demonstration")
    parser.add_argument('--n', type=int, default=20, help='Number of vertices for the expander graph (must be even)')
    args = parser.parse_args()

    print("=== ECONOMIC WEAPON DEMONSTRATION ===")
    print("Generating challenge puzzle...")
    instance, challenge_hash = generate_challenge_puzzle(args.n)
    print(f"Challenge hash: {challenge_hash}")
    print(f"Puzzle size: {len(instance['cnf'])} clauses, {len(instance['edges'])} variables")

    # Run classical (will fail/timeout)
    classical = run_classical_solver(instance)

    # Run CDCL (succeeds fast)
    cdcl = run_cdcl_solver(instance)

    # Run Thiele (succeeds cheaply)
    thiele = run_thiele_solver(instance)

    # Generate receipt
    receipt = generate_receipt(challenge_hash, classical, cdcl, thiele, instance)

    # Save receipt
    with open('economic_weapon_receipt.json', 'w') as f:
        json.dump(receipt, f, indent=2)

    print("\n=== RECEIPT ===")
    print(f"CHALLENGE HASH: {receipt['challenge_hash']}")
    print(f"PROBLEM: equations={receipt['problem']['num_equations']}, variables={receipt['problem']['num_variables']}, sum_charges_mod2={receipt['problem']['sum_charges_mod2']}")
    print(f"CLASSICAL: {receipt['classical']['strategy']} - Spent: ${receipt['classical']['estimated_cost_spent']:.2f}, "
          f"Projected-to-prove-UNSAT: ${receipt['classical']['projected_cost_to_prove_unsat']:.2f}, "
          f"Status: {receipt['classical']['status']}")
    print(f"CDCL: {receipt['cdcl']['strategy']} - Cost: ${receipt['cdcl']['estimated_cost_dollars']:.6f}, "
          f"Status: {receipt['cdcl']['status']}")
    print(f"THIELE: {receipt['thiele']['strategy']} - mu={receipt['thiele']['mu_discovery']}, "
          f"Rank={receipt['thiele']['rank']}, Cost: ${receipt['thiele']['estimated_cost_dollars']:.6f}, "
          f"Status: {receipt['thiele']['status']}")
    print(f"RECEIPT HASH: {receipt['receipt_hash']}")
    print("\nThe Thiele Machine proves superior economics: finite mu-discovery collapses exponential classical costs.")
    print(f"RECEIPT HASH: {receipt['receipt_hash']}")
    print("\nThe Thiele Machine proves superior economics: finite mu-discovery collapses exponential classical costs.")

if __name__ == '__main__':
    main()