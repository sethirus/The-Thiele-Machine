# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

import multiprocessing
import time
from typing import List

from scripts.multiplier_cnf_provider import CnfProvider, TARGET_COMPOSITE_250_N
from thielecpu.vm import VM
from thielecpu.state import State
import ast


# --- The Worker Process -------------------------------------------------
def solve_worker(assumptions: List[int], result_queue: multiprocessing.Queue) -> None:
    """Solve the CNF under the given assumptions and report any solution."""
    try:
        provider = CnfProvider(bit_width=415, N=TARGET_COMPOSITE_250_N)
        # Solve using the virtual machine
        clauses = provider.clauses
        for assumption in assumptions:
            clauses.append([assumption])
        code = f"""
from pysat.solvers import Glucose4

clauses = {clauses}

solver = Glucose4()
for cls in clauses:
    solver.add_clause(cls)

if solver.solve():
    model = solver.get_model()
    print('SAT')
    print(repr(model))
else:
    print('UNSAT')
"""
        vm = VM(State())
        _, output = vm.execute_python(code)
        if 'SAT' in output:
            lines = output.strip().split('\n')
            for line in lines:
                if line.startswith('[') and line.endswith(']'):
                    model = ast.literal_eval(line)
                    solution = provider.decode(model)  # Assume provider has decode
                    if solution:
                        p, q = solution
                        result_queue.put((p, q))
                    break
    except Exception:
        # Ignore failures so a single worker can't kill the pool
        pass


# --- Main execution -----------------------------------------------------
if __name__ == "__main__":
    num_workers = multiprocessing.cpu_count()
    print(f"Commander: Deploying army of {num_workers} workers.")

    result_queue: multiprocessing.Queue = multiprocessing.Queue()

    # Prepare assumptions for the two least significant bits of p and q
    # N is odd, so p[0] and q[0] must be true.
    provider_for_vars = CnfProvider(bit_width=415, N=TARGET_COMPOSITE_250_N)
    p_low = [provider_for_vars.p_bits[0], provider_for_vars.p_bits[1]]
    q_low = [provider_for_vars.q_bits[0], provider_for_vars.q_bits[1]]

    base_assumptions = [p_low[0], q_low[0]]

    jobs = []
    for p1_val in (-1, 1):
        for q1_val in (-1, 1):
            assumptions = base_assumptions + [
                p1_val * p_low[1],
                q1_val * q_low[1],
            ]
            jobs.append(assumptions)

    with multiprocessing.Pool(processes=num_workers) as pool:
        pool.starmap_async(solve_worker, [(job, result_queue) for job in jobs])
        print("Commander: Bottom-Up Cascade attack is underway. Awaiting reports...")
        start_time = time.time()
        while time.time() - start_time < 90:
            if not result_queue.empty():
                p, q = result_queue.get()
                end_time = time.time()
                print("\n" + "=" * 80)
                print(">>> MISSION ACCOMPLISHED <<<")
                print(f"Commander: Solution received after {end_time - start_time:.4f} seconds.")
                print("=" * 80)
                print(f"\nFactor p:\n{p}")
                print(f"\nFactor q:\n{q}")
                print("\nVerifying result...")
                if p * q == TARGET_COMPOSITE_250_N:
                    print("VERIFICATION SUCCESSFUL: p * q = example-250 composite")
                else:
                    print("VERIFICATION FAILED: p * q != RSA_250")
                pool.terminate()
                exit(0)
            time.sleep(0.2)

    print("\n" + "=" * 80)
    print(">>> MISSION FAILED <<<")
    print("Commander: No solution found within the 90-second operational window.")
    print("=" * 80)
    exit(1)
