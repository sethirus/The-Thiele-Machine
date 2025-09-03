import multiprocessing
import time
from typing import List

from scripts.multiplier_cnf_provider import CnfProvider, RSA_250_N
from scripts.thiele_simulator import ThieleSimulator


# --- The Worker Process -------------------------------------------------
def solve_worker(assumptions: List[int], result_queue: multiprocessing.Queue) -> None:
    """Solve the CNF under the given assumptions and report any solution."""
    try:
        provider = CnfProvider(bit_width=415, N=RSA_250_N)
        simulator = ThieleSimulator(provider)
        solution = simulator.solve(assumptions=assumptions)
        if solution:
            p, q = solution
            result_queue.put((p, q))
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
    provider_for_vars = CnfProvider(bit_width=415, N=RSA_250_N)
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
                if p * q == RSA_250_N:
                    print("VERIFICATION SUCCESSFUL: p * q = RSA-250")
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
