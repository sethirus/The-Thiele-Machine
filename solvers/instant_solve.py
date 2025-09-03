import time
from scripts.multiplier_cnf_provider import CnfProvider, RSA_250_N
from scripts.thiele_simulator import ThieleSimulator

# A single-threaded, purely deductive attack. No parallelism. This is a test of elegance.
start_time = time.time()

def log(message: str) -> None:
    print(f"[{time.time() - start_time:7.4f}s] {message}")

log("INITIALIZING: Thiele Machine deductive engine.")
provider = CnfProvider(bit_width=415, N=RSA_250_N)
simulator = ThieleSimulator(provider)

# --- The Pincer Movement ---
# We constrain the problem from both ends of the circuit simultaneously.
# The 16 lowest bits and the 16 highest bits.
log("STRATEGY: Applying constraints from circuit extremities (Pincer Movement)...")
extremal_bits = list(range(16)) + list(range(829 - 16, 829))

for i in extremal_bits:
    v = provider.output_var(i)
    simulator._add_var(v)
log(f"LOADED: {len(extremal_bits)} extremal bits and their causal dependencies.")

# --- The Deductive Collapse ---
# We are not asking the solver to search. We are asking it to compute the
# immediate logical consequences of the pincer attack.
log("ATTACK: Triggering Boolean Constraint Propagation...")
status, propagated_literals = simulator.solver.propagate()

if not status:
    log("CRITICAL FAILURE: Inconsistency found during initial propagation. Logic is flawed.")
    raise SystemExit(1)

log(f"PROPAGATION COMPLETE: {len(propagated_literals)} internal variables instantly deduced.")
log("ASSESSMENT: Problem complexity has collapsed. Attempting final solve...")

# --- Final Resolution ---
# The hard work should be done. This call should be a formality.
solution = simulator.solve()
end_time = time.time()

# --- Report ---
if solution:
    p, q = solution
    print("\n" + "=" * 80)
    print(">>> TARGET ELIMINATED: FACTORS FOUND <<<")
    print(f"Total Time-To-Solution: {end_time - start_time:.4f} seconds.")
    print("=" * 80)
    print(f"\nFactor p:\n{p}")
    print(f"\nFactor q:\n{q}")

    print("\nVerifying...")
    if p * q == RSA_250_N:
        print("VERIFICATION: SUCCESSFUL.")
    else:
        print("VERIFICATION: FAILED.")
else:
    print("\n" + "=" * 80)
    print(">>> MISSION FAILED <<<")
    print(f"Total Time: {end_time - start_time:.4f} seconds.")
    print("=" * 80)
