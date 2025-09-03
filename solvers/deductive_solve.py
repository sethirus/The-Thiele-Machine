import time

from scripts.multiplier_cnf_provider import CnfProvider, RSA_250_N
from scripts.thiele_simulator import ThieleSimulator

print("=" * 80)
print("Executing Deductive Cascade Attack")
print("Target: RSA-250")
print("Method: Constraint propagation from circuit extremities.")
print("=" * 80)

start_time = time.time()

# 1. Instantiate the logical space of the problem.
print(f"[{time.time() - start_time:.2f}s] Initializing CnfProvider...")
provider = CnfProvider(bit_width=415, N=RSA_250_N)
simulator = ThieleSimulator(provider)

# 2. Identify and load the points of maximum leverage.
# The highest and lowest bits of the product N.
print(f"[{time.time() - start_time:.2f}s] Identifying circuit extremities...")
leverage_points = [
    0,
    1,
    2,
    3,  # The least significant bits
    828,
    827,
    826,
    825,  # The most significant bits
]
for i in leverage_points:
    v = provider.output_var(i)
    simulator._add_var(v)

# 3. Trigger the deductive cascade.
# We call the solver's internal propagation engine without searching.
# This forces all immediate logical consequences.
print(f"[{time.time() - start_time:.2f}s] Triggering Boolean Constraint Propagation...")
assumptions = []  # No assumptions needed; the constraints on N are hard clauses.
status, propagated_literals = simulator.solver.propagate(assumptions=assumptions)

if not status:
    print("ERROR: Inconsistency found during initial propagation. Check logic.")
else:
    print(
        f"[{time.time() - start_time:.2f}s] Propagation complete. "
        f"{len(propagated_literals)} literals deduced."
    )
    print(
        f"[{time.time() - start_time:.2f}s] Handing simplified problem to solver for final resolution..."
    )

    # 4. Solve the remaining, potentially trivial, problem.
    solution = simulator.solve()

    end_time = time.time()

    if solution:
        p, q = solution
        print("\n" + "=" * 80)
        print(">>> DEDUCTION COMPLETE: FACTORS FOUND <<<")
        print(f"Total time: {end_time - start_time:.4f} seconds.")
        print("=" * 80)
        print(f"\nFactor p:\n{p}")
        print(f"\nFactor q:\n{q}")

        print("\nVerifying result...")
        if p * q == RSA_250_N:
            print("VERIFICATION SUCCESSFUL: p * q = RSA-250")
        else:
            print("VERIFICATION FAILED: p * q != RSA-250")
    else:
        print("\n" + "=" * 80)
        print(">>> DEDUCTION FAILED: NO SOLUTION FOUND <<<")
        print(f"Total time: {end_time - start_time:.4f} seconds.")
        print("=" * 80)
