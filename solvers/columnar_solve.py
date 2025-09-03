import time
import sys
from scripts.multiplier_cnf_provider import CnfProvider, RSA_250_N
from scripts.thiele_simulator import ThieleSimulator

# --- The Dashboard ---
def print_dashboard(start_time, k, bit_width, p_bits, q_bits):
    """Renders the progress of the column-by-column solve."""
    progress = int(50 * k / bit_width)
    bar = '█' * progress + '-' * (50 - progress)
    p_str = "".join(map(str, p_bits[::-1]))
    q_str = "".join(map(str, q_bits[::-1]))
    line = (
        f"\rDeducing bit {k:3d}/{bit_width}: [{bar}] p={p_str[:30]}... q={q_str[:30]}..."
    )
    sys.stdout.write(line)
    sys.stdout.flush()

# --- Main Execution ---
start_time = time.time()
BIT_WIDTH = 3
N = 35

print("=" * 120)
print("Thiele Machine: Column-by-Column Deductive Solve Activated")
print("=" * 120)

provider = CnfProvider(bit_width=BIT_WIDTH, N=N)
simulator = ThieleSimulator(provider)

# This list will hold the permanent, deduced values of the factor bits.
final_model = []
p_solution_bits = ["?" for _ in range(BIT_WIDTH)]
q_solution_bits = ["?" for _ in range(BIT_WIDTH)]

try:
    # Load all output constraints first
    for i in range(provider.output_count()):
        simulator._add_var(provider.output_var(i))

    # --- The Main Loop: Solve one column at a time ---
    for k in range(BIT_WIDTH):
        print_dashboard(start_time, k, BIT_WIDTH, p_solution_bits, q_solution_bits)
        
        # Load the logic for the next two output columns to constrain the solver.
        # This ensures the carries are properly handled.
        simulator._add_var(provider.output_var(k))
        if k + 1 < provider.output_count():
            simulator._add_var(provider.output_var(k+1))
            
        # The "frontier" variables we want to solve for in this step.
        frontier_vars = [provider.p_bits[k], provider.q_bits[k]]
        
        # Ask the oracle: "Given what we know, what are the possible values for p[k] and q[k]?"
        # Try all 4 possible assignments for the two bits.
        solutions = []
        for p_val in [0, 1]:
            for q_val in [0, 1]:
                assumptions = final_model + [p_val * 2 - 1 if p_val else -provider.p_bits[k],
                                             q_val * 2 - 1 if q_val else -provider.q_bits[k]]
                if simulator.solver.solve(assumptions=assumptions):
                    solutions.append((p_val, q_val))
        
        if len(solutions) == 1:
            # The perfect case: There is only ONE possible assignment. This is a forced deduction.
            p_val, q_val = solutions[0]
            final_model.append(p_val * 2 - 1 if p_val else -provider.p_bits[k])
            final_model.append(q_val * 2 - 1 if q_val else -provider.q_bits[k])
            
            # Update our solution display
            p_solution_bits[k] = str(p_val)
            q_solution_bits[k] = str(q_val)
        else:
            # This is a failure condition. It means the problem is not fully constrained
            # or we have hit a point of ambiguity.
            print(f"\n\n!!! DEDUCTION FAILED at bit {k} !!!")
            print(f"    Solver found {len(solutions)} possible models for (p[{k}], q[{k}]).")
            print("    The problem's structure is not as rigid as hypothesized.")
            exit(1)

    # --- Finalization ---
    print_dashboard(start_time, BIT_WIDTH, BIT_WIDTH, p_solution_bits, q_solution_bits)
    print("\n\nDEDUCTION COMPLETE: All bits for p and q have been determined.")
    
    p = CnfProvider.decode_bits(provider.p_bits, final_model)
    q = CnfProvider.decode_bits(provider.q_bits, final_model)
    solution = (p, q)

except KeyboardInterrupt:
    print("\n\nExperiment manually terminated.")
    exit(1)

# --- Final Report ---
end_time = time.time()

if solution:
    p, q = solution
    print("\n" + "=" * 80)
    print(">>> MISSION ACCOMPLISHED: FACTORS FOUND <<<")
    print(f"Total Time: {end_time-start_time:.4f} seconds.")
    print("=" * 80)
    print(f"\nFactor p:\n{p}")
    print(f"\nFactor q:\n{q}")
    
    # Add verification
    print("\nVerifying result...")
    if p * q == RSA_250_N:
        print("✅ VERIFICATION SUCCESSFUL: p * q = RSA-250")
    else:
        print("❌ VERIFICATION FAILED: p * q != RSA-250")
        print(f"p * q = {p * q}")
        print(f"RSA-250 = {RSA_250_N}")
else:
    print("\n" + "=" * 80)
    print(">>> MISSION FAILED: NO SOLUTION FOUND <<<")