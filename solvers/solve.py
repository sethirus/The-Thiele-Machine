import time, sys, os
from scripts.multiplier_cnf_provider import CnfProvider
from scripts.thiele_simulator import ThieleLookaheadSimulator

# Live N from www.paypal.com
LIVE_N = 24030732654970541194892849389693252301206880637859034827795867088826854622012013487860379727848745665577191337769334012529839722134742882175504895504496616087595646170752800820157021262450054592767949208800948073416464224970194480925705099101828482229779817890547941048549932337743400666286693213134874525525333498925162417632878494236731760743960180382069037217774813373462491363176076199469810807852957100836841554118788369368442010701214251272837033503474558211466222338267908278007099426066068565444014491832855810922086493050042236073553333125792785582447968050121186086155668681221963371436841036771143859906999

def print_dashboard(start_time, k, bit_width, p_bits, q_bits, lookahead_depth):
    # (Implementation remains the same as before, but adds lookahead depth)
    progress = int(50 * (k + 1) / bit_width)
    bar = '█' * progress + '-' * (50 - progress)
    p_str = "".join(map(str, p_bits[::-1]))
    q_str = "".join(map(str, q_bits[::-1]))
    line = (
        f"\rBit {k:3d}/{bit_width-1} [LA:{lookahead_depth:2d}] [{bar}] p={p_str[:30]}... q={q_str[:30]}..."
    )
    sys.stdout.write(line)
    sys.stdout.flush()

# --- Main Execution ---
start_time = time.time()
BIT_WIDTH = 1024

# Read strategy from environment variables set by the master script
INITIAL_LOOKAHEAD = int(os.getenv('INITIAL_LOOKAHEAD', 0))
MAX_LOOKAHEAD = int(os.getenv('MAX_LOOKAHEAD', 10))

provider = CnfProvider(bit_width=BIT_WIDTH, N=LIVE_N)
simulator = ThieleLookaheadSimulator(provider)
solution = None
final_model = []
p_solution_bits = ["?" for _ in range(BIT_WIDTH)]
q_solution_bits = ["?" for _ in range(BIT_WIDTH)]

try:
    for k in range(BIT_WIDTH):
        lookahead_depth = INITIAL_LOOKAHEAD
        while True:
            print_dashboard(start_time, k, BIT_WIDTH, p_solution_bits, q_solution_bits, lookahead_depth)
            
            frontier_vars = [provider.p_bits[k], provider.q_bits[k]]
            deduced_bits = simulator.deduce_frontier_with_lookahead(final_model, frontier_vars, lookahead_depth)
            
            if deduced_bits is not None:
                final_model.extend(deduced_bits)
                for lit in deduced_bits:
                    var, val = (abs(lit), 1) if lit > 0 else (abs(lit), 0)
                    if var == provider.p_bits[k]: p_solution_bits[k] = str(val)
                    elif var == provider.q_bits[k]: q_solution_bits[k] = str(val)
                break # Success, move to next bit k
            
            lookahead_depth += 1
            if lookahead_depth > MAX_LOOKAHEAD:
                print(f"\n\n!!! STRATEGY FAILURE at bit {k} !!!")
                print(f"    Max lookahead of {MAX_LOOKAHEAD} exceeded.")
                sys.exit(2) # Exit code for lookahead failure

    p = CnfProvider.decode_bits(provider.p_bits, final_model)
    q = CnfProvider.decode_bits(provider.q_bits, final_model)
    solution = (p, q)

except KeyboardInterrupt:
    print("\n\nManually terminated.")
    sys.exit(1)

# (Final success report)
end_time = time.time()

if solution:
    p, q = solution
    print("\n" + "=" * 80)
    print(">>> MISSION ACCOMPLISHED: FACTORS FOUND <<<")
    print(f"Total Time: {end_time - start_time:.4f} seconds.")
    print("=" * 80)
    print(f"\nFactor p:\n{p}")
    print(f"\nFactor q:\n{q}")
    
    print("\nVerifying result...")
    if p * q == LIVE_N:
        print("✅ VERIFICATION SUCCESSFUL: p * q = LIVE_N")
    else:
        print("❌ VERIFICATION FAILED: p * q != LIVE_N")
        print(f"p * q = {p * q}")
        print(f"LIVE_N = {LIVE_N}")
else:
    print("\nNo solution found.")