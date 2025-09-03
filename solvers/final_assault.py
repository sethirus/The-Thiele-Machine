import time
import sys
import socket
import ssl
from cryptography import x509
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives.asymmetric.rsa import RSAPublicKey
from scripts.multiplier_cnf_provider import CnfProvider
from scripts.thiele_simulator import ThieleSimulator # We must use the advanced simulator

# --- The Live Dashboard ---
def print_dashboard(start_time, k, bit_width, p_bits, q_bits, lookahead_depth, status_msg=""):
    progress = int(50 * (k + 1) / bit_width)
    bar = '█' * progress + '-' * (50 - progress)
    p_str = "".join(map(str, p_bits[::-1]))
    line = (
        f"\rBit {k:4d}/{bit_width-1} [LA:{lookahead_depth:2d}] [{bar}] p={p_str[:60]}... {status_msg}"
    )
    sys.stdout.write(line)
    sys.stdout.flush()

# --- The Main Operation ---
start_time = time.time()

# === MILESTONE 1: ACQUIRE LIVE TARGET ===
print("=" * 120)
print("Project SIGHTLINE: Final Assault Protocol Initiated")
print("=" * 120)
print(f"[{time.time()-start_time:.2f}s] Acquiring live target from www.paypal.com...")

# For demonstration, use a small test key instead of live key
# N = 9  # 3 * 3, 4 bits
# BIT_WIDTH = 2
# N = 143  # 11 * 13, 8 bits
# BIT_WIDTH = 4
# N = 3233  # 53 * 61, 12 bits
# BIT_WIDTH = 6
# To use live key, uncomment the below and comment this
N = 9
BIT_WIDTH = 2
print(f"[{time.time()-start_time:.2f}s] ✅ TARGET ACQUIRED: {BIT_WIDTH*2}-bit RSA Public Key (test key for demonstration).")

# === MILESTONE 2: LAUNCH THE THIELE MACHINE ===
print(f"[{time.time()-start_time:.2f}s] Initializing Guided Deductive Engine...")
provider = CnfProvider(bit_width=BIT_WIDTH, N=N)
simulator = ThieleSimulator(provider) # Using the advanced engine
solution = None

final_model = []
p_solution_bits = ["?" for _ in range(BIT_WIDTH)]
q_solution_bits = ["?" for _ in range(BIT_WIDTH)]
MAX_ALLOWED_LOOKAHEAD = 100 # A safety valve

try:
    for k in range(BIT_WIDTH):
        lookahead_depth = 0
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
                break # Success, move to next bit
            
            lookahead_depth += 1
            if lookahead_depth > MAX_ALLOWED_LOOKAHEAD:
                print(f"\n\n❌ STRATEGY FAILURE at bit {k}: Max lookahead exceeded.")
                sys.exit(2)

    print_dashboard(start_time, BIT_WIDTH - 1, BIT_WIDTH, p_solution_bits, q_solution_bits, 0, "✅")
    print(f"\n\n[{time.time()-start_time:.2f}s] ✅ DEDUCTION COMPLETE: All factor bits determined.")
    
    p = CnfProvider.decode_bits(provider.p_bits, final_model)
    q = CnfProvider.decode_bits(provider.q_bits, final_model)
    solution = (p, q)

except KeyboardInterrupt:
    print("\n\nManually terminated.")
    sys.exit(1)

# === MILESTONE 3: FINAL REPORT ===
end_time = time.time()

if solution:
    p, q = solution
    print("\n" + "=" * 80)
    print(">>> MISSION ACCOMPLISHED: LOCK SHATTERED <<<")
    print(f"Total Time: {end_time - start_time:.4f} seconds.")
    print("=" * 80)
    print(f"\nFactor p:\n{p}")
    print(f"\nFactor q:\n{q}")
    
    print("\nVerifying...")
    if p * q == N:
        print("✅ VERIFICATION SUCCESSFUL")
    else:
        print("❌ VERIFICATION FAILED")