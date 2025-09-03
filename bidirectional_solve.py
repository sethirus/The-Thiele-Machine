import time
import sys
import os
from scripts.multiplier_cnf_provider import CnfProvider
from scripts.thiele_simulator import ThieleSimulator

def load_live_n_from_file(filename):
    """Load N from a file containing the modulus"""
    try:
        with open(filename, 'r') as f:
            content = f.read().strip()
            # Try to parse as integer
            return int(content)
    except (FileNotFoundError, ValueError) as e:
        print(f"Error loading N from {filename}: {e}")
        return None

def print_dashboard(start_time, phase, bit_width=None, current_bit=None):
    """Render a simple dashboard"""
    elapsed = time.time() - start_time
    line = f"\r[{elapsed:8.2f}s] Phase: {phase}"
    if bit_width and current_bit is not None:
        progress = int(50 * (current_bit + 1) / bit_width)
        bar = '█' * progress + '-' * (50 - progress)
        line += f" [{bar}] Bit {current_bit+1}/{bit_width}"
    sys.stdout.write(line)
    sys.stdout.flush()

def main():
    if len(sys.argv) < 2:
        print("Usage: python bidirectional_solve.py <modulus_file> [bit_width]")
        print("  modulus_file: File containing the modulus N to factor")
        print("  bit_width: Optional bit width (default: 64)")
        sys.exit(1)

    modulus_file = sys.argv[1]
    bit_width = int(sys.argv[2]) if len(sys.argv) > 2 else 64

    start_time = time.time()

    print("=" * 120)
    print("Thiele Machine: Bidirectional Solve")
    print("=" * 120)

    # Load the modulus
    print(f"Loading modulus from: {modulus_file}")
    N = load_live_n_from_file(modulus_file)
    if N is None:
        print("Failed to load modulus. Exiting.")
        sys.exit(1)

    print(f"Target modulus: {N}")
    print(f"Bit width: {bit_width}")
    print(f"Number has {len(str(N))} digits")

    phase = "Setup"
    print_dashboard(start_time, phase)
    provider = CnfProvider(bit_width=bit_width, N=N)
    simulator = ThieleSimulator(provider)

    phase = "Load"
    # Load all output variables (lazy loading will handle the rest)
    for idx in range(min(provider.output_count(), 1000)):  # Limit for practicality
        simulator._add_var(provider.output_var(idx))
        if idx % 100 == 0:
            print_dashboard(start_time, phase, bit_width, idx)

    print_dashboard(start_time, phase, bit_width, min(provider.output_count(), 1000) - 1)

    phase = "Solve"
    print_dashboard(start_time, phase)
    solution = simulator.solve()

    end_time = time.time()

    if solution:
        p = CnfProvider.decode_bits(provider.p_bits, solution)
        q = CnfProvider.decode_bits(provider.q_bits, solution)

        print("\n" + "=" * 80)
        print(">>> MISSION ACCOMPLISHED: FACTORS FOUND <<<")
        print(f"Total Time: {end_time - start_time:.4f} seconds.")
        print("=" * 80)
        print(f"\nFactor p:\n{p}")
        print(f"\nFactor q:\n{q}")

        # Add verification
        print("\nVerifying result...")
        if p * q == N:
            print("✅ VERIFICATION SUCCESSFUL: p * q = N")
        else:
            print("❌ VERIFICATION FAILED: p * q != N")
            print(f"p * q = {p * q}")
            print(f"N = {N}")
    else:
        print("\n" + "=" * 80)
        print(">>> MISSION FAILED: NO SOLUTION FOUND <<<")
        print(f"Total Time: {end_time - start_time:.4f} seconds.")
        print("=" * 80)

if __name__ == "__main__":
    main()
