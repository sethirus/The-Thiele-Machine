# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
RSA Scaling Demo for Thiele Machine

Generates synthetic RSA-like composites of various sizes and measures
μ_discovery + μ_operational costs using pure Thiele operations.
"""

import sys
import os
import random
import json
import matplotlib.pyplot as plt
import numpy as np

# Add parent directory to path
sys.path.insert(0, os.path.dirname(os.path.dirname(__file__)))

from thielecpu.state import State
from thielecpu.mdl import mdlacc
from thielecpu._types import ModuleId

def generate_blum_integer(bits):
    """Generate a Blum integer (product of two primes ≡ 3 mod 4)."""
    while True:
        # Generate two random primes
        p = random_prime(bits // 2)
        q = random_prime(bits // 2)
        if p % 4 == 3 and q % 4 == 3:
            return p * q

def random_prime(bits):
    """Generate a random prime of specified bit length."""
    while True:
        n = random.getrandbits(bits)
        if n.bit_length() == bits and is_prime(n):
            return n

def is_prime(n, k=5):
    """Miller-Rabin primality test."""
    if n <= 1:
        return False
    if n <= 3:
        return True
    if n % 2 == 0:
        return False

    # Write n-1 as 2^r * d
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2

    # Witness loop
    for _ in range(k):
        a = random.randint(2, n - 2)
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True

def thiele_trial_division(state: State, composite: int, timeout_seconds: int = 30):
    """Pure Thiele operations for trial division factoring with timeout."""
    import time
    factors = []
    n = composite
    start_time = time.time()

    # Simple trial division (simplified for demo)
    for i in range(2, int(n**0.5) + 1):
        # Check timeout
        if time.time() - start_time > timeout_seconds:
            print(f"  Timeout after {timeout_seconds}s - charging ∞ μ")
            state.mu = float('inf')  # Charge infinite μ for timeout
            return []

        if n % i == 0:
            # Found factor - create verification partition
            verify_module = state.pnew(set(range(100, 110)))  # Non-overlapping region
            mdlacc(state, verify_module, consistent=True)

            factors = [i, n // i]
            break

    return factors

def measure_rsa_cost(bits: int, trials: int = 3):
    # Reduce trials for larger bit sizes to keep runtime reasonable
    if bits > 32:
        trials = 2
    if bits > 48:
        trials = 1

    # Set timeout based on bit size (longer for smaller problems)
    timeout = 60 if bits <= 32 else 30 if bits <= 48 else 10

    """Measure μ costs for factoring RSA-like composites of given bit size."""
    results = []

    for trial in range(trials):
        # Generate synthetic composite
        composite = generate_blum_integer(bits)
        print(f"Trial {trial + 1}: {bits}-bit composite = {composite}")

        # Initialize Thiele state
        state = State()
        initial_mu = state.mu

        # Discovery phase: trial division
        factors = thiele_trial_division(state, composite, timeout_seconds=timeout)
        discovery_mu = state.mu - initial_mu if state.mu != float('inf') else float('inf')

        # Operational phase: verification
        operational_mu = 0
        if factors and len(factors) == 2:
            # Verify factors multiply to original
            p, q = factors
            if p * q == composite:
                operational_mu = bits  # Bit length as proxy
                state.mu += operational_mu

        total_mu = state.mu
        result = {
            "bits": bits,
            "composite": composite,
            "factors": factors,
            "mu_discovery": discovery_mu,
            "mu_operational": operational_mu,
            "mu_total": total_mu,
            "success": len(factors) == 2 and factors[0] * factors[1] == composite
        }
        results.append(result)

    # Average results
    avg_result = {
        "bits": bits,
        "avg_mu_discovery": np.mean([r["mu_discovery"] for r in results]),
        "avg_mu_operational": np.mean([r["mu_operational"] for r in results]),
        "avg_mu_total": np.mean([r["mu_total"] for r in results]),
        "success_rate": sum(r["success"] for r in results) / len(results),
        "trials": results
    }

    return avg_result

def run_scaling_experiment():
    """Run scaling experiment for various bit sizes."""
    bit_sizes = [12, 16, 20, 24, 28, 32, 40, 48, 56, 64]  # Extended range
    results = []

    print("RSA Scaling Experiment")
    print("=" * 30)

    for bits in bit_sizes:
        print(f"\nTesting {bits}-bit composites...")
        result = measure_rsa_cost(bits, trials=2)  # Reduced trials for speed
        results.append(result)
        print(".2e")

    # Save results
    with open("rsa_scaling_results.json", "w") as f:
        json.dump(results, f, indent=2)

    # Generate plots
    plot_scaling_results(results)

    return results

def plot_scaling_results(results):
    """Plot scaling results."""
    bits = [r["bits"] for r in results]
    mu_discovery = [r["avg_mu_discovery"] for r in results]
    mu_operational = [r["avg_mu_operational"] for r in results]
    mu_total = [r["avg_mu_total"] for r in results]

    plt.figure(figsize=(12, 8))

    # μ discovery vs bits
    plt.subplot(2, 2, 1)
    plt.plot(bits, mu_discovery, 'o-', label='μ_discovery')
    plt.xlabel('Bits')
    plt.ylabel('μ_discovery')
    plt.title('Discovery Cost vs Bit Size')
    plt.grid(True, alpha=0.3)

    # μ operational vs bits
    plt.subplot(2, 2, 2)
    plt.plot(bits, mu_operational, 'o-', label='μ_operational', color='orange')
    plt.xlabel('Bits')
    plt.ylabel('μ_operational')
    plt.title('Operational Cost vs Bit Size')
    plt.grid(True, alpha=0.3)

    # Total μ vs bits
    plt.subplot(2, 2, 3)
    plt.plot(bits, mu_total, 'o-', label='μ_total', color='green')
    plt.xlabel('Bits')
    plt.ylabel('μ_total')
    plt.title('Total Cost vs Bit Size')
    plt.grid(True, alpha=0.3)

    # Log-log plot
    plt.subplot(2, 2, 4)
    plt.loglog(bits, mu_total, 'o-', label='μ_total', color='red')
    plt.xlabel('Bits (log)')
    plt.ylabel('μ_total (log)')
    plt.title('Total Cost vs Bit Size (log-log)')
    plt.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig("rsa_scaling_plots.png", dpi=150, bbox_inches='tight')
    print("Plots saved to rsa_scaling_plots.png")

if __name__ == "__main__":
    random.seed(42)  # For reproducibility
    results = run_scaling_experiment()

    print("\nScaling Results Summary:")
    for r in results:
        print(f"{r['bits']:2d} bits: μ_total = {r['avg_mu_total']:.2e}, success = {r['success_rate']:.1%}")