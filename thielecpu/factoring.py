# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

# thielecpu/factoring.py

from math import gcd, isqrt
import random

# --- NEW: Import the powerful sympy library for factoring ---
try:
    from sympy.ntheory import factorint
    SYMPY_AVAILABLE = True
except ImportError:
    SYMPY_AVAILABLE = False
    print("WARNING: sympy library not found. Factoring large numbers will be very slow or fail.")
    print("Install it with: pip install sympy")


def recover_factors_partitioned(n: int, show_progress: bool = True) -> tuple[int, int]:
    """
    Recovers the prime factors of n using the Thiele partitioning concept.
    
    In the Thiele Machine model, this function represents the outcome of
    a 'sighted' operation where the correct partition is discovered by
    paying a mu_discovery cost.
    
    For this *simulation*, we use a powerful classical factoring algorithm as an
    'oracle' to stand in for the discovery process. This allows us to measure
    the mu_operational cost of using the factors, which the Thiele model
    predicts is constant regardless of the size of n.
    """
    if n < 2:
        raise ValueError("Number to be factored must be greater than 1.")
    
    if show_progress:
        print(f"    Starting partition discovery for {n.bit_length()}-bit number...")
    
    if n % 2 == 0:
        if show_progress:
            print("    ✓ Found factor 2 (even number)")
        return 2, n // 2

    if SYMPY_AVAILABLE:
        try:
            if show_progress:
                print("    Using sympy's elliptic curve method...")
            # Use sympy's highly optimized factoring function. It returns a dict of {prime: exponent}.
            # For a typical two-prime composite we expect two primes, each with an exponent of 1.
            factors = factorint(n)
            factor_list = list(factors.items())
            if len(factor_list) == 2 and factor_list[0][1] == 1 and factor_list[1][1] == 1:
                p = int(factor_list[0][0])
                q = int(factor_list[1][0])
                if show_progress:
                    print(f"    ✓ Found prime factors: {p} and {q}")
                return (p, q) if p < q else (q, p)
            else:
                # Fallback for non-RSA numbers or if sympy gives an unexpected result
                p = int(factor_list[0][0])
                if show_progress:
                    print(f"    ✓ Found factor: {p}")
                return p, n // p
        except Exception as e:
            if show_progress:
                print(f"    sympy factoring failed with error: {e}. The number may be prime or very difficult.")
            raise ValueError(f"Factoring failed for n={n}") from e
    else:
        # If sympy is not available, fall back to the slower, less reliable Pollard's Rho
        # This will likely fail for numbers > 100 bits.
        if show_progress:
            print("    Falling back to Pollard's rho algorithm...")
        p = pollard_rho(n)
        if p == n:
            raise ValueError("Factoring failed: pollard_rho returned n, number may be prime.")
        if show_progress:
            print(f"    ✓ Found factor: {p}")
        return p, n // p


# Your original pollard_rho remains as a conceptual example of a "blind" algorithm.
def pollard_rho(n: int) -> int:
    """Pollard's rho algorithm for integer factorization."""
    if n % 2 == 0:
        return 2
    x = random.randint(1, n - 2)
    y = x
    c = random.randint(1, n - 1)
    d = 1
    
    f = lambda val: (val * val + c) % n

    # The progress printing from here is extremely verbose and slows things down.
    # We can remove it or reduce its frequency for benchmarks.
    # For now, let's keep it but recognize it's a bottleneck.
    
    step = 0
    max_steps = 2000000 # Increased limit
    
    while d == 1:
        x = f(x)
        y = f(f(y))
        d = gcd(abs(x - y), n)
        step += 1
        if step > max_steps:
             raise ValueError("Pollard's rho failed to find factor within iteration limit")

    if d == n:
        # This can happen. The algorithm can fail.
        # A more robust implementation would try again with a different starting x and c.
        raise ValueError("Pollard's rho failed to find factor (d == n)")
    
    return d
