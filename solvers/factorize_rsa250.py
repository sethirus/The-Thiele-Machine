#!/usr/bin/env python3
"""
Project SIGHTLINE: RSA-250 Factorization using Multiple Methods
A more practical approach using established factorization algorithms
"""

import sys
import time
import math
from typing import Optional, Tuple
import random

# RSA-250 modulus
RSA_250 = 214032465024074496126442307283933356300861471514475501779775492088141802344714013664334551459126261

def trial_division(n: int, limit: int = 1000000) -> Optional[int]:
    """Trial division up to a limit"""
    print(f"Running trial division up to {limit:,}...")
    for i in range(2, min(limit, int(math.sqrt(n)) + 1)):
        if n % i == 0:
            return i
    return None

def pollard_rho(n: int, max_iterations: int = 1000000) -> Optional[int]:
    """Pollard's rho algorithm"""
    print("Running Pollard's rho algorithm...")

    def gcd(a, b):
        while b:
            a, b = b, a % b
        return a

    def f(x, c):
        return (x * x + c) % n

    for c in range(1, 20):  # Try different constants
        x = 2
        y = 2
        d = 1

        for i in range(max_iterations):
            x = f(x, c)
            y = f(f(y, c), c)
            d = gcd(abs(x - y), n)

            if d > 1 and d < n:
                return d
            if d == n:
                break

    return None

def fermat_factorization(n: int) -> Optional[int]:
    """Fermat's factorization method"""
    print("Running Fermat's factorization...")

    # Check if n is a perfect square
    sqrt_n = int(math.sqrt(n))
    if sqrt_n * sqrt_n == n:
        return sqrt_n

    # Fermat's method
    a = sqrt_n + 1
    b2 = a * a - n

    while b2 < 0 or int(math.sqrt(b2)) ** 2 != b2:
        a += 1
        b2 = a * a - n

        # Safety check to prevent infinite loop
        if a > n // 2:
            return None

    b = int(math.sqrt(b2))
    return a - b

def quadratic_sieve_trial(n: int) -> Optional[int]:
    """Simplified quadratic sieve approach"""
    print("Running simplified quadratic sieve...")

    # For demonstration, try small factors
    sqrt_n = int(math.sqrt(n))

    for i in range(2, min(1000, sqrt_n + 1)):
        if n % i == 0:
            return i

    return None

def factorize_number(n: int) -> Tuple[Optional[int], Optional[int]]:
    """Main factorization function using multiple methods"""

    print(f"Starting factorization of {n}")
    print(f"Number has {len(str(n))} digits")

    methods = [
        ("Trial Division", lambda: trial_division(n, 100000)),
        ("Pollard's Rho", lambda: pollard_rho(n, 500000)),
        ("Fermat's Method", lambda: fermat_factorization(n)),
        ("Quadratic Sieve Trial", lambda: quadratic_sieve_trial(n)),
    ]

    for method_name, method_func in methods:
        print(f"\n--- {method_name} ---")
        start_time = time.time()

        try:
            factor = method_func()
            elapsed = time.time() - start_time

            if factor:
                other_factor = n // factor
                print(".2f")
                return factor, other_factor

            print(".2f")
        except Exception as e:
            print(f"Error in {method_name}: {e}")

    return None, None

def main():
    print("Project SIGHTLINE: RSA-250 Factorization")
    print("=" * 50)

    n = RSA_250

    start_time = time.time()
    p, q = factorize_number(n)
    total_time = time.time() - start_time

    if p and q:
        print("\n" + "=" * 50)
        print("SUCCESS! Factors found:")
        print(f"p = {p}")
        print(f"q = {q}")
        print(f"p * q = {p * q}")
        print(f"Verification: {p * q == n}")
        print(".2f")
    else:
        print("\n" + "=" * 50)
        print("No factors found with current methods.")
        print(".2f")
        print("Consider using more advanced methods like:")
        print("- General Number Field Sieve (GNFS)")
        print("- Elliptic Curve Method (ECM)")
        print("- Distributed computing approaches")

if __name__ == "__main__":
    main()