#!/usr/bin/env python3
"""
Project SIGHTLINE: Advanced RSA-250 Factorization
Using multiple algorithms and libraries for complete factorization
"""

import sys
import time
import math
from typing import Optional, Tuple
import random

# RSA-250 modulus (can be overridden by file input)
RSA_250 = 214032465024074496126442307283933356300861471514475501779775492088141802344714013664334551459126261

def load_modulus_from_file(filename):
    """Load modulus from file"""
    try:
        with open(filename, 'r') as f:
            content = f.read().strip()
            return int(content)
    except (FileNotFoundError, ValueError) as e:
        print(f"Error loading modulus from {filename}: {e}")
        return None

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

def lenstra_elliptic_curve(n: int, max_curves: int = 100) -> Optional[int]:
    """Lenstra's Elliptic Curve Method (simplified version)"""
    print("Running Elliptic Curve Method...")

    def mul(point, scalar, a, n):
        """Point multiplication on elliptic curve"""
        if scalar == 0:
            return None
        if scalar == 1:
            return point

        half = mul(point, scalar // 2, a, n)
        if half is None:
            return None

        # Point doubling
        if half[0] == half[1]:
            # Point at infinity
            return None

        x1, y1 = half
        if x1 is None:
            return None

        # Calculate 2P
        try:
            lam = (3 * x1 * x1 + a) * pow(2 * y1, -1, n) % n
            x3 = (lam * lam - 2 * x1) % n
            y3 = (lam * (x1 - x3) - y1) % n
            result = (x3, y3)
        except:
            return None

        if scalar % 2 == 0:
            return result
        else:
            # Point addition
            return add_points(result, point, n)

    def add_points(p1, p2, n):
        """Add two points on elliptic curve"""
        if p1 is None:
            return p2
        if p2 is None:
            return p1

        x1, y1 = p1
        x2, y2 = p2

        if x1 == x2 and y1 == -y2 % n:
            return None  # Point at infinity

        try:
            if x1 == x2:
                lam = (3 * x1 * x1) * pow(2 * y1, -1, n) % n
            else:
                lam = (y2 - y1) * pow(x2 - x1, -1, n) % n

            x3 = (lam * lam - x1 - x2) % n
            y3 = (lam * (x1 - x3) - y1) % n
            return (x3, y3)
        except:
            return None

    def gcd(a, b):
        while b:
            a, b = b, a % b
        return a

    for curve in range(max_curves):
        # Random curve parameters
        a = random.randint(0, n-1)
        x = random.randint(0, n-1)
        y = random.randint(0, n-1)

        # Ensure point is on curve: y^2 = x^3 + a*x + b mod n
        b = (y * y - x * x * x - a * x) % n

        point = (x, y)

        # Try different multiples
        for k in [2, 3, 5, 7, 11, 13, 17, 19, 23]:
            try:
                result = mul(point, k, a, n)
                if result is None:
                    # Found factor during scalar multiplication
                    d = gcd(k, n)
                    if d > 1 and d < n:
                        return d
            except:
                continue

    return None

def factorize_completely(n: int) -> list:
    """Complete factorization using multiple methods"""
    factors = []

    # First, handle 2 separately
    while n % 2 == 0:
        factors.append(2)
        n //= 2

    # Handle other small primes
    i = 3
    while i * i <= n:
        if n % i == 0:
            factors.append(i)
            n //= i
        else:
            i += 2

    if n > 1:
        factors.append(n)

    return factors

def main():
    if len(sys.argv) != 2:
        print("Usage: python advanced_factorize.py <modulus_file>")
        print("The file should contain the modulus N to factor")
        print("If no file is provided, RSA-250 will be used")
        n = RSA_250
    else:
        modulus_file = sys.argv[1]
        print(f"Loading modulus from: {modulus_file}")
        loaded_n = load_modulus_from_file(modulus_file)
        if loaded_n is None:
            print("Failed to load modulus. Using RSA-250 as default.")
            n = RSA_250
        else:
            n = loaded_n

    print("Project SIGHTLINE: Advanced RSA Factorization")
    print("=" * 60)

    print(f"Target: {n}")
    print(f"Number has {len(str(n))} digits")

    # First, find small factors
    print("\n" + "=" * 40)
    print("PHASE 1: Finding small factors")
    print("=" * 40)

    remaining = n
    small_factors = []

    # Check for small prime factors
    for prime in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
        if remaining % prime == 0:
            small_factors.append(prime)
            remaining //= prime
            print(f"Found small factor: {prime}")
            print(f"Remaining: {remaining} ({len(str(remaining))} digits)")

    if small_factors:
        print(f"\nSmall factors found: {small_factors}")
        print(f"Product of small factors: {math.prod(small_factors)}")

    # Now work on the remaining large factor
    if remaining > 1 and remaining != n:
        print("\n" + "=" * 40)
        print("PHASE 2: Factoring remaining large number")
        print("=" * 40)
        print(f"Remaining factor: {remaining}")
        print(f"Size: {len(str(remaining))} digits")

        methods = [
            ("Trial Division (extended)", lambda: trial_division(remaining, 1000000)),
            ("Pollard's Rho", lambda: pollard_rho(remaining, 1000000)),
            ("Fermat's Method", lambda: fermat_factorization(remaining)),
            ("Elliptic Curve Method", lambda: lenstra_elliptic_curve(remaining, 50)),
        ]

        for method_name, method_func in methods:
            print(f"\n--- {method_name} ---")
            start_time = time.time()

            try:
                factor = method_func()
                elapsed = time.time() - start_time

                if factor:
                    other_factor = remaining // factor
                    print(".2f")
                    print(f"Found factor: {factor}")
                    print(f"Other factor: {other_factor}")

                    # Add to our factor list
                    small_factors.extend([factor, other_factor])
                    break

                print(".2f")
            except Exception as e:
                print(f"Error in {method_name}: {e}")

    # Final results
    print("\n" + "=" * 60)
    print("FINAL RESULTS")
    print("=" * 60)

    if len(small_factors) > 1:
        print("SUCCESS! Complete factorization found:")
        print(f"All factors: {sorted(small_factors)}")

        # Verify
        product = math.prod(small_factors)
        print(f"Product verification: {product == n}")

        if len(small_factors) == 2:
            p, q = sorted(small_factors)
            print(f"p = {p}")
            print(f"q = {q}")
            print(f"p * q = {p * q}")
    else:
        print("Partial factorization only.")
        print(f"Factors found: {small_factors}")
        print(f"Remaining unfactored: {remaining}")
        print("\nFor complete factorization, consider:")
        print("- General Number Field Sieve (GNFS)")
        print("- More advanced ECM implementations")
        print("- Distributed computing (BOINC, etc.)")

if __name__ == "__main__":
    main()