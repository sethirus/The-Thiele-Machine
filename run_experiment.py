import multiprocessing
import time
import random
import math
from typing import List, Tuple, Optional

from scripts.multiplier_cnf_provider import CnfProvider, RSA_250_N
from scripts.thiele_simulator import ThieleSimulator


# --- Pollard's Rho Factoring Algorithm -------------------------------------------------
def pollards_rho(n: int, max_iterations: int = 100000) -> Optional[int]:
    """Pollard's rho algorithm for factoring. Returns a non-trivial factor or None."""
    if n % 2 == 0:
        return 2

    # Simple polynomial: x^2 + c mod n
    def polynomial(x, c):
        return (x * x + c) % n

    for c in range(1, 20):  # Try different constants
        x = 2
        y = 2
        d = 1

        for i in range(max_iterations):
            x = polynomial(x, c)
            y = polynomial(polynomial(y, c), c)
            d = math.gcd(abs(x - y), n)

            if d > 1 and d < n:
                return d

            if i % 1000 == 0 and i > 0:
                # Check if we're stuck
                if x == y:
                    break

    return None


# --- Brent's Cycle Detection for Pollard's Rho -------------------------------------------------
def pollards_rho_brent(n: int, max_iterations: int = 100000) -> Optional[int]:
    """Pollard's rho with Brent's cycle detection for better performance."""
    if n % 2 == 0:
        return 2
    if n % 3 == 0:
        return 3

    y = random.randint(1, n - 1)
    c = random.randint(1, n - 1)
    m = random.randint(1, n - 1)

    g = 1
    r = 1
    q = 1

    while g == 1:
        x = y
        for _ in range(r):
            y = (y * y + c) % n

        k = 0
        while k < r and g == 1:
            ys = y
            for _ in range(min(m, r - k)):
                y = (y * y + c) % n
                q = (q * abs(x - y)) % n
            g = math.gcd(q, n)
            k += m

        r *= 2

        if max_iterations and r > max_iterations:
            break

    if g == n:
        return None  # Failed to find factor
    return g


# --- Lenstra Elliptic Curve Method -------------------------------------------------
def lenstra_ecm(n: int, max_curves: int = 50, max_iterations: int = 10000) -> Optional[int]:
    """Lenstra's Elliptic Curve Method for factoring."""
    def mul_mod(a, b, mod):
        return (a * b) % mod

    def elliptic_add(p1, p2, a, mod):
        if p1 is None:
            return p2
        if p2 is None:
            return p1

        x1, y1 = p1
        x2, y2 = p2

        if x1 == x2 and (y1 + y2) % mod == 0:
            return None  # Point at infinity

        if x1 == x2:
            # Point doubling
            lam = mul_mod(3 * x1 * x1 + a, mod_inverse(2 * y1, mod), mod)
        else:
            # Point addition
            lam = mul_mod(y2 - y1, mod_inverse(x2 - x1, mod), mod)

        x3 = (lam * lam - x1 - x2) % mod
        y3 = (lam * (x1 - x3) - y1) % mod
        return (x3, y3)

    def mod_inverse(a, m):
        m0, y, x = m, 0, 1
        if m == 1:
            return 0
        while a > 1:
            q = a // m
            m, a = a % m, m
            y, x = x - q * y, y
        if x < 0:
            x += m0
        return x

    for _ in range(max_curves):
        # Random curve parameters
        a = random.randint(0, n - 1)
        x = random.randint(0, n - 1)
        y = random.randint(0, n - 1)

        # Starting point
        p = (x, y)

        for i in range(2, max_iterations):
            try:
                # Scalar multiplication by i
                result = None
                temp = p
                while i > 0:
                    if i % 2 == 1:
                        result = elliptic_add(result, temp, a, n)
                    temp = elliptic_add(temp, temp, a, n)
                    i //= 2

                if result is None:
                    continue

                # Check for factorization
                x_coord = result[0]
                if x_coord != 0:
                    g = math.gcd(x_coord, n)
                    if g > 1 and g < n:
                        return g

            except (ZeroDivisionError, ValueError):
                # If we get an error (like division by zero), try next curve
                break

    return None


# --- Trial Division with Optimizations -------------------------------------------------
def trial_division_optimized(n: int, limit: int = 1000000) -> Optional[int]:
    """Optimized trial division with small prime checks."""
    if n % 2 == 0:
        return 2
    if n % 3 == 0:
        return 3

    # Check divisibility by 6k±1 up to sqrt(n)
    i = 5
    while i * i <= min(n, limit):
        if n % i == 0:
            return i
        if n % (i + 2) == 0:
            return i + 2
        i += 6

    return None


# --- Complete Factoring Function -------------------------------------------------
def factor_number(n: int) -> List[int]:
    """Complete factoring using multiple algorithms."""
    factors = []
    remaining = n

    # Quick checks
    while remaining % 2 == 0:
        factors.append(2)
        remaining //= 2
    while remaining % 3 == 0:
        factors.append(3)
        remaining //= 3

    # Try trial division first
    factor = trial_division_optimized(remaining, 100000)
    if factor:
        factors.append(factor)
        remaining //= factor

    # Try Pollard's rho
    if remaining > 1:
        factor = pollards_rho_brent(remaining, 50000)
        if factor:
            factors.append(factor)
            remaining //= factor

    # Try ECM for remaining factors
    while remaining > 1:
        if remaining < 1000000:  # Small enough for trial division
            for i in range(2, int(math.sqrt(remaining)) + 1):
                if remaining % i == 0:
                    factors.append(i)
                    remaining //= i
                    break
            else:
                factors.append(remaining)
                break
        else:
            factor = lenstra_ecm(remaining, 20, 5000)
            if factor:
                factors.append(factor)
                remaining //= factor
            else:
                # Give up on very large factors
                factors.append(remaining)
                break

    return sorted(factors)


# --- Algorithm Comparison Function -------------------------------------------------
def compare_algorithms():
    """Compare different factoring algorithms on various numbers."""
    test_numbers = [
        15,      # 3 * 5
        21,      # 3 * 7
        33,      # 3 * 11
        35,      # 5 * 7
        77,      # 7 * 11
        143,     # 11 * 13
        323,     # 17 * 19
        899,     # 29 * 31
        1763,    # 41 * 43
        3599,    # 59 * 61
    ]

    print("\n" + "="*80)
    print("ALGORITHM COMPARISON: Classical Factoring vs SAT Approach")
    print("="*80)

    algorithms = [
        ("Trial Division", trial_division_optimized),
        ("Pollard's Rho", pollards_rho_brent),
        ("ECM", lenstra_ecm),
        ("Complete Factor", factor_number),
    ]

    for num in test_numbers:
        print(f"\nFactoring {num}:")
        print("-" * 30)

        for name, algorithm in algorithms:
            start_time = time.time()
            try:
                if name == "Complete Factor":
                    result = algorithm(num)
                    elapsed = time.time() - start_time
                    print(f"  {name:15}: {result} ({elapsed:.4f}s)")
                else:
                    result = algorithm(num, 10000)  # 10k iterations limit
                    elapsed = time.time() - start_time
                    if result:
                        print(f"  {name:15}: {result} ({elapsed:.4f}s)")
                    else:
                        print(f"  {name:15}: No factor found ({elapsed:.4f}s)")
            except (ValueError, ZeroDivisionError, OverflowError) as e:
                elapsed = time.time() - start_time
                print(f"  {name:15}: Error - {e} ({elapsed:.4f}s)")

    print("\n" + "="*80)
    print("PERFORMANCE ANALYSIS:")
    print("- Trial Division: Fast for small factors, slow for large")
    print("- Pollard's Rho: Good general-purpose algorithm")
    print("- ECM: Excellent for finding medium-sized factors")
    print("- SAT Approach: Exponential time, but can find any factor")
    print("- For RSA-250: GNFS (General Number Field Sieve) is fastest")
    print("="*80)


# --- SAT vs Classical Algorithm Comparison -------------------------------------------------
def sat_vs_classical_comparison():
    """Compare SAT-based factoring with classical algorithms."""
    print("\n" + "="*80)
    print("SAT-BASED FACTORING vs CLASSICAL ALGORITHMS")
    print("="*80)

    # Test on a small number that SAT can handle
    test_n = 77  # 7 * 11

    print(f"Testing factorization of {test_n} = {7} × {11}")
    print()

    # Classical approach
    print("CLASSICAL APPROACH:")
    start_time = time.time()
    factors = factor_number(test_n)
    classical_time = time.time() - start_time
    print(f"  Factors found: {factors}")
    print(".4f")
    print()

    # SAT approach
    print("SAT-BASED APPROACH:")
    start_time = time.time()

    try:
        provider = CnfProvider(bit_width=16, N=test_n)  # Small enough for SAT
        simulator = ThieleSimulator(provider)

        # Try different assumptions
        p_top = [provider.p_bits[15], provider.p_bits[14]]
        q_top = [provider.q_bits[15], provider.q_bits[14]]

        sat_attempts = 0
        solution = None

        for p_msb in (-1, 1):
            for p_next in (-1, 1):
                for q_msb in (-1, 1):
                    for q_next in (-1, 1):
                        assumptions = [p_msb * p_top[0], p_next * p_top[1],
                                     q_msb * q_top[0], q_next * q_top[1]]
                        sat_attempts += 1
                        solution = simulator.solve(assumptions=assumptions)
                        if solution:
                            break
                    if solution:
                        break
                if solution:
                    break
            if solution:
                break

        sat_time = time.time() - start_time

        if solution:
            p, q = solution
            print(f"  Factors found: {p}, {q}")
            print(".4f")
            print(f"  SAT attempts: {sat_attempts}")
        else:
            print("  No solution found")
            print(".4f")
            print(f"  SAT attempts: {sat_attempts}")

        print()
        print("COMPARISON:")
        if solution:
            speedup = sat_time / classical_time
            print(".2f")
            print(".1f")
        else:
            print("  SAT approach failed to find factors")
            print("  Classical approach succeeded")

    except ImportError as e:
        print(f"  PySAT not available: {e}")
        print(".4f")
        print("  SAT approach cannot be tested without PySAT")
        print()
        print("COMPARISON:")
        print("  Classical approach succeeded")
        print("  SAT approach requires PySAT installation")

    print("\nCONCLUSION:")
    print("- Classical algorithms are optimized for factoring")
    print("- SAT can solve any problem but is often slower")
    print("- The Thiele Machine demonstrates the concept")
    print("- Real factoring uses specialized algorithms like GNFS")


# --- The Worker Process -------------------------------------------------
def solve_worker(assumptions: List[int], result_queue: multiprocessing.Queue) -> None:
    """Solve the CNF under the given assumptions and report any solution."""
    try:
        provider = CnfProvider(bit_width=415, N=RSA_250_N)
        simulator = ThieleSimulator(provider)
        solution = simulator.solve(assumptions=assumptions)
        if solution:
            p, q = solution
            result_queue.put((p, q))
    except Exception:
        # Ignore failures so a single worker can't kill the pool
        pass


# --- Main execution -----------------------------------------------------
if __name__ == "__main__":
    print("The Thiele Machine - Algorithm Comparison Demo")
    print("=" * 60)

    # Run algorithm comparison (doesn't require PySAT)
    print("Running classical algorithm comparison...")
    compare_algorithms()

    print("\n" + "="*60)
    print("Running SAT vs Classical comparison...")
    sat_vs_classical_comparison()

    print("\n" + "="*60)
    print("DEMO COMPLETE")
    print("The script demonstrates:")
    print("- Classical factoring algorithms (Pollard's Rho, ECM, etc.)")
    print("- Performance comparison between different approaches")
    print("- SAT-based factoring concepts (requires PySAT for full demo)")
    print("="*60)
