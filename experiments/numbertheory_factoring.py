#!/usr/bin/env python3
"""
Number-Theoretic SMT Encoding for Factoring

Key insight: The factors p, q have STRUCTURE we can encode:
1. They're prime (not just any integers)
2. Euler's theorem: a^φ(N) ≡ 1 (mod N) where φ(N) = (p-1)(q-1)
3. Order of elements divides φ(N)

What if we encode this structure and let Z3 exploit it?
"""

import time
import math
from z3 import *


def factor_with_primality_hints(n: int, timeout_ms: int = 60000) -> dict:
    """
    Factor with explicit primality encoding.
    
    We can't tell Z3 "p is prime" directly, but we CAN encode:
    - p is odd (unless p = 2)
    - p is not divisible by small primes
    """
    start = time.time()
    
    p = Int('p')
    q = Int('q')
    
    solver = Solver()
    solver.set("timeout", timeout_ms)
    
    sqrt_n = int(math.isqrt(n)) + 1
    
    # Basic constraints
    solver.add(p >= 2)
    solver.add(p <= sqrt_n)
    solver.add(q >= p)
    solver.add(p * q == n)
    
    # Primality hints: p and q are not divisible by small primes
    # This eliminates many false candidates
    small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]
    for sp in small_primes:
        if n % sp != 0:  # If N isn't divisible by sp, neither is p or q
            solver.add(p % sp != 0)
            solver.add(q % sp != 0)
    
    # Also: if p > 2, p is odd
    solver.add(Or(p == 2, p % 2 == 1))
    solver.add(Or(q == 2, q % 2 == 1))
    
    result = solver.check()
    elapsed = time.time() - start
    
    if result == sat:
        model = solver.model()
        p_val = model[p].as_long()
        q_val = model[q].as_long()
        return {
            "success": True,
            "factors": (p_val, q_val),
            "time_s": elapsed,
            "method": "primality_hints"
        }
    else:
        return {"success": False, "result": str(result), "time_s": elapsed}


def factor_with_euler_structure(n: int, timeout_ms: int = 60000) -> dict:
    """
    Encode Euler's theorem structure.
    
    If N = pq, then φ(N) = (p-1)(q-1)
    And for any a coprime to N: a^φ(N) ≡ 1 (mod N)
    
    We encode: Find p, q such that 2^((p-1)(q-1)) mod N = 1
    """
    start = time.time()
    
    # First compute some residues of 2^k mod N
    # If we find k where 2^k ≡ 1, then k is a multiple of the order
    # and the order divides φ(N) = (p-1)(q-1)
    
    # Find the order of 2 mod N (or a multiple of it)
    k = 1
    power = 2
    max_k = min(n, 100000)
    found_order = None
    
    while k < max_k:
        if power == 1:
            found_order = k
            break
        power = (power * 2) % n
        k += 1
    
    if found_order is None:
        return {"success": False, "result": "order_not_found", "time_s": time.time() - start}
    
    # Now we know: order of 2 divides (p-1)(q-1)
    # So (p-1)(q-1) is a multiple of found_order
    
    p = Int('p')
    q = Int('q')
    phi = Int('phi')
    k_mult = Int('k')
    
    solver = Solver()
    solver.set("timeout", timeout_ms)
    
    sqrt_n = int(math.isqrt(n)) + 1
    
    # Basic constraints
    solver.add(p >= 2)
    solver.add(p <= sqrt_n)
    solver.add(q >= p)
    solver.add(p * q == n)
    
    # Euler structure
    solver.add(phi == (p - 1) * (q - 1))
    solver.add(k_mult >= 1)
    solver.add(phi == k_mult * found_order)
    
    result = solver.check()
    elapsed = time.time() - start
    
    if result == sat:
        model = solver.model()
        p_val = model[p].as_long()
        q_val = model[q].as_long()
        return {
            "success": True,
            "factors": (p_val, q_val),
            "time_s": elapsed,
            "method": "euler_structure",
            "order": found_order
        }
    else:
        return {"success": False, "result": str(result), "time_s": elapsed, "order": found_order}


def factor_with_order_divisibility(n: int, timeout_ms: int = 60000) -> dict:
    """
    Use multiple orders to constrain φ(N).
    
    Key insight: If we find orders of several bases, their LCM divides φ(N).
    This constrains (p-1)(q-1) severely.
    """
    start = time.time()
    
    # Find orders of several small bases
    orders = []
    for base in [2, 3, 5, 7]:
        if math.gcd(base, n) != 1:
            # Base shares a factor with N - we found it!
            g = math.gcd(base, n)
            return {
                "success": True,
                "factors": (g, n // g),
                "time_s": time.time() - start,
                "method": "gcd_lucky"
            }
        
        # Find order
        k = 1
        power = base
        max_k = min(n, 50000)
        while k < max_k:
            if power == 1:
                orders.append(k)
                break
            power = (power * base) % n
            k += 1
    
    if not orders:
        return {"success": False, "result": "no_orders_found", "time_s": time.time() - start}
    
    # LCM of orders divides φ(N)
    from functools import reduce
    def lcm(a, b):
        return abs(a * b) // math.gcd(a, b)
    
    order_lcm = reduce(lcm, orders)
    
    # Now: (p-1)(q-1) is a multiple of order_lcm
    # Also: (p-1)(q-1) = pq - p - q + 1 = N - p - q + 1
    # So: p + q = N + 1 - (p-1)(q-1) = N + 1 - k*order_lcm for some k
    
    # Additionally: (p-1) and (q-1) must each have order_lcm as a divisor
    # in a specific way...
    
    p = Int('p')
    q = Int('q')
    phi = Int('phi')
    k_mult = Int('k')
    
    solver = Solver()
    solver.set("timeout", timeout_ms)
    
    sqrt_n = int(math.isqrt(n)) + 1
    
    # Basic constraints
    solver.add(p >= 2)
    solver.add(p <= sqrt_n)
    solver.add(q >= p)
    solver.add(p * q == n)
    
    # Structure from orders
    solver.add(phi == (p - 1) * (q - 1))
    solver.add(k_mult >= 1)
    solver.add(k_mult * order_lcm <= phi)  # phi is a multiple of lcm
    solver.add(phi % order_lcm == 0)  # Make it explicit
    
    result = solver.check()
    elapsed = time.time() - start
    
    if result == sat:
        model = solver.model()
        p_val = model[p].as_long()
        q_val = model[q].as_long()
        return {
            "success": True,
            "factors": (p_val, q_val),
            "time_s": elapsed,
            "method": "order_divisibility",
            "orders": orders,
            "lcm": order_lcm
        }
    else:
        return {
            "success": False, 
            "result": str(result), 
            "time_s": elapsed,
            "orders": orders,
            "lcm": order_lcm
        }


def factor_chinese_remainder(n: int, timeout_ms: int = 60000) -> dict:
    """
    Use Chinese Remainder Theorem structure.
    
    Key insight: Z_N ≅ Z_p × Z_q when N = pq
    This means any x mod N is determined by (x mod p, x mod q)
    
    If we find x where x² ≡ 1 (mod N) but x ≢ ±1 (mod N),
    then gcd(x-1, N) or gcd(x+1, N) is a factor.
    """
    start = time.time()
    
    # Find non-trivial square roots of 1 mod N
    # This is essentially what Miller-Rabin primality test uses
    
    # For N = pq, there are 4 square roots of 1: ±1, and two more
    # The non-trivial ones reveal the factorization
    
    # Random search for x where x² ≡ 1 but x ≢ ±1
    import random
    random.seed(42)
    
    for _ in range(1000):
        # Generate random a, compute a^((N-1)/2) mod N
        a = random.randint(2, n - 2)
        
        # Find highest power of 2 dividing n-1
        d = n - 1
        s = 0
        while d % 2 == 0:
            d //= 2
            s += 1
        
        # Compute a^d mod n
        x = pow(a, d, n)
        
        if x == 1 or x == n - 1:
            continue
        
        # Square repeatedly
        for _ in range(s - 1):
            prev_x = x
            x = (x * x) % n
            
            if x == 1:
                # prev_x² = 1 but prev_x ≠ ±1
                # So gcd(prev_x - 1, N) or gcd(prev_x + 1, N) is a factor
                g1 = math.gcd(prev_x - 1, n)
                g2 = math.gcd(prev_x + 1, n)
                
                if 1 < g1 < n:
                    return {
                        "success": True,
                        "factors": (g1, n // g1),
                        "time_s": time.time() - start,
                        "method": "crt_sqrt"
                    }
                if 1 < g2 < n:
                    return {
                        "success": True,
                        "factors": (g2, n // g2),
                        "time_s": time.time() - start,
                        "method": "crt_sqrt"
                    }
            
            if x == n - 1:
                break
    
    return {"success": False, "result": "no_nontrivial_sqrt", "time_s": time.time() - start}


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(math.sqrt(n)) + 1, 2):
        if n % i == 0:
            return False
    return True


def generate_semiprime(bits: int) -> tuple:
    import random
    while True:
        p = random.getrandbits(bits // 2) | 1
        if is_prime(p) and p > 3:
            break
    while True:
        q = random.getrandbits(bits // 2) | 1
        if is_prime(q) and q > 3 and q != p:
            break
    return p * q, min(p, q), max(p, q)


def run_experiment():
    """Test number-theoretic SMT factoring."""
    import random
    random.seed(42)
    
    print("=" * 70)
    print("NUMBER-THEORETIC SMT FACTORING")
    print("=" * 70)
    print("\nCan encoding NUMBER THEORY help Z3 factor?")
    print()
    
    methods = [
        ("Primality Hints", factor_with_primality_hints),
        ("Euler Structure", factor_with_euler_structure),
        ("Order Divisibility", factor_with_order_divisibility),
        ("CRT Square Roots", factor_chinese_remainder),
    ]
    
    for bits in [30, 40, 50, 60]:
        print(f"\n{'='*70}")
        print(f"Testing {bits}-bit semiprimes")
        print(f"{'='*70}")
        
        for trial in range(3):
            n, p, q = generate_semiprime(bits)
            print(f"\nTrial {trial+1}: N = {n} = {p} × {q}")
            print("-" * 50)
            
            for name, method in methods:
                try:
                    result = method(n, timeout_ms=30000)
                    if result["success"]:
                        factors = result["factors"]
                        correct = (factors[0] == p and factors[1] == q) or \
                                   (factors[0] == q and factors[1] == p)
                        status = "✓" if correct else "✗ WRONG"
                        print(f"  [{name:25s}] {status} {factors} in {result['time_s']:.3f}s")
                    else:
                        print(f"  [{name:25s}] ✗ {result.get('result', 'failed')} in {result['time_s']:.3f}s")
                except Exception as e:
                    print(f"  [{name:25s}] ERROR: {e}")


if __name__ == "__main__":
    run_experiment()
