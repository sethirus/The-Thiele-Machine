#!/usr/bin/env python3
"""
Logic-Only Factoring via SMT Theory Solvers

The hypothesis: Z3's theory solvers can "perceive" structure that
SAT solvers cannot. The μ-cost is the internal work Z3 does.

We encode factoring as a constraint satisfaction problem in the
INTEGER theory and let Z3's theory combination do the work.
"""

import time
import math
from z3 import *


def factor_via_smt_integer(n: int, timeout_ms: int = 30000) -> dict:
    """
    Factor N using Z3's integer theory.
    
    Encoding: Find p, q such that p * q = N, p > 1, q > 1
    
    This is the most direct encoding. Z3 must reason about
    multiplication over integers.
    """
    start = time.time()
    
    p = Int('p')
    q = Int('q')
    
    solver = Solver()
    solver.set("timeout", timeout_ms)
    
    # Constraints
    solver.add(p > 1)
    solver.add(q > 1)
    solver.add(p <= q)  # Symmetry breaking
    solver.add(p * q == n)
    
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
            "method": "smt_integer",
            "stats": str(solver.statistics())
        }
    else:
        return {
            "success": False,
            "result": str(result),
            "time_s": elapsed,
            "method": "smt_integer"
        }


def factor_via_bitvector(n: int, bits: int = 64, timeout_ms: int = 30000) -> dict:
    """
    Factor N using Z3's bitvector theory.
    
    BV theory has specialized reasoning for multiplication.
    """
    start = time.time()
    
    p = BitVec('p', bits)
    q = BitVec('q', bits)
    
    solver = Solver()
    solver.set("timeout", timeout_ms)
    
    # Constraints (using unsigned comparison)
    solver.add(UGT(p, BitVecVal(1, bits)))
    solver.add(UGT(q, BitVecVal(1, bits)))
    solver.add(ULE(p, q))  # Symmetry breaking
    solver.add(p * q == BitVecVal(n, bits))
    
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
            "method": "bitvector",
            "stats": str(solver.statistics())
        }
    else:
        return {
            "success": False,
            "result": str(result),
            "time_s": elapsed,
            "method": "bitvector"
        }


def factor_via_modular_reasoning(n: int, timeout_ms: int = 30000) -> dict:
    """
    Factor N using modular arithmetic properties.
    
    Key insight: If N = pq, then for random a:
    - a^(p-1) ≡ 1 (mod p)  [Fermat's little theorem]
    - So a^(p-1) - 1 ≡ 0 (mod p)
    - So gcd(a^(p-1) - 1, N) might reveal p
    
    We encode this as constraints and let Z3 find p.
    """
    start = time.time()
    
    p = Int('p')
    q = Int('q')
    a = 2  # Fixed base
    
    solver = Solver()
    solver.set("timeout", timeout_ms)
    
    # Basic factoring constraints
    solver.add(p > 1)
    solver.add(q > 1)
    solver.add(p <= q)
    solver.add(p * q == n)
    solver.add(p < n)
    solver.add(q < n)
    
    # Fermat constraint: a^(p-1) ≡ 1 (mod p)
    # This is always true for prime p, so it's a necessary condition
    # We can't directly encode modular exponentiation, but we can
    # use the consequence: p divides a^(p-1) - 1
    
    # Actually, let's try a different approach:
    # If p is prime and p | N, then for the ORDER of a mod p,
    # we know order | (p-1)
    
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
            "method": "modular_reasoning",
            "stats": str(solver.statistics())
        }
    else:
        return {
            "success": False,
            "result": str(result),
            "time_s": elapsed,
            "method": "modular_reasoning"
        }


def factor_via_sqrt_bound(n: int, timeout_ms: int = 30000) -> dict:
    """
    Factor N with tight bounds.
    
    Key insight: At least one factor p ≤ √N
    """
    start = time.time()
    
    sqrt_n = int(math.isqrt(n)) + 1
    
    p = Int('p')
    q = Int('q')
    
    solver = Solver()
    solver.set("timeout", timeout_ms)
    
    # Tight bounds
    solver.add(p >= 2)
    solver.add(p <= sqrt_n)
    solver.add(q >= p)
    solver.add(p * q == n)
    
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
            "method": "sqrt_bound",
            "sqrt_n": sqrt_n,
            "stats": str(solver.statistics())
        }
    else:
        return {
            "success": False,
            "result": str(result),
            "time_s": elapsed,
            "method": "sqrt_bound"
        }


def factor_via_difference_of_squares(n: int, timeout_ms: int = 30000) -> dict:
    """
    Fermat's method via SMT.
    
    N = a² - b² = (a-b)(a+b)
    
    Find a, b such that a² - b² = N
    """
    start = time.time()
    
    a = Int('a')
    b = Int('b')
    
    solver = Solver()
    solver.set("timeout", timeout_ms)
    
    sqrt_n = int(math.isqrt(n))
    
    # Constraints
    solver.add(a > sqrt_n)  # a > √N
    solver.add(b >= 0)
    solver.add(b < a)
    solver.add(a * a - b * b == n)
    
    result = solver.check()
    elapsed = time.time() - start
    
    if result == sat:
        model = solver.model()
        a_val = model[a].as_long()
        b_val = model[b].as_long()
        p = a_val - b_val
        q = a_val + b_val
        return {
            "success": True,
            "factors": (p, q),
            "a": a_val,
            "b": b_val,
            "time_s": elapsed,
            "method": "difference_of_squares"
        }
    else:
        return {
            "success": False,
            "result": str(result),
            "time_s": elapsed,
            "method": "difference_of_squares"
        }


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
    """Test all SMT-based factoring methods."""
    import random
    random.seed(42)
    
    print("=" * 70)
    print("LOGIC-ONLY FACTORING EXPERIMENT")
    print("=" * 70)
    print("\nCan Z3's theory solvers 'perceive' factors without brute force?")
    print()
    
    methods = [
        ("Integer Theory", factor_via_smt_integer),
        ("Bitvector (64-bit)", lambda n: factor_via_bitvector(n, 64)),
        ("√N Bound", factor_via_sqrt_bound),
        ("Difference of Squares", factor_via_difference_of_squares),
    ]
    
    for bits in [20, 30, 40, 50]:
        print(f"\n{'='*70}")
        print(f"Testing {bits}-bit semiprimes")
        print(f"{'='*70}")
        
        for trial in range(3):
            n, p, q = generate_semiprime(bits)
            print(f"\nTrial {trial+1}: N = {n} = {p} × {q}")
            print("-" * 50)
            
            for name, method in methods:
                try:
                    result = method(n)
                    if result["success"]:
                        print(f"  [{name:25s}] ✓ Found {result['factors']} in {result['time_s']:.3f}s")
                    else:
                        print(f"  [{name:25s}] ✗ {result['result']} in {result['time_s']:.3f}s")
                except Exception as e:
                    print(f"  [{name:25s}] ERROR: {e}")


if __name__ == "__main__":
    run_experiment()
