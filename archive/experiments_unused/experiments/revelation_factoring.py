#!/usr/bin/env python3
"""
The Logic-Only Factoring Hypothesis - Final Test

The user's claim: "Logic alone can factor."

Here's the strongest interpretation:
- The Thiele Machine's Logic Engine (L) can perceive structure
- Factoring structure is: N = p × q with p,q > 1
- The μ-cost is the REVELATION cost, not the COMPUTATION cost

What if we phrase factoring as a REVELATION problem?

Instead of: "Compute the factors of N"
We ask: "REVEAL the factors of N"

In the Thiele framework:
- REVEAL costs μ
- μ = Landauer entropy
- The logic engine L can check if a revelation is correct

The question: Can L do better than exhaustive search?
"""

import time
import math
from z3 import *


def factor_as_revelation(n: int, timeout_ms: int = 60000) -> dict:
    """
    Frame factoring as revelation to a logic engine.
    
    The insight: We don't ask Z3 to FIND factors.
    We ask Z3 to CONFIRM revelations are correct.
    
    But who provides the revelations?
    - Random guessing: O(√N) expected
    - Structured guessing: ???
    
    This tests whether Z3's internal heuristics can
    guide the revelation process efficiently.
    """
    start = time.time()
    
    sqrt_n = int(math.isqrt(n)) + 1
    
    # Strategy: Use Z3's optimizer to find p
    # Treat it as: minimize p subject to p | N
    
    opt = Optimize()
    opt.set("timeout", timeout_ms)
    
    p = Int('p')
    q = Int('q')
    
    # Hard constraints
    opt.add(p >= 2)
    opt.add(q >= 2)
    opt.add(p * q == n)
    
    # Soft objective: find smallest p (for faster convergence)
    opt.minimize(p)
    
    result = opt.check()
    elapsed = time.time() - start
    
    if result == sat:
        model = opt.model()
        p_val = model[p].as_long()
        q_val = model[q].as_long()
        return {
            "success": True,
            "factors": (p_val, q_val),
            "time_s": elapsed,
            "method": "revelation_optimize"
        }
    else:
        return {"success": False, "result": str(result), "time_s": elapsed}


def factor_incremental(n: int, timeout_s: float = 60.0) -> dict:
    """
    Incremental constraint revelation.
    
    Strategy: Start with weak constraints, strengthen incrementally.
    Each strengthening is a "revelation" that costs μ.
    
    The question: Does the logic engine learn from each step?
    """
    start = time.time()
    
    solver = Solver()
    p = Int('p')
    q = Int('q')
    
    sqrt_n = int(math.isqrt(n)) + 1
    mu_cost = 0
    
    # Initial constraints (μ = 0, all implied by problem statement)
    solver.add(p >= 2)
    solver.add(q >= 2)
    solver.add(p * q == n)
    solver.add(p <= q)  # Symmetry break
    solver.add(p <= sqrt_n)  # p ≤ √n
    
    # Incremental revelations based on N's properties
    revelations = []
    
    # Revelation 1: Parity
    if n % 2 == 1:
        solver.add(p % 2 == 1)
        solver.add(q % 2 == 1)
        mu_cost += 2  # 2 bits revealed
        revelations.append("both_odd")
    
    # Revelation 2: Small prime divisibility
    for small_p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
        if time.time() - start > timeout_s:
            break
        if n % small_p == 0:
            # N is divisible by small_p - is it a factor?
            if n // small_p > 1 and (n // small_p) * small_p == n:
                elapsed = time.time() - start
                return {
                    "success": True,
                    "factors": (small_p, n // small_p),
                    "time_s": elapsed,
                    "mu_cost": mu_cost,
                    "method": "small_prime_check",
                    "revelations": revelations
                }
        else:
            # Neither factor is this small prime
            solver.add(p % small_p != 0)
            mu_cost += math.log2(small_p)  # bits to specify divisibility
            revelations.append(f"not_div_{small_p}")
    
    # Revelation 3: Fermat bounds
    # If factors are close to √N, Fermat's method works fast
    # If factors are far apart, we can bound them
    fermat_a = int(math.isqrt(n)) + 1
    fermat_bound = min(1000, sqrt_n - fermat_a)
    
    for offset in range(fermat_bound):
        if time.time() - start > timeout_s:
            break
        a = fermat_a + offset
        b_sq = a * a - n
        if b_sq >= 0:
            b = int(math.isqrt(b_sq))
            if b * b == b_sq:
                # Found! N = (a-b)(a+b)
                p_val = a - b
                q_val = a + b
                if p_val > 1 and q_val > 1:
                    elapsed = time.time() - start
                    return {
                        "success": True,
                        "factors": (p_val, q_val),
                        "time_s": elapsed,
                        "mu_cost": mu_cost + math.log2(offset + 1),
                        "method": "fermat",
                        "revelations": revelations + [f"fermat_offset_{offset}"]
                    }
    
    # Revelation 4: Let Z3 solve with accumulated constraints
    solver.set("timeout", int((timeout_s - (time.time() - start)) * 1000))
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
            "mu_cost": mu_cost,
            "method": "z3_solve_constrained",
            "revelations": revelations
        }
    else:
        return {
            "success": False,
            "result": str(result),
            "time_s": elapsed,
            "mu_cost": mu_cost,
            "revelations": revelations
        }


def factor_binary_search_revelation(n: int, timeout_s: float = 60.0) -> dict:
    """
    Binary search over factor space with logic validation.
    
    Key insight: Each comparison is a REVELATION
    "Is there a factor ≤ mid?" can be answered by Z3
    
    This uses O(log √N) = O(log N / 2) queries to logic engine.
    Each query costs μ. Total μ = O(log N).
    
    BUT: Can Z3 answer "∃p: 2 ≤ p ≤ mid ∧ p | N" efficiently?
    """
    start = time.time()
    
    sqrt_n = int(math.isqrt(n)) + 1
    
    lo = 2
    hi = sqrt_n
    mu_cost = 0
    queries = 0
    
    def check_range(low: int, high: int) -> bool:
        """Check if there exists a factor in [low, high]."""
        solver = Solver()
        solver.set("timeout", 5000)  # 5 second per query
        
        p = Int('p')
        solver.add(p >= low)
        solver.add(p <= high)
        solver.add(n % p == 0)  # p divides N
        
        return solver.check() == sat
    
    # Binary search for smallest factor
    while lo < hi and time.time() - start < timeout_s:
        mid = (lo + hi) // 2
        queries += 1
        mu_cost += math.log2(hi - lo + 1)  # bits of information gained
        
        if check_range(lo, mid):
            hi = mid
        else:
            lo = mid + 1
    
    elapsed = time.time() - start
    
    # Verify lo is actually a factor
    if n % lo == 0:
        return {
            "success": True,
            "factors": (lo, n // lo),
            "time_s": elapsed,
            "mu_cost": mu_cost,
            "queries": queries,
            "method": "binary_search_revelation"
        }
    else:
        return {
            "success": False,
            "result": "search_failed",
            "time_s": elapsed,
            "mu_cost": mu_cost,
            "queries": queries
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
    """Test revelation-based factoring."""
    import random
    random.seed(42)
    
    print("=" * 70)
    print("FACTORING AS REVELATION")
    print("=" * 70)
    print("\nCan the logic engine answer factor queries efficiently?")
    print()
    
    methods = [
        ("Binary Search", factor_binary_search_revelation),
        ("Incremental", factor_incremental),
        ("Optimizer", factor_as_revelation),
    ]
    
    for bits in [20, 30, 40, 50]:
        print(f"\n{'='*70}")
        print(f"Testing {bits}-bit semiprimes")
        print(f"{'='*70}")
        
        for trial in range(2):
            n, p, q = generate_semiprime(bits)
            print(f"\nTrial {trial+1}: N = {n} = {p} × {q}")
            print("-" * 50)
            
            for name, method in methods:
                try:
                    result = method(n, timeout_s=30.0)
                    if result["success"]:
                        factors = result["factors"]
                        correct = (factors[0] * factors[1] == n)
                        mu = result.get("mu_cost", "?")
                        meth = result.get("method", "?")
                        status = "✓" if correct else "✗ WRONG"
                        print(f"  [{name:15s}] {status} {factors} in {result['time_s']:.3f}s, μ={mu}, via {meth}")
                    else:
                        print(f"  [{name:15s}] ✗ {result.get('result', 'failed')} in {result['time_s']:.3f}s")
                except Exception as e:
                    print(f"  [{name:15s}] ERROR: {e}")


if __name__ == "__main__":
    run_experiment()
