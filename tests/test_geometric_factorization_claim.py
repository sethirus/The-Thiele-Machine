#!/usr/bin/env python3
"""HONEST Factorization Analysis

This test demonstrates period finding GIVEN known factors.
It does NOT demonstrate any speedup over classical factorization.

WHAT THIS CODE ACTUALLY DOES:
1. claim_factorization() uses TRIAL DIVISION - O(√N) complexity
2. find_period_from_factorization() tests divisors of φ(N)
3. The "speedup" comparison was misleading - it hid the trial division cost

HONEST COMPLEXITY:
- Trial division to find factors: O(√N) iterations
- Divisor testing for period: O(d(φ(N)) × log N)
- Total: O(√N) - same as classical trial division

NO QUANTUM ADVANTAGE IS DEMONSTRATED.
"""

import math
from typing import Tuple, Optional, List
from dataclasses import dataclass
import time


@dataclass
class FactorizationClaim:
    """A geometric claim about factorization."""
    n: int
    p: int
    q: int
    mu_cost: float  # Information cost to specify p, q
    valid: bool
    trial_divisions: int  # HONEST: count the actual work done


@dataclass
class PeriodResult:
    period: int
    operations: int
    mu_cost: float
    method: str
    success: bool


def claim_factorization(n: int) -> FactorizationClaim:
    """Find factors using TRIAL DIVISION.
    
    HONEST DESCRIPTION:
    This is standard trial division - O(√N) complexity.
    We iterate from 2 to √N testing divisibility.
    
    This is NOT accessing structure without computing.
    This is NOT a quantum-like oracle.
    This is just classical trial division.
    """
    mu_cost = math.log2(n)
    trial_divisions = 0
    
    print(f"  TRIAL DIVISION: Finding factors of N={n}")
    
    sqrt_n = int(math.sqrt(n)) + 1
    for p in range(2, sqrt_n):
        trial_divisions += 1
        if n % p == 0:
            q = n // p
            print(f"  → Found: {n} = {p} × {q}")
            print(f"  → Trial divisions performed: {trial_divisions}")
            
            valid = is_prime(p) and is_prime(q)
            if valid:
                print(f"  ✓ Valid: both {p} and {q} are prime")
            
            return FactorizationClaim(
                n=n, p=p, q=q, mu_cost=mu_cost, 
                valid=valid, trial_divisions=trial_divisions
            )
    
    print(f"  ✗ Failed: {n} appears to be prime")
    print(f"  → Trial divisions performed: {trial_divisions}")
    return FactorizationClaim(
        n=n, p=-1, q=-1, mu_cost=mu_cost, 
        valid=False, trial_divisions=trial_divisions
    )


def is_prime(n: int) -> bool:
    """Quick primality check."""
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


def find_period_from_factorization(n: int, a: int, p: int, q: int) -> PeriodResult:
    """Find period using claimed factorization.
    
    Given N = p×q, we know φ(N) = (p-1)(q-1).
    The period r divides φ(N), so we only need to test divisors of φ(N).
    
    For typical φ(N), the divisor count is O((log N)^k) for small k.
    Each divisor test costs O(log N) via fast modular exponentiation.
    Total: O((log N)^(k+1)) = polylog(N)
    """
    start = time.time()
    operations = 0
    
    # Compute φ(N) = (p-1)(q-1)
    phi_n = (p - 1) * (q - 1)
    print(f"  φ({n}) = ({p}-1)×({q}-1) = {phi_n}")
    
    # Generate divisors of φ(N)
    divisors = []
    sqrt_phi = int(math.sqrt(phi_n)) + 1
    
    for d in range(1, min(sqrt_phi, 10000)):  # Limit for practical demonstration
        if phi_n % d == 0:
            divisors.append(d)
            if d != phi_n // d:
                divisors.append(phi_n // d)
    
    divisors = sorted(set(divisors))
    print(f"  Generated {len(divisors)} divisors of φ(N)")
    
    # Test divisors (smallest first for minimality)
    for candidate in divisors:
        operations += 1
        
        if pow(a, candidate, n) == 1:
            elapsed = time.time() - start
            print(f"  ✓ Found period: r={candidate} (tested {operations} divisors)")
            
            return PeriodResult(
                period=candidate,
                operations=operations,
                mu_cost=0.0,  # No additional μ-cost (factorization already claimed)
                method="factorization_claim",
                success=True
            )
    
    # Shouldn't reach here if claim was valid
    elapsed = time.time() - start
    return PeriodResult(
        period=-1,
        operations=operations,
        mu_cost=0.0,
        method="factorization_claim_failed",
        success=False
    )


def classical_period_finding(n: int, a: int) -> PeriodResult:
    """Classical O(r) period finding for comparison."""
    start = time.time()
    operations = 0
    
    for k in range(1, n):
        operations += 1
        if pow(a, k, n) == 1:
            elapsed = time.time() - start
            return PeriodResult(
                period=k,
                operations=operations,
                mu_cost=0.0,
                method="classical_enumeration",
                success=True
            )
    
    elapsed = time.time() - start
    return PeriodResult(
        period=-1,
        operations=operations,
        mu_cost=0.0,
        method="classical_failed",
        success=False
    )


def test_geometric_factorization_breakthrough():
    """Test honest factorization complexity analysis."""
    
    test_cases = [
        (15, 2, 4, "Tiny: 15=3×5"),
        (21, 2, 6, "Small: 21=3×7"),
        (3233, 3, 260, "Critical: 3233=53×61"),
        (10403, 2, 780, "Large: 10403=101×103"),
    ]
    
    print("=" * 80)
    print("HONEST FACTORIZATION COMPLEXITY ANALYSIS")
    print("=" * 80)
    print()
    print("This test demonstrates that our implementation uses TRIAL DIVISION.")
    print("There is NO quantum advantage or polylog speedup.")
    print("=" * 80)
    print()
    
    for n, a, expected_period, desc in test_cases:
        print(f"Test: {desc} (N={n}, a={a})")
        print(f"  Expected period: {expected_period}")
        print()
        
        # Classical baseline
        print("  [Baseline] Classical O(r) period enumeration:")
        classical = classical_period_finding(n, a)
        print(f"    Period: {classical.period}, Operations: {classical.operations}")
        print()
        
        # Our approach with HONEST accounting
        print("  [Our Method] Trial division + divisor testing:")
        claim = claim_factorization(n)
        
        if claim.valid:
            result = find_period_from_factorization(n, a, claim.p, claim.q)
            
            # HONEST total cost
            total_operations = claim.trial_divisions + result.operations
            
            print()
            print(f"  HONEST RESULT:")
            print(f"    Trial divisions (hidden before): {claim.trial_divisions}")
            print(f"    Divisor tests: {result.operations}")
            print(f"    TOTAL operations: {total_operations}")
            print(f"    Classical baseline: {classical.operations}")
            
            if result.success and result.period == expected_period:
                if total_operations < classical.operations:
                    speedup = classical.operations / total_operations
                    print(f"    Speedup: {speedup:.2f}x (HONEST)")
                else:
                    print(f"    NO SPEEDUP: our method uses {total_operations} vs {classical.operations}")
                print(f"    ✓ Period correct: {result.period}")
            else:
                print(f"    ✗ WRONG: got {result.period}, expected {expected_period}")
        else:
            print(f"    ✗ Factorization failed")
        
        print()
        print("-" * 80)
        print()


if __name__ == "__main__":
    test_geometric_factorization_breakthrough()
