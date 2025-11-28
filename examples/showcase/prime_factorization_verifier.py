# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Prime Factorization Verifier - Scientific Thiele Machine Program

Demonstrates information-theoretic μ-bit accounting:
- Factoring costs μ ∝ log₂(N) bits of information
- Verification costs O(1) μ bits
- Shows asymmetry: finding is hard, verifying is easy
- Connects to cryptographic one-way functions

This is an ADVANCED/SCIENTIFIC program showing μ-accounting.
"""

from typing import Dict, Any, Optional, Tuple
import math
import hashlib


def verify_factorization(n: int, p: int, q: int) -> Dict[str, Any]:
    """
    Verify a factorization with μ-cost accounting.
    
    Verification is CHEAP - just check p * q == n and nontriviality.
    
    Args:
        n: Number to factor
        p, q: Claimed factors
    
    Returns:
        Verification result with validity and μ-cost
    """
    # Product check - O(1) μ-cost
    product_correct = (p * q == n)
    
    # Nontriviality check - factors must be > 1 and < n
    factors_nontrivial = (1 < p < n) and (1 < q < n)
    
    # Valid factorization requires both
    valid = product_correct and factors_nontrivial
    
    # μ-cost for verification: just the description length
    # This is O(log n) for describing n, p, q
    description = f"(verify-factor {n} {p} {q})"
    mu_cost = len(description) * 8  # 8 bits per character (μ-spec v2)
    
    # But no information gain - we already know the answer
    # Verification reveals 0 new bits
    
    return {
        'valid': valid,
        'product_correct': product_correct,
        'factors_nontrivial': factors_nontrivial,
        'mu_cost': mu_cost,
        'certificate': {
            'type': 'factorization_verification',
            'n': n,
            'p': p,
            'q': q,
            'valid': valid,
            'hash': hashlib.sha256(f"{n}:{p}:{q}:{valid}".encode()).hexdigest()[:16]
        }
    }


def factor_with_mu_accounting(n: int) -> Dict[str, Any]:
    """
    Factor a number with full μ-cost accounting.
    
    EXPENSIVE - requires searching through candidates.
    μ-cost proportional to information revealed: log₂(N/2)
    
    Args:
        n: Number to factor
    
    Returns:
        Factorization result with factors and μ-cost
    """
    if n < 4:
        return {
            'found': False,
            'p': None,
            'q': None,
            'mu_cost': 0,
            'error': 'n must be >= 4 for nontrivial factorization'
        }
    
    # Track μ-cost
    mu_question = 0  # Cost of asking questions
    mu_information = 0  # Information gained
    
    # Search for factors (trial division)
    candidates_before = n - 3  # Possible factors: 2 to n-2
    
    for candidate in range(2, int(math.sqrt(n)) + 1):
        # Each test costs μ (question bits)
        question = f"(divides? {candidate} {n})"
        mu_question += len(question) * 8
        
        if n % candidate == 0:
            p = candidate
            q = n // candidate
            
            # Information revealed: went from candidates_before to 1
            mu_information = math.log2(candidates_before) if candidates_before > 1 else 0
            
            total_mu = mu_question + mu_information
            
            return {
                'found': True,
                'p': p,
                'q': q,
                'mu_cost': total_mu,
                'mu_question': mu_question,
                'mu_information': mu_information,
                'candidates_searched': candidate - 1,
                'certificate': {
                    'type': 'factorization_discovery',
                    'n': n,
                    'p': p,
                    'q': q,
                    'mu_total': total_mu,
                    'hash': hashlib.sha256(f"factor:{n}:{p}:{q}:{total_mu}".encode()).hexdigest()[:16]
                }
            }
    
    # n is prime
    return {
        'found': False,
        'p': None,
        'q': None,
        'mu_cost': mu_question,
        'mu_question': mu_question,
        'mu_information': 0,
        'error': f'{n} is prime'
    }


def demonstrate_asymmetry(n: int) -> Dict[str, Any]:
    """
    Demonstrate the asymmetry between factoring and verification.
    
    This is the core insight: finding structure is expensive,
    verifying structure is cheap.
    
    Args:
        n: Number to factor and verify
    
    Returns:
        Comparison of factoring vs verification costs
    """
    # Factor (expensive)
    factor_result = factor_with_mu_accounting(n)
    
    if not factor_result['found']:
        return {
            'n': n,
            'factorable': False,
            'error': factor_result.get('error')
        }
    
    p, q = factor_result['p'], factor_result['q']
    
    # Verify (cheap)
    verify_result = verify_factorization(n, p, q)
    
    # Calculate asymmetry ratio
    ratio = factor_result['mu_cost'] / verify_result['mu_cost'] if verify_result['mu_cost'] > 0 else float('inf')
    
    return {
        'n': n,
        'p': p,
        'q': q,
        'factoring_mu': factor_result['mu_cost'],
        'verification_mu': verify_result['mu_cost'],
        'asymmetry_ratio': ratio,
        'interpretation': (
            f"Factoring {n} cost {factor_result['mu_cost']:.1f} μ-bits. "
            f"Verifying cost only {verify_result['mu_cost']:.1f} μ-bits. "
            f"Asymmetry ratio: {ratio:.1f}×"
        )
    }


# Example Thiele program for prime factorization
FACTORIZATION_THIELE_PROGRAM = """; prime_factorization_verifier.thm
; Demonstrates μ-accounting for information revelation

; Create partition for the search space
PNEW {2..sqrt(n)}

; Execute factorization with μ-tracking
PYEXEC "result = factor_with_mu_accounting(n)"

; Record information cost
MDLACC  ; Accumulates μ from the search

; Assert the factorization is valid
LASSERT factor_valid.smt2

; Emit witness
EMIT "Factorization found with μ-cost tracking"

; The key insight: factoring costs ~log₂(N) μ-bits
; but verification costs only O(1) μ-bits
; This asymmetry is fundamental to cryptography
"""


if __name__ == '__main__':
    # Demo: Factor several numbers and show μ-accounting
    test_numbers = [15, 21, 35, 77, 143, 221]
    
    print("Prime Factorization with μ-Accounting")
    print("=" * 50)
    
    for n in test_numbers:
        result = demonstrate_asymmetry(n)
        if result.get('factorable', True):
            print(f"\nn = {n}")
            print(f"  Factors: {result['p']} × {result['q']}")
            print(f"  Factoring μ-cost: {result['factoring_mu']:.1f}")
            print(f"  Verification μ-cost: {result['verification_mu']:.1f}")
            print(f"  Asymmetry: {result['asymmetry_ratio']:.1f}×")
        else:
            print(f"\nn = {n}: {result.get('error')}")
    
    print("\n" + "=" * 50)
    print("Key Insight: The asymmetry shows that FINDING structure")
    print("(factoring) is expensive in μ-bits, while VERIFYING")
    print("structure (checking p*q=n) is cheap. This is the")
    print("information-theoretic basis of cryptographic security.")
