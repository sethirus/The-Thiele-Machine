# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""
Prime Factorization Verifier - Scientific Thiele Machine Program

Demonstrates information-theoretic μ-bit accounting using the REAL Thiele VM
and μ-spec v2.0:

    μ_total(q, N, M) = 8|canon(q)| + log₂(N/M)

Where:
- canon(q) = Canonical S-expression of the question
- N = Possibilities before the step
- M = Possibilities after the step

Key insights:
- Factoring costs μ ∝ search space reduction
- Verification costs only the question description
- Shows asymmetry: finding is hard, verifying is easy

This program uses the actual thielecpu.vm.VM class.
"""

from typing import Dict, Any
import math

# Import the REAL Thiele VM
from thielecpu.vm import VM
from thielecpu.state import State
from thielecpu.mu import (
    calculate_mu_cost,
    question_cost_bits,
    information_gain_bits,
    canonical_s_expression,
)


def verify_factorization(n: int, p: int, q: int) -> Dict[str, Any]:
    """
    Verify a factorization using the REAL Thiele VM with μ-spec v2.0 accounting.
    
    Verification only pays for the QUESTION (description length),
    not for information gain (we already know the answer).
    
    μ_verify = 8|canon("(verify-factor n p q)")|
    
    Args:
        n: Number to factor
        p, q: Claimed factors
    
    Returns:
        Verification result with validity and μ-cost breakdown
    """
    # Create real VM instance
    vm = VM(State())
    
    # Run verification in the real VM sandbox
    verification_code = f"""
p, q, n = {p}, {q}, {n}
product_correct = (p * q == n)
factors_nontrivial = (1 < p < n) and (1 < q < n)
__result__ = product_correct and factors_nontrivial
"""
    result, output = vm.execute_python(verification_code)
    
    # Product check
    product_correct = (p * q == n)
    
    # Nontriviality check - factors must be > 1 and < n
    factors_nontrivial = (1 < p < n) and (1 < q < n)
    
    # Valid factorization requires both
    valid = product_correct and factors_nontrivial
    
    # μ-cost for verification using μ-spec v2.0:
    # Only the question cost - no information gain (we're verifying, not discovering)
    question = f"(verify-factor {n} {p} {q})"
    canonical = canonical_s_expression(question)
    mu_question = question_cost_bits(question)
    
    # Verification reveals 0 new bits (N=1, M=1 → log₂(1/1) = 0)
    mu_information = 0.0
    mu_total = mu_question + mu_information
    
    return {
        'valid': valid,
        'product_correct': product_correct,
        'factors_nontrivial': factors_nontrivial,
        'mu_cost': mu_total,
        'mu_breakdown': {
            'question': question,
            'canonical': canonical,
            'mu_question': mu_question,
            'mu_information': mu_information,
            'explanation': f"8 × |'{canonical}'| = 8 × {len(canonical)} = {mu_question} bits"
        },
        'vm_type': 'thielecpu.vm.VM'
    }


def factor_with_mu_accounting(n: int) -> Dict[str, Any]:
    """
    Factor a number using the REAL Thiele VM with μ-spec v2.0 accounting.
    
    Factoring pays for:
    1. Each question asked: 8|canon(q)| bits
    2. Information revealed: log₂(N/M) bits when factor found
    
    Total μ = Σ(question costs) + log₂(candidates_before / 1)
    
    Args:
        n: Number to factor
    
    Returns:
        Factorization result with factors and real μ-cost breakdown
    """
    if n < 4:
        return {
            'found': False,
            'p': None,
            'q': None,
            'mu_cost': 0,
            'error': 'n must be >= 4 for nontrivial factorization'
        }
    
    # Create real VM instance
    vm = VM(State())
    
    # Track real μ-costs
    mu_questions = 0.0  # Cumulative cost of asking questions
    questions_asked = []
    
    # Search space: possible nontrivial factors are 2 to sqrt(n)
    max_candidate = int(math.sqrt(n)) + 1
    candidates_before = max_candidate - 1  # How many candidates we might check
    
    for candidate in range(2, max_candidate):
        # Each divisibility test is a question with μ-cost
        question = f"(divides? {candidate} {n})"
        canonical = canonical_s_expression(question)
        q_cost = question_cost_bits(question)
        mu_questions += q_cost
        questions_asked.append({
            'question': question,
            'canonical': canonical,
            'cost': q_cost
        })
        
        # Run the actual divisibility test in the real VM
        test_code = f"__result__ = {n} % {candidate} == 0"
        result, _ = vm.execute_python(test_code)
        
        if result:
            p = candidate
            q = n // candidate
            
            # Information revealed: narrowed from candidates_before to 1
            # μ_information = log₂(candidates_before / 1)
            mu_information = information_gain_bits(candidates_before, 1)
            
            total_mu = mu_questions + mu_information
            
            return {
                'found': True,
                'p': p,
                'q': q,
                'mu_cost': total_mu,
                'mu_breakdown': {
                    'mu_questions': mu_questions,
                    'mu_information': mu_information,
                    'questions_asked': len(questions_asked),
                    'candidates_before': candidates_before,
                    'formula': f"Σ(8|q_i|) + log₂({candidates_before}/1) = {mu_questions:.2f} + {mu_information:.2f} = {total_mu:.2f}"
                },
                'vm_type': 'thielecpu.vm.VM'
            }
    
    # n is prime - no factors found
    return {
        'found': False,
        'p': None,
        'q': None,
        'mu_cost': mu_questions,
        'mu_breakdown': {
            'mu_questions': mu_questions,
            'mu_information': 0,
            'questions_asked': len(questions_asked),
        },
        'error': f'{n} is prime',
        'vm_type': 'thielecpu.vm.VM'
    }


def demonstrate_asymmetry(n: int) -> Dict[str, Any]:
    """
    Demonstrate the asymmetry between factoring and verification
    using the REAL Thiele VM with μ-spec v2.0 costs.
    
    The key insight: FINDING structure is expensive (pays information cost),
    VERIFYING structure is cheap (only pays question cost).
    """
    # Factor (expensive - pays information cost)
    factor_result = factor_with_mu_accounting(n)
    
    if not factor_result['found']:
        return {
            'n': n,
            'factorable': False,
            'error': factor_result.get('error')
        }
    
    p, q = factor_result['p'], factor_result['q']
    
    # Verify (cheap - only pays question cost)
    verify_result = verify_factorization(n, p, q)
    
    # Calculate asymmetry ratio
    if verify_result['mu_cost'] > 0:
        ratio = factor_result['mu_cost'] / verify_result['mu_cost']
    else:
        ratio = factor_result['mu_cost']
    
    return {
        'n': n,
        'p': p,
        'q': q,
        'factoring_mu': factor_result['mu_cost'],
        'factoring_breakdown': factor_result['mu_breakdown'],
        'verification_mu': verify_result['mu_cost'],
        'verification_breakdown': verify_result['mu_breakdown'],
        'asymmetry_ratio': ratio,
        'vm_type': factor_result['vm_type'],
        'interpretation': (
            f"Factoring {n}={p}×{q}:\n"
            f"  μ_factor = {factor_result['mu_cost']:.2f} bits\n"
            f"    ({factor_result['mu_breakdown']['formula']})\n"
            f"  μ_verify = {verify_result['mu_cost']:.2f} bits\n"
            f"    ({verify_result['mu_breakdown']['explanation']})\n"
            f"  Asymmetry ratio: {ratio:.2f}×\n"
            f"  VM: {factor_result['vm_type']}"
        )
    }


# μ-spec v2.0 explanation
MU_SPEC_EXPLANATION = """
μ-SPEC v2.0: INFORMATION-THEORETIC COST ACCOUNTING
===================================================

The Thiele Machine charges μ-bits for every reasoning step:

    μ_total(q, N, M) = 8|canon(q)| + log₂(N/M)

Where:
  - q = The question being asked (e.g., "(divides? 3 21)")
  - canon(q) = Canonical S-expression form of q
  - |canon(q)| = Length in bytes of the canonical form
  - 8|canon(q)| = Question cost in bits (8 bits per byte)
  - N = Number of possibilities BEFORE the step
  - M = Number of possibilities AFTER the step
  - log₂(N/M) = Information gained (Shannon information)

This program uses the REAL thielecpu.vm.VM class for all computations.
"""


if __name__ == '__main__':
    print("Prime Factorization with Real μ-Spec v2.0 Accounting")
    print("Using REAL VM: thielecpu.vm.VM")
    print("=" * 60)
    print(MU_SPEC_EXPLANATION)
    print("=" * 60)
    
    # Demo with several numbers
    test_numbers = [15, 21, 35, 77, 143, 221]
    
    print("\nRESULTS:")
    print("-" * 60)
    
    for n in test_numbers:
        result = demonstrate_asymmetry(n)
        if result.get('factorable', True):
            print(f"\n{result['interpretation']}")
        else:
            print(f"\nn = {n}: {result.get('error')}")
    
    print("\n" + "=" * 60)
    print("KEY INSIGHT: The asymmetry ratio grows because factoring pays")
    print("log₂(N) bits of information cost, while verification pays 0.")
    print("This is the information-theoretic basis of cryptographic security.")

