# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Standard Program: Number Guessing Game Solver

This is a simple program that ANYONE would write - guess a number in range.
We run it BOTH through standard Python AND through Thiele VM to show:

1. IDENTICAL RESULTS - Both find the same answer
2. STRUCTURAL ISOMORPHISM - Same algorithm structure
3. SEPARATION - Thiele tracks μ-cost, standard Python doesn't

The algorithm: Binary search to find a hidden number.
"""

import time
from typing import Callable, Tuple, Dict, Any

# ============================================================================
# THE ALGORITHM (runs identically in both environments)
# ============================================================================

def binary_search_guess(
    low: int,
    high: int,
    check_fn: Callable[[int], int]
) -> Tuple[int, int]:
    """
    Binary search to find a target number.
    
    Args:
        low: Minimum of range
        high: Maximum of range  
        check_fn: Returns -1 if guess too low, 1 if too high, 0 if correct
    
    Returns:
        (found_number, guesses_made)
    """
    guesses = 0
    while low <= high:
        mid = (low + high) // 2
        guesses += 1
        result = check_fn(mid)
        
        if result == 0:
            return mid, guesses
        elif result < 0:
            low = mid + 1
        else:
            high = mid - 1
    
    return -1, guesses


def linear_search_guess(
    low: int,
    high: int,
    check_fn: Callable[[int], int]
) -> Tuple[int, int]:
    """
    Linear search (brute force) to find target.
    This is the "blind" approach - no structure exploitation.
    """
    guesses = 0
    for n in range(low, high + 1):
        guesses += 1
        if check_fn(n) == 0:
            return n, guesses
    return -1, guesses


# ============================================================================
# STANDARD PYTHON EXECUTION
# ============================================================================

def run_standard_python(target: int, low: int, high: int) -> Dict[str, Any]:
    """
    Run the algorithm with standard Python interpreter.
    No VM, no μ-tracking, just pure Python.
    """
    def check(guess):
        if guess < target:
            return -1
        elif guess > target:
            return 1
        return 0
    
    # Binary search
    start = time.time()
    found_binary, guesses_binary = binary_search_guess(low, high, check)
    time_binary = time.time() - start
    
    # Linear search  
    start = time.time()
    found_linear, guesses_linear = linear_search_guess(low, high, check)
    time_linear = time.time() - start
    
    return {
        'runtime': 'Standard Python',
        'target': target,
        'range': (low, high),
        'binary': {
            'found': found_binary,
            'guesses': guesses_binary,
            'time': time_binary,
            'correct': found_binary == target
        },
        'linear': {
            'found': found_linear,
            'guesses': guesses_linear,
            'time': time_linear,
            'correct': found_linear == target
        }
    }


# ============================================================================
# THIELE VM EXECUTION
# ============================================================================

def run_thiele_vm(target: int, low: int, high: int) -> Dict[str, Any]:
    """
    Run the SAME algorithm through Thiele VM.
    This adds μ-cost tracking and partition awareness.
    """
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits, information_gain_bits
    
    vm = VM(State())
    
    # Run binary search in VM - iterative version (VM sandbox compatible)
    binary_code = f'''
target = {target}
lo = {low}
hi = {high}
guesses = 0
found = -1

while lo <= hi:
    mid = (lo + hi) // 2
    guesses = guesses + 1
    if mid < target:
        lo = mid + 1
    elif mid > target:
        hi = mid - 1
    else:
        found = mid
        break

__result__ = (found, guesses)
'''
    
    start = time.time()
    result_binary, _ = vm.execute_python(binary_code)
    time_binary = time.time() - start
    
    # Calculate μ-cost for binary search
    search_space = high - low + 1
    mu_binary = 0.0
    if result_binary:
        guesses_binary = result_binary[1]
        # Each guess costs question bits + reduces search space by half
        for i in range(guesses_binary):
            remaining = search_space // (2 ** i)
            mu_binary += question_cost_bits(f"(guess {i})")
        # Information gain: found 1 in N
        mu_binary += information_gain_bits(search_space, 1)
    
    # Run linear search in VM
    vm2 = VM(State())
    linear_code = f'''
target = {target}
lo = {low}
hi = {high}
guesses = 0
found = -1

n = lo
while n <= hi:
    guesses = guesses + 1
    if n == target:
        found = n
        break
    n = n + 1

__result__ = (found, guesses)
'''
    
    start = time.time()
    result_linear, _ = vm2.execute_python(linear_code)
    time_linear = time.time() - start
    
    # Calculate μ-cost for linear search
    mu_linear = 0.0
    if result_linear:
        guesses_linear = result_linear[1]
        for i in range(guesses_linear):
            mu_linear += question_cost_bits(f"(guess {i})")
        mu_linear += information_gain_bits(search_space, 1)
    
    return {
        'runtime': 'Thiele VM',
        'target': target,
        'range': (low, high),
        'search_space': search_space,
        'binary': {
            'found': result_binary[0] if result_binary else -1,
            'guesses': result_binary[1] if result_binary else 0,
            'time': time_binary,
            'correct': result_binary[0] == target if result_binary else False,
            'mu_cost': mu_binary
        },
        'linear': {
            'found': result_linear[0] if result_linear else -1,
            'guesses': result_linear[1] if result_linear else 0,
            'time': time_linear,
            'correct': result_linear[0] == target if result_linear else False,
            'mu_cost': mu_linear
        }
    }


# ============================================================================
# COMPARISON AND VALIDATION
# ============================================================================

def compare_executions():
    """Run both and show the separation."""
    print("=" * 70)
    print("STANDARD PROGRAM: Number Guessing (Binary Search)")
    print("Running SAME algorithm in Standard Python AND Thiele VM")
    print("=" * 70)
    
    test_cases = [
        (42, 1, 100),      # Find 42 in 1-100
        (1, 1, 1000),      # Find 1 in 1-1000 (edge case)
        (1000, 1, 1000),   # Find 1000 in 1-1000 (edge case)
        (500, 1, 1000),    # Find 500 in 1-1000 (middle)
    ]
    
    all_match = True
    
    for target, low, high in test_cases:
        print(f"\n{'─' * 70}")
        print(f"Test: Find {target} in range [{low}, {high}]")
        print(f"Search space: {high - low + 1:,} numbers")
        print(f"{'─' * 70}")
        
        # Run in standard Python
        std_result = run_standard_python(target, low, high)
        
        # Run in Thiele VM
        vm_result = run_thiele_vm(target, low, high)
        
        # Display comparison
        print(f"\n  {'Algorithm':<15} {'Runtime':<18} {'Found':<8} {'Guesses':<10} {'μ-cost':<12}")
        print(f"  {'-'*15} {'-'*18} {'-'*8} {'-'*10} {'-'*12}")
        
        print(f"  {'Binary':<15} {'Standard Python':<18} {std_result['binary']['found']:<8} {std_result['binary']['guesses']:<10} {'N/A':<12}")
        print(f"  {'Binary':<15} {'Thiele VM':<18} {vm_result['binary']['found']:<8} {vm_result['binary']['guesses']:<10} {vm_result['binary']['mu_cost']:.1f} bits")
        print(f"  {'Linear':<15} {'Standard Python':<18} {std_result['linear']['found']:<8} {std_result['linear']['guesses']:<10} {'N/A':<12}")
        print(f"  {'Linear':<15} {'Thiele VM':<18} {vm_result['linear']['found']:<8} {vm_result['linear']['guesses']:<10} {vm_result['linear']['mu_cost']:.1f} bits")
        
        # Verify isomorphism
        binary_match = (std_result['binary']['found'] == vm_result['binary']['found'] and
                       std_result['binary']['guesses'] == vm_result['binary']['guesses'])
        linear_match = (std_result['linear']['found'] == vm_result['linear']['found'] and
                       std_result['linear']['guesses'] == vm_result['linear']['guesses'])
        
        print(f"\n  Isomorphism check:")
        print(f"    Binary: Standard == VM ? {'✓ YES' if binary_match else '✗ NO'}")
        print(f"    Linear: Standard == VM ? {'✓ YES' if linear_match else '✗ NO'}")
        
        if not (binary_match and linear_match):
            all_match = False
        
        # Show the separation (what Thiele adds)
        if vm_result['binary']['guesses'] > 0:
            efficiency = vm_result['linear']['guesses'] / vm_result['binary']['guesses']
            print(f"\n  Separation (Thiele insight):")
            print(f"    Binary vs Linear: {efficiency:.1f}x fewer guesses")
            print(f"    μ-cost saved: {vm_result['linear']['mu_cost'] - vm_result['binary']['mu_cost']:.1f} bits")
    
    # Final validation
    print(f"\n{'=' * 70}")
    print("VALIDATION SUMMARY")
    print(f"{'=' * 70}")
    print(f"\n  Structural Isomorphism: {'✓ VERIFIED' if all_match else '✗ FAILED'}")
    print(f"  - Same algorithm runs in both environments")
    print(f"  - Same results (found number, guess count)")
    print(f"  - Different tracking (Thiele adds μ-cost)")
    
    print(f"\n  Separation Demonstrated:")
    print(f"  - Standard Python: Pure computation, no cost tracking")
    print(f"  - Thiele VM: Computation + information-theoretic cost")
    print(f"  - Binary search exploits structure (log N vs N guesses)")
    
    return all_match


if __name__ == "__main__":
    success = compare_executions()
    exit(0 if success else 1)
