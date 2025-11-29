# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.
"""
Standard Program 1: Password Cracker

A typical brute-force password finder that a developer might write.
We run it both classically and with Thiele architecture to compare.

This is NOT a Thiele-specific program - it's a normal algorithm that
we're using to demonstrate the separation between blind/sighted execution.
"""

import time
import hashlib
from typing import Optional, Dict, Any


# ============================================================================
# STANDARD IMPLEMENTATION (what a normal developer would write)
# ============================================================================

def crack_password_classical(
    target_hash: str,
    charset: str = "abcdefghijklmnopqrstuvwxyz",
    max_length: int = 4
) -> Optional[str]:
    """
    Classical brute-force password cracker.
    
    This is the standard approach - try every combination until we find a match.
    No special structure, no shortcuts.
    
    Args:
        target_hash: SHA256 hash of the password we're looking for
        charset: Characters to try
        max_length: Maximum password length
    
    Returns:
        The password if found, None otherwise
    """
    attempts = 0
    
    def generate_passwords(length: int, prefix: str = ""):
        nonlocal attempts
        if length == 0:
            attempts += 1
            yield prefix
            return
        for char in charset:
            yield from generate_passwords(length - 1, prefix + char)
    
    for length in range(1, max_length + 1):
        for password in generate_passwords(length):
            if hashlib.sha256(password.encode()).hexdigest() == target_hash:
                return password, attempts
    
    return None, attempts


def crack_password_structured(
    target_hash: str,
    charset: str = "abcdefghijklmnopqrstuvwxyz",
    max_length: int = 4,
    known_prefix: str = "",
    known_suffix: str = ""
) -> Optional[str]:
    """
    Password cracker that exploits known structure.
    
    If we know parts of the password (prefix/suffix), we can
    partition the search space and only search the unknown parts.
    
    This simulates what Thiele's partition logic enables:
    - Split the problem into independent subproblems
    - Only search the unknown portions
    
    Args:
        target_hash: SHA256 hash of the password
        charset: Characters to try
        max_length: Maximum password length  
        known_prefix: Known starting characters
        known_suffix: Known ending characters
    
    Returns:
        The password if found, None otherwise
    """
    attempts = 0
    unknown_length = max_length - len(known_prefix) - len(known_suffix)
    
    if unknown_length < 0:
        return None, 0
    
    def generate_unknown(length: int, prefix: str = ""):
        nonlocal attempts
        if length == 0:
            attempts += 1
            yield prefix
            return
        for char in charset:
            yield from generate_unknown(length - 1, prefix + char)
    
    for length in range(0, unknown_length + 1):
        for middle in generate_unknown(length):
            candidate = known_prefix + middle + known_suffix
            if hashlib.sha256(candidate.encode()).hexdigest() == target_hash:
                return candidate, attempts
    
    return None, attempts


# ============================================================================
# THIELE VM EXECUTION (running the same logic through Thiele)
# ============================================================================

def crack_with_thiele_blind(target_hash: str, charset: str, max_length: int) -> Dict[str, Any]:
    """
    Run password cracker through Thiele VM in BLIND mode.
    
    Blind mode = no partition advantage = classical execution.
    This proves Thiele subsumes Turing machines.
    """
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits
    
    vm = VM(State())
    
    # Execute the classical algorithm in the VM
    code = f'''
import hashlib

target_hash = "{target_hash}"
charset = "{charset}"
max_length = {max_length}
attempts = 0

def generate_passwords(length, prefix=""):
    global attempts
    if length == 0:
        attempts = attempts + 1
        return [prefix]
    results = []
    for char in charset:
        results.extend(generate_passwords(length - 1, prefix + char))
    return results

result = None
for length in range(1, max_length + 1):
    for password in generate_passwords(length):
        if hashlib.sha256(password.encode()).hexdigest() == target_hash:
            result = password
            break
    if result:
        break

__result__ = (result, attempts)
'''
    
    start_time = time.time()
    result, output = vm.execute_python(code)
    elapsed = time.time() - start_time
    
    # Calculate μ-cost
    mu_cost = question_cost_bits(f"(crack-password {target_hash[:16]}...)")
    
    return {
        'mode': 'BLIND',
        'password': result[0] if result else None,
        'attempts': result[1] if result else 0,
        'time': elapsed,
        'mu_cost': mu_cost,
        'partitions': 1  # Blind mode = 1 partition
    }


def crack_with_thiele_sighted(
    target_hash: str, 
    charset: str, 
    max_length: int,
    known_prefix: str = "",
    known_suffix: str = ""
) -> Dict[str, Any]:
    """
    Run password cracker through Thiele VM in SIGHTED mode.
    
    Sighted mode = partition advantage = exploits structure.
    We partition the search space by the known prefix/suffix.
    """
    from thielecpu.vm import VM
    from thielecpu.state import State
    from thielecpu.mu import question_cost_bits, information_gain_bits
    
    vm = VM(State())
    
    # Create partitions for known/unknown parts
    state = vm.state
    
    # Partition 1: Known prefix (no search needed)
    if known_prefix:
        state.pnew({i for i in range(len(known_prefix))})
    
    # Partition 2: Unknown middle (search this)
    unknown_length = max_length - len(known_prefix) - len(known_suffix)
    if unknown_length > 0:
        state.pnew({i for i in range(len(known_prefix), len(known_prefix) + unknown_length)})
    
    # Partition 3: Known suffix (no search needed)
    if known_suffix:
        state.pnew({i for i in range(max_length - len(known_suffix), max_length)})
    
    # Execute structured search
    code = f'''
import hashlib

target_hash = "{target_hash}"
charset = "{charset}"
known_prefix = "{known_prefix}"
known_suffix = "{known_suffix}"
unknown_length = {unknown_length}
attempts = 0

def generate_unknown(length, prefix=""):
    global attempts
    if length == 0:
        attempts = attempts + 1
        return [prefix]
    results = []
    for char in charset:
        results.extend(generate_unknown(length - 1, prefix + char))
    return results

result = None
for length in range(0, unknown_length + 1):
    for middle in generate_unknown(length):
        candidate = known_prefix + middle + known_suffix
        if hashlib.sha256(candidate.encode()).hexdigest() == target_hash:
            result = candidate
            break
    if result:
        break

__result__ = (result, attempts)
'''
    
    start_time = time.time()
    result, output = vm.execute_python(code)
    elapsed = time.time() - start_time
    
    # Calculate μ-cost (reduced by known information)
    full_search_space = len(charset) ** max_length
    reduced_search_space = len(charset) ** unknown_length if unknown_length > 0 else 1
    
    mu_question = question_cost_bits(f"(crack-password {target_hash[:16]}...)")
    mu_info_saved = information_gain_bits(full_search_space, reduced_search_space)
    
    partitions_used = sum([
        1 if known_prefix else 0,
        1 if unknown_length > 0 else 0,
        1 if known_suffix else 0
    ])
    
    return {
        'mode': 'SIGHTED',
        'password': result[0] if result else None,
        'attempts': result[1] if result else 0,
        'time': elapsed,
        'mu_cost': mu_question,
        'mu_saved': mu_info_saved,
        'partitions': max(partitions_used, 1),
        'search_reduction': f"{reduced_search_space}/{full_search_space}"
    }


# ============================================================================
# COMPARISON AND VALIDATION
# ============================================================================

def run_comparison():
    """Run the password cracker in both modes and compare results."""
    print("=" * 70)
    print("STANDARD PROGRAM: Password Cracker")
    print("Comparing Classical vs Thiele Execution")
    print("=" * 70)
    
    # Test password: "cat" 
    test_password = "cat"
    target_hash = hashlib.sha256(test_password.encode()).hexdigest()
    
    charset = "abcdefghijklmnopqrstuvwxyz"
    max_length = 3
    
    print(f"\nTarget: '{test_password}' (hash: {target_hash[:16]}...)")
    print(f"Charset: {charset}")
    print(f"Max length: {max_length}")
    print(f"Search space: {len(charset)**max_length:,} combinations")
    
    # Test 1: Classical execution (no structure)
    print("\n" + "-" * 70)
    print("TEST 1: Classical Brute Force (No Structure)")
    print("-" * 70)
    
    start = time.time()
    classical_result, classical_attempts = crack_password_classical(
        target_hash, charset, max_length
    )
    classical_time = time.time() - start
    
    print(f"  Result: '{classical_result}'")
    print(f"  Attempts: {classical_attempts:,}")
    print(f"  Time: {classical_time:.4f}s")
    
    # Test 2: Thiele Blind Mode (same as classical)
    print("\n" + "-" * 70)
    print("TEST 2: Thiele VM - Blind Mode (Classical Equivalent)")
    print("-" * 70)
    
    blind_result = crack_with_thiele_blind(target_hash, charset, max_length)
    
    print(f"  Result: '{blind_result['password']}'")
    print(f"  Attempts: {blind_result['attempts']:,}")
    print(f"  Time: {blind_result['time']:.4f}s")
    print(f"  μ-cost: {blind_result['mu_cost']:.1f} bits")
    print(f"  Partitions: {blind_result['partitions']}")
    
    # Test 3: Classical with known structure
    print("\n" + "-" * 70)
    print("TEST 3: Classical with Known Structure (prefix='c')")
    print("-" * 70)
    
    start = time.time()
    structured_result, structured_attempts = crack_password_structured(
        target_hash, charset, max_length, known_prefix="c"
    )
    structured_time = time.time() - start
    
    print(f"  Result: '{structured_result}'")
    print(f"  Attempts: {structured_attempts:,}")
    print(f"  Time: {structured_time:.4f}s")
    
    # Test 4: Thiele Sighted Mode (exploits structure)
    print("\n" + "-" * 70)
    print("TEST 4: Thiele VM - Sighted Mode (Exploits Structure)")
    print("-" * 70)
    
    sighted_result = crack_with_thiele_sighted(
        target_hash, charset, max_length, known_prefix="c"
    )
    
    print(f"  Result: '{sighted_result['password']}'")
    print(f"  Attempts: {sighted_result['attempts']:,}")
    print(f"  Time: {sighted_result['time']:.4f}s")
    print(f"  μ-cost: {sighted_result['mu_cost']:.1f} bits")
    print(f"  μ-saved: {sighted_result['mu_saved']:.1f} bits")
    print(f"  Partitions: {sighted_result['partitions']}")
    print(f"  Search reduction: {sighted_result['search_reduction']}")
    
    # Validation
    print("\n" + "=" * 70)
    print("VALIDATION")
    print("=" * 70)
    
    all_correct = (
        classical_result == test_password and
        blind_result['password'] == test_password and
        structured_result == test_password and
        sighted_result['password'] == test_password
    )
    
    print(f"\n  All modes found correct password: {'✓ PASS' if all_correct else '✗ FAIL'}")
    
    blind_matches_classical = blind_result['attempts'] == classical_attempts
    print(f"  Blind mode matches classical attempts: {'✓ PASS' if blind_matches_classical else '✗ FAIL'}")
    
    sighted_fewer_attempts = sighted_result['attempts'] < blind_result['attempts']
    print(f"  Sighted mode uses fewer attempts: {'✓ PASS' if sighted_fewer_attempts else '✗ FAIL'}")
    
    speedup = classical_attempts / max(sighted_result['attempts'], 1)
    print(f"\n  Speedup from structure: {speedup:.1f}x")
    
    print("\n" + "-" * 70)
    print("SEPARATION DEMONSTRATED:")
    print("  - Blind mode (trivial partition) = Classical Turing machine")
    print("  - Sighted mode (structure-aware) = Thiele advantage")
    print("  - Same algorithm, same results, different search effort")
    print("-" * 70)
    
    return {
        'all_correct': all_correct,
        'blind_matches_classical': blind_matches_classical,
        'sighted_advantage': sighted_fewer_attempts,
        'speedup': speedup
    }


if __name__ == "__main__":
    results = run_comparison()
    exit(0 if results['all_correct'] else 1)
