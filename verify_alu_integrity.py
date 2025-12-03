#!/usr/bin/env python3
"""
Verify μ-ALU Integrity: Test for Hash Collision Bugs

This script specifically tests the cases mentioned in the code review:
- 7 -> 5 should NOT return log2(3) 
- 11 -> 1 should NOT return log2(3)
- 4 -> 1 should NOT return 0 bits

These are the "hash collision" cases that would occur if the implementation
incorrectly used bit-masking (before & 0b11) instead of proper ratio calculation.
"""

from thielecpu.mu_fixed import FixedPointMu
import math


def test_hash_collision_7_to_5():
    """Test case: 7 -> 5 should compute log2(7/5) ≈ 0.485, NOT log2(3) ≈ 1.585."""
    calc = FixedPointMu()
    
    result = calc.information_gain_q16(7, 5)
    actual = FixedPointMu.from_q16(result)
    expected = math.log2(7/5)
    log2_3 = math.log2(3)
    
    print(f"Test 7 -> 5:")
    print(f"  Expected: {expected:.4f} bits (log2(7/5))")
    print(f"  Actual:   {actual:.4f} bits")
    print(f"  Bad value would be: {log2_3:.4f} bits (log2(3))")
    
    # Verify it's NOT returning log2(3)
    assert abs(actual - log2_3) > 0.5, "FAIL: Returned log2(3) - hash collision bug detected!"
    # Verify it IS returning log2(7/5)
    assert abs(actual - expected) < 0.01, f"FAIL: Expected {expected:.4f}, got {actual:.4f}"
    
    print(f"  ✓ PASS: Correctly computed log2(7/5)")
    print()


def test_hash_collision_11_to_1():
    """Test case: 11 -> 1 should compute log2(11/1) ≈ 3.459, NOT log2(3) ≈ 1.585."""
    calc = FixedPointMu()
    
    result = calc.information_gain_q16(11, 1)
    actual = FixedPointMu.from_q16(result)
    expected = math.log2(11/1)
    log2_3 = math.log2(3)
    
    print(f"Test 11 -> 1:")
    print(f"  Expected: {expected:.4f} bits (log2(11))")
    print(f"  Actual:   {actual:.4f} bits")
    print(f"  Bad value would be: {log2_3:.4f} bits (log2(3))")
    
    # Verify it's NOT returning log2(3)
    assert abs(actual - log2_3) > 0.5, "FAIL: Returned log2(3) - hash collision bug detected!"
    # Verify it IS returning log2(11)
    assert abs(actual - expected) < 0.01, f"FAIL: Expected {expected:.4f}, got {actual:.4f}"
    
    print(f"  ✓ PASS: Correctly computed log2(11)")
    print()


def test_factoring_4_to_1():
    """Test case: 4 -> 1 should compute log2(4/1) = 2.0, NOT 0 bits."""
    calc = FixedPointMu()
    
    result = calc.information_gain_q16(4, 1)
    actual = FixedPointMu.from_q16(result)
    expected = math.log2(4/1)
    
    print(f"Test 4 -> 1 (Factoring Demo):")
    print(f"  Expected: {expected:.4f} bits (log2(4))")
    print(f"  Actual:   {actual:.4f} bits")
    
    # Verify it's NOT returning 0
    assert actual > 1.9, f"FAIL: Returned {actual:.4f}, factoring would cost 0 bits!"
    # Verify it IS returning 2.0
    assert abs(actual - expected) < 0.01, f"FAIL: Expected {expected:.4f}, got {actual:.4f}"
    
    print(f"  ✓ PASS: Factoring has correct μ-cost")
    print()


def test_general_ratios():
    """Test a variety of ratios to ensure no systematic errors."""
    calc = FixedPointMu()
    
    test_cases = [
        (2, 1),   # Powers of 2
        (8, 4),
        (16, 8),
        (3, 2),   # Non-powers
        (5, 3),
        (21, 7),  # From user example
        (100, 10),
        (1000, 1),
    ]
    
    print("Testing general ratios:")
    all_pass = True
    for before, after in test_cases:
        result = calc.information_gain_q16(before, after)
        actual = FixedPointMu.from_q16(result)
        expected = math.log2(before/after)
        error = abs(actual - expected)
        
        status = "✓" if error < 0.01 else "✗"
        print(f"  {status} {before}/{after}: Expected {expected:.4f}, Got {actual:.4f}, Error {error:.4f}")
        
        if error >= 0.01:
            all_pass = False
    
    assert all_pass, "FAIL: Some ratios had excessive error"
    print()


if __name__ == "__main__":
    print("=" * 70)
    print("μ-ALU Integrity Verification")
    print("Testing for Hash Collision Bugs")
    print("=" * 70)
    print()
    
    try:
        test_hash_collision_7_to_5()
        test_hash_collision_11_to_1()
        test_factoring_4_to_1()
        test_general_ratios()
        
        print("=" * 70)
        print("✅ ALL TESTS PASSED")
        print("   No hash collision bugs detected")
        print("   Factoring demo is supported")
        print("   μ-ALU integrity verified")
        print("=" * 70)
        
    except AssertionError as e:
        print("=" * 70)
        print(f"❌ TEST FAILED: {e}")
        print("=" * 70)
        exit(1)
