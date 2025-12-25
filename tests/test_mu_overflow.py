"""Attack #3: μ-Overflow Vulnerability Test.

Tests whether the receipt system properly bounds μ values to valid Q16.16 range.
"""

import pytest
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from thielecpu.mu_fixed import Q16_MAX, Q16_MIN
from thielecpu.receipts import mu_in_valid_range


class TestMuOverflow:
    """Test μ-overflow vulnerability."""
    
    def test_huge_mu_rejected_by_range_check(self):
        """Test that huge mu values outside Q16.16 range are rejected."""
        # Q16.16 max is 2^31-1, but attacker could try to claim more
        huge_mu = 2**64  # Way beyond Q16.16
        
        # The FIX: mu_in_valid_range rejects values outside Q16.16
        assert not mu_in_valid_range(huge_mu), "Huge μ should be rejected"
    
    def test_negative_overflow_rejected(self):
        """Test that negative mu values outside Q16.16 range are detected."""
        # Q16.16 min is -2^31
        huge_negative = -(2**64)
        
        assert huge_negative < Q16_MIN, "Test setup: value should be below Q16_MIN"
        assert not mu_in_valid_range(huge_negative), "Huge negative μ should be rejected"
    
    def test_q16_bounds(self):
        """Document Q16.16 bounds that should be enforced."""
        print(f"\nQ16.16 bounds:")
        print(f"  Q16_MAX = {Q16_MAX} = 0x{Q16_MAX:08X}")
        print(f"  Q16_MIN = {Q16_MIN} = 0x{Q16_MIN & 0xFFFFFFFF:08X}")
        print(f"  Range: [{Q16_MIN}, {Q16_MAX}]")
        
        # Valid values
        assert Q16_MAX == 0x7FFFFFFF
        assert Q16_MIN == -0x80000000


class TestMuRangeValidation:
    """Tests for proper μ range validation."""
    
    def test_valid_mu_values(self):
        """Test that valid mu values pass range check."""
        assert mu_in_valid_range(0)
        assert mu_in_valid_range(1000)
        assert mu_in_valid_range(Q16_MAX)
        assert mu_in_valid_range(Q16_MIN)
    
    def test_invalid_mu_values(self):
        """Test that invalid mu values fail range check."""
        assert not mu_in_valid_range(Q16_MAX + 1)
        assert not mu_in_valid_range(Q16_MIN - 1)
        assert not mu_in_valid_range(2**64)
        assert not mu_in_valid_range(-(2**64))
    
    def test_boundary_values(self):
        """Test exact boundary values."""
        # At boundaries - should pass
        assert mu_in_valid_range(Q16_MAX)
        assert mu_in_valid_range(Q16_MIN)
        
        # Just outside - should fail
        assert not mu_in_valid_range(Q16_MAX + 1)
        assert not mu_in_valid_range(Q16_MIN - 1)


if __name__ == "__main__":
    print("=== ATTACK #3: μ-Overflow Vulnerability Test ===\n")
    
    # Run tests
    test = TestMuOverflow()
    
    print("Test 1: Huge μ should be REJECTED by range check")
    try:
        test.test_huge_mu_rejected_by_range_check()
        print("  PASSED - overflow attack blocked!")
    except AssertionError as e:
        print(f"  FAILED: {e}")
    
    print("\nTest 2: Negative overflow should be REJECTED")
    try:
        test.test_negative_overflow_rejected()
        print("  PASSED - negative overflow attack blocked!")
    except AssertionError as e:
        print(f"  FAILED: {e}")
    
    print("\nTest 3: Valid range values")
    valid_test = TestMuRangeValidation()
    
    try:
        valid_test.test_valid_mu_values()
        print("  PASSED - valid μ values accepted")
    except AssertionError as e:
        print(f"  FAILED: {e}")
    
    try:
        valid_test.test_invalid_mu_values()
        print("  PASSED - invalid μ values rejected")
    except AssertionError as e:
        print(f"  FAILED: {e}")
    
    print("\n=== CONCLUSION ===")
    print("VULNERABILITY FIXED: receipts.py now validates μ in Q16.16 range")
    print("- mu_in_valid_range() checks Q16_MIN <= mu <= Q16_MAX")
    print("- StepReceipt.verify_mu_range() uses this for receipt validation")
    print("- Coq spec includes mu_in_range predicate and overflow theorems")
