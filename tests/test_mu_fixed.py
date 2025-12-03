# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

"""Tests for fixed-point μ-calculations (μ-ALU v1.0)."""

import pytest
from thielecpu.mu_fixed import (
    FixedPointMu,
    mu_breakdown_fixed,
    Q16_ONE,
    Q16_MAX,
    Q16_MIN,
)


class TestQ16Conversion:
    """Test Q16.16 conversion functions."""
    
    def test_to_q16_basic(self):
        """Test basic float to Q16.16 conversion."""
        assert FixedPointMu.to_q16(0.0) == 0x00000000
        assert FixedPointMu.to_q16(1.0) == 0x00010000
        assert FixedPointMu.to_q16(2.0) == 0x00020000
        assert FixedPointMu.to_q16(0.5) == 0x00008000
        assert FixedPointMu.to_q16(0.25) == 0x00004000
    
    def test_to_q16_negative(self):
        """Test negative values."""
        result = FixedPointMu.to_q16(-1.0)
        # Should be 0xFFFF0000 in unsigned representation
        assert result == 0xFFFF0000
    
    def test_from_q16_basic(self):
        """Test Q16.16 to float conversion."""
        assert FixedPointMu.from_q16(0x00000000) == 0.0
        assert FixedPointMu.from_q16(0x00010000) == 1.0
        assert FixedPointMu.from_q16(0x00020000) == 2.0
        assert FixedPointMu.from_q16(0x00008000) == 0.5
    
    def test_from_q16_negative(self):
        """Test negative Q16.16 to float."""
        result = FixedPointMu.from_q16(0xFFFF0000)
        assert result == -1.0
    
    def test_round_trip(self):
        """Test conversion round-trip."""
        values = [0.0, 1.0, 2.0, 0.5, 0.25, -1.0, -2.5, 100.5]
        for val in values:
            q16 = FixedPointMu.to_q16(val)
            result = FixedPointMu.from_q16(q16)
            assert abs(result - val) < 0.0001, f"Round-trip failed for {val}"


class TestQ16Arithmetic:
    """Test Q16.16 arithmetic operations."""
    
    def test_addition(self):
        """Test Q16.16 addition."""
        # 1.0 + 1.0 = 2.0
        assert FixedPointMu.add_q16(0x00010000, 0x00010000) == 0x00020000
        
        # 0.5 + 0.25 = 0.75
        assert FixedPointMu.add_q16(0x00008000, 0x00004000) == 0x0000C000
    
    def test_addition_saturation(self):
        """Test addition saturation at max."""
        result = FixedPointMu.add_q16(Q16_MAX, 0x00000001)
        assert result == Q16_MAX
    
    def test_subtraction(self):
        """Test Q16.16 subtraction."""
        # 2.0 - 1.0 = 1.0
        assert FixedPointMu.sub_q16(0x00020000, 0x00010000) == 0x00010000
        
        # 1.0 - 0.5 = 0.5
        assert FixedPointMu.sub_q16(0x00010000, 0x00008000) == 0x00008000
    
    def test_subtraction_negative(self):
        """Test subtraction producing negative result."""
        # 0.0 - 1.0 = -1.0
        result = FixedPointMu.sub_q16(0x00000000, 0x00010000)
        assert result == 0xFFFF0000
    
    def test_multiplication(self):
        """Test Q16.16 multiplication."""
        # 1.0 × 2.0 = 2.0
        assert FixedPointMu.mul_q16(0x00010000, 0x00020000) == 0x00020000
        
        # 0.5 × 0.5 = 0.25
        assert FixedPointMu.mul_q16(0x00008000, 0x00008000) == 0x00004000
        
        # 2.0 × 3.0 = 6.0
        assert FixedPointMu.mul_q16(0x00020000, 0x00030000) == 0x00060000
    
    def test_division(self):
        """Test Q16.16 division."""
        # 2.0 ÷ 1.0 = 2.0
        assert FixedPointMu.div_q16(0x00020000, 0x00010000) == 0x00020000
        
        # 1.0 ÷ 2.0 = 0.5
        assert FixedPointMu.div_q16(0x00010000, 0x00020000) == 0x00008000
        
        # 6.0 ÷ 3.0 = 2.0
        assert FixedPointMu.div_q16(0x00060000, 0x00030000) == 0x00020000
    
    def test_division_by_zero(self):
        """Test division by zero raises error."""
        with pytest.raises(ZeroDivisionError):
            FixedPointMu.div_q16(0x00010000, 0x00000000)


class TestLog2Q16:
    """Test Q16.16 log₂ implementation."""
    
    def test_log2_one(self):
        """Test log₂(1.0) = 0."""
        result = FixedPointMu.log2_q16(0x00010000)
        assert result == 0x00000000
    
    def test_log2_two(self):
        """Test log₂(2.0) = 1.0."""
        result = FixedPointMu.log2_q16(0x00020000)
        # Should be very close to 1.0 (0x00010000)
        assert abs(result - 0x00010000) < 0x100  # Within small tolerance
    
    def test_log2_four(self):
        """Test log₂(4.0) = 2.0."""
        result = FixedPointMu.log2_q16(0x00040000)
        # Should be very close to 2.0 (0x00020000)
        assert abs(result - 0x00020000) < 0x100
    
    def test_log2_zero(self):
        """Test log₂(0) returns minimum."""
        result = FixedPointMu.log2_q16(0x00000000)
        # Should return minimum representable value
        assert result == (Q16_MIN & 0xFFFFFFFF)
    
    def test_log2_fractional(self):
        """Test log₂ of fractional values."""
        # log₂(0.5) = -1.0
        result = FixedPointMu.log2_q16(0x00008000)
        expected = 0xFFFF0000  # -1.0 in Q16.16
        # Allow some tolerance due to LUT approximation
        result_signed = result if result < 0x80000000 else result - 0x100000000
        expected_signed = expected if expected < 0x80000000 else expected - 0x100000000
        assert abs(result_signed - expected_signed) < 0x1000


class TestInformationGain:
    """Test information gain calculation."""
    
    def test_information_gain_basic(self):
        """Test basic information gain."""
        calc = FixedPointMu()
        
        # log₂(2/1) = 1.0 bit
        result = calc.information_gain_q16(2, 1)
        # Should be close to 1.0 (0x00010000)
        assert abs(result - 0x00010000) < 0x100
    
    def test_information_gain_no_change(self):
        """Test zero information gain when no change."""
        calc = FixedPointMu()
        result = calc.information_gain_q16(10, 10)
        assert result == 0
    
    def test_information_gain_large(self):
        """Test information gain with large numbers."""
        calc = FixedPointMu()
        
        # log₂(100/1) ≈ 6.64 bits
        result = calc.information_gain_q16(100, 1)
        result_float = FixedPointMu.from_q16(result)
        assert 6.0 < result_float < 7.0
    
    def test_information_gain_invalid(self):
        """Test invalid inputs."""
        calc = FixedPointMu()
        
        with pytest.raises(ValueError):
            calc.information_gain_q16(0, 1)
        
        with pytest.raises(ValueError):
            calc.information_gain_q16(1, 2)


class TestMuCostCalculation:
    """Test complete μ-cost calculation."""
    
    def test_mu_cost_simple(self):
        """Test simple μ-cost calculation."""
        calc = FixedPointMu()
        
        # Simple expression with known cost
        expr = "(test)"
        result = calc.calculate_mu_cost_q16(expr, 10, 5)
        
        # Should be question_bits + info_gain
        # Question: "( test )" canonical = 8 chars = 64 bits
        # Info gain: log₂(10/5) = log₂(2) = 1 bit
        result_float = FixedPointMu.from_q16(result)
        assert 64.0 < result_float < 66.0  # 64 + 1 = 65
    
    def test_mu_breakdown_fixed(self):
        """Test breakdown structure."""
        breakdown = mu_breakdown_fixed("(test)", 10, 5)
        
        assert breakdown.canonical == "( test )"
        assert breakdown.question_bits > 0
        assert breakdown.information_gain > 0
        assert breakdown.total > breakdown.question_bits


class TestMuAccumulator:
    """Test μ-accumulator."""
    
    def test_accumulator_initialization(self):
        """Test accumulator starts at zero."""
        calc = FixedPointMu()
        assert calc.get_accumulator() == 0
    
    def test_accumulator_addition(self):
        """Test accumulating μ-costs."""
        calc = FixedPointMu()
        
        # Add 1.0
        calc.accumulate_mu(0x00010000)
        assert calc.get_accumulator() == 0x00010000
        
        # Add another 1.0
        calc.accumulate_mu(0x00010000)
        assert calc.get_accumulator() == 0x00020000
    
    def test_accumulator_reset(self):
        """Test resetting accumulator."""
        calc = FixedPointMu()
        
        calc.accumulate_mu(0x00010000)
        calc.reset_accumulator()
        assert calc.get_accumulator() == 0
    
    def test_accumulator_saturation(self):
        """Test accumulator saturation."""
        calc = FixedPointMu()
        
        # Accumulate to max
        calc.accumulator = Q16_MAX - 1
        calc.accumulate_mu(0x00010000)
        
        # Should saturate at max
        assert calc.get_accumulator() == Q16_MAX


class TestLongRunConsistency:
    """Test long-run consistency for Phase 1 falsifiability."""
    
    def test_repeated_operations(self):
        """Test consistency over many operations."""
        calc = FixedPointMu()
        
        # Perform 100 operations (reduced to avoid saturation)
        for i in range(100):
            mu_delta = calc.calculate_mu_cost_q16("(op)", 10, 5)
            calc.accumulate_mu(mu_delta)
        
        # Check accumulator is reasonable
        result = calc.get_accumulator()
        assert result > 0
        assert result <= Q16_MAX  # Allow saturation at max
    
    def test_deterministic_sequence(self):
        """Test deterministic behavior."""
        calc1 = FixedPointMu()
        calc2 = FixedPointMu()
        
        # Same operations on both calculators
        operations = [
            ("(test1)", 10, 5),
            ("(test2)", 20, 10),
            ("(test3)", 100, 50),
        ]
        
        for expr, before, after in operations:
            mu1 = calc1.calculate_mu_cost_q16(expr, before, after)
            mu2 = calc2.calculate_mu_cost_q16(expr, before, after)
            
            # Must be bit-exact
            assert mu1 == mu2
            
            calc1.accumulate_mu(mu1)
            calc2.accumulate_mu(mu2)
        
        # Accumulators must match exactly
        assert calc1.get_accumulator() == calc2.get_accumulator()
