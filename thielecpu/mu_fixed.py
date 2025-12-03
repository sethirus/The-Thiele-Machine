"""Fixed-point μ-calculations implementing μ-ALU v1.0 specification.

This module provides bit-exact Q16.16 fixed-point arithmetic that matches
the Verilog hardware implementation. All operations must produce identical
results to the hardware to ensure ledger consistency.

CRITICAL: This implementation MUST NOT use floating-point math internally.
All intermediate values are Q16.16 fixed-point.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Tuple
import math


# Q16.16 constants
Q16_SHIFT = 16
Q16_ONE = 1 << Q16_SHIFT  # 0x00010000 = 1.0
Q16_MAX = 0x7FFFFFFF      # Maximum positive value
Q16_MIN = -0x80000000     # Maximum negative value (as signed 32-bit)


class FixedPointMu:
    """Q16.16 fixed-point arithmetic for μ-calculations.
    
    This class provides bit-exact implementations of all μ-ALU operations
    defined in spec/mu_alu_v1.md.
    """
    
    # Log2 LUT for values in [1.0, 2.0) with 256 entries
    # Each entry is Q16.16 format
    # Generated using: log2(1.0 + i/256.0) for i in 0..255
    _LOG2_LUT = None
    
    @classmethod
    def _init_lut(cls):
        """Initialize the log2 lookup table if not already initialized."""
        if cls._LOG2_LUT is not None:
            return
        
        cls._LOG2_LUT = []
        for i in range(256):
            x = 1.0 + (i / 256.0)
            log2_x = math.log2(x)
            # Convert to Q16.16 by multiplying by 2^16 and rounding
            q16_value = int(log2_x * Q16_ONE)
            cls._LOG2_LUT.append(q16_value)
    
    def __init__(self):
        """Initialize the fixed-point μ calculator."""
        FixedPointMu._init_lut()
        self.accumulator = 0  # Q16.16 μ-bit accumulator
    
    @staticmethod
    def to_q16(value: float) -> int:
        """Convert a float to Q16.16 fixed-point.
        
        Args:
            value: Floating-point number to convert
            
        Returns:
            Q16.16 representation as a signed 32-bit integer
        """
        q16 = int(value * Q16_ONE)
        # Clamp to valid range
        if q16 > Q16_MAX:
            return Q16_MAX
        if q16 < Q16_MIN:
            return Q16_MIN
        # Convert to signed 32-bit representation
        if q16 < 0:
            return (q16 & 0xFFFFFFFF)
        return q16
    
    @staticmethod
    def from_q16(q16: int) -> float:
        """Convert Q16.16 fixed-point to float.
        
        Args:
            q16: Q16.16 representation as 32-bit integer
            
        Returns:
            Floating-point approximation
        """
        # Interpret as signed 32-bit
        if q16 & 0x80000000:
            q16 = q16 - 0x100000000
        return q16 / Q16_ONE
    
    @staticmethod
    def add_q16(a: int, b: int) -> int:
        """Add two Q16.16 numbers with saturation.
        
        Args:
            a, b: Q16.16 values
            
        Returns:
            Q16.16 result, saturated at bounds
        """
        # Interpret as signed
        if a & 0x80000000:
            a = a - 0x100000000
        if b & 0x80000000:
            b = b - 0x100000000
        
        result = a + b
        
        # Saturate
        if result > Q16_MAX:
            result = Q16_MAX
        elif result < Q16_MIN:
            result = Q16_MIN
        
        # Convert back to unsigned 32-bit representation
        if result < 0:
            return (result & 0xFFFFFFFF)
        return result
    
    @staticmethod
    def sub_q16(a: int, b: int) -> int:
        """Subtract two Q16.16 numbers with saturation.
        
        Args:
            a, b: Q16.16 values
            
        Returns:
            Q16.16 result (a - b), saturated at bounds
        """
        # Interpret as signed
        if a & 0x80000000:
            a = a - 0x100000000
        if b & 0x80000000:
            b = b - 0x100000000
        
        result = a - b
        
        # Saturate
        if result > Q16_MAX:
            result = Q16_MAX
        elif result < Q16_MIN:
            result = Q16_MIN
        
        # Convert back to unsigned 32-bit representation
        if result < 0:
            return (result & 0xFFFFFFFF)
        return result
    
    @staticmethod
    def mul_q16(a: int, b: int) -> int:
        """Multiply two Q16.16 numbers.
        
        Args:
            a, b: Q16.16 values
            
        Returns:
            Q16.16 result (a × b)
        """
        # Interpret as signed
        if a & 0x80000000:
            a = a - 0x100000000
        if b & 0x80000000:
            b = b - 0x100000000
        
        # Multiply and shift
        temp = a * b
        result = temp >> Q16_SHIFT
        
        # Saturate
        if result > Q16_MAX:
            result = Q16_MAX
        elif result < Q16_MIN:
            result = Q16_MIN
        
        # Convert back to unsigned 32-bit representation
        if result < 0:
            return (result & 0xFFFFFFFF)
        return result
    
    @staticmethod
    def div_q16(a: int, b: int) -> int:
        """Divide two Q16.16 numbers.
        
        Args:
            a, b: Q16.16 values
            
        Returns:
            Q16.16 result (a ÷ b)
            
        Raises:
            ZeroDivisionError: If b is zero
        """
        # Interpret as signed
        if a & 0x80000000:
            a = a - 0x100000000
        if b & 0x80000000:
            b = b - 0x100000000
        
        if b == 0:
            raise ZeroDivisionError("Division by zero in Q16.16")
        
        # Shift and divide
        temp = (a << Q16_SHIFT) // b
        
        # Saturate
        if temp > Q16_MAX:
            result = Q16_MAX
        elif temp < Q16_MIN:
            result = Q16_MIN
        else:
            result = temp
        
        # Convert back to unsigned 32-bit representation
        if result < 0:
            return (result & 0xFFFFFFFF)
        return result
    
    @staticmethod
    def log2_q16(x: int) -> int:
        """Compute log₂(x) using LUT for Q16.16 values.
        
        Args:
            x: Q16.16 value (must be positive)
            
        Returns:
            Q16.16 result representing log₂(x)
        """
        # Ensure LUT is initialized
        FixedPointMu._init_lut()
        
        if x <= 0:
            # Return minimum representable value for log2(0) or negative
            return Q16_MIN & 0xFFFFFFFF
        
        # Special case: log2(1.0) = 0
        if x == Q16_ONE:
            return 0
        
        # Count leading zeros to find exponent
        # Python doesn't have a built-in clz, so we implement it
        temp = x
        leading_zeros = 0
        for i in range(32):
            if temp & 0x80000000:
                break
            temp <<= 1
            leading_zeros += 1
        
        # Exponent adjustment (16 bits for fractional part)
        exponent = 15 - leading_zeros  # Adjust for Q16.16 format
        
        # Normalize to [1.0, 2.0) range
        if exponent >= 0:
            normalized = x >> exponent
        else:
            normalized = x << (-exponent)
        
        # Extract LUT index from top 8 bits of fractional part
        # normalized is in range [1.0, 2.0), so subtract 1.0 and take top 8 bits
        frac_part = normalized - Q16_ONE
        if frac_part < 0:
            frac_part = 0
        
        index = (frac_part >> 8) & 0xFF
        if index > 255:
            index = 255
        
        # Look up fractional log
        frac_log = FixedPointMu._LOG2_LUT[index]
        
        # Combine: log2(x) = exponent + frac_log
        exp_q16 = exponent * Q16_ONE
        result_signed = exp_q16 + frac_log
        
        # Saturate
        if result_signed > Q16_MAX:
            result_signed = Q16_MAX
        elif result_signed < Q16_MIN:
            result_signed = Q16_MIN
        
        # Convert to unsigned 32-bit representation
        if result_signed < 0:
            return (result_signed & 0xFFFFFFFF)
        return result_signed
    
    def information_gain_q16(self, before: int, after: int) -> int:
        """Compute information gain in Q16.16 format.
        
        Args:
            before: Number of possibilities before (integer)
            after: Number of possibilities after (integer)
            
        Returns:
            Q16.16 value representing log₂(before/after)
        """
        if before <= 0 or after <= 0:
            raise ValueError("before and after must be positive integers")
        if after > before:
            raise ValueError("after cannot exceed before")
        if after == before:
            return 0
        
        # Convert integers to Q16.16
        before_q16 = before << Q16_SHIFT
        after_q16 = after << Q16_SHIFT
        
        # Compute log2(before) - log2(after)
        log_before = self.log2_q16(before_q16)
        log_after = self.log2_q16(after_q16)
        
        return self.sub_q16(log_before, log_after)
    
    def question_cost_bits_q16(self, expr: str) -> int:
        """Compute question cost in Q16.16 format.
        
        Args:
            expr: S-expression string
            
        Returns:
            Q16.16 value representing bit cost
        """
        # Tokenize and canonicalize
        tokens = []
        current = []
        for ch in expr:
            if ch in "()":
                if current:
                    tokens.append("".join(current))
                    current = []
                tokens.append(ch)
            elif ch.isspace():
                if current:
                    tokens.append("".join(current))
                    current = []
            else:
                current.append(ch)
        if current:
            tokens.append("".join(current))
        
        canonical = " ".join(tokens)
        bit_cost = len(canonical.encode("utf-8")) * 8
        
        # Convert to Q16.16
        return bit_cost << Q16_SHIFT
    
    def calculate_mu_cost_q16(self, expr: str, before: int, after: int) -> int:
        """Calculate total μ-cost in Q16.16 format.
        
        Args:
            expr: S-expression string
            before: Number of possibilities before
            after: Number of possibilities after
            
        Returns:
            Q16.16 value representing total μ-cost
        """
        question_bits = self.question_cost_bits_q16(expr)
        info_bits = self.information_gain_q16(before, after)
        return self.add_q16(question_bits, info_bits)
    
    def accumulate_mu(self, mu_delta: int):
        """Accumulate μ-cost to the accumulator.
        
        Args:
            mu_delta: Q16.16 μ-cost to add
        """
        self.accumulator = self.add_q16(self.accumulator, mu_delta)
    
    def get_accumulator(self) -> int:
        """Get the current μ-accumulator value.
        
        Returns:
            Q16.16 accumulator value
        """
        return self.accumulator
    
    def reset_accumulator(self):
        """Reset the μ-accumulator to zero."""
        self.accumulator = 0


@dataclass(frozen=True)
class MuBreakdownFixed:
    """Structured breakdown of a μ-cost computation using fixed-point."""
    
    canonical: str
    question_bits_q16: int  # Q16.16
    information_gain_q16: int  # Q16.16
    
    @property
    def total_q16(self) -> int:
        """Total μ-cost in Q16.16 format."""
        return FixedPointMu.add_q16(self.question_bits_q16, self.information_gain_q16)
    
    @property
    def question_bits(self) -> float:
        """Question bits as float for display."""
        return FixedPointMu.from_q16(self.question_bits_q16)
    
    @property
    def information_gain(self) -> float:
        """Information gain as float for display."""
        return FixedPointMu.from_q16(self.information_gain_q16)
    
    @property
    def total(self) -> float:
        """Total μ-cost as float for display."""
        return FixedPointMu.from_q16(self.total_q16)


def mu_breakdown_fixed(expr: str, before: int, after: int) -> MuBreakdownFixed:
    """Convenience helper returning the fixed-point breakdown structure.
    
    Args:
        expr: S-expression string
        before: Number of possibilities before
        after: Number of possibilities after
        
    Returns:
        MuBreakdownFixed with Q16.16 values
    """
    calc = FixedPointMu()
    
    # Canonicalize
    tokens = []
    current = []
    for ch in expr:
        if ch in "()":
            if current:
                tokens.append("".join(current))
                current = []
            tokens.append(ch)
        elif ch.isspace():
            if current:
                tokens.append("".join(current))
                current = []
        else:
            current.append(ch)
    if current:
        tokens.append("".join(current))
    canonical = " ".join(tokens)
    
    question_bits_q16 = calc.question_cost_bits_q16(expr)
    info_bits_q16 = calc.information_gain_q16(before, after)
    
    return MuBreakdownFixed(
        canonical=canonical,
        question_bits_q16=question_bits_q16,
        information_gain_q16=info_bits_q16
    )
