"""Fixed-point μ-calculations implementing μ-ALU v1.0 specification.

This module provides bit-exact Q16.16 fixed-point arithmetic that matches
the Verilog hardware implementation. All operations must produce identical
results to the hardware to ensure ledger consistency.

CRITICAL: This implementation MUST NOT use floating-point math internally.
All intermediate values are Q16.16 fixed-point. The LUT is precomputed offline.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Tuple


# Q16.16 constants
Q16_SHIFT = 16
Q16_ONE = 1 << Q16_SHIFT  # 0x00010000 = 1.0
Q16_MAX = 0x7FFFFFFF      # Maximum positive value
Q16_MIN = -0x80000000     # Maximum negative value (as signed 32-bit)


# Precomputed log2 LUT for [1.0, 2.0) in Q16.16 format
# Generated offline using: int(math.log2(1.0 + i/256.0) * 65536) for i in 0..255
_LOG2_LUT_PRECOMPUTED = [
    0x00000000, 0x00000170, 0x000002DF, 0x0000044D, 0x000005B9, 0x00000724, 0x0000088E, 0x000009F6,
    0x00000B5D, 0x00000CC2, 0x00000E26, 0x00000F89, 0x000010EB, 0x0000124B, 0x000013AA, 0x00001507,
    0x00001663, 0x000017BE, 0x00001918, 0x00001A71, 0x00001BC8, 0x00001D1E, 0x00001E72, 0x00001FC6,
    0x00002118, 0x00002269, 0x000023B9, 0x00002508, 0x00002655, 0x000027A2, 0x000028ED, 0x00002A37,
    0x00002B80, 0x00002CC7, 0x00002E0E, 0x00002F53, 0x00003098, 0x000031DB, 0x0000331D, 0x0000345E,
    0x0000359E, 0x000036DD, 0x0000381B, 0x00003958, 0x00003A93, 0x00003BCE, 0x00003D08, 0x00003E40,
    0x00003F78, 0x000040AE, 0x000041E4, 0x00004318, 0x0000444C, 0x0000457E, 0x000046B0, 0x000047E0,
    0x00004910, 0x00004A3E, 0x00004B6C, 0x00004C98, 0x00004DC4, 0x00004EEF, 0x00005019, 0x00005141,
    0x00005269, 0x00005390, 0x000054B6, 0x000055DC, 0x00005700, 0x00005823, 0x00005946, 0x00005A67,
    0x00005B88, 0x00005CA8, 0x00005DC7, 0x00005EE5, 0x00006002, 0x0000611E, 0x0000623A, 0x00006355,
    0x0000646E, 0x00006587, 0x000066A0, 0x000067B7, 0x000068CD, 0x000069E3, 0x00006AF8, 0x00006C0C,
    0x00006D1F, 0x00006E32, 0x00006F43, 0x00007054, 0x00007164, 0x00007274, 0x00007382, 0x00007490,
    0x0000759D, 0x000076A9, 0x000077B4, 0x000078BF, 0x000079C9, 0x00007AD2, 0x00007BDB, 0x00007CE3,
    0x00007DEA, 0x00007EF0, 0x00007FF5, 0x000080FA, 0x000081FE, 0x00008302, 0x00008404, 0x00008506,
    0x00008608, 0x00008708, 0x00008808, 0x00008907, 0x00008A06, 0x00008B04, 0x00008C01, 0x00008CFD,
    0x00008DF9, 0x00008EF4, 0x00008FEF, 0x000090E8, 0x000091E2, 0x000092DA, 0x000093D2, 0x000094C9,
    0x000095C0, 0x000096B6, 0x000097AB, 0x0000989F, 0x00009993, 0x00009A87, 0x00009B79, 0x00009C6C,
    0x00009D5D, 0x00009E4E, 0x00009F3E, 0x0000A02E, 0x0000A11D, 0x0000A20B, 0x0000A2F9, 0x0000A3E7,
    0x0000A4D3, 0x0000A5BF, 0x0000A6AB, 0x0000A796, 0x0000A880, 0x0000A96A, 0x0000AA53, 0x0000AB3C,
    0x0000AC24, 0x0000AD0B, 0x0000ADF2, 0x0000AED8, 0x0000AFBE, 0x0000B0A3, 0x0000B188, 0x0000B26C,
    0x0000B350, 0x0000B433, 0x0000B515, 0x0000B5F7, 0x0000B6D8, 0x0000B7B9, 0x0000B899, 0x0000B979,
    0x0000BA58, 0x0000BB37, 0x0000BC15, 0x0000BCF3, 0x0000BDD0, 0x0000BEAD, 0x0000BF89, 0x0000C065,
    0x0000C140, 0x0000C21A, 0x0000C2F5, 0x0000C3CE, 0x0000C4A7, 0x0000C580, 0x0000C658, 0x0000C730,
    0x0000C807, 0x0000C8DD, 0x0000C9B3, 0x0000CA89, 0x0000CB5E, 0x0000CC33, 0x0000CD07, 0x0000CDDB,
    0x0000CEAE, 0x0000CF81, 0x0000D053, 0x0000D125, 0x0000D1F7, 0x0000D2C8, 0x0000D398, 0x0000D468,
    0x0000D538, 0x0000D607, 0x0000D6D6, 0x0000D7A4, 0x0000D872, 0x0000D93F, 0x0000DA0C, 0x0000DAD8,
    0x0000DBA4, 0x0000DC70, 0x0000DD3B, 0x0000DE05, 0x0000DED0, 0x0000DF9A, 0x0000E063, 0x0000E12C,
    0x0000E1F4, 0x0000E2BC, 0x0000E384, 0x0000E44B, 0x0000E512, 0x0000E5D9, 0x0000E69F, 0x0000E764,
    0x0000E829, 0x0000E8EE, 0x0000E9B3, 0x0000EA77, 0x0000EB3A, 0x0000EBFD, 0x0000ECC0, 0x0000ED82,
    0x0000EE44, 0x0000EF06, 0x0000EFC7, 0x0000F088, 0x0000F148, 0x0000F208, 0x0000F2C8, 0x0000F387,
    0x0000F446, 0x0000F504, 0x0000F5C2, 0x0000F680, 0x0000F73D, 0x0000F7FA, 0x0000F8B7, 0x0000F973,
    0x0000FA2F, 0x0000FAEA, 0x0000FBA5, 0x0000FC60, 0x0000FD1A, 0x0000FDD4, 0x0000FE8D, 0x0000FF47,
]


class FixedPointMu:
    """Q16.16 fixed-point arithmetic for μ-calculations.
    
    This class provides bit-exact implementations of all μ-ALU operations
    defined in spec/mu_alu_v1.md.
    """
    
    # Log2 LUT is precomputed and loaded from constant
    _LOG2_LUT = _LOG2_LUT_PRECOMPUTED
    
    def __init__(self):
        """Initialize the fixed-point μ calculator."""
        self.accumulator = 0  # Q16.16 μ-bit accumulator
    
    @staticmethod
    def _to_unsigned32(value: int) -> int:
        """Convert signed value to unsigned 32-bit representation.
        
        Args:
            value: Signed integer
            
        Returns:
            Unsigned 32-bit representation
        """
        if value < 0:
            return value & 0xFFFFFFFF
        return value
    
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
        return FixedPointMu._to_unsigned32(q16)
    
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
        
        return FixedPointMu._to_unsigned32(result)
    
    @staticmethod
    def log2_q16(x: int) -> int:
        """Compute log₂(x) using LUT for Q16.16 values.
        
        This function computes log2 of a Q16.16 fixed-point number.
        
        Args:
            x: Q16.16 value (must be positive)
            
        Returns:
            Q16.16 result representing log₂(x)
        """
        if x <= 0:
            # Return minimum representable value for log2(0) or negative
            return FixedPointMu._to_unsigned32(Q16_MIN)
        
        # Special case: log2(1.0) = 0
        if x == Q16_ONE:
            return 0
        
        # Find the position of the highest set bit
        # For Q16.16, bit 16 represents 1.0
        # We need to normalize to [1.0, 2.0) which is [0x00010000, 0x00020000)
        
        # Count leading zeros
        temp = x
        leading_zeros = 0
        for i in range(32):
            if temp & 0x80000000:
                break
            temp <<= 1
            leading_zeros += 1
        
        # The integer part of log2(x) is the position of MSB relative to bit 16
        # If MSB is at bit 20, then x is in range [2^4, 2^5) so log2(x) is in [4, 5)
        highest_bit = 31 - leading_zeros
        integer_log2 = highest_bit - 16  # Relative to Q16.16 format
        
        # Normalize x to [1.0, 2.0) range for LUT lookup
        # This means shifting so the MSB is at bit 16
        shift_amount = highest_bit - 16
        if shift_amount > 0:
            normalized = x >> shift_amount
        elif shift_amount < 0:
            normalized = x << (-shift_amount)
        else:
            normalized = x
        
        # Now normalized is in [0x00010000, 0x00020000) range
        # Extract fractional part and look up in LUT
        frac_part = normalized - Q16_ONE
        if frac_part < 0:
            frac_part = 0
        
        # Use top 8 bits of fractional part as index
        index = (frac_part >> 8) & 0xFF
        if index > 255:
            index = 255
        
        # Look up fractional log
        frac_log = FixedPointMu._LOG2_LUT[index]
        
        # Combine: log2(x) = integer_part + fractional_part
        result_q16 = (integer_log2 << Q16_SHIFT) + frac_log
        
        # Saturate
        if result_q16 > Q16_MAX:
            return Q16_MAX
        elif result_q16 < Q16_MIN:
            return FixedPointMu._to_unsigned32(Q16_MIN)
        
        return FixedPointMu._to_unsigned32(result_q16)
    
    def information_gain_q16(self, before: int, after: int) -> int:
        """Compute information gain in Q16.16 format.
        
        Args:
            before: Number of possibilities before (integer count)
            after: Number of possibilities after (integer count)
            
        Returns:
            Q16.16 value representing log₂(before/after)
        """
        if before <= 0 or after <= 0:
            raise ValueError("before and after must be positive integers")
        if after > before:
            raise ValueError("after cannot exceed before")
        if after == before:
            return 0
        
        # Compute the ratio before/after in Q16.16 format
        # ratio_q16 = (before << 16) / after
        # This gives us a Q16.16 representation of the ratio
        ratio_q16 = (before << Q16_SHIFT) // after
        
        # Now compute log2 of this ratio
        # log2(before/after) = log2(ratio_q16)
        return self.log2_q16(ratio_q16)
    
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
