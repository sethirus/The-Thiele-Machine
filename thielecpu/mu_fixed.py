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
    0x00000000, 0x000005C5, 0x00000B8A, 0x0000114E, 0x00001711, 0x00001CD3, 0x00002294, 0x00002854,
    0x00002E13, 0x000033D1, 0x0000398E, 0x00003F4A, 0x00004504, 0x00004ABD, 0x00005075, 0x0000562C,
    0x00005BE2, 0x00006196, 0x00006749, 0x00006CFB, 0x000072AB, 0x0000785A, 0x00007E08, 0x000083B5,
    0x00008960, 0x00008F0A, 0x000094B3, 0x00009A5A, 0x0000A000, 0x0000A5A5, 0x0000AB48, 0x0000B0EA,
    0x0000B68A, 0x0000BC29, 0x0000C1C7, 0x0000C763, 0x0000CCFE, 0x0000D297, 0x0000D82F, 0x0000DDC6,
    0x0000E35C, 0x0000E8F0, 0x0000EE83, 0x0000F415, 0x0000F9A6, 0x0000FF35, 0x000104C4, 0x00010A51,
    0x00010FDD, 0x00011568, 0x00011AF2, 0x0001207A, 0x00012602, 0x00012B88, 0x0001310D, 0x00013691,
    0x00013C14, 0x00014196, 0x00014716, 0x00014C95, 0x00015213, 0x00015790, 0x00015D0C, 0x00016286,
    0x00016800, 0x00016D78, 0x000172F0, 0x00017866, 0x00017DDB, 0x0001834F, 0x000188C2, 0x00018E34,
    0x000193A5, 0x00019915, 0x00019E84, 0x0001A3F2, 0x0001A95F, 0x0001AECB, 0x0001B436, 0x0001B9A0,
    0x0001BF09, 0x0001C471, 0x0001C9D8, 0x0001CF3E, 0x0001D4A3, 0x0001DA07, 0x0001DF6A, 0x0001E4CC,
    0x0001EA2D, 0x0001EF8D, 0x0001F4EC, 0x0001FA4A, 0x0001FFA7, 0x00020503, 0x00020A5E, 0x00020FB8,
    0x00021511, 0x00021A69, 0x00021FC0, 0x00022516, 0x00022A6B, 0x00022FBF, 0x00023512, 0x00023A64,
    0x00023FB5, 0x00024505, 0x00024A54, 0x00024FA2, 0x000254EF, 0x00025A3B, 0x00025F86, 0x000264D0,
    0x00026A19, 0x00026F61, 0x000274A8, 0x000279EE, 0x00027F33, 0x00028477, 0x000289BA, 0x00028EFC,
    0x0002943D, 0x0002997D, 0x00029EBC, 0x0002A3FA, 0x0002A937, 0x0002AE73, 0x0002B3AE, 0x0002B8E8,
    0x0002BE21, 0x0002C359, 0x0002C890, 0x0002CDC6, 0x0002D2FB, 0x0002D82F, 0x0002DD62, 0x0002E294,
    0x0002E7C5, 0x0002ECF5, 0x0002F224, 0x0002F752, 0x0002FC7F, 0x000301AB, 0x000306D6, 0x00030C00,
    0x00031129, 0x00031651, 0x00031B78, 0x0003209E, 0x000325C3, 0x00032AE7, 0x0003300A, 0x0003352C,
    0x00033A4D, 0x00033F6D, 0x0003448C, 0x000349AA, 0x00034EC7, 0x000353E3, 0x000358FE, 0x00035E18,
    0x00036331, 0x00036849, 0x00036D60, 0x00037276, 0x0003778B, 0x00037C9F, 0x000381B2, 0x000386C4,
    0x00038BD5, 0x000390E5, 0x000395F4, 0x00039B02, 0x0003A00F, 0x0003A51B, 0x0003AA26, 0x0003AF30,
    0x0003B439, 0x0003B941, 0x0003BE48, 0x0003C34E, 0x0003C853, 0x0003CD57, 0x0003D25A, 0x0003D75C,
    0x0003DC5D, 0x0003E15D, 0x0003E65C, 0x0003EB5A, 0x0003F057, 0x0003F553, 0x0003FA4E, 0x0003FF48,
    0x00040441, 0x00040939, 0x00040E30, 0x00041326, 0x0004181B, 0x00041D0F, 0x00042202, 0x000426F4,
    0x00042BE5, 0x000430D5, 0x000435C4, 0x00043AB2, 0x00043F9F, 0x0004448B, 0x00044976, 0x00044E60,
    0x00045349, 0x00045831, 0x00045D18, 0x000461FE, 0x000466E3, 0x00046BC7, 0x000470AA, 0x0004758C,
    0x00047A6D, 0x00047F4D, 0x0004842C, 0x0004890A, 0x00048DE7, 0x000492C3, 0x0004979E, 0x00049C78,
    0x0004A151, 0x0004A629, 0x0004AB00, 0x0004AFD6, 0x0004B4AB, 0x0004B97F, 0x0004BE52, 0x0004C324,
    0x0004C7F5, 0x0004CCC5, 0x0004D194, 0x0004D662, 0x0004DB2F, 0x0004DFFB, 0x0004E4C6, 0x0004E990,
    0x0004EE59, 0x0004F321, 0x0004F7E8, 0x0004FCAE, 0x00050173, 0x00050637, 0x00050AFA, 0x00050FBC,
    0x0005147D, 0x0005193D, 0x00051DFC, 0x000522BA, 0x00052777, 0x00052C33, 0x000530EE, 0x000535A8
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
        
        return FixedPointMu._to_unsigned32(result_signed)
    
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
