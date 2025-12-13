#!/usr/bin/env python3
"""
Predicate DSL for partition split operations (PSPLIT).

This module replaces the hardcoded even/odd predicate in the RTL
with a flexible expression-based system.

Predicate Expression Language:
------------------------------
- even(val) - value is even
- odd(val) - value is odd
- threshold(val, N) - value >= N
- bitwise(val, mask, expected) - (val & mask) == expected
- modulo(val, divisor, remainder) - (val % divisor) == remainder
- prime(val) - value is prime
- range(val, min, max) - min <= val <= max

Examples:
---------
- "even(val)" - split evens and odds
- "threshold(val, 100)" - split values >= 100 vs < 100
- "modulo(val, 3, 0)" - split multiples of 3 vs non-multiples
- "bitwise(val, 0x0F, 0x05)" - split based on low nibble pattern
"""

from typing import Callable, Any
import re


class PredicateError(Exception):
    """Raised when predicate parsing or evaluation fails."""
    pass


def is_prime(n: int) -> bool:
    """Check if n is prime."""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(n**0.5) + 1, 2):
        if n % i == 0:
            return False
    return True


class PredicateParser:
    """Parse and compile predicate expressions."""
    
    def __init__(self):
        self.functions = {
            'even': lambda val: val % 2 == 0,
            'odd': lambda val: val % 2 == 1,
            'prime': is_prime,
        }
    
    def parse(self, expr: str) -> Callable[[int], bool]:
        """
        Parse a predicate expression into a callable function.
        
        Args:
            expr: Predicate expression string (e.g., "even(val)", "threshold(val, 100)")
        
        Returns:
            Function that takes an integer and returns bool
        
        Raises:
            PredicateError: If expression is malformed
        """
        expr = expr.strip()
        
        # Match function call pattern: name(args)
        match = re.match(r'(\w+)\((.*)\)', expr)
        if not match:
            raise PredicateError(f"Invalid predicate expression: {expr}")
        
        func_name, args_str = match.groups()
        args = [arg.strip() for arg in args_str.split(',')]
        
        # Handle simple predicates (no arguments except val)
        if func_name in self.functions:
            if len(args) != 1 or args[0] != 'val':
                raise PredicateError(f"{func_name} expects exactly one argument: val")
            return self.functions[func_name]
        
        # Handle parametric predicates
        if func_name == 'threshold':
            if len(args) != 2 or args[0] != 'val':
                raise PredicateError("threshold expects: threshold(val, N)")
            try:
                threshold = int(args[1])
            except ValueError:
                raise PredicateError(f"threshold value must be integer: {args[1]}")
            return lambda val: val >= threshold
        
        elif func_name == 'bitwise':
            if len(args) != 3 or args[0] != 'val':
                raise PredicateError("bitwise expects: bitwise(val, mask, expected)")
            try:
                mask = int(args[1], 0)  # Support hex
                expected = int(args[2], 0)
            except ValueError:
                raise PredicateError(f"bitwise arguments must be integers: {args[1]}, {args[2]}")
            return lambda val: (val & mask) == expected
        
        elif func_name == 'modulo':
            if len(args) != 3 or args[0] != 'val':
                raise PredicateError("modulo expects: modulo(val, divisor, remainder)")
            try:
                divisor = int(args[1])
                remainder = int(args[2])
            except ValueError:
                raise PredicateError(f"modulo arguments must be integers: {args[1]}, {args[2]}")
            if divisor == 0:
                raise PredicateError("modulo divisor cannot be zero")
            return lambda val: val % divisor == remainder
        
        elif func_name == 'range':
            if len(args) != 3 or args[0] != 'val':
                raise PredicateError("range expects: range(val, min, max)")
            try:
                min_val = int(args[1])
                max_val = int(args[2])
            except ValueError:
                raise PredicateError(f"range arguments must be integers: {args[1]}, {args[2]}")
            return lambda val: min_val <= val <= max_val
        
        else:
            raise PredicateError(f"Unknown predicate function: {func_name}")
    
    def compile_for_rtl(self, expr: str) -> dict:
        """
        Compile predicate to RTL-compatible representation.
        
        Returns:
            Dictionary with mode and parameters for Verilog implementation.
        """
        expr = expr.strip()
        match = re.match(r'(\w+)\((.*)\)', expr)
        if not match:
            raise PredicateError(f"Invalid predicate expression: {expr}")
        
        func_name, args_str = match.groups()
        args = [arg.strip() for arg in args_str.split(',')]
        
        if func_name == 'even':
            return {'mode': 0, 'param1': 0, 'param2': 0}  # EVEN_ODD mode
        
        elif func_name == 'odd':
            return {'mode': 0, 'param1': 1, 'param2': 0}  # EVEN_ODD mode, inverted
        
        elif func_name == 'threshold':
            threshold = int(args[1])
            return {'mode': 1, 'param1': threshold, 'param2': 0}  # THRESHOLD mode
        
        elif func_name == 'bitwise':
            mask = int(args[1], 0)
            expected = int(args[2], 0)
            return {'mode': 2, 'param1': mask, 'param2': expected}  # BITWISE mode
        
        elif func_name == 'modulo':
            divisor = int(args[1])
            remainder = int(args[2])
            return {'mode': 3, 'param1': divisor, 'param2': remainder}  # MODULO mode
        
        else:
            # For prime/range, we'd need to extend the RTL
            # For now, fall back to Python-only evaluation
            raise PredicateError(f"Predicate {func_name} not yet supported in RTL")


# Global parser instance
default_parser = PredicateParser()


def parse_predicate(expr: str) -> Callable[[int], bool]:
    """
    Parse a predicate expression.
    
    Args:
        expr: Predicate expression (e.g., "even(val)", "threshold(val, 100)")
    
    Returns:
        Callable that takes an integer and returns bool
    """
    return default_parser.parse(expr)


def compile_predicate_for_rtl(expr: str) -> dict:
    """
    Compile predicate to RTL parameters.
    
    Args:
        expr: Predicate expression
    
    Returns:
        Dict with 'mode', 'param1', 'param2' fields
    """
    return default_parser.compile_for_rtl(expr)
