#!/usr/bin/env python3
"""Tests for predicate DSL parsing and evaluation."""

import pytest
from thielecpu.predicates import (
    parse_predicate,
    compile_predicate_for_rtl,
    PredicateError,
    is_prime,
)


class TestPredicateParsing:
    """Test parsing of predicate expressions."""
    
    def test_even_predicate(self):
        """Parse even(val) predicate."""
        pred = parse_predicate("even(val)")
        assert pred(0) is True
        assert pred(1) is False
        assert pred(2) is True
        assert pred(100) is True
        assert pred(101) is False
    
    def test_odd_predicate(self):
        """Parse odd(val) predicate."""
        pred = parse_predicate("odd(val)")
        assert pred(0) is False
        assert pred(1) is True
        assert pred(2) is False
        assert pred(99) is True
        assert pred(100) is False
    
    def test_threshold_predicate(self):
        """Parse threshold(val, N) predicate."""
        pred = parse_predicate("threshold(val, 100)")
        assert pred(99) is False
        assert pred(100) is True
        assert pred(101) is True
        assert pred(1000) is True
    
    def test_bitwise_predicate(self):
        """Parse bitwise(val, mask, expected) predicate."""
        # Check if low nibble is 0x5
        pred = parse_predicate("bitwise(val, 0x0F, 0x05)")
        assert pred(0x05) is True   # 0101
        assert pred(0x15) is True   # 0001 0101
        assert pred(0x25) is True   # 0010 0101
        assert pred(0x04) is False  # 0100
        assert pred(0x06) is False  # 0110
    
    def test_modulo_predicate(self):
        """Parse modulo(val, divisor, remainder) predicate."""
        # Multiples of 3
        pred = parse_predicate("modulo(val, 3, 0)")
        assert pred(0) is True
        assert pred(3) is True
        assert pred(6) is True
        assert pred(1) is False
        assert pred(2) is False
        assert pred(4) is False
    
    def test_prime_predicate(self):
        """Parse prime(val) predicate."""
        pred = parse_predicate("prime(val)")
        assert pred(2) is True
        assert pred(3) is True
        assert pred(5) is True
        assert pred(7) is True
        assert pred(11) is True
        assert pred(0) is False
        assert pred(1) is False
        assert pred(4) is False
        assert pred(6) is False
        assert pred(8) is False
        assert pred(9) is False
    
    def test_range_predicate(self):
        """Parse range(val, min, max) predicate."""
        pred = parse_predicate("range(val, 10, 20)")
        assert pred(9) is False
        assert pred(10) is True
        assert pred(15) is True
        assert pred(20) is True
        assert pred(21) is False


class TestPredicateErrors:
    """Test error handling in predicate parser."""
    
    def test_invalid_syntax(self):
        """Reject malformed expressions."""
        with pytest.raises(PredicateError, match="Invalid predicate"):
            parse_predicate("not a predicate")
    
    def test_unknown_function(self):
        """Reject unknown predicate functions."""
        with pytest.raises(PredicateError, match="Unknown predicate"):
            parse_predicate("unknown(val)")
    
    def test_wrong_argument_count(self):
        """Reject wrong number of arguments."""
        with pytest.raises(PredicateError, match="expects"):
            parse_predicate("even(val, extra)")
    
    def test_threshold_missing_value(self):
        """Reject threshold without numeric parameter."""
        with pytest.raises(PredicateError, match="threshold expects"):
            parse_predicate("threshold(val)")
    
    def test_modulo_zero_divisor(self):
        """Reject modulo with zero divisor."""
        with pytest.raises(PredicateError, match="divisor cannot be zero"):
            parse_predicate("modulo(val, 0, 0)")


class TestRTLCompilation:
    """Test compilation to RTL-compatible format."""
    
    def test_compile_even(self):
        """Compile even predicate to RTL params."""
        params = compile_predicate_for_rtl("even(val)")
        assert params == {'mode': 0, 'param1': 0, 'param2': 0}
    
    def test_compile_odd(self):
        """Compile odd predicate to RTL params."""
        params = compile_predicate_for_rtl("odd(val)")
        assert params == {'mode': 0, 'param1': 1, 'param2': 0}
    
    def test_compile_threshold(self):
        """Compile threshold predicate to RTL params."""
        params = compile_predicate_for_rtl("threshold(val, 50)")
        assert params == {'mode': 1, 'param1': 50, 'param2': 0}
    
    def test_compile_bitwise(self):
        """Compile bitwise predicate to RTL params."""
        params = compile_predicate_for_rtl("bitwise(val, 0xFF, 0x42)")
        assert params == {'mode': 2, 'param1': 0xFF, 'param2': 0x42}
    
    def test_compile_modulo(self):
        """Compile modulo predicate to RTL params."""
        params = compile_predicate_for_rtl("modulo(val, 7, 3)")
        assert params == {'mode': 3, 'param1': 7, 'param2': 3}
    
    def test_unsupported_in_rtl(self):
        """Some predicates not yet supported in RTL."""
        with pytest.raises(PredicateError, match="not yet supported in RTL"):
            compile_predicate_for_rtl("prime(val)")


class TestPrimeHelper:
    """Test the is_prime helper function."""
    
    def test_small_primes(self):
        """Verify small prime numbers."""
        primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
        for p in primes:
            assert is_prime(p), f"{p} should be prime"
    
    def test_non_primes(self):
        """Verify non-prime numbers."""
        non_primes = [0, 1, 4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22]
        for n in non_primes:
            assert not is_prime(n), f"{n} should not be prime"
    
    def test_larger_primes(self):
        """Test larger prime numbers."""
        assert is_prime(97)
        assert is_prime(101)
        assert is_prime(1009)
        assert not is_prime(100)
        assert not is_prime(1000)


def test_integration_example():
    """Integration test: use predicates in PSPLIT context."""
    # Simulate PSPLIT with threshold
    pred = parse_predicate("threshold(val, 100)")
    
    values = [50, 75, 100, 125, 150]
    true_partition = [v for v in values if pred(v)]
    false_partition = [v for v in values if not pred(v)]
    
    assert true_partition == [100, 125, 150]
    assert false_partition == [50, 75]


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
