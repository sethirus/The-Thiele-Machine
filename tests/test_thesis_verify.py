"""Tests for thesis_verify module - the canonical thesis-compliant verifier."""

import pytest
from thielecpu.thesis_verify import (
    ThesisVerifier,
    TrustedTestCase,
    TrustLevel,
    ThesisReceipt,
    ThesisReceiptChain,
    compute_information_gain,
    estimate_search_space,
    Z3LAssertVerifier,
    thesis_verify_endpoint,
)


class TestTrustBoundary:
    """Test trust boundary enforcement."""
    
    def test_reject_untrusted_test_cases(self):
        """CRITICAL: LLM-generated tests must be rejected."""
        with pytest.raises(ValueError, match="TRUST BOUNDARY VIOLATION"):
            TrustedTestCase(
                inputs={"x": 1},
                expected=2,
                source="llm",
                source_trust=TrustLevel.UNTRUSTED,
            )
    
    def test_accept_user_trust(self):
        """User-provided tests should be accepted."""
        tc = TrustedTestCase(
            inputs={"x": 1},
            expected=2,
            source="user",
            source_trust=TrustLevel.USER,
        )
        assert tc.source_trust == TrustLevel.USER
    
    def test_accept_spec_trust(self):
        """Specification-based tests should be accepted."""
        tc = TrustedTestCase(
            inputs={"n": 10},
            expected=55,
            source="fibonacci_spec",
            source_trust=TrustLevel.SPECIFICATION,
        )
        assert tc.source_trust == TrustLevel.SPECIFICATION
    
    def test_accept_invariant_trust(self):
        """Mathematical invariant tests should be accepted."""
        tc = TrustedTestCase(
            inputs={"n": 0},
            expected=0,
            source="math_definition",
            source_trust=TrustLevel.INVARIANT,
        )
        assert tc.source_trust == TrustLevel.INVARIANT


class TestInformationTheoreticCost:
    """Test information-theoretic μ-cost computation."""
    
    def test_information_gain_full_collapse(self):
        """Full collapse from large space to single point."""
        gain = compute_information_gain(1024, 1)
        assert abs(gain - 10.0) < 0.01  # log2(1024) = 10
    
    def test_information_gain_binary(self):
        """Binary search space."""
        gain = compute_information_gain(2, 1)
        assert abs(gain - 1.0) < 0.01  # log2(2) = 1
    
    def test_information_gain_no_collapse(self):
        """No collapse (failed verification)."""
        gain = compute_information_gain(1024, 1024)
        assert gain == 0.0
    
    def test_estimate_search_space_bool(self):
        """Boolean has search space of 2."""
        space = estimate_search_space(True)
        assert space == 2
    
    def test_estimate_search_space_int(self):
        """Integer search space is 2^(bits+1)."""
        space = estimate_search_space(55)  # 6 bits
        assert space >= 64  # At least 2^6


class TestMerkleReceiptChain:
    """Test Merkle-linked receipt chain."""
    
    def test_empty_chain_valid(self):
        """Empty chain is valid."""
        chain = ThesisReceiptChain(
            initial_state_hash="abc123",
            final_state_hash="abc123",
            receipts=[],
            total_mu_cost=0.0,
        )
        valid, error = chain.verify()
        assert valid
        assert error is None
    
    def test_single_receipt_chain(self):
        """Single receipt chain."""
        receipt = ThesisReceipt(
            step=0,
            pre_state_hash="hash_a",
            instruction="TEST add(1, 2)",
            post_state_hash="hash_b",
            mu_cost=1.0,
            chain_link="",  # First receipt has empty chain_link
        )
        
        chain = ThesisReceiptChain(
            initial_state_hash="hash_a",
            final_state_hash="hash_b",
            receipts=[receipt],
            total_mu_cost=1.0,
        )
        
        valid, error = chain.verify()
        assert valid, error
    
    def test_chain_link_verification(self):
        """Chain links must match previous receipt hash."""
        r1 = ThesisReceipt(
            step=0,
            pre_state_hash="hash_a",
            instruction="LOAD",
            post_state_hash="hash_b",
            mu_cost=1.0,
            chain_link="",
        )
        
        r2 = ThesisReceipt(
            step=1,
            pre_state_hash="hash_b",
            instruction="TEST",
            post_state_hash="hash_c",
            mu_cost=2.0,
            chain_link=r1.receipt_hash(),  # Correct chain link
        )
        
        chain = ThesisReceiptChain(
            initial_state_hash="hash_a",
            final_state_hash="hash_c",
            receipts=[r1, r2],
            total_mu_cost=3.0,
        )
        
        valid, error = chain.verify()
        assert valid, error
    
    def test_broken_chain_link(self):
        """Broken chain link must be detected."""
        r1 = ThesisReceipt(
            step=0,
            pre_state_hash="hash_a",
            instruction="LOAD",
            post_state_hash="hash_b",
            mu_cost=1.0,
            chain_link="",
        )
        
        r2 = ThesisReceipt(
            step=1,
            pre_state_hash="hash_b",
            instruction="TEST",
            post_state_hash="hash_c",
            mu_cost=2.0,
            chain_link="WRONG_HASH",  # Invalid chain link
        )
        
        chain = ThesisReceiptChain(
            initial_state_hash="hash_a",
            final_state_hash="hash_c",
            receipts=[r1, r2],
            total_mu_cost=3.0,
        )
        
        valid, error = chain.verify()
        assert not valid
        assert "chain_link" in error
    
    def test_negative_mu_rejected(self):
        """Negative μ-cost violates monotonicity."""
        receipt = ThesisReceipt(
            step=0,
            pre_state_hash="hash_a",
            instruction="TEST",
            post_state_hash="hash_b",
            mu_cost=-1.0,  # INVALID: negative
            chain_link="",
        )
        
        chain = ThesisReceiptChain(
            initial_state_hash="hash_a",
            final_state_hash="hash_b",
            receipts=[receipt],
            total_mu_cost=-1.0,
        )
        
        valid, error = chain.verify()
        assert not valid
        assert "negative" in error.lower() or "monotonicity" in error.lower()


class TestZ3Verification:
    """Test Z3/SMT LASSERT verification."""
    
    def test_z3_positive_assertion(self):
        """Z3 should verify positive assertion."""
        verifier = Z3LAssertVerifier()
        cert = verifier.verify_assertion(
            "x is positive",
            {"x": 5},
        )
        assert cert.is_verified()
        assert cert.result == "sat"
    
    def test_z3_even_assertion(self):
        """Z3 should verify even assertion."""
        verifier = Z3LAssertVerifier()
        cert = verifier.verify_assertion(
            "x is even",
            {"x": 4},
        )
        assert cert.is_verified()
    
    def test_z3_equality_assertion(self):
        """Z3 should verify equality assertion."""
        verifier = Z3LAssertVerifier()
        cert = verifier.verify_assertion(
            "x == 10",
            {"x": 10},
        )
        assert cert.is_verified()


class TestThesisVerifier:
    """Test the complete thesis verifier."""
    
    def test_verify_simple_function(self):
        """Verify a simple add function."""
        verifier = ThesisVerifier()
        
        code = "def add(a, b): return a + b"
        test_cases = [
            TrustedTestCase({"a": 1, "b": 2}, 3, "user", TrustLevel.USER),
            TrustedTestCase({"a": 10, "b": 20}, 30, "user", TrustLevel.USER),
        ]
        
        result = verifier.verify(code, "add", test_cases)
        
        assert result.success
        assert result.tests_passed == 2
        assert result.tests_total == 2
        assert result.mu_total > 0
        
        # Receipt chain must be valid
        valid, error = result.receipt_chain.verify()
        assert valid, error
    
    def test_verify_failing_function(self):
        """Verify a failing function."""
        verifier = ThesisVerifier()
        
        code = "def add(a, b): return a - b"  # BUG: subtracts instead
        test_cases = [
            TrustedTestCase({"a": 1, "b": 2}, 3, "user", TrustLevel.USER),
        ]
        
        result = verifier.verify(code, "add", test_cases)
        
        assert not result.success
        assert result.tests_passed == 0
    
    def test_verify_fibonacci(self):
        """Verify Fibonacci implementation."""
        verifier = ThesisVerifier()
        
        code = '''
def fibonacci(n):
    if n <= 1:
        return n
    a, b = 0, 1
    for _ in range(n - 1):
        a, b = b, a + b
    return b
'''
        test_cases = [
            TrustedTestCase({"n": 0}, 0, "math", TrustLevel.INVARIANT),
            TrustedTestCase({"n": 1}, 1, "math", TrustLevel.INVARIANT),
            TrustedTestCase({"n": 10}, 55, "oeis", TrustLevel.SPECIFICATION),
        ]
        
        result = verifier.verify(code, "fibonacci", test_cases)
        
        assert result.success
        assert result.tests_passed == 3
        assert result.mu_information > 0  # Information was gained


class TestEndpoint:
    """Test HTTP endpoint."""
    
    def test_endpoint_success(self):
        """Test successful verification via endpoint."""
        data = {
            "code": "def add(a, b): return a + b",
            "function_name": "add",
            "test_cases": [
                {"inputs": {"a": 1, "b": 2}, "expected": 3, "source": "user", "trust_level": "user"},
            ],
        }
        
        result = thesis_verify_endpoint(data)
        
        assert result["success"]
        assert result["tests"]["passed"] == 1
        assert result["receipt_chain_valid"]
    
    def test_endpoint_trust_boundary(self):
        """Test endpoint rejects untrusted test cases."""
        data = {
            "code": "def add(a, b): return a + b",
            "function_name": "add",
            "test_cases": [
                {"inputs": {"a": 1, "b": 2}, "expected": 3, "source": "llm", "trust_level": "untrusted"},
            ],
        }
        
        result = thesis_verify_endpoint(data)
        
        assert not result["success"]
        assert "TRUST BOUNDARY VIOLATION" in result["error"]
    
    def test_endpoint_no_code(self):
        """Test endpoint with missing code."""
        data = {
            "function_name": "add",
            "test_cases": [{"inputs": {"a": 1}, "expected": 2}],
        }
        
        result = thesis_verify_endpoint(data)
        
        assert not result["success"]
        assert "No code" in result["error"]
