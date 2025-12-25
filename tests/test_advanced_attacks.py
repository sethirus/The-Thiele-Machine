"""Attack #6-8: Advanced Adversarial Tests.

These are more sophisticated attacks targeting:
6. Timing/side-channel: Can we infer μ through timing?
7. Negative μ delta: Can we decrease μ (information destruction)?
8. Floating-point precision: Can we exploit float vs fixed-point mismatch?
"""

import pytest
import sys
import os
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from thielecpu.receipts import (
    StepReceipt, WitnessState, StepObservation, InstructionWitness,
    verify_receipt_chain, mu_in_valid_range, Q16_MAX, Q16_MIN
)
from thielecpu.mu_fixed import FixedPointMu, Q16_ONE


class TestNegativeMuDelta:
    """Attack #6: Can we decrease μ (violate monotonicity)?"""
    
    def test_negative_delta_in_receipt(self):
        """
        ATTACK: Try to create a receipt with negative mu_delta.
        This would violate μ-monotonicity (information can only increase).
        """
        pre_state = WitnessState(pc=0, status=0, mu_acc=100, cert_addr="")
        post_state = WitnessState(pc=4, status=0, mu_acc=90, cert_addr="")  # DECREASE!
        
        instruction = InstructionWitness(op="PDISCOVER", payload={"cost": -10})
        observation = StepObservation(event=None, mu_delta=-10, cert={})  # Negative delta!
        
        receipt = StepReceipt.assemble(
            step=0,
            instruction=instruction,
            pre_state=pre_state,
            post_state=post_state,
            observation=observation,
        )
        
        # The verify_mu_integrity checks: post_mu == pre_mu + mu_delta
        # With pre=100, post=90, delta=-10: 90 == 100 + (-10) = 90 ✓
        # So arithmetic is "consistent" but violates monotonicity!
        
        assert receipt.verify_mu_integrity(), "Arithmetic is technically consistent"
        
        # verify_instruction_cost should now REJECT negative delta
        # This is the monotonicity fix
        cost_valid = receipt.verify_instruction_cost()
        
        print(f"\nNegative delta receipt:")
        print(f"  pre_mu: {pre_state.mu_acc}")
        print(f"  post_mu: {post_state.mu_acc}")
        print(f"  mu_delta: {observation.mu_delta}")
        print(f"  verify_mu_integrity: {receipt.verify_mu_integrity()}")
        print(f"  verify_instruction_cost: {cost_valid}")
        
        # With the fix, negative costs are rejected
        assert not cost_valid, "Negative mu_delta should be rejected (monotonicity)"
        print("  MONOTONICITY ENFORCED: negative delta rejected!")
    
    def test_monotonicity_should_be_enforced(self):
        """μ should NEVER decrease. This is a fundamental property."""
        # In Coq: instruction_cost always returns nat (non-negative)
        # Python should enforce the same
        
        fp = FixedPointMu()
        
        # Try to compute negative information gain
        # information_gain_q16(before, after) requires after <= before
        with pytest.raises(ValueError):
            fp.information_gain_q16(10, 20)  # after > before - should fail
        
        print("\nMonotonicity enforced: can't compute info gain when after > before")


class TestFloatingPointPrecision:
    """Attack #7: Exploit float vs fixed-point mismatch."""
    
    def test_precision_mismatch_attack(self):
        """
        ATTACK: Use floating-point values that look equal but differ in fixed-point.
        """
        fp = FixedPointMu()
        
        # In float: these might round to the same value
        val1 = 1.0000001
        val2 = 1.0000002
        
        # But in Q16.16, they should be different
        q1 = fp.to_q16(val1)
        q2 = fp.to_q16(val2)
        
        print(f"\nFloat vs Fixed-point:")
        print(f"  val1 = {val1} -> Q16.16 = {q1} (0x{q1:08X})")
        print(f"  val2 = {val2} -> Q16.16 = {q2} (0x{q2:08X})")
        print(f"  Q16.16 values equal: {q1 == q2}")
        
        # The Q16.16 representation has 1/65536 precision
        # Values within that precision will map to the same fixed-point
        
        # Test at the precision boundary
        epsilon = 1.0 / Q16_ONE  # Smallest representable difference
        
        val_a = 1.0
        val_b = 1.0 + epsilon
        val_c = 1.0 + epsilon / 2  # Within same Q16.16 bucket
        
        qa = fp.to_q16(val_a)
        qb = fp.to_q16(val_b)
        qc = fp.to_q16(val_c)
        
        print(f"\n  epsilon = {epsilon}")
        print(f"  1.0 -> {qa}")
        print(f"  1.0 + epsilon -> {qb}")
        print(f"  1.0 + epsilon/2 -> {qc}")
        
        assert qa != qb, "Values separated by epsilon should differ"
        # qc might equal qa due to rounding
    
    def test_receipt_uses_exact_values(self):
        """Verify receipts store exact integer μ values, not floats."""
        pre_state = WitnessState(pc=0, status=0, mu_acc=100, cert_addr="")
        post_state = WitnessState(pc=4, status=0, mu_acc=110, cert_addr="")
        
        instruction = InstructionWitness(op="PDISCOVER", payload={"cost": 10})
        observation = StepObservation(event=None, mu_delta=10, cert={})
        
        receipt = StepReceipt.assemble(
            step=0,
            instruction=instruction,
            pre_state=pre_state,
            post_state=post_state,
            observation=observation,
        )
        
        # Check that stored values are exact integers
        assert isinstance(receipt.pre_state["mu_acc"], int)
        assert isinstance(receipt.post_state["mu_acc"], int)
        
        print("\nReceipt stores exact integer μ values")


class TestSignatureReuse:
    """Attack #8: Can we reuse signatures across receipts?"""
    
    def test_signature_binds_to_content(self):
        """Signature should be invalid if any content changes."""
        pre_state = WitnessState(pc=0, status=0, mu_acc=0, cert_addr="")
        post_state = WitnessState(pc=4, status=0, mu_acc=10, cert_addr="")
        
        instruction = InstructionWitness(op="PDISCOVER", payload={"cost": 10})
        observation = StepObservation(event=None, mu_delta=10, cert={})
        
        receipt = StepReceipt.assemble(
            step=0,
            instruction=instruction,
            pre_state=pre_state,
            post_state=post_state,
            observation=observation,
        )
        
        original_sig = receipt.signature
        
        # Try to tamper with the receipt
        tampered_receipt = StepReceipt(
            step=0,
            instruction=instruction,
            pre_state={"pc": 0, "status": 0, "mu_acc": 0, "cert_addr": ""},
            post_state={"pc": 4, "status": 0, "mu_acc": 20, "cert_addr": ""},  # TAMPERED!
            observation=observation,
            pre_state_hash=receipt.pre_state_hash,
            post_state_hash=receipt.post_state_hash,  # Wrong hash now
            signature=original_sig,  # Reuse original signature
        )
        
        # The signature should fail verification
        assert not tampered_receipt.verify(
            verify_mu_integrity=False,  # Skip μ check to test signature only
            verify_instruction_cost=False,
            verify_mu_range=False,
        ), "Tampered receipt should fail signature verification"
        
        print("\nSignature reuse attack blocked - signature binds to content")


class TestEdgeCases:
    """Attack #9: Edge cases and boundary conditions."""
    
    def test_zero_mu_receipt(self):
        """Can we create valid receipt with zero μ?"""
        pre_state = WitnessState(pc=0, status=0, mu_acc=0, cert_addr="")
        post_state = WitnessState(pc=4, status=0, mu_acc=0, cert_addr="")
        
        instruction = InstructionWitness(op="HALT", payload={})
        observation = StepObservation(event=None, mu_delta=0, cert={})
        
        receipt = StepReceipt.assemble(
            step=0,
            instruction=instruction,
            pre_state=pre_state,
            post_state=post_state,
            observation=observation,
        )
        
        # HALT has zero cost, so this should be valid
        assert receipt.verify(), "Zero-cost HALT receipt should be valid"
        print("\nZero μ receipt (HALT) is valid")
    
    def test_max_valid_mu(self):
        """Test receipt at maximum valid μ value."""
        max_mu = Q16_MAX
        
        pre_state = WitnessState(pc=0, status=0, mu_acc=max_mu, cert_addr="")
        post_state = WitnessState(pc=4, status=0, mu_acc=max_mu, cert_addr="")  # HALT, no change
        
        instruction = InstructionWitness(op="HALT", payload={})
        observation = StepObservation(event=None, mu_delta=0, cert={})
        
        receipt = StepReceipt.assemble(
            step=0,
            instruction=instruction,
            pre_state=pre_state,
            post_state=post_state,
            observation=observation,
        )
        
        assert receipt.verify_mu_range(), "Max valid μ should pass range check"
        print(f"\nMax μ = {max_mu} passes range check")
    
    def test_one_over_max_mu(self):
        """Test receipt just over maximum - should fail."""
        over_max = Q16_MAX + 1
        
        assert not mu_in_valid_range(over_max), "One over max should fail range check"
        print(f"\nμ = {over_max} (Q16_MAX + 1) correctly fails range check")


if __name__ == "__main__":
    print("=" * 60)
    print("ADVANCED ADVERSARIAL TESTS")
    print("=" * 60)
    
    print("\n### Attack #6: Negative μ Delta ###")
    neg_test = TestNegativeMuDelta()
    neg_test.test_negative_delta_in_receipt()
    try:
        neg_test.test_monotonicity_should_be_enforced()
        print("  PASSED")
    except Exception as e:
        print(f"  ERROR: {e}")
    
    print("\n### Attack #7: Floating-Point Precision ###")
    fp_test = TestFloatingPointPrecision()
    fp_test.test_precision_mismatch_attack()
    fp_test.test_receipt_uses_exact_values()
    
    print("\n### Attack #8: Signature Reuse ###")
    sig_test = TestSignatureReuse()
    try:
        sig_test.test_signature_binds_to_content()
        print("  PASSED")
    except AssertionError as e:
        print(f"  FAILED: {e}")
    
    print("\n### Attack #9: Edge Cases ###")
    edge_test = TestEdgeCases()
    edge_test.test_zero_mu_receipt()
    edge_test.test_max_valid_mu()
    edge_test.test_one_over_max_mu()
    
    print("\n" + "=" * 60)
    print("ADVANCED TESTS COMPLETE")
    print("=" * 60)
