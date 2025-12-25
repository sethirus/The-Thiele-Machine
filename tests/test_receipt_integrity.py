"""
Test suite for receipt integrity verification.

Validates the fix for the receipt forgery vulnerability discovered on December 24, 2025.

The vulnerability: The original receipt system signed CLAIMS without verifying
that the claimed μ_delta matched the actual instruction cost.

The fix implements the Coq receipt_mu_consistent property:
    post_mu = pre_mu + instruction_cost(instruction)

Tests cover:
1. Legitimate receipts pass all verification
2. Forged receipts (inflated μ) are rejected
3. Arithmetic mismatches are detected
4. Chain verification works correctly
5. Edge cases and boundary conditions
"""

import pytest
from thielecpu.receipts import (
    StepReceipt,
    WitnessState,
    InstructionWitness,
    StepObservation,
    verify_receipt_chain,
    compute_chain_final_mu,
)


class TestReceiptIntegrity:
    """Test individual receipt integrity verification."""

    def test_legitimate_receipt_passes(self):
        """A properly constructed receipt should pass all verification."""
        pre = WitnessState(pc=0, status=0, mu_acc=0, cert_addr='')
        post = WitnessState(pc=1, status=0, mu_acc=100, cert_addr='')
        instr = InstructionWitness(op='PNEW', payload={'region': list(range(100))})
        obs = StepObservation(event=None, mu_delta=100, cert={})
        
        receipt = StepReceipt.assemble(0, instr, pre, post, obs)
        
        assert receipt.verify_mu_integrity() is True
        assert receipt.verify_instruction_cost() is True
        assert receipt.verify() is True

    def test_forged_receipt_rejected(self):
        """A forged receipt claiming inflated μ should be rejected."""
        # Attacker claims 9999 μ for a tiny 1-element operation
        pre = WitnessState(pc=0, status=0, mu_acc=0, cert_addr='')
        post = WitnessState(pc=1, status=0, mu_acc=9999, cert_addr='')
        instr = InstructionWitness(op='PNEW', payload={'region': [1]})  # Only 1 item!
        obs = StepObservation(event=None, mu_delta=9999, cert={})  # Claims 9999!
        
        receipt = StepReceipt.assemble(0, instr, pre, post, obs)
        
        # Signature is valid (attacker can sign anything)
        assert receipt.verify(verify_mu_integrity=False, verify_instruction_cost=False) is True
        # But instruction cost check FAILS
        assert receipt.verify_instruction_cost() is False
        # Full verification FAILS
        assert receipt.verify() is False

    def test_arithmetic_mismatch_detected(self):
        """A receipt with inconsistent μ arithmetic should be rejected."""
        # pre=0, post=50, but delta=100 - doesn't add up!
        pre = WitnessState(pc=0, status=0, mu_acc=0, cert_addr='')
        post = WitnessState(pc=1, status=0, mu_acc=50, cert_addr='')  # 0 + 100 ≠ 50
        instr = InstructionWitness(op='PNEW', payload={'region': list(range(100))})
        obs = StepObservation(event=None, mu_delta=100, cert={})
        
        receipt = StepReceipt.assemble(0, instr, pre, post, obs)
        
        assert receipt.verify_mu_integrity() is False
        assert receipt.verify() is False

    def test_zero_cost_halt(self):
        """HALT instruction should have zero cost."""
        pre = WitnessState(pc=0, status=0, mu_acc=100, cert_addr='')
        post = WitnessState(pc=1, status=0, mu_acc=100, cert_addr='')  # Same μ
        instr = InstructionWitness(op='HALT', payload={})
        obs = StepObservation(event=None, mu_delta=0, cert={})
        
        receipt = StepReceipt.assemble(0, instr, pre, post, obs)
        
        assert receipt.verify_mu_integrity() is True
        assert receipt.verify_instruction_cost() is True
        assert receipt.verify() is True

    def test_pnew_cost_matches_region_size(self):
        """PNEW cost should equal the region size."""
        # Small region
        pre1 = WitnessState(pc=0, status=0, mu_acc=0, cert_addr='')
        post1 = WitnessState(pc=1, status=0, mu_acc=5, cert_addr='')
        instr1 = InstructionWitness(op='PNEW', payload={'region': [0, 1, 2, 3, 4]})
        obs1 = StepObservation(event=None, mu_delta=5, cert={})
        receipt1 = StepReceipt.assemble(0, instr1, pre1, post1, obs1)
        assert receipt1.verify() is True

        # Large region
        pre2 = WitnessState(pc=0, status=0, mu_acc=0, cert_addr='')
        post2 = WitnessState(pc=1, status=0, mu_acc=1000, cert_addr='')
        instr2 = InstructionWitness(op='PNEW', payload={'region': list(range(1000))})
        obs2 = StepObservation(event=None, mu_delta=1000, cert={})
        receipt2 = StepReceipt.assemble(0, instr2, pre2, post2, obs2)
        assert receipt2.verify() is True


class TestReceiptChain:
    """Test receipt chain verification."""

    def test_valid_chain(self):
        """A valid chain should pass verification."""
        # Receipt 1: 0 → 100
        r1 = StepReceipt.assemble(
            0,
            InstructionWitness(op='PNEW', payload={'region': list(range(100))}),
            WitnessState(pc=0, status=0, mu_acc=0, cert_addr=''),
            WitnessState(pc=1, status=0, mu_acc=100, cert_addr=''),
            StepObservation(event=None, mu_delta=100, cert={}),
        )
        
        # Receipt 2: 100 → 150
        r2 = StepReceipt.assemble(
            1,
            InstructionWitness(op='PNEW', payload={'region': list(range(50))}),
            WitnessState(pc=1, status=0, mu_acc=100, cert_addr=''),  # Chains from r1
            WitnessState(pc=2, status=0, mu_acc=150, cert_addr=''),
            StepObservation(event=None, mu_delta=50, cert={}),
        )
        
        # Receipt 3: 150 → 150 (HALT)
        r3 = StepReceipt.assemble(
            2,
            InstructionWitness(op='HALT', payload={}),
            WitnessState(pc=2, status=0, mu_acc=150, cert_addr=''),
            WitnessState(pc=3, status=0, mu_acc=150, cert_addr=''),
            StepObservation(event=None, mu_delta=0, cert={}),
        )
        
        chain = [r1, r2, r3]
        valid, error = verify_receipt_chain(chain, initial_mu=0)
        
        assert valid is True
        assert error is None
        assert compute_chain_final_mu(chain, initial_mu=0) == 150

    def test_chain_with_wrong_initial_mu(self):
        """Chain starting from wrong μ should fail."""
        r1 = StepReceipt.assemble(
            0,
            InstructionWitness(op='PNEW', payload={'region': list(range(100))}),
            WitnessState(pc=0, status=0, mu_acc=50, cert_addr=''),  # Starts at 50, not 0
            WitnessState(pc=1, status=0, mu_acc=150, cert_addr=''),
            StepObservation(event=None, mu_delta=100, cert={}),
        )
        
        valid, error = verify_receipt_chain([r1], initial_mu=0)
        
        assert valid is False
        assert "initial_mu" in error

    def test_chain_break_detected(self):
        """A chain with a break should be detected."""
        r1 = StepReceipt.assemble(
            0,
            InstructionWitness(op='PNEW', payload={'region': list(range(100))}),
            WitnessState(pc=0, status=0, mu_acc=0, cert_addr=''),
            WitnessState(pc=1, status=0, mu_acc=100, cert_addr=''),
            StepObservation(event=None, mu_delta=100, cert={}),
        )
        
        # r2 starts from wrong μ (50 instead of 100)
        r2 = StepReceipt.assemble(
            1,
            InstructionWitness(op='PNEW', payload={'region': list(range(50))}),
            WitnessState(pc=1, status=0, mu_acc=50, cert_addr=''),  # BREAK! Should be 100
            WitnessState(pc=2, status=0, mu_acc=100, cert_addr=''),
            StepObservation(event=None, mu_delta=50, cert={}),
        )
        
        valid, error = verify_receipt_chain([r1, r2], initial_mu=0)
        
        assert valid is False
        assert "Chain break" in error

    def test_empty_chain_valid(self):
        """An empty chain should be valid."""
        valid, error = verify_receipt_chain([], initial_mu=0)
        assert valid is True
        assert error is None


class TestForgeryScenarios:
    """Test various forgery attack scenarios."""

    def test_inflated_single_receipt(self):
        """Single receipt with inflated cost should fail."""
        # Attacker creates receipt claiming 10000 μ for empty operation
        pre = WitnessState(pc=0, status=0, mu_acc=0, cert_addr='')
        post = WitnessState(pc=1, status=0, mu_acc=10000, cert_addr='')
        instr = InstructionWitness(op='PNEW', payload={'region': []})  # Empty!
        obs = StepObservation(event=None, mu_delta=10000, cert={})
        
        receipt = StepReceipt.assemble(0, instr, pre, post, obs)
        
        # Expected cost for empty region is 0
        assert receipt.verify_instruction_cost() is False

    def test_forged_chain(self):
        """A chain with a forged receipt should fail."""
        # Legitimate receipt 1
        r1 = StepReceipt.assemble(
            0,
            InstructionWitness(op='PNEW', payload={'region': list(range(10))}),
            WitnessState(pc=0, status=0, mu_acc=0, cert_addr=''),
            WitnessState(pc=1, status=0, mu_acc=10, cert_addr=''),
            StepObservation(event=None, mu_delta=10, cert={}),
        )
        
        # Forged receipt 2 - claims 1000 μ for 1 item
        r2 = StepReceipt.assemble(
            1,
            InstructionWitness(op='PNEW', payload={'region': [99]}),  # 1 item
            WitnessState(pc=1, status=0, mu_acc=10, cert_addr=''),
            WitnessState(pc=2, status=0, mu_acc=1010, cert_addr=''),
            StepObservation(event=None, mu_delta=1000, cert={}),  # Claims 1000!
        )
        
        valid, error = verify_receipt_chain([r1, r2], initial_mu=0)
        
        assert valid is False  # Should detect the forgery

    def test_hash_chain_attack(self):
        """Attack: forge receipt from different state with same μ.
        
        VULNERABILITY (fixed): verify_chain_link only checked μ, not state hash.
        
        ATTACK SCENARIO:
        1. Attacker has legitimate receipts for states A -> B (μ = 10)
        2. Attacker wants to claim state C (different data, same μ)
        3. Create forged receipt: starts from C (not B) but claims same μ
        4. OLD: Chain passed because μ values matched
        5. NEW: Chain fails because post_hash(B) ≠ pre_hash(C)
        """
        # Legitimate receipt 1: state A -> B
        r1 = StepReceipt.assemble(
            0,
            InstructionWitness(op='PNEW', payload={'region': list(range(10))}),
            WitnessState(pc=0, status=0, mu_acc=0, cert_addr=''),
            WitnessState(pc=1, status=0, mu_acc=10, cert_addr=''),
            StepObservation(event=None, mu_delta=10, cert={}),
        )
        
        # Forged receipt 2: claims to start from DIFFERENT state C
        # (different pc value means different state hash)
        r2_forged = StepReceipt.assemble(
            1,
            InstructionWitness(op='PNEW', payload={'region': list(range(5))}),
            WitnessState(pc=99, status=0, mu_acc=10, cert_addr='fake'),  # Different state!
            WitnessState(pc=100, status=0, mu_acc=15, cert_addr='fake'),
            StepObservation(event=None, mu_delta=5, cert={}),
        )
        
        # Verify individual receipts pass (signatures are valid)
        assert r1.verify() is True
        assert r2_forged.verify() is True
        
        # BUT the chain should FAIL due to hash discontinuity
        valid, error = verify_receipt_chain([r1, r2_forged], initial_mu=0)
        
        assert valid is False, "Hash chain attack should be detected"
        assert "Chain break" in error or "hash" in error.lower()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
