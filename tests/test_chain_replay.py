"""Attack #4: Chain Replay Attack.

Tests whether valid receipt chains can be replayed in different contexts
to fraudulently claim μ that wasn't earned in the current execution.

Attack vector:
1. Execute program A, earn μ_A with valid receipt chain
2. Start new execution context (program B)
3. Replay the receipts from A in context B
4. Claim μ_A was earned in B without doing the work

The defense should bind receipts to their execution context.
"""

import pytest
import sys
import os
import hashlib
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from thielecpu.receipts import (
    StepReceipt, WitnessState, StepObservation, InstructionWitness,
    verify_receipt_chain, hash_snapshot
)


def make_receipt_with_context(
    step: int,
    op: str,
    pre_mu: int,
    mu_delta: int,
    context_id: str,
) -> StepReceipt:
    """Create a receipt bound to a specific execution context."""
    pre_state = WitnessState(pc=step * 4, status=0, mu_acc=pre_mu, cert_addr=context_id)
    post_state = WitnessState(pc=(step + 1) * 4, status=0, mu_acc=pre_mu + mu_delta, cert_addr=context_id)
    
    instruction = InstructionWitness(op=op, payload={"cost": mu_delta, "context": context_id})
    observation = StepObservation(event=None, mu_delta=mu_delta, cert={"context": context_id})
    
    return StepReceipt.assemble(
        step=step,
        instruction=instruction,
        pre_state=pre_state,
        post_state=post_state,
        observation=observation,
    )


class TestChainReplayAttack:
    """Test chain replay attack scenarios."""
    
    def test_same_context_replay_should_pass(self):
        """Replaying receipts in same context should work."""
        context_a = "execution_context_A"
        
        # Create valid chain in context A
        r1 = make_receipt_with_context(0, "PDISCOVER", 0, 10, context_a)
        r2 = make_receipt_with_context(1, "PDISCOVER", 10, 5, context_a)
        
        chain = [r1, r2]
        
        # Verify in same context - should pass
        valid, error = verify_receipt_chain(chain, initial_mu=0)
        assert valid, f"Same-context verification should pass: {error}"
    
    def test_replay_attack_different_context(self):
        """
        Replay attack: Taking receipts from context A and claiming them in context B.
        
        QUESTION: Does the current system detect this?
        """
        context_a = "execution_context_A_" + str(int(time.time()))
        context_b = "execution_context_B_" + str(int(time.time() + 1))
        
        # Create valid chain in context A
        r1 = make_receipt_with_context(0, "PDISCOVER", 0, 10, context_a)
        r2 = make_receipt_with_context(1, "PDISCOVER", 10, 5, context_a)
        
        chain_from_a = [r1, r2]
        
        # Verify the chain is valid
        valid, error = verify_receipt_chain(chain_from_a, initial_mu=0)
        assert valid, f"Original chain should be valid: {error}"
        
        # ATTACK: Try to claim this chain was from context B
        # The current implementation doesn't check context binding!
        
        # The receipts contain cert_addr = context_a
        # If we try to use them in context B, they should be rejected
        
        # Check if receipts are bound to their context
        assert r1.pre_state.get("cert_addr") == context_a
        assert r2.pre_state.get("cert_addr") == context_a
        
        # Currently: The chain validates without checking context!
        # This is a potential vulnerability
        print(f"\nReceipt context binding: {r1.pre_state.get('cert_addr')}")
        print(f"Chain valid even though context doesn't match claimed B: {valid}")
        
        # The fix would be: verify_receipt_chain should take expected_context
        # and verify all receipts are bound to that context
    
    def test_context_mismatch_within_chain(self):
        """Test chain with mixed contexts - should this be detected?"""
        context_a = "context_A"
        context_b = "context_B"
        
        # Receipt 1 from context A
        r1 = make_receipt_with_context(0, "PDISCOVER", 0, 10, context_a)
        
        # Receipt 2 claims to continue but is from context B!
        # This is a forgery attempt
        pre2 = WitnessState(pc=4, status=0, mu_acc=10, cert_addr=context_b)  # Wrong context!
        post2 = WitnessState(pc=8, status=0, mu_acc=15, cert_addr=context_b)
        
        r2 = StepReceipt.assemble(
            step=1,
            instruction=InstructionWitness(op="PDISCOVER", payload={"cost": 5}),
            pre_state=pre2,
            post_state=post2,
            observation=StepObservation(event=None, mu_delta=5, cert={}),
        )
        
        chain = [r1, r2]
        
        # Currently this passes because we only check μ and hash, not context
        valid, error = verify_receipt_chain(chain, initial_mu=0)
        
        # The chain should be INVALID because contexts don't match
        # But currently it may pass because context isn't checked
        print(f"\nMixed context chain valid: {valid}, error: {error}")
        
        # Check: does hash chain catch the context mismatch?
        # post_state_hash of r1 includes cert_addr = context_a
        # pre_state_hash of r2 includes cert_addr = context_b
        # So hash chain SHOULD break!
        
        if not valid:
            print("GOOD: Hash chain caught context mismatch!")
        else:
            print("BAD: Mixed context chain was accepted - replay attack possible!")


class TestReplayDefenses:
    """Test existing defenses against replay attacks."""
    
    def test_hash_chain_prevents_context_splice(self):
        """
        The hash chain should prevent splicing receipts from different contexts
        because the state hash includes the cert_addr (context).
        """
        context_a = "context_alpha"
        context_b = "context_beta"
        
        # Create receipt in context A
        r1_a = make_receipt_with_context(0, "PDISCOVER", 0, 10, context_a)
        
        # Create receipt in context B that would "continue" from r1_a
        pre_b = WitnessState(pc=4, status=0, mu_acc=10, cert_addr=context_b)
        post_b = WitnessState(pc=8, status=0, mu_acc=15, cert_addr=context_b)
        
        r2_b = StepReceipt.assemble(
            step=1,
            instruction=InstructionWitness(op="PDISCOVER", payload={"cost": 5}),
            pre_state=pre_b,
            post_state=post_b,
            observation=StepObservation(event=None, mu_delta=5, cert={}),
        )
        
        # The hash of r1_a.post_state includes cert_addr = context_a
        # The hash of r2_b.pre_state includes cert_addr = context_b
        # These SHOULD be different!
        
        print(f"\nr1_a.post_state_hash: {r1_a.post_state_hash}")
        print(f"r2_b.pre_state_hash:  {r2_b.pre_state_hash}")
        
        assert r1_a.post_state_hash != r2_b.pre_state_hash, \
            "Different contexts should produce different hashes"
        
        # verify_chain_link should catch this
        chain_ok = r2_b.verify_chain_link(r1_a)
        assert not chain_ok, "Chain link should fail for different contexts"
        
        print("DEFENSE VERIFIED: Hash chain prevents context splicing!")


if __name__ == "__main__":
    print("=== ATTACK #4: Chain Replay Attack ===\n")
    
    test = TestChainReplayAttack()
    
    print("Test 1: Same context replay (should pass)")
    try:
        test.test_same_context_replay_should_pass()
        print("  PASSED")
    except AssertionError as e:
        print(f"  FAILED: {e}")
    
    print("\nTest 2: Replay attack - different context")
    try:
        test.test_replay_attack_different_context()
        print("  CHECK OUTPUT ABOVE")
    except Exception as e:
        print(f"  ERROR: {e}")
    
    print("\nTest 3: Mixed context within chain")
    try:
        test.test_context_mismatch_within_chain()
        print("  CHECK OUTPUT ABOVE")
    except Exception as e:
        print(f"  ERROR: {e}")
    
    print("\n" + "="*60)
    print("DEFENSE TESTS")
    print("="*60)
    
    defense = TestReplayDefenses()
    
    print("\nTest 4: Hash chain prevents context splice")
    try:
        defense.test_hash_chain_prevents_context_splice()
        print("  PASSED")
    except AssertionError as e:
        print(f"  FAILED: {e}")
    
    print("\n=== CONCLUSION ===")
    print("The hash chain (which includes cert_addr/context) SHOULD prevent replay attacks")
    print("because receipts from different contexts have different state hashes.")
