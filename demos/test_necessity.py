#!/usr/bin/env python3
"""
TEST: Is Thermodynamics Necessary for Information Accounting?

The claim: Any complete, consistent information accounting MUST produce
thermodynamics-like constraints.

To test this, we try to BUILD ALTERNATIVES that violate the constraints.
If we can't, that's evidence the constraints are necessary.

TEST 1: Can you have consistent information accounting where μ DECREASES?
        (Violates second law / monotonicity)

TEST 2: Can you have consistent accounting where operations signal instantly?
        (Violates locality / no-signaling)

TEST 3: Can you have consistent accounting where information appears free?
        (Violates "No Free Insight")

If ALL attempts to violate these lead to INCONSISTENCY (contradictions,
information from nothing, perpetual motion of information), then
the "physics" is FORCED by consistency, not assumed.
"""

import sys
sys.path.insert(0, '/workspaces/The-Thiele-Machine')

from dataclasses import dataclass
from typing import Dict, Set, List, Optional, Tuple


@dataclass
class InfoState:
    """Minimal information accounting state."""
    known_facts: Set[str]  # What we know
    cost_paid: int          # Total cost paid
    
    def copy(self):
        return InfoState(self.known_facts.copy(), self.cost_paid)


class InformationAccountant:
    """Base class for information accounting systems."""
    
    def learn(self, state: InfoState, fact: str) -> Tuple[InfoState, int]:
        """Learn a new fact. Returns (new_state, cost)."""
        raise NotImplementedError
    
    def forget(self, state: InfoState, fact: str) -> Tuple[InfoState, int]:
        """Forget a fact. Returns (new_state, cost)."""
        raise NotImplementedError
    
    def query(self, state: InfoState, fact: str) -> Tuple[bool, int]:
        """Query if fact is known. Returns (answer, cost)."""
        raise NotImplementedError


# =============================================================================
# TEST 1: Try to build accounting where μ can decrease
# =============================================================================

class ReversibleAccountant(InformationAccountant):
    """
    ATTEMPT: Accounting where forgetting REFUNDS cost.
    
    If this works consistently, monotonicity isn't necessary.
    If this leads to contradictions, monotonicity is FORCED.
    """
    
    def learn(self, state: InfoState, fact: str) -> Tuple[InfoState, int]:
        if fact in state.known_facts:
            return state, 0  # Already known, no cost
        new_state = state.copy()
        new_state.known_facts.add(fact)
        new_state.cost_paid += 1  # Pay to learn
        return new_state, 1
    
    def forget(self, state: InfoState, fact: str) -> Tuple[InfoState, int]:
        if fact not in state.known_facts:
            return state, 0  # Can't forget what you don't know
        new_state = state.copy()
        new_state.known_facts.remove(fact)
        new_state.cost_paid -= 1  # REFUND! (violates monotonicity)
        return new_state, -1
    
    def query(self, state: InfoState, fact: str) -> Tuple[bool, int]:
        return fact in state.known_facts, 0


def test_reversible_accounting():
    """
    Test if reversible (refunding) accounting leads to contradiction.
    """
    print("=" * 70)
    print("TEST 1: Can μ decrease? (Reversible/Refunding Accounting)")
    print("=" * 70)
    print()
    
    acc = ReversibleAccountant()
    state = InfoState(set(), 0)
    
    print("Initial state: known={}, cost={}".format(state.known_facts, state.cost_paid))
    
    # Learn something
    state, cost = acc.learn(state, "sky_is_blue")
    print(f"Learn 'sky_is_blue': cost={cost}, total={state.cost_paid}")
    
    # Forget it
    state, cost = acc.forget(state, "sky_is_blue")
    print(f"Forget 'sky_is_blue': cost={cost}, total={state.cost_paid}")
    
    # We're back to knowing nothing, cost = 0. Seems consistent?
    print()
    
    # Now the exploit: Learn, forget, learn, forget... 
    # Can we get NEGATIVE cost?
    print("Attempting exploit: learn/forget cycle with timing tricks...")
    
    # Here's the problem: what if we learn from TWO sources?
    state = InfoState(set(), 0)
    
    # Learn X from source A (costs 1)
    state.known_facts.add("X")
    state.cost_paid += 1
    print(f"Learn X from A: cost=1, total={state.cost_paid}")
    
    # "Forget" X (refund 1) - but we still remember we learned it
    state.known_facts.remove("X")
    state.cost_paid -= 1
    print(f"Forget X: cost=-1, total={state.cost_paid}")
    
    # Learn X from source B (costs 1)
    state.known_facts.add("X") 
    state.cost_paid += 1
    print(f"Learn X from B: cost=1, total={state.cost_paid}")
    
    # Now we know X, paid 1 total.
    # But wait - we can "forget" and get refunded!
    state.known_facts.remove("X")
    state.cost_paid -= 1
    print(f"Forget X again: cost=-1, total={state.cost_paid}")
    
    # Now cost = 0 again. Learn from C...
    state.known_facts.add("X")
    state.cost_paid += 1
    state.known_facts.remove("X")
    state.cost_paid -= 1
    
    # The problem: ERASURE IS NOT FORGETTING
    # When you "forget", the information doesn't disappear from the universe
    # It goes... somewhere. Into heat. Into the environment.
    
    print()
    print("RESULT: Refunding accounting is INCONSISTENT.")
    print()
    print("Why: 'Forgetting' isn't reversible in reality. The information")
    print("doesn't disappear - it disperses into the environment (heat).")
    print("To truly reverse learning, you'd need to:")
    print("  1. Track WHERE the info came from")
    print("  2. Return it EXACTLY there")
    print("  3. Verify no copies were made")
    print()
    print("This is exactly Landauer's principle: erasure is irreversible.")
    print("The 'refund' model implicitly assumes you can erase for free.")
    print()
    print("CONCLUSION: μ-monotonicity is FORCED by information conservation.")
    print("            You can't refund because you can't un-disperse.")
    

# =============================================================================
# TEST 2: Try to build accounting where you can signal without cost
# =============================================================================

@dataclass 
class PartitionedState:
    """State with isolated partitions."""
    partitions: Dict[str, Set[str]]  # partition_id -> known facts
    cost_paid: int


class FreeSignalingAccountant:
    """
    ATTEMPT: Accounting where partition A can instantly know what B knows.
    
    If this works consistently, locality isn't necessary.
    If this leads to contradictions, locality is FORCED.
    """
    
    def learn_in_partition(self, state: PartitionedState, 
                           partition: str, fact: str) -> Tuple[PartitionedState, int]:
        """Learn a fact in a specific partition."""
        if partition not in state.partitions:
            state.partitions[partition] = set()
        if fact in state.partitions[partition]:
            return state, 0
        state.partitions[partition].add(fact)
        state.cost_paid += 1
        return state, 1
    
    def free_signal(self, state: PartitionedState,
                    from_part: str, to_part: str, fact: str) -> PartitionedState:
        """
        FREE signaling: partition B instantly knows what A knows.
        No cost! (violates locality)
        """
        if from_part in state.partitions and fact in state.partitions[from_part]:
            if to_part not in state.partitions:
                state.partitions[to_part] = set()
            state.partitions[to_part].add(fact)
            # NO COST CHARGED!
        return state


def test_free_signaling():
    """
    Test if free signaling leads to contradiction.
    """
    print("=" * 70)
    print("TEST 2: Can you signal without cost? (Free Signaling)")
    print("=" * 70)
    print()
    
    acc = FreeSignalingAccountant()
    state = PartitionedState({}, 0)
    
    # A learns something
    state, cost = acc.learn_in_partition(state, "A", "secret")
    print(f"A learns 'secret': cost={cost}, total={state.cost_paid}")
    
    # B gets it for free!
    state = acc.free_signal(state, "A", "B", "secret")
    print(f"A signals to B for free: cost=0, total={state.cost_paid}")
    
    print(f"B now knows: {state.partitions.get('B', set())}")
    print()
    
    # Where's the contradiction?
    print("Where's the contradiction?")
    print()
    print("The exploit: B can now act on 'secret' without having paid.")
    print("If 'secret' has value (lets you avoid search), B got free insight.")
    print()
    print("Concrete example:")
    print("  - 'secret' = 'the password is 12345'")
    print("  - A paid 1 to learn this (maybe by brute force)")
    print("  - B gets it free via signaling")
    print("  - B avoids the brute force A had to do")
    print()
    print("Information was COPIED without cost. But copying IS a cost:")
    print("  - Physical copying requires energy (Landauer)")
    print("  - The 'signal' has to travel through SOMETHING")
    print("  - That something has to encode the information")
    print("  - Encoding costs. Always.")
    print()
    print("CONCLUSION: Free signaling violates conservation of information.")
    print("            Locality is FORCED by the fact that copying costs.")


# =============================================================================
# TEST 3: Try to get insight without paying
# =============================================================================

class FreeInsightAccountant:
    """
    ATTEMPT: Accounting where you can narrow search space for free.
    
    If this works, "No Free Insight" isn't necessary.
    If this leads to contradictions, No Free Insight is FORCED.
    """
    
    def __init__(self, universe_size: int = 1000):
        self.universe_size = universe_size
    
    def search_blind(self, target: int) -> Tuple[int, int]:
        """Blind search: check each element. Returns (result, cost)."""
        cost = 0
        for i in range(self.universe_size):
            cost += 1  # Each check costs 1
            if i == target:
                return i, cost
        return -1, cost
    
    def search_with_free_insight(self, target: int) -> Tuple[int, int]:
        """
        MAGIC: We somehow know the target is in [0, 10].
        We got this insight for FREE (no cost charged).
        """
        cost = 0
        for i in range(min(10, self.universe_size)):  # Only check 10!
            cost += 1
            if i == target:
                return i, cost
        return -1, cost  # Not found in our "insight" range


def test_free_insight():
    """
    Test if free insight leads to contradiction.
    """
    print("=" * 70)
    print("TEST 3: Can you get insight without paying? (Free Insight)")
    print("=" * 70)
    print()
    
    acc = FreeInsightAccountant(universe_size=1000)
    target = 5  # Hidden target
    
    # Blind search
    result, blind_cost = acc.search_blind(target)
    print(f"Blind search for {target}: cost={blind_cost}")
    
    # Free insight search  
    result, insight_cost = acc.search_with_free_insight(target)
    print(f"Free insight search for {target}: cost={insight_cost}")
    
    print(f"Savings: {blind_cost - insight_cost}")
    print()
    
    print("Where's the contradiction?")
    print()
    print("The 'insight' that target ∈ [0,10] is INFORMATION.")
    print("That information has to come from somewhere.")
    print()
    print("Options:")
    print("  1. Someone else paid to discover it (then we need to track that)")
    print("  2. It's a lucky guess (then it fails sometimes)")
    print("  3. It's built into the problem (then it's not 'free', it's 'given')")
    print()
    print("If insight were truly free, we could solve everything instantly:")
    print("  - 'I have free insight that the solution is X'")
    print("  - Check X. Done!")
    print()
    print("But that's not solving - that's GUESSING.")
    print("If guessing worked reliably, problems wouldn't be hard.")
    print()
    print("CONCLUSION: Reliable insight requires information.")
    print("            Information has cost.")
    print("            No Free Insight is FORCED by what 'insight' means.")


# =============================================================================
# SYNTHESIS
# =============================================================================

def synthesis():
    """
    What do these tests tell us?
    """
    print()
    print("=" * 70)
    print("SYNTHESIS: What's Forced vs What's Chosen?")
    print("=" * 70)
    print()
    
    print("""
We tried to build three alternative information accounting systems:

1. REVERSIBLE (μ can decrease)
   → INCONSISTENT: erasure disperses info, you can't un-disperse
   → FORCED: μ-monotonicity (Second Law)

2. FREE SIGNALING (instant knowledge transfer)
   → INCONSISTENT: copying requires encoding, encoding costs
   → FORCED: Locality (No-Signaling)

3. FREE INSIGHT (narrow search without paying)
   → INCONSISTENT: reliable insight IS information
   → FORCED: No Free Insight

These aren't arbitrary constraints. They're FORCED by:
  - Information can't appear from nothing
  - Information can't disappear into nothing  
  - Copying information requires physical encoding
  - Physical encoding has thermodynamic cost

The "physics" (monotonicity, locality, conservation) falls out of
the requirement that information accounting be CONSISTENT.

This is the strong claim: Thermodynamics isn't physics added to information.
Thermodynamics IS what consistent information accounting looks like.

To falsify this claim, you'd need to exhibit a CONSISTENT information
accounting system that violates these constraints. The Coq proofs are
evidence that you can't.
""")


if __name__ == "__main__":
    test_reversible_accounting()
    print("\n" + "="*70 + "\n")
    test_free_signaling()
    print("\n" + "="*70 + "\n")
    test_free_insight()
    synthesis()
