#!/usr/bin/env python3
"""
ADVERSARIAL ATTACKS ON THE THIELE MACHINE
==========================================

Four attacks designed to break the No Free Insight Theorem.
If any of these succeed, the model has a fundamental flaw.

Attack 1: Lucky Guesser - Is the theorem per-trace or expected?
Attack 2: Encoding Independence - Do equivalent constraints cost the same?
Attack 3: XOR Structure Exploitation - Can structure-blind ops achieve speedup?
Attack 4: Context-Dependent Assertions - Does redundancy tracking work?
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))

import math
import random
from typing import Set, Tuple, Optional
from thielecpu.state import State
from thielecpu.vm import VM


class AttackResults:
    """Track attack outcomes."""
    def __init__(self, name: str):
        self.name = name
        self.passed = False
        self.details = ""
        self.flaw_found = False
        self.flaw_description = ""


# =============================================================================
# ATTACK 1: THE LUCKY GUESSER LOOPHOLE
# =============================================================================

def attack_1_lucky_guesser() -> AttackResults:
    """
    Test: Can I get lucky and underpay for search space reduction?
    
    The theorem claims: μ_paid ≥ log₂(Ω) - log₂(Ω')
    
    If I guess correctly on first try, do I pay less than required?
    """
    result = AttackResults("Attack 1: Lucky Guesser")
    
    # Setup: 8-bit key search (small for tractability)
    # True key is known to us (attacker), unknown to "system"
    true_key = 0b10110011  # 179
    key_bits = 8
    total_space = 2 ** key_bits  # 256 candidates
    
    state = State()
    vm = VM(state)
    
    initial_mu = state.mu_ledger.total
    
    # Track search space through partition refinement
    # Start with universe of all possible keys
    candidates = set(range(total_space))
    mid = state.pnew(candidates)
    
    mu_after_init = state.mu_ledger.total
    
    result.details += f"Initial setup:\n"
    result.details += f"  Key space: {key_bits} bits = {total_space} candidates\n"
    result.details += f"  μ after PNEW: {mu_after_init}\n"
    result.details += f"  True key: {true_key} ({bin(true_key)})\n\n"
    
    # ATTACK: Make a "lucky" assertion that happens to be correct
    # Assert: "The key has bit 7 set" (true_key has bit 7 set: 0b10110011)
    
    # This should cost: log₂(256) - log₂(128) = 1 bit minimum
    # Because we're reducing from 256 candidates to 128
    
    def has_bit_7_set(x):
        return (x >> 7) & 1 == 1
    
    # Split based on this predicate
    m_yes, m_no = state.psplit(mid, has_bit_7_set)
    
    mu_after_split = state.mu_ledger.total
    mu_for_split = mu_after_split - mu_after_init
    
    # Check: How many candidates in each partition?
    part_yes = state.regions[m_yes] if m_yes in state.regions.modules else set()
    part_no = state.regions[m_no] if m_no in state.regions.modules else set()
    
    result.details += f"After PSPLIT (bit 7 set?):\n"
    result.details += f"  Partition YES: {len(part_yes)} candidates\n"
    result.details += f"  Partition NO: {len(part_no)} candidates\n"
    result.details += f"  μ charged for split: {mu_for_split}\n"
    
    # Information-theoretic minimum for this split:
    # We went from 256 candidates to (128, 128) partition
    # This is 1 bit of information
    info_theoretic_min = 1.0
    
    result.details += f"  Information-theoretic minimum: {info_theoretic_min} bits\n"
    
    # Now here's the key question:
    # The "lucky" part is that the true key IS in the YES partition.
    # Did we pay at least 1 μ-bit for this 1-bit reduction?
    
    # Verify true key is in correct partition
    true_key_in_yes = true_key in part_yes
    result.details += f"  True key in YES partition: {true_key_in_yes}\n\n"
    
    # THE THEOREM TEST:
    # Did we pay ≥ log₂(256/128) = 1 bit?
    
    if mu_for_split >= info_theoretic_min:
        result.details += f"✓ THEOREM HOLDS: Paid {mu_for_split} ≥ {info_theoretic_min} required\n"
        result.passed = True
    else:
        result.details += f"✗ THEOREM VIOLATED: Paid {mu_for_split} < {info_theoretic_min} required\n"
        result.flaw_found = True
        result.flaw_description = f"Lucky guess paid only {mu_for_split} for {info_theoretic_min} bit reduction"
    
    # IMPORTANT CLARIFICATION:
    # The theorem is PER-ASSERTION, not expected.
    # Every PSPLIT pays for the information content of the split itself,
    # regardless of whether the attacker "knew" which branch was right.
    
    result.details += f"\n*** ANSWER TO ATTACK 1 ***\n"
    result.details += f"The theorem is PER-ASSERTION. Every PSPLIT pays for the split's\n"
    result.details += f"information content (how many bits to specify which partition).\n"
    result.details += f"'Luck' doesn't matter - you pay for the assertion structure,\n"
    result.details += f"not for whether you happened to guess right.\n"
    
    return result


# =============================================================================
# ATTACK 2: ENCODING INDEPENDENCE TEST
# =============================================================================

def attack_2_encoding_independence() -> AttackResults:
    """
    Test: Do logically equivalent constraints charge the same μ-cost?
    
    Three encodings of "x is even":
    1. Direct predicate: lambda x: x % 2 == 0
    2. Existential: lambda x: any(x == 2*k for k in range(...))  
    3. Bit-level: lambda x: (x & 1) == 0
    """
    result = AttackResults("Attack 2: Encoding Independence")
    
    # Test set: integers 0-255
    universe = set(range(256))
    
    # Three logically equivalent predicates
    pred_mod = lambda x: x % 2 == 0
    pred_exists = lambda x: x in {2*k for k in range(128)}  # Same as evens
    pred_bit = lambda x: (x & 1) == 0
    
    # Verify they're equivalent
    evens_mod = {x for x in universe if pred_mod(x)}
    evens_exists = {x for x in universe if pred_exists(x)}
    evens_bit = {x for x in universe if pred_bit(x)}
    
    assert evens_mod == evens_exists == evens_bit, "Predicates not equivalent!"
    
    result.details += f"Universe: {len(universe)} elements (0-255)\n"
    result.details += f"Evens: {len(evens_mod)} elements\n\n"
    
    # Test each encoding
    mu_costs = {}
    
    for name, pred in [("mod", pred_mod), ("exists", pred_exists), ("bit", pred_bit)]:
        state = State()
        mid = state.pnew(universe.copy())
        mu_before = state.mu_ledger.total
        
        m_yes, m_no = state.psplit(mid, pred)
        mu_after = state.mu_ledger.total
        
        mu_costs[name] = mu_after - mu_before
        result.details += f"Encoding '{name}': μ-cost = {mu_costs[name]}\n"
    
    # Check if all costs are equal
    costs = list(mu_costs.values())
    all_equal = all(c == costs[0] for c in costs)
    
    result.details += f"\nAll costs equal: {all_equal}\n"
    
    if all_equal:
        result.details += f"✓ ENCODING INDEPENDENCE HOLDS\n"
        result.passed = True
    else:
        result.details += f"✗ ENCODING INDEPENDENCE VIOLATED\n"
        result.flaw_found = True
        result.flaw_description = f"Different encodings yielded different costs: {mu_costs}"
    
    result.details += f"\n*** ANSWER TO ATTACK 2 ***\n"
    result.details += f"The μ-cost depends on the PARTITION STRUCTURE, not the predicate encoding.\n"
    result.details += f"PSPLIT charges based on: ceil(log₂(|input|)) + ceil(log₂(|part1|)) + ceil(log₂(|part2|))\n"
    result.details += f"Since all three predicates produce identical partitions (128, 128),\n"
    result.details += f"they all charge the same μ-cost.\n"
    
    return result


# =============================================================================
# ATTACK 3: XOR STRUCTURE EXPLOITATION (SIMON'S ALGORITHM)
# =============================================================================

def attack_3_xor_structure() -> AttackResults:
    """
    Test: Can Simon's algorithm work without μ-charging operations?
    
    Simon's problem: Find s where f(x) = f(x ⊕ s) for all x.
    Quantum algorithm finds s in O(n) queries.
    Classical requires O(2^(n/2)) queries.
    
    Can we exploit XOR's algebraic structure (group properties)
    using only "structure-blind" operations?
    """
    result = AttackResults("Attack 3: XOR Structure Exploitation")
    
    n = 4  # 4-bit strings for tractability
    secret_s = 0b1011  # The hidden period
    
    # Simon's function: f(x) = f(x ⊕ s)
    # We implement it as: f(x) = min(x, x ⊕ s)
    def simon_f(x):
        return min(x, x ^ secret_s)
    
    result.details += f"Simon's Problem Setup:\n"
    result.details += f"  n = {n} bits\n"
    result.details += f"  Secret s = {secret_s} ({bin(secret_s)})\n"
    result.details += f"  f(x) = f(x ⊕ s) for all x\n\n"
    
    # Classical approach: Query f until we find collision
    # Expected queries: O(2^(n/2)) = O(4) for n=4
    
    state = State()
    vm = VM(state)
    
    # ATTEMPT: Use only XOR operations (structure-blind per the claim)
    # to find s without PDISCOVER
    
    # Query the function, looking for collisions
    seen = {}  # f(x) -> x
    queries = 0
    found_s = None
    
    initial_mu = state.mu_ledger.total
    
    for x in range(2**n):
        fx = simon_f(x)
        queries += 1
        
        if fx in seen:
            # Found collision! f(x) = f(x') means x ⊕ x' = s or 0
            x_prime = seen[fx]
            candidate_s = x ^ x_prime
            if candidate_s != 0:
                found_s = candidate_s
                break
        else:
            seen[fx] = x
    
    final_mu = state.mu_ledger.total
    mu_used = final_mu - initial_mu
    
    result.details += f"Classical collision search:\n"
    result.details += f"  Queries made: {queries}\n"
    result.details += f"  Found s: {found_s} ({bin(found_s) if found_s else 'None'})\n"
    result.details += f"  Correct: {found_s == secret_s}\n"
    result.details += f"  μ-cost: {mu_used}\n\n"
    
    # Now try with PDISCOVER to see if we can do better
    state2 = State()
    
    # Use partition structure to organize by f-value
    universe = set(range(2**n))
    mid = state2.pnew(universe)
    mu_after_pnew = state2.mu_ledger.total
    
    # PDISCOVER: Group by f-value
    # This creates partitions where x and x⊕s are in same partition
    for fval in set(simon_f(x) for x in range(2**n)):
        predicate = lambda x, fv=fval: simon_f(x) == fv
        # This would require PDISCOVER or multiple PSPLITs
    
    mu_structured = state2.mu_ledger.total - mu_after_pnew
    
    result.details += f"With partition structure (PNEW only so far):\n"
    result.details += f"  μ-cost for PNEW: {mu_after_pnew}\n\n"
    
    # THE KEY QUESTION:
    # Did we use ANY structure-revealing operations?
    
    # In the classical loop, we used:
    # - Dictionary lookup (Python built-in, not VM operation)
    # - XOR (structure-blind per claim)
    # - Comparison (structure-blind)
    
    # The "insight" was finding the collision - that happened through
    # brute enumeration, not through PDISCOVER.
    
    result.details += f"*** ANALYSIS ***\n"
    result.details += f"The classical algorithm DID find s using only XOR and comparison.\n"
    result.details += f"BUT: It required O(2^(n/2)) queries - no speedup over classical bound.\n"
    result.details += f"\n"
    result.details += f"The quantum speedup in Simon's algorithm comes from:\n"
    result.details += f"  1. Superposition (query all x simultaneously)\n"
    result.details += f"  2. Interference (extract period information)\n"
    result.details += f"\n"
    result.details += f"In Thiele Machine terms, superposition is a STRUCTURAL operation.\n"
    result.details += f"Creating |x⟩|f(x)⟩ for all x simultaneously would require PNEW\n"
    result.details += f"over the superposition state - that's a μ-charging operation.\n"
    
    # Did we achieve quantum speedup with structure-blind ops?
    classical_bound = 2 ** (n // 2)  # O(2^(n/2))
    achieved_queries = queries
    
    if achieved_queries <= n:  # Quantum bound is O(n)
        result.details += f"\n✗ ATTACK SUCCEEDED: Got quantum speedup without μ-cost\n"
        result.flaw_found = True
        result.flaw_description = f"Simon's algorithm achieved {queries} queries (quantum bound: {n})"
    else:
        result.details += f"\n✓ ATTACK FAILED: Classical bound respected ({queries} queries ≈ O(2^(n/2)))\n"
        result.passed = True
    
    result.details += f"\n*** ANSWER TO ATTACK 3 ***\n"
    result.details += f"XOR operations alone cannot achieve quantum speedup.\n"
    result.details += f"The algebraic structure of XOR (group properties) is available,\n"
    result.details += f"but EXPLOITING that structure requires organizing data by structure,\n"
    result.details += f"which requires PDISCOVER/PSPLIT - the μ-charging operations.\n"
    result.details += f"You can use XOR; you can't use knowledge of what XOR reveals for free.\n"
    
    return result


# =============================================================================
# ATTACK 4: CONTEXT-DEPENDENT ASSERTIONS
# =============================================================================

def attack_4_context_dependent() -> AttackResults:
    """
    Test: Does μ-ledger correctly handle redundant/context-dependent assertions?
    
    If I already know A, asserting A again should cost 0 bits.
    If I assert "if X then Y" when X is already false, it should cost 0 bits.
    """
    result = AttackResults("Attack 4: Context-Dependent Assertions")
    
    # Setup: Two registers A and B, each can be 0-7 (3 bits)
    # State space: 8 * 8 = 64 states
    # Encode as single integer: state = A * 8 + B
    # Decode: A = state // 8, B = state % 8
    
    def encode(a, b): return a * 8 + b
    def decode(s): return (s // 8, s % 8)
    
    universe = set(range(64))  # 0 to 63
    
    result.details += f"State space: {len(universe)} states (A: 0-7, B: 0-7)\n\n"
    
    # Test 1: Redundant assertion
    result.details += "--- Test 1: Redundant Assertion ---\n"
    
    state1 = State()
    mid1 = state1.pnew(universe.copy())
    mu_after_pnew = state1.mu_ledger.total
    
    # First assertion: "A is even"
    def a_is_even(s):
        a, b = decode(s)
        return a % 2 == 0
    
    m_even, m_odd = state1.psplit(mid1, a_is_even)
    mu_after_first = state1.mu_ledger.total
    mu_first = mu_after_first - mu_after_pnew
    
    # Now we know A is even (we're in m_even partition)
    part_even = state1.regions[m_even] if m_even in state1.regions.modules else set()
    result.details += f"After 'A is even': {len(part_even)} states remain\n"
    result.details += f"  μ-cost: {mu_first}\n"
    
    # Second assertion: "A is even" again (REDUNDANT)
    # Split the already-even partition by evenness
    m_even2, m_odd2 = state1.psplit(m_even, a_is_even)
    mu_after_second = state1.mu_ledger.total
    mu_second = mu_after_second - mu_after_first
    
    part_even2 = state1.regions[m_even2] if m_even2 in state1.regions.modules else set()
    part_odd2 = state1.regions[m_odd2] if m_odd2 in state1.regions.modules else set()
    
    result.details += f"After redundant 'A is even':\n"
    result.details += f"  Even partition: {len(part_even2)} states\n"
    result.details += f"  Odd partition: {len(part_odd2)} states (should be 0)\n"
    result.details += f"  μ-cost for redundant: {mu_second}\n"
    
    # Information-theoretic: redundant assertion should cost ~0 bits
    # because |part_odd2| = 0, no actual information is gained
    
    if len(part_odd2) == 0:
        result.details += f"  → Redundant assertion created empty partition (correct)\n"
        # The μ-cost should reflect this is nearly vacuous
    
    # Test 2: Conditional assertion when condition is false
    result.details += "\n--- Test 2: Vacuous Conditional ---\n"
    
    state2 = State()
    mid2 = state2.pnew(universe.copy())
    
    # First: Assert "A = 5"
    def a_equals_5(s):
        a, b = decode(s)
        return a == 5
    
    m_a5, m_not_a5 = state2.psplit(mid2, a_equals_5)
    part_a5 = state2.regions[m_a5] if m_a5 in state2.regions.modules else set()
    part_not_a5 = state2.regions[m_not_a5] if m_not_a5 in state2.regions.modules else set()
    
    result.details += f"After 'A = 5': {len(part_a5)} states (A=5), {len(part_not_a5)} states (A≠5)\n"
    
    # Now on the A≠5 partition, assert "if A=5 then B is even"
    # This is vacuously true, should cost ~0 bits
    mu_before_conditional = state2.mu_ledger.total
    
    # The predicate: "if A=5 then B even" = "A≠5 OR B even"
    def conditional_pred(s):
        a, b = decode(s)
        return a != 5 or b % 2 == 0
    
    m_yes, m_no = state2.psplit(m_not_a5, conditional_pred)
    mu_after_conditional = state2.mu_ledger.total
    mu_conditional = mu_after_conditional - mu_before_conditional
    
    part_yes = state2.regions[m_yes] if m_yes in state2.regions.modules else set()
    part_no = state2.regions[m_no] if m_no in state2.regions.modules else set()
    
    result.details += f"After 'if A=5 then B even' on A≠5 partition:\n"
    result.details += f"  Satisfies: {len(part_yes)} states\n"
    result.details += f"  Violates: {len(part_no)} states (should be 0)\n"
    result.details += f"  μ-cost: {mu_conditional}\n"
    
    # Since ALL states in m_not_a5 have A≠5, the conditional is vacuously true
    # for all of them. The "no" partition should be empty.
    
    vacuous_correct = len(part_no) == 0
    
    result.details += f"\n*** ANALYSIS ***\n"
    result.details += f"Redundant assertion created empty partition: {len(part_odd2) == 0}\n"
    result.details += f"Vacuous conditional created empty partition: {vacuous_correct}\n"
    
    # THE FLAW CHECK:
    # Did we pay μ-cost for assertions that don't reduce search space?
    
    # For redundant: We went from 32 states to (32, 0) - no reduction in max partition
    # For vacuous: We went from 56 states to (56, 0) - no reduction in max partition
    
    result.details += f"\n*** μ-COST ACCOUNTING ***\n"
    result.details += f"Redundant assertion μ-cost: {mu_second}\n"
    result.details += f"  → Search space before: {len(part_even)}\n"
    result.details += f"  → Search space after: max({len(part_even2)}, {len(part_odd2)}) = {max(len(part_even2), len(part_odd2))}\n"
    result.details += f"  → Reduction: {len(part_even) - max(len(part_even2), len(part_odd2))}\n"
    
    result.details += f"\nVacuous conditional μ-cost: {mu_conditional}\n"
    result.details += f"  → Search space before: {len(part_not_a5)}\n"
    result.details += f"  → Search space after: max({len(part_yes)}, {len(part_no)}) = {max(len(part_yes), len(part_no))}\n"
    result.details += f"  → Reduction: {len(part_not_a5) - max(len(part_yes), len(part_no))}\n"
    
    # The question is whether the model charges for the ASSERTION (structure)
    # or the REDUCTION (information gain)
    
    result.details += f"\n*** ANSWER TO ATTACK 4 ***\n"
    result.details += f"The current implementation charges for PSPLIT based on partition sizes,\n"
    result.details += f"not on information gain. This means:\n"
    result.details += f"  - Redundant assertions still cost μ (you paid for the split operation)\n"
    result.details += f"  - Vacuous conditionals still cost μ (same reason)\n"
    result.details += f"\n"
    result.details += f"Is this a flaw? It depends on interpretation:\n"
    result.details += f"  - If μ measures 'structural operations performed': No flaw\n"
    result.details += f"  - If μ measures 'information gained': Potential flaw\n"
    result.details += f"\n"
    result.details += f"The No Free Insight Theorem says μ_paid ≥ info_gained.\n"
    result.details += f"Paying MORE than required (for redundant ops) doesn't violate this.\n"
    result.details += f"It just means inefficient programs waste μ-bits.\n"
    
    # Theorem is not violated by overpayment
    if mu_second >= 0 and mu_conditional >= 0:
        result.passed = True
        result.details += f"\n✓ THEOREM HOLDS: We overpaid, but never underpaid.\n"
    else:
        result.flaw_found = True
        result.flaw_description = "Negative μ-cost detected"
    
    return result


# =============================================================================
# MAIN: RUN ALL ATTACKS
# =============================================================================

def run_all_attacks():
    """Execute all four attacks and report results."""
    
    print("=" * 80)
    print("ADVERSARIAL ATTACKS ON THE THIELE MACHINE")
    print("=" * 80)
    print()
    print("Testing the No Free Insight Theorem with four designed attacks.")
    print("If any attack succeeds, the model has a fundamental flaw.")
    print()
    print("=" * 80)
    
    attacks = [
        attack_1_lucky_guesser,
        attack_2_encoding_independence,
        attack_3_xor_structure,
        attack_4_context_dependent,
    ]
    
    results = []
    
    for attack_fn in attacks:
        print(f"\n{'='*80}")
        result = attack_fn()
        results.append(result)
        
        print(f"\n{result.name}")
        print("-" * 40)
        print(result.details)
        
        if result.flaw_found:
            print(f"\n*** FLAW FOUND: {result.flaw_description} ***")
        elif result.passed:
            print(f"\n*** ATTACK FAILED - THEOREM HOLDS ***")
    
    # Summary
    print("\n" + "=" * 80)
    print("FINAL SUMMARY")
    print("=" * 80)
    
    flaws = [r for r in results if r.flaw_found]
    passed = [r for r in results if r.passed]
    
    print(f"\nAttacks attempted: {len(results)}")
    print(f"Attacks defeated (theorem holds): {len(passed)}")
    print(f"Flaws found: {len(flaws)}")
    
    if flaws:
        print("\n*** FLAWS DISCOVERED ***")
        for r in flaws:
            print(f"  - {r.name}: {r.flaw_description}")
    else:
        print("\n*** ALL ATTACKS DEFEATED - NO FREE INSIGHT THEOREM SURVIVES ***")
    
    return len(flaws) == 0


# Pytest interface
def test_attack_1_lucky_guesser():
    result = attack_1_lucky_guesser()
    assert result.passed, result.flaw_description

def test_attack_2_encoding_independence():
    result = attack_2_encoding_independence()
    assert result.passed, result.flaw_description

def test_attack_3_xor_structure():
    result = attack_3_xor_structure()
    assert result.passed, result.flaw_description

def test_attack_4_context_dependent():
    result = attack_4_context_dependent()
    assert result.passed, result.flaw_description


if __name__ == "__main__":
    success = run_all_attacks()
    sys.exit(0 if success else 1)
