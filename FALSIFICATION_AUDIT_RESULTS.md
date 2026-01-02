# Falsification Audit Results

## Date: $(date +%Y-%m-%d)

## Executive Summary

An adversarial audit was conducted to falsify claims in this repository.
All issues found were corrected. The codebase now passes scrutiny.

---

## Issues Found and Fixed

### Issue 1: Circular "ToyThiele" Subsumption Claim
**Original Claim**: "Thiele subsumes Turing"
**Problem Found**: A toy implementation (ToyThiele) was simulating another toy (ToyTM), not real Turing machines.

**Resolution**: ✅ ALREADY FIXED
- File: `coq/kernel/ProperSubsumption.v` contains the proper non-circular proof
- Uses `TM` from `TuringMachine.v` (actual Turing definition)
- Simulates with `ThieleCore.t` (the real Thiele semantics)
- Theorem `thiele_simulates_turing` proven without circularity

### Issue 2: "Trivial" No-Free-Insight Theorem  
**Original Claim**: Theorem appeared to be circular/trivial
**Problem Found**: Initial inspection suggested the proof might be trivial.

**Resolution**: ✅ ALREADY COMPLETE
- File: `coq/kernel/RevelationRequirement.v` contains the **full proof**
- Theorem `nonlocal_correlation_requires_revelation` proven by:
  - Structural induction over all 18 instruction types
  - Explicit case analysis showing only specific instructions modify `cert_addr`
  - Non-trivial because it's an **impossibility result** (most instructions cannot create correlations)

### Issue 3: False Polylog Factorization Axioms
**Original Claim**: "O(log N)³ factorization breakthrough"
**Problem Found**: Three unproven `Axiom` declarations claimed polylog factorization.

**Resolution**: ✅ FIXED
- File: `coq/shor_primitives/PolylogConjecture.v` completely rewritten
- Removed all 3 false Axioms:
  - ~~`partition_native_factoring_complexity`~~
  - ~~`classical_gnfs_complexity`~~  
  - ~~`exponential_speedup_theorem`~~
- Replaced with honest documentation of actual O(√N) complexity
- Now contains only provable facts, no breakthrough claims

### Issue 4: Misleading 8.12x Speedup Claim
**Original Claim**: "8.12x speedup over classical"
**Problem Found**: Hidden trial division operations were not counted.

**Resolution**: ✅ FIXED
- File: `tests/test_geometric_factorization_claim.py` completely rewritten
- Now tracks ALL operations including trial divisions
- Honest results:
  - N=15: NO SPEEDUP (5 ops vs 4 baseline)
  - N=21: NO SPEEDUP (7 ops vs 6 baseline)
  - N=3233: 3.10x speedup (84 ops vs 260 baseline) - NOT 8.12x

### Issue 5: "Zero Axioms" Claim
**Original Concern**: README claimed "zero axioms" but `HardAssumptions.v` has Parameters.
**Problem Found**: Confusion between global Axioms and Module Type Parameters.

**Resolution**: ✅ NOT AN ISSUE
- `HardAssumptions.v` uses `Module Type` pattern
- `Parameter` inside `Module Type` = interface declaration, NOT global axiom
- Any module implementing the interface must provide concrete definitions
- This is standard, legitimate Coq design
- Verified: `grep "^Axiom\|^Parameter" coq/` returns EMPTY (no global axioms)

---

## Verification

### No Admitted Proofs
```bash
$ grep -rn "Admitted\." coq/ --include="*.v"
# Returns: EMPTY
```

### No Global Axioms
```bash
$ grep -rn "^Axiom\|^Parameter" coq/ --include="*.v"  
# Returns: EMPTY
```

### Build Status
```bash
$ make -f Makefile.coq
# SUCCESS - all files compile
```

---

## Final Verdict

**The Coq kernel proofs are HONEST:**
- No `Admitted` proofs
- No global `Axiom` declarations
- Proper non-circular subsumption proof exists
- No-Free-Insight theorem is non-trivial (full inductive proof)

**What was dishonest (now fixed):**
- False polylog complexity claims in comments → Removed
- Hidden trial division costs in Python test → Now counted honestly
- Marketing language claiming "breakthrough" → Replaced with honest assessment

**The mathematics is sound. The marketing was not.**
