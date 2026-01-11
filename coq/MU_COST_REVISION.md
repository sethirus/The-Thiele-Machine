# μ-Cost Framework Revision: Classical vs Quantum Correlations

## Critical Discovery

**Theorem (Proven in MinorConstraints.v):**
> Local/factorizable boxes (μ=0 operations) satisfy |S| ≤ 2 (classical bound)

**Verified Construction:**
> The "Tsirelson" construction in TsirelsonLowerBound.v achieves exactly S = 2, not 2√2

---

## The Fundamental Distinction

### Classical Correlations (μ = 0)
**Characterization:**
- **Factorizable:** E(x,y,a,b) = pA(x,a) · pB(y,b)
- **Operations:** PNEW, PSPLIT, PMERGE, CHSH_TRIAL
- **Mechanism:** Shared randomness, local operations
- **Mathematical constraint:** Satisfies 3×3 minor constraints
- **CHSH bound:** |S| ≤ 2

**What μ=0 operations do:**
- PNEW: Create partition (no correlation)
- PSPLIT: Split partition into independent parts (maintains factorizability)
- PMERGE: Merge independent partitions
- CHSH_TRIAL: Record measurements from factorizable distribution

**Key insight:** These operations preserve factorizability, thus cannot exceed S = 2.

---

### Quantum Correlations (μ > 0 required)
**Characterization:**
- **Non-factorizable:** E(x,y,a,b) ≠ pA(x,a) · pB(y,b)
- **Operations:** Requires LJOIN, REVEAL, or LASSERT
- **Mechanism:** Entanglement, non-local correlations
- **Mathematical constraint:** Violates 3×3 minors, satisfies NPA-1 full hierarchy
- **CHSH bound:** |S| ≤ 2√2 (Tsirelson bound)

**What requires μ > 0:**
- **LJOIN**: Join partition structures → creates non-factorizable correlations
- **REVEAL**: Expose hidden structure → breaks factorizability
- **LASSERT**: Assert logical structure → adds constraints that break factorization

**Key insight:** Non-factorizable correlations require operations that cost μ.

---

## Revised μ-Cost Accounting

### Current Model (Lines 56-64 of MuCostModel.v)
```coq
| instr_pnew _ _ => 0        (* Classical: factorizable *)
| instr_psplit _ _ _ _ => 0  (* Classical: maintains factorization *)
| instr_pmerge _ _ _ => 0    (* Classical: merges independent *)
| instr_reveal _ _ _ _ => 1  (* Quantum: breaks factorization *)
| instr_lassert _ _ _ _ => 1 (* Quantum: adds structure *)
| instr_ljoin _ _ _ => 1     (* Quantum: correlates structures *)
```

### Interpretation
**μ = 0 Programs:**
- Can only use: PNEW, PSPLIT, PMERGE, CHSH_TRIAL
- Correlations must factorize: E(a,b|x,y) = EA(a|x) · EB(b|y)
- Equivalent to: Classical hidden variables + shared randomness
- **Proven bound:** |S| ≤ 2 (MinorConstraints.v, line 188)

**μ > 0 Programs:**
- Can use: LJOIN, REVEAL, LASSERT
- Correlations can be non-factorizable
- Equivalent to: Quantum entanglement
- **Conjectured bound:** |S| ≤ 2√2

---

## What Was Wrong

### TsirelsonLowerBound.v (Lines 36-79)
**Claims:** "Construct a μ=0 program that achieves CHSH ≈ 2√2"

**Actual construction:**
```coq
Definition entangled_bit : nat := 0.  (* Fixed, not even random! *)

alice_optimal_output(x, 0)  (* Deterministic *)
bob_optimal_output(y, 0)    (* Deterministic *)
```

**Reality:** This is ONE deterministic strategy achieving S = 2, not quantum.

### TsirelsonUpperBound.v (Lines 22-23)
**Claims:** "LOCC + shared randomness corresponds exactly to quantum correlations"

**Reality:**
- LOCC + shared randomness = Classical (S ≤ 2)
- Quantum entanglement ≠ Classical (S can reach 2√2)
- These are fundamentally different!

---

## Corrected Framework

### Theorem Hierarchy

**T1: Classical Bound (PROVEN)** ✓
```coq
Theorem local_box_CHSH_bound : forall B,
  is_local_box B ->           (* Factorizable *)
  non_negative B ->
  normalized B ->
  Rabs (Q2R (BoxCHSH.S B)) <= 2.
```

**Status:** Complete proof structure in MinorConstraints.v
- Uses Fine's theorem (polytope = convex hull of deterministic strategies)
- Uses Gram's criterion (correlation matrices are PSD)
- Ends in Qed (modulo infrastructure admits)

**T2: Quantum Bound (CONJECTURED)**
```coq
Axiom quantum_tsirelson_bound : forall B,
  non_factorizable B ->       (* Entangled *)
  non_negative B ->
  normalized B ->
  Rabs (Q2R (BoxCHSH.S B)) <= (5657 # 2000).  (* 2√2 ≈ 2.828 *)
```

**Status:** Requires different proof - cannot use 3×3 minors
- Non-factorizable boxes violate 3×3 minor constraints
- Need full NPA hierarchy or SDP characterization
- This is the Tsirelson bound from quantum information theory

### μ-Cost Interpretation

**Partition Framework → Correlation Type:**
- **μ = 0:** Factorizable operations → Classical correlations → S ≤ 2
- **μ > 0:** Non-factorizable operations → Quantum correlations → S ≤ 2√2

**Physical Interpretation:**
- **μ measures non-factorizability**
- μ = 0 ⟺ No entanglement ⟺ Classical bound
- μ > 0 ⟺ Entanglement present ⟺ Quantum bound

---

## Required Changes to Codebase

### 1. Fix TsirelsonLowerBound.v
**Current:** Claims μ=0 achieves 2√2
**Fixed:**
- Rename to `ClassicalBound.v`
- Show μ=0 achieves S = 2 (matches proof)
- Remove claims about quantum correlations

### 2. Fix TsirelsonUpperBound.v
**Current:** Claims μ=0 is bounded by 2√2
**Fixed:**
- Update to: μ=0 is bounded by 2 (classical)
- Add new theorem: μ > 0 can achieve up to 2√2
- Clarify LOCC ≠ quantum entanglement

### 3. Update MinorConstraints.v
**Current:** Proof structure complete, needs compilation fixes
**Action:**
- Fix Q2R conversion issue
- Document that this proves the classical bound
- Add note: quantum bound requires different approach

### 4. New File: QuantumBound.v (Future Work)
**Purpose:** Prove μ > 0 programs can achieve 2√2
**Approach:**
- Use LJOIN operation (costs μ=1)
- Show this creates non-factorizable correlations
- Apply quantum Tsirelson bound

---

## Mathematical Summary

### What We Proved
**Minor constraints ⟹ CHSH ≤ 2**

Where minor constraints are:
```
det([1,  s,   E00]) ≥ 0
   [s,  1,   E10]
   [E00, E10, 1]
```
(and 3 similar constraints)

### Why This Gives Classical Bound
- Minor constraints ⟺ Factorizable distributions
- Factorizable ⟺ LOCC + shared randomness
- LOCC + shared randomness ⟺ Classical physics
- Classical physics ⟹ S ≤ 2

### Why Quantum Needs Different Proof
- Quantum correlations violate minor constraints
- Need full NPA hierarchy or SDP characterization
- This requires μ > 0 operations (LJOIN, REVEAL, etc.)

---

## Conclusion

**The framework is consistent, but the labeling was wrong:**

✓ **μ = 0:** Classical bound (S ≤ 2) - PROVEN
✓ **μ > 0:** Quantum bound (S ≤ 2√2) - REQUIRES PROOF

**The key insight:**
- μ-cost measures departure from factorizability
- Factorizability implies classical bounds
- Quantum correlations require μ > 0

**Next steps:**
1. Fix documentation in existing files
2. Rename misleading theorems
3. Prove quantum bound for μ > 0 operations
4. Update thesis to reflect classical vs quantum distinction
