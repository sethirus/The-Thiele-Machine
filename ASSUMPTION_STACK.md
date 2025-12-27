# ASSUMPTION STACK

**The Thiele Machine Physics Bridge**

This document explicitly lists all assumptions in the Thiele Machine framework, categorized by their nature and scope.

---

## A. FORMAL ASSUMPTIONS (Inside the Model)

These are the primitive definitions and rules within our Coq-verified model. They are **not disputed**—they are the starting point.

### A.1 What μ Measures (Definition)

**μ is an operational cost counter that increments when an agent performs a "revelation" operation.**

Formally:
- `μ : ℕ` — a non-negative integer counter in the VM state
- Each instruction has a μ-cost defined in `MuCostModel.v`
- Total μ-cost of a trace = sum of individual instruction costs

### A.2 μ-Cost Assignment (Operational Rules)

| Operation       | μ-Cost | Reason                                    |
|-----------------|--------|-------------------------------------------|
| `PNEW`          | 0      | Partition creation (structural only)      |
| `PSPLIT`        | 0      | Partition splitting (no new correlations) |
| `PMERGE`        | 0      | Partition merging (no new correlations)   |
| `REVEAL`        | 1      | Exposes hidden partition structure        |
| `LASSERT`       | 1      | Adds correlated structure                 |
| `LJOIN`         | 1      | Joins existing correlations               |
| All other ops   | 0      | Don't modify partition graph              |

**Critical**: These rules are **defined**, not derived. They encode "what counts as revelation."

### A.3 Revelation Primitives

**Revelation** = any operation that:
1. Exposes previously hidden partition structure to an observer
2. Adds entangled/correlated structure between partitions
3. Requires coordination beyond local classical communication

The three revelation operations are:
- `REVEAL(mid, addr, len, μ)` — expose structure
- `LASSERT(mid₁, mid₂, pattern, μ)` — assert correlation
- `LJOIN(mid₁, mid₂, mid_target)` — join correlations

### A.4 μ=0 Class Definition

**Definition**: A program/trace is μ=0 if its total μ-cost equals zero.

```coq
Definition mu_zero_program (fuel : nat) (trace : list vm_instruction) : Prop :=
  mu_cost_of_trace fuel trace 0 = 0.
```

**Consequence**: μ=0 programs can only use:
- Partition rearrangement (`PNEW`, `PSPLIT`, `PMERGE`)
- Local operations
- Classical communication

This is the **LOCC-like class** induced by operational constraints.

---

## B. PHYSICAL INTERPRETATION ASSUMPTIONS (The Bridge)

These are the assumptions that connect our formal model to physical reality. **This is where physics enters.**

### B.1 Irreversibility Assumption

**Statement**: Physical processes implementing "revelation" operations are **thermodynamically irreversible**.

**More precisely**: Any physical process that corresponds to `REVEAL`, `LASSERT`, or `LJOIN` must:
- Export entropy to an environment, OR
- Require work input that dissipates

**Falsifiability**: If a physical revelation process were found that has zero entropy cost, this assumption would be violated.

### B.2 μ-Entropy Proportionality Assumption

**Statement**: μ counts a quantity proportional to **unavoidable entropy increase** or **unavoidable information transfer to environment**.

**Formal**: There exists a constant κ > 0 such that:
```
ΔS_environment ≥ κ · μ
```

where ΔS_environment is the entropy increase in the environment.

**Not claimed**: Exact value of κ (this requires experiments).  
**Claimed**: The relationship is **linear lower bound**.

### B.3 Physical LOCC Correspondence

**Statement**: The μ=0 operational class corresponds to physical LOCC (Local Operations and Classical Communication).

**Justification** (from `NonCircularityAudit.v`):
- μ=0 operations are closed under composition ✓
- μ=0 operations include identity ✓
- Partition ops (`PNEW/PSPLIT/PMERGE`) are μ=0 (classical comm) ✓
- Revelation ops are NOT μ=0 (non-LOCC) ✓

**Caveat**: We say "LOCC-like class induced by μ=0 constraints" not "exactly physical LOCC."

### B.4 Landauer Scaling Assumption

**Statement**: Under standard thermodynamic conditions, μ scales as:
```
E_μ ≥ k_B T ln(2) · μ
```

where:
- E_μ = minimum energy cost
- k_B = Boltzmann constant
- T = temperature
- μ = our operational counter

**This is the testable bridge**: μ-bits map to Landauer's limit.

---

## C. CLAIMS WE ARE **NOT** MAKING

### C.1 NOT: "QM is the universe"

We do **not** claim that the Thiele Machine is a complete model of physical reality. We prove structural equivalences, not ontological identity.

### C.2 NOT: "This proves physics"

Our proofs are **conditional**:
- IF the physical bridge assumptions (B.1-B.4) hold
- THEN 2√2 is the cost-free correlation boundary

The antecedent requires experimental verification.

### C.3 NOT: "All quantum structure is derived"

We derive the **correlation boundary** (Tsirelson bound) from μ-accounting.

We do **not** derive:
- The quantum state space structure
- The tensor product rule
- Specific measurement postulates
- Time evolution (Schrödinger equation)

### C.4 NOT: "We explain why nature has this μ-cost structure"

We take μ-cost rules as **primitives**. The question "why does revelation cost μ?" is outside our model—it's the next level of inquiry.

### C.5 NOT: "Exact joules"

We claim **scaling law** (linear lower bound), not exact energy values. The proportionality constant κ requires measurement.

---

## D. WHAT WE **DO** CLAIM

### D.1 Formal Claim (Proven)

**Theorem** (in Coq, zero admits):
```
max{CHSH : μ=0 program} = 2√2
```

This is a mathematical theorem about our model. It is **not disputed**.

### D.2 Conditional Physical Claim

**IF** Assumptions B.1-B.4 hold,  
**THEN** the Tsirelson bound (2√2) is the cost-free correlation frontier.

### D.3 Testable Prediction

**Prediction**: Any physical process that certifies correlations beyond 2√2 must have detectable thermodynamic cost ≥ κ·μ.

This is **falsifiable** by finding a zero-cost supra-quantum certification.

---

## E. SUMMARY TABLE

| Layer | What | Status |
|-------|------|--------|
| Formal (A) | μ-cost model, VM semantics | **PROVEN** (Coq) |
| Bridge (B) | μ ↔ entropy/irreversibility | **ASSUMED** |
| Physical | 2√2 boundary explanation | **CONDITIONAL** |

---

## F. PASS/FAIL CRITERIA

**This document succeeds if:**

✅ Any skeptic can point to a **specific assumption line** (B.1, B.2, etc.) and say "I disagree with this assumption"

✅ No skeptic can say "you're handwaving" without identifying which assumption they reject

✅ The formal claims (A) are orthogonal to the physical interpretation (B)

---

*Document version: 1.0*  
*Generated: 2025-12-27*  
*Machine-verified components: A.1-A.4 (Coq proofs in coq/kernel/)*
