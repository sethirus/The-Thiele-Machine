# Proof Debt Ledger

This document tracks all assumptions, admits, and incomplete proofs in the Thiele Machine formalization. The goal is 100% constructive proofs with zero proof debt.

**Last Updated**: 2025-01-XX
**INQUISITOR Status**: HIGH: 0, MEDIUM: 4, LOW: 4

---

## Current Status

### ✅ ELIMINATED (Previously HIGH, now resolved)
- All global `Axiom`/`Parameter` declarations → Converted to explicit Context parameters
- All `Admitted` proofs in kernel files → Converted to parameterized theorems
- All `admit` tactics → Removed

### 🟡 ACTIVE DEBT (Tracked & Prioritized)

#### Tier 1: Elementary Proofs (Feasible, ~1-2 weeks total)

These should be proven next. They're all finite/arithmetic and unlock downstream work.

| ID | Assumption | Difficulty | Lines | Priority | Blocker For |
|----|------------|------------|-------|----------|-------------|
| **T1-1** | `normalized_E_bound` | LOW | ~100 | P2 | valid_box_S_le_4 |
| **T1-2** | `valid_box_S_le_4` | LOW | ~50 | P1 | Many CHSH theorems |
| **T1-3** | `local_box_S_le_2` | MEDIUM | ~300 | P2 | Bell inequality chain |
| **T1-4** | `pr_box_no_extension` | MEDIUM | ~400 | P3 | Tripartite results |

**Total Tier 1 debt**: ~850 lines of straightforward Coq

#### Tier 2: Deep Mathematical Results (Long-term)

These encode research-level theorems. Keep as explicit assumptions.

| ID | Assumption | Strategy | Status |
|----|------------|----------|--------|
| **T2-1** | `symmetric_coherence_bound` | SDP certificate checking | CONDITIONAL |
| **T2-2** | `tsirelson_from_algebraic_coherence` | Operator algebra OR reduce to T2-1 | CONDITIONAL |

**Tier 2 Status**: Explicitly parameterized via `HardMathFacts` record. Not blocking progress.

---

## Detailed Breakdown

### T1-1: `normalized_E_bound`
**Statement**: For normalized probability distribution `B`, correlation `E` satisfies `|E| ≤ 1`.

**Proof Strategy**:
```coq
1. Expand E = p00 - p01 - p10 + p11
2. Use normalization: p00 + p01 + p10 + p11 = 1
3. Derive E = 2(p00 + p11) - 1
4. Bound: 0 ≤ p00 + p11 ≤ 1 (from non-negativity + normalization)
5. Therefore: -1 ≤ E ≤ 1
6. Convert to Qabs: need lemma Qabs_bound_iff
```

**Required Infrastructure**:
- `Qabs_bound_iff`: `-a ≤ x ≤ a ↔ Qabs x ≤ a`
- `Q_linear_comb_bound`: Linear combinations of probabilities
- ~10 basic Q arithmetic lemmas

**Estimated Effort**: 1-2 days
**Assignee**: TODO
**Exit Condition**: Theorem proven, INQUISITOR clean, `Print Assumptions` shows only Coq stdlib

---

### T1-2: `valid_box_S_le_4`
**Statement**: `S = E00 + E01 + E10 - E11` with `|Eij| ≤ 1` implies `|S| ≤ 4`.

**Proof Strategy**:
```coq
1. Apply triangle inequality: |S| ≤ |E00| + |E01| + |E10| + |-E11|
2. Use |E11| = |-E11|
3. Sum bounds: |E00| + |E01| + |E10| + |E11| ≤ 1 + 1 + 1 + 1 = 4
```

**Required Infrastructure**:
- `Qabs_triangle`: Triangle inequality for Qabs
- `Qabs_opp`: |−x| = |x|
- `Qabs_add_le`: |a + b| ≤ |a| + |b|

**Estimated Effort**: 1 day (depends on T1-1)
**Assignee**: TODO
**Exit Condition**: Theorem proven, follows from normalized_E_bound

---

### T1-3: `local_box_S_le_2`
**Statement**: Bell's CHSH inequality - local models satisfy `|S| ≤ 2`.

**Proof Strategy**:
```coq
1. Define deterministic strategy type: (nat -> bool) × (nat -> bool)
2. Enumerate all 16 deterministic strategies (2^4 combinations)
3. For each strategy, compute S explicitly
4. Verify |S| ≤ 2 using decide/compute
5. Extend to convex combinations: convex combination of bounded values is bounded
```

**Required Infrastructure**:
- Finite type for deterministic strategies
- Automation for case analysis (ltac or reflect)
- Convexity lemma for Q bounds

**Estimated Effort**: 3-4 days
**Assignee**: TODO
**Exit Condition**: Full constructive proof, no assumptions

---

### T1-4: `pr_box_no_extension`
**Statement**: PR box has no valid tripartite extension.

**Proof Strategy**:
```coq
1. Assume ∃ Box3 satisfying marginal constraints
2. PR box: a⊕b = xy with certainty
3. Case x=y=z=0: Derive a=b, a=c, b=c (consistent)
4. Case x=y=1, z=0: Derive a≠b, a=c, b=c
5. Contradiction: a≠b ∧ a=c ∧ b=c implies a≠a
6. Use Qeq_dec for case analysis on probabilities
```

**Required Infrastructure**:
- Tripartite consistency checking
- XOR arithmetic lemmas
- Case analysis automation

**Estimated Effort**: 4-5 days
**Assignee**: TODO
**Exit Condition**: Proof by contradiction, fully constructive

---

## Medium Priority Items (from INQUISITOR)

| File | Issue | Severity | Action |
|------|-------|----------|--------|
| TsirelsonUniqueness.v:25 | SUSPICIOUS_SHORT_PROOF | MEDIUM | Audit `mu_zero_algebraic_bound` |
| TsirelsonUpperBound.v:347 | SUSPICIOUS_SHORT_PROOF | MEDIUM | Audit `tsirelson_bound_lt_algebraic_max` |
| MuAlu.v:189 | MU_COST_ZERO | MEDIUM | Verify `mu_zero` is intentional |
| OracleImpossibility.v:88 | PROBLEMATIC_IMPORT | MEDIUM | Document Classical axiom usage |

---

## Low Priority Items (from INQUISITOR)

| File | Issue | Severity | Note |
|------|-------|----------|------|
| BellCheck.v:134 | CHSH_BOUND_MISSING | LOW | Tsirelson bound reference |
| BellInequality.v:701,839 | CHSH_BOUND_MISSING | LOW | Tsirelson bound reference |
| BellReceiptLocalGeneral.v:291 | CHSH_BOUND_MISSING | LOW | Tsirelson bound reference |

---

## Progress Tracking

### Milestones

- [x] **M1**: Eliminate all global Axioms (2025-01-XX)
- [ ] **M2**: Prove all Tier 1 assumptions
  - [ ] T1-2: valid_box_S_le_4
  - [ ] T1-3: local_box_S_le_2
  - [ ] T1-4: pr_box_no_extension
  - [ ] T1-1: normalized_E_bound
- [ ] **M3**: Resolve all MEDIUM severity issues
- [ ] **M4**: Clean up LOW severity issues
- [ ] **M5**: 100% constructive kernel (Tier 2 kept conditional)

### Velocity Tracking

| Week | Lines Proven | Assumptions Eliminated | Issues Closed |
|------|--------------|------------------------|---------------|
| W1 (current) | 0 | 6 → Context params | 9 HIGH → 0 |
| W2 | TBD | TBD | TBD |

---

## Notes

### Why These Assumptions Are Reasonable

**Tier 1**: All four are elementary mathematics. Keeping them as assumptions is technical debt, not fundamental - they SHOULD be proven.

**Tier 2**: These encode deep results:
- `symmetric_coherence_bound`: NPA hierarchy (Navascués-Pironio-Acín PRL 98)
- `tsirelson_from_algebraic_coherence`: Tsirelson's theorem (LMP 1980)

These are acceptable as conditional assumptions IF:
1. They're explicitly parameterized (✓ done)
2. They're well-documented with references (✓ done)
3. They're tracked in this ledger (✓ done)
4. Downstream work doesn't hide the dependency (✓ done via Section/Context)

### Future: Certificate Checking

For Tier 2, we can upgrade from "trust the math" to "verify certificates":
- Generate SDP certificate externally (CSDP, SDPA)
- Check certificate in Coq (PSD verification, feasibility check)
- Reduces trust from "NPA theory" to "arithmetic checker"

This is the path to 100% verified, but it's a separate multi-month project.

---

## CI Integration

To prevent regression, add:

```bash
# Guard 1: No new global axioms in kernel
scripts/check_no_axioms.sh coq/kernel/

# Guard 2: Assumption surface doesn't grow
scripts/check_assumptions.sh > assumptions.txt
git diff assumptions.txt  # Fail if new assumptions appear

# Guard 3: INQUISITOR HIGH must stay at 0
python3 scripts/inquisitor.py | grep "HIGH: 0" || exit 1
```

See `CONTRIBUTING.md` for implementation details.
