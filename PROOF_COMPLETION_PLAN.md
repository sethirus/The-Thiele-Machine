# Coq Proof Completion Plan - Discharging Admits and Axioms

## Overview

This document outlines the plan for discharging all admits and axioms in the representation theorem proof files, following the guidance in `REPRESENTATION_THEOREM_PROVEN.md`.

## Current Status

### Files with Admits/Axioms:
1. **SpacelandComplete.v** - Does NOT compile (proof loop at line 150)
2. **ThieleSpaceland.v** - ✅ Compiles with 9 admits
3. **AbstractLTS.v** - ✅ Compiles with 2 admits  
4. **RepresentationTheorem.v** - ✅ Compiles with 21 axioms (exploratory by design)

### Files Complete (0 admits):
- ✅ SpacelandProved.v
- ✅ Spaceland.v
- ✅ CoreSemantics.v

## Priority 1: Fix SpacelandComplete.v Compilation (BLOCKING)

**Status:** Currently does NOT compile due to proof loop at line 150

**Issue:** `mu_gauge_freedom_multistep` theorem has a proof that creates circular rewrites in the TNil/TNil case

**Problem Analysis:**
```coq
Goal: partition_seq (TNil s1') = partition_seq (TNil s2')
Where: s1' = (p, mu1) and s2' = (p, mu2)
Expands to: [fst s1'] = [fst s2']
```

After `rewrite Hi1, Hi2`, this becomes `[fst (p, mu1)] = [fst (p, mu2)]` which simplifies to `[p] = [p]`, but the rewrite creates a loop.

**Solution Attempted:**
- Destruct states before rewriting: `destruct s1' as [p1 m1], s2' as [p2 m2]`
- Extract equalities with injection: `injection Hi1 as Hp1 Hm1`
- This avoids the rewrite loop

**Remaining Issue:**
- TNil/TCons case needs proper contradiction from Hlabels ([] = l2 :: ...)
- TCons/TCons case is more complex and needs induction

**Estimated Time:** 4-6 hours for complete proof

**Strategy:**
1. Fix TNil/TNil case (use injection approach) ✅ Attempted
2. Handle TNil/TCons contradiction (need list discrimination lemma)
3. Complete TCons/TCons case with induction hypothesis

## Priority 2: Complete ThieleSpaceland.v Proofs (9 admits)

### 2.1 step_deterministic (Line 124)
**TODO:** Requires program-indexed semantics

**Analysis:** 
- Need to show `step s l s1 -> step s l s2 -> s1 = s2`
- Thiele step depends on program state
- Requires connecting to CoreSemantics.step

**Dependencies:**
- CoreSemantics.step properties
- Program-indexed state transitions

**Estimated Time:** 2-3 days
**Strategy:** 
1. Analyze CoreSemantics.step definition
2. Prove determinism for each instruction type
3. Lift to ThieleSpaceland step

### 2.2 module_independence (Line 138)
**TODO:** Case analysis on instructions

**Analysis:**
- Show blind steps don't affect other modules
- Requires per-instruction analysis

**Dependencies:**
- Instruction semantics
- Partition structure preservation

**Estimated Time:** 2-3 days
**Strategy:**
1. Case-split on instruction types
2. Show partition preservation per case
3. Prove module isolation

### 2.3 mu_nonneg (Line 160)
**TODO:** Extract from CoreSemantics μ-ledger properties

**Analysis:**
- Show μ costs are non-negative
- CoreSemantics maintains μ-ledger

**Dependencies:**
- CoreSemantics μ-ledger invariants
- Instruction cost definitions

**Estimated Time:** 1-2 days
**Strategy:**
1. Identify CoreSemantics μ-ledger lemmas
2. Extract non-negativity property
3. Lift to ThieleSpaceland

### 2.4 mu_monotone (Line 199)
**TODO:** Fix step relation to connect states properly

**Analysis:**
- Similar to AbstractLTS.mu_monotone
- Need proper state connection in traces

**Estimated Time:** 1 day
**Strategy:**
1. Use trace validity to connect states
2. Apply mu_nonneg
3. Arithmetic with lia

### 2.5 mu_additive (Line 214)
**TODO:** Fix arithmetic reasoning with proper case analysis

**Analysis:**
- Prove trace_mu (trace_concat t1 t2) = trace_mu t1 + trace_mu t2
- Requires induction on trace structure

**Estimated Time:** 1 day
**Strategy:**
1. Induction on t1
2. Case analysis on t1/t2 structure
3. Careful arithmetic with lia

### 2.6 mu_blind_free (Line 231)
**TODO:** Detailed analysis of CoreSemantics μ-update

**Analysis:**
- Show blind steps cost 0
- Requires understanding μ-update in CoreSemantics

**Dependencies:**
- CoreSemantics blind step definition
- μ-update semantics

**Estimated Time:** 2-3 days

### 2.7 mu_observe (Line 242)
**TODO:** Map LObserve to PDISCOVER, prove cost > 0

**Analysis:**
- Connect observation label to PDISCOVER instruction
- Show discovery has positive cost

**Dependencies:**
- PDISCOVER instruction cost
- Observation semantics

**Estimated Time:** 2-3 days

### 2.8 split_positive (Line 252)
**TODO:** Analyze PSPLIT μ-cost in CoreSemantics

**Analysis:**
- Show split operations have positive cost
- Connect to PSPLIT instruction

**Dependencies:**
- PSPLIT instruction semantics
- Split cost definition

**Estimated Time:** 2-3 days

### 2.9 Execution replay (Line 344)
**TODO:** Requires execution replay logic

**Analysis:**
- Build trace from receipt
- Requires forward execution

**Estimated Time:** 2-3 days

**ThieleSpaceland.v Total:** 15-20 days

## Priority 3: Complete AbstractLTS.v Proofs (2 admits)

### 3.1 mu_monotone (Line 237)
**Analysis:** Same as ThieleSpaceland but simpler model
**Estimated Time:** 4-6 hours
**Strategy:** Use trace structure + mu_nonneg

### 3.2 mu_additive (Line 252)
**Analysis:** Trace concatenation preserves μ sum
**Estimated Time:** 4-6 hours
**Strategy:** Induction on trace structure

**AbstractLTS.v Total:** 1-2 days

## Priority 4: RepresentationTheorem.v (21 axioms by design)

**Status:** These are intentionally axioms for exploratory theorem statements

**Analysis:**
- ObservationalEquivalence module: 2 parameters (equivalence relations between different Spaceland instances)
- IsomorphismConstruction module: 2 parameters (comparison functions)
- HiddenStateSpaceland module: 15 axioms (counterexample model demonstrating naive theorem is false)
- RefinedTheorem module: 2 axioms (refined theorem statements)

**Decision:** These should remain as axioms - they're theorem statements and counterexamples, not proofs to complete.

**Time:** N/A (intentional design)

## Overall Timeline Summary

| Task | Estimated Time | Dependencies |
|------|---------------|--------------|
| Fix SpacelandComplete.v | 4-6 hours | None |
| AbstractLTS.v (2 admits) | 1-2 days | None |
| ThieleSpaceland.v (9 admits) | 15-20 days | CoreSemantics analysis |
| RepresentationTheorem.v | N/A | Intentional axioms |

**Total Estimated Time:** 18-24 days of focused proof work

## Recommended Approach

### Phase 1 (Immediate - 1 week):
1. ✅ Fix SpacelandComplete.v compilation (4-6 hours)
2. Complete AbstractLTS.v admits (1-2 days)
3. Complete simpler ThieleSpaceland admits (mu_monotone, mu_additive) (2-3 days)

### Phase 2 (Short-term - 2-3 weeks):
4. Analyze CoreSemantics and document properties needed
5. Complete ThieleSpaceland.v core admits (step_deterministic, module_independence, mu_nonneg)

### Phase 3 (Long-term - 3-4 weeks):
6. Complete remaining ThieleSpaceland.v admits requiring deep CoreSemantics analysis
7. Document final representation theorem status

## Next Steps

1. **Immediate:** Fix SpacelandComplete.v line 150 proof loop
   - Use injection approach to avoid rewrite loop
   - Add helper lemma for list discrimination if needed
   - Complete the inductive case

2. **Next:** Complete AbstractLTS.v admits
   - Both are relatively straightforward
   - Good warm-up for more complex proofs

3. **Then:** Tackle ThieleSpaceland.v systematically
   - Start with simpler admits (mu_monotone, mu_additive)
   - Analyze CoreSemantics properties needed
   - Work through instruction-dependent admits

## Success Criteria

- [ ] SpacelandComplete.v compiles with 0 admits
- [ ] AbstractLTS.v compiles with 0 admits
- [ ] ThieleSpaceland.v compiles with 0 admits
- [ ] All core representation theorem files building cleanly
- [ ] Documentation updated to reflect completed proofs
