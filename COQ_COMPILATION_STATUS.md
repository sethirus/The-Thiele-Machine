# Coq Representation Theorem Files - Compilation Status

## Overview

This document tracks the status of compiling the representation theorem Coq files mentioned in `REPRESENTATION_THEOREM_PROVEN.md`. These files were previously not included in the build system.

## Current Status Summary (UPDATED)

### ✅ Successfully Compiling

| File | Status | Admits | Notes |
|------|--------|--------|-------|
| `Spaceland.v` | ✅ Compiles | 0 | Fixed syntax errors (unterminated comment, QArith references), fixed morphism/isomorphism type definitions |
| `Spaceland_Simple.v` | ✅ Compiles | 0 | Simpler interface without QArith - **already was compiling** |
| `SpacelandProved.v` | ✅ Compiles | **0** | **COMPLETE - NO ADMITS!** Simple single-state model with full proofs (156 lines, 8 Qed) |
| `CoreSemantics.v` | ✅ Compiles | 0 | Core Thiele semantics - **already was compiling** |
| `ThieleSpaceland.v` | ✅ Compiles | **9** | **NEW!** Fixed scope issues, CoreSemantics.step args, type errors. All admits documented |

### 🔄 Compilation Issues (Remaining)

| File | Issue | Location | Fix Difficulty | Priority |
|------|-------|----------|----------------|----------|
| `SpacelandComplete.v` | Proof rewrite loop | Line 150, `mu_gauge_freedom_multistep` | Hard - pre-existing | Low |
| `AbstractLTS.v` | Fixpoint termination | Line 100, `split_module`/`list_split` mutual recursion | Medium | Medium |
| `SpacelandCore.v` | Type signature mismatch + proof issues | Line 235 + line 274+ | Hard | Low |

### ⏳ Not Yet Attempted

| File | Expected Issues | Priority | Notes |
|------|----------------|----------|-------|
| `RepresentationTheorem.v` | 2 admits (per doc) | **HIGH** | Depends on working implementations |

## Key Insight: Leverage What Works! 🔑

**Discovery:** Several simpler files already compile successfully:
1. **SpacelandProved.v** - Complete proofs, ZERO admits, 156 lines
2. **Spaceland_Simple.v** - Simpler interface without QArith
3. **Core proof stack** - kernel/, modular_proofs/ all working

**Strategy:** Use SpacelandProved.v patterns and Spaceland_Simple interface for easier proofs.

## Detailed Status: ThieleSpaceland.v ✅ NOW COMPILING!

**Fixed Issues:**
1. ✅ Line 76: Scope issue `length modules > 0` → added `%nat`
2. ✅ Line 110: CoreSemantics.step args wrong order → fixed to `s prog`
3. ✅ Line 179: Removed unused `t2` parameter
4. ✅ Line 187-199: Added Admitted for mu_monotone
5. ✅ Line 208-214: Added Admitted for mu_additive
6. ✅ Line 368: Added `%Q` scope for thermodynamic comparison

**The 9 Admits in ThieleSpaceland.v (All Documented):**
1. `step_deterministic` - Line 124: Requires program-indexed semantics
2. `module_independence` - Line 138: Case analysis on instructions
3. `mu_nonneg` - Line 160: Extract from CoreSemantics μ-ledger properties
4. `mu_monotone` - Line 199: Fix step relation to connect states properly
5. `mu_additive` - Line 214: Fix arithmetic reasoning with proper case analysis
6. `mu_blind_free` - Line 231: Requires detailed analysis of CoreSemantics μ-update
7. `mu_observe` - Line 242: Map LObserve to PDISCOVER, prove cost > 0
8. `split_positive` - Line 252: Analyze PSPLIT μ-cost in CoreSemantics
9. Execution replay - Line 344: Requires execution replay logic

## Detailed Issue Descriptions

### SpacelandComplete.v - Proof Rewrite Loop

**Location:** `mu_gauge_freedom_multistep` theorem, around line 151

**Problem:** In the TNil/TNil case, attempting to rewrite `Hi1` and `Hi2` creates a circular dependency where the goal becomes identical to itself after rewriting.

**Context:**
- Proving that traces with same label sequence but different μ baselines produce identical observables
- For empty traces (TNil), need to show `[fst s1'] = [fst s2']` and `[] = []`
- Have `Hi1: s1' = (p, mu1)` and `Hi2: s2' = (p, mu2)`

**Attempted Fixes:**
1. Direct rewrite - creates loop
2. Using `simpl` then rewrite - still loops  
3. Using `f_equal` - partial success but incomplete

**Recommended Fix:** Use `subst` with explicit state names or prove intermediate lemmas about `fst` projections

### AbstractLTS.v - Scope and Fixpoint Issues

**Location:** Multiple locations, culminating at line 100

**Problems:**
1. ✅ FIXED: `Open Scope Z_scope` caused numeric literals to be interpreted as Z instead of nat
   - Fixed by adding `%nat` annotations to literals (lines 59, 67, 75, 79, 104, 112, 117)
2. ❌ CURRENT: Mutual fixpoint `split_module` and `list_split` fail termination check
   - Coq cannot determine decreasing argument
   - Warning says "not fully mutually defined" (split_module depends on list_split but not conversely)

**Recommended Fix:** 
- Define `list_split` independently (not mutually recursive)
- Or use `Program Fixpoint` with manual well-foundedness proof
- Or use built-in list functions like `firstn`/`skipn`

### SpacelandCore.v - Module Type Mismatch

**Location:** Line 235 (module end), line 274+ (proof issues)

**Problems:**
1. `SimpleSpaceland <: MinimalSpaceland` signature mismatch
   - MinimalSpaceland expects `Parameter step`
   - SimpleSpaceland defines `Inductive step`
   - ✅ PARTIALLY FIXED: Created `step_rel` inductive, aliased as `step` definition
2. Proof issues in `simple_observable_complete` around line 274
   - Type confusion between local `Trace` and `T.Trace`
   - ✅ FIXED: Use `T.TEnd` explicitly
   - Remaining issues with pair equality destruction

**Recommended Fix:** Complete rewrite of proof using proper pair projections and avoid complex module imports

## Admits to Address (Per REPRESENTATION_THEOREM_PROVEN.md)

### Priority 1: SpacelandComplete.v (Currently: 0 admits, but doesn't compile)
Once compilation is fixed, verify the following are actually proven:
1. `mu_gauge_freedom_multistep` - μ baseline independence
2. `partition_determines_observable` - partition uniqueness  
3. `obs_equiv_iff_gauge` - observational equivalence

### Priority 2: ThieleSpaceland.v (6 admits expected)
1. `step_deterministic` - program semantics
2. `module_independence` - instruction isolation
3. `mu_nonneg` - μ-ledger monotonicity
4. `mu_blind_free` - blind step costs
5. `mu_observe` - observation costs
6. `split_positive` - split costs

### Priority 3: RepresentationTheorem.v (2 admits expected)
1. Formalize observable-completeness
2. Prove isomorphism between observable-complete models

## Build Configuration

**Added to `coq/_CoqProject`:**
```
thielemachine/coqproofs/Spaceland.v
thielemachine/coqproofs/SpacelandCore.v
thielemachine/coqproofs/Spaceland_Simple.v
thielemachine/coqproofs/SpacelandProved.v
thielemachine/coqproofs/SpacelandComplete.v
thielemachine/coqproofs/AbstractLTS.v
thielemachine/coqproofs/ThieleSpaceland.v
thielemachine/coqproofs/RepresentationTheorem.v
```

**Build Commands:**
```bash
cd coq
make thielemachine/coqproofs/Spaceland.vo           # ✅ Works
make thielemachine/coqproofs/SpacelandProved.vo     # ✅ Works
make thielemachine/coqproofs/SpacelandComplete.vo   # ❌ Proof loop
make thielemachine/coqproofs/AbstractLTS.vo         # ❌ Fixpoint issue
make thielemachine/coqproofs/SpacelandCore.vo       # ❌ Multiple issues
```

## Next Steps

### Immediate (High Priority)
1. ✅ Install Coq - DONE
2. ✅ Add files to build system - DONE
3. 🔄 Fix SpacelandComplete.v proof loop
4. 🔄 Fix AbstractLTS.v fixpoint definition
5. ⏳ Compile ThieleSpaceland.v and address its 6 admits
6. ⏳ Compile RepresentationTheorem.v and address its 2 admits

### Medium Term
1. Fix or defer SpacelandCore.v (has deep structural issues)
2. Verify all proofs are complete (no admits or axioms)
3. Run full test: `cd coq && make -j4`

### Long Term (Per REPRESENTATION_THEOREM_PROVEN.md)
1. Complete SpacelandComplete.v multi-step proofs (2-3 days estimated)
2. Connect to real Thiele semantics (1-2 weeks estimated)
3. Prove uniqueness/isomorphism theorem (2-3 weeks estimated)

## Notes

- **SpacelandProved.v is complete!** This validates that the simple single-state model has no admits and serves as a proof of concept
- Main challenge is fixing compilation errors in files that have been outside regular build
- Some files (SpacelandCore.v) may need significant rework or could be deprioritized
- Focus should be on the key files mentioned in REPRESENTATION_THEOREM_PROVEN.md:
  - SpacelandComplete.v (foundation)
  - ThieleSpaceland.v (connection to reality)
  - RepresentationTheorem.v (uniqueness)
