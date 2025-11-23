# ThieleUniversalBridge Compilation Progress Log

## Session 2025-11-23 (Continued)

### Optimization Iterations

#### Iteration 1: Helper Lemmas with Qed (Previous session)
**Status**: Helper lemmas compile fast (0.003-0.005s), main lemma times out
**Approach**: Created `temp1_preserved_through_addr_write` and `temp1_preserved_through_pc_write` as separate lemmas
**Result**: TIMEOUT - Main lemma still times out during Qed

#### Iteration 2: Wrapped Everything in Abstract
**Status**: Helper lemmas compile fast, main lemma times out
**Approach**: Wrapped all proof bodies in `abstract` tactic
**Result**: TIMEOUT - No improvement, compilation hangs after intros in main lemma

#### Iteration 3: Helper Lemmas with Defined (Current)
**Status**: IN PROGRESS - Testing now
**Approach**: Changed helper lemmas from Qed to Defined (transparent), simplified main lemma to use `eq_trans` directly
**Compilation Progress**:
- Helper lemmas compile: 0.005s and 0.003s ✓
- Main lemma starts, gets through setup tactics
- Hangs after `unfold CPU.step`

**Analysis**: The issue appears to be in applying the helper lemmas even when they're transparent. The composition via `eq_trans` might still be creating a large term.

### Root Cause Refinement

The problem is NOT just in the helper lemmas themselves, but in **how they compose** when applied to symbolic `run_n cpu N` terms. Even with transparent definitions, the kernel has to type-check the composition, which involves:
1. Expanding `run_n cpu 5` to `run1 (run_n cpu 4)`
2. Expanding `CPU.step` 
3. Matching the complex write_reg patterns
4. Type-checking the equality chain

### Next Approaches to Try

#### Option A: Axiomatize This One Lemma Temporarily
- Replace proof with `Admitted` temporarily  
- Get rest of file compiling to see if there are other bottlenecks
- Come back to prove it later after other issues are resolved
- **Pros**: Unblocks progress, identifies other issues
- **Cons**: Leaves proof incomplete

#### Option B: Split the File
- Move problematic lemmas to separate file
- Import from main file
- **Pros**: Isolates the issue
- **Cons**: Significant refactoring

#### Option C: Simplify the Lemma Statement
- Maybe the lemma is proving something too complex
- Try proving a more specific version first
- **Pros**: Might avoid the bottleneck
- **Cons**: May not be sufficient for downstream uses

#### Option D: Pre-compute More
- Add explicit definitions for `run_n cpu 3`, `run_n cpu 4`, `run_n cpu 5`
- Work with concrete definitions rather than applications
- **Pros**: Reduces runtime expansion
- **Cons**: Requires careful state management

### Recommendation

Given time constraints and need for progress:
1. **Short term**: Try Option D (pre-compute states) - 15-30 min
2. If that doesn't work: Use Option A (admit temporarily) - 5 min
3. Document the issue thoroughly
4. Continue with rest of file to identify other bottlenecks
5. Return to this specific lemma with fresh approach

The goal is to make **measurable progress** and identify **all bottlenecks**, not get stuck on one lemma indefinitely.

### Time Tracking
- Session 1: ~3.5 hours (infrastructure + initial optimization)
- Session 2 so far: ~1.5 hours (iterations 1-3)
- **Total**: ~5 hours
- **Estimate to complete**: Unknown - this one lemma is proving very difficult

### Key Learning
Proof term explosion in Coq is a very challenging problem. The standard techniques (abstract, Defined, helper lemmas) are not sufficient for this particular proof structure. More radical approaches (file splitting, temporary admits, or complete proof restructuring) may be necessary.
