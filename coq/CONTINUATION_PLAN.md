# Continuation Plan for ThieleUniversalBridge.v Proofs

## Current Status

File compiles successfully with documented admits. Previous work identified `length_run_n_eq_bounded` as the critical blocker.

## Work Attempted in This Session

Attempted to prove the TODOs in `loop_iteration_no_match` using admitted `length_run_n_eq_bounded`:

### TODOs Attempted:

1. **Line 1936** (TEMP1 preservation through Jz): 
   - **Technical Challenge**: After `unfold CPU.step. simpl.`, the `read_reg_write_reg_diff` lemma pattern doesn't match
   - The goal expands into `nth` on `firstn`/`skipn`/`app` expressions
   - Need manual list reasoning to prove register preservation

2. **Line 1948** (length of cpu4 = 10):
   - **Approach**: Prove `cpu4 = run_n cpu 4` then apply `length_run_n_eq_bounded`
   - **Issue**: The proof `unfold cpu4, cpu3, cpu2, cpu1. unfold run1. rewrite run_n_S...` causes compilation timeout
   - Likely due to aggressive unfolding creating large proof terms

3. **Line 1953** (TEMP1 preservation through AddConst):
   - Same issue as TODO 1 - pattern matching fails after simpl

4. **Line 1957** (length of cpu5 = 10):
   - Same issue as TODO 2 - compilation timeout with unfolding approach

### Root Cause Analysis

The fundamental issue is that after `simpl` or extensive unfolding:
- `CPU.read_reg` expands to `nth r regs 0`
- `CPU.write_reg` expands to `firstn r regs ++ [v] ++ skipn (S r) regs`
- Existing lemmas like `read_reg_write_reg_diff` no longer match the expanded forms
- Trying to prove equalities by excessive unfolding creates large proof terms that cause timeouts

### Viable Approaches Forward

#### Approach 1: Strengthen Helper Lemmas

Create wrapper lemmas that work after simpl:
```coq
Lemma read_reg_nth_preservation : forall r r' v regs,
  r <> r' ->
  r < length regs ->
  r' < length regs ->
  nth r (firstn r' regs ++ [v] ++ skipn (S r') regs) 0 = nth r regs 0.
```

This lemma would match the expanded form and could be proved once, then reused.

#### Approach 2: Avoid Simpl, Use Abstract Reasoning

Don't use `simpl` after `unfold CPU.step`. Instead:
1. Reason about `CPU.step` abstractly using its properties
2. Use `change` tactic to transform goals without expanding definitions
3. Apply lemmas at the abstract level before any simplification

#### Approach 3: Use run_n Properties Directly

Instead of unfolding cpu4 to run_n cpu 4, state it as a separate lemma:
```coq
Lemma cpu4_is_run_n_4 : cpu4 = run_n cpu 4.
Proof. (* Prove once, seal it *) Qed.
```

Then reuse without re-unfolding.

## Recommendation

The original plan to "use admitted `length_run_n_eq_bounded` to unblock dependent lemmas" encounters the same fundamental issues that blocked `length_run_n_eq_bounded` itself: Coq's simplification and unfolding create forms that don't match existing lemma patterns.

**Revised Strategy**:

1. **Create infrastructure lemmas first** (Approach 1 above)
   - Lemmas that work on the expanded nth/firstn/skipn forms
   - Prove once, use many times
   
2. **Then tackle TODOs systematically** using the new infrastructure

3. **Alternative: Extract CPU reasoning to separate module**
   - Create a CPU_Properties module with all register tracking lemmas
   - Prove them once in their natural expanded form
   - Import and use throughout ThieleUniversalBridge

This is more foundational work but would unblock all the register tracking proofs at once.

## Attempted Work in This Session

Successfully identified:
- Exact location and nature of pattern matching failures
- Compilation timeout issues with excessive unfolding
- Need for infrastructure lemmas at the expanded form level

The work demonstrates that the proof strategy is sound but requires better tooling/infrastructure before the individual TODOs can be completed efficiently.

## Next Concrete Steps

1. Create `read_reg_nth_preservation` and similar infrastructure lemmas
2. Test on one TODO to validate approach
3. Apply systematically to remaining TODOs
4. Return to `length_run_n_eq_bounded` with same infrastructure

This foundational work would benefit not just these proofs but all future register-tracking proofs in the file.
