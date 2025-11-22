# Continuation Plan for ThieleUniversalBridge.v Proofs

## Current Status

File compiles successfully with documented admits. Previous work identified `length_run_n_eq_bounded` as the critical blocker.

## Attempted Work

Tried to prove `length_run_n_eq_bounded` by:
1. Creating `instr_writes_bounded` predicate to classify instructions writing to registers < n
2. Proving `step_preserves_length_bounded` lemma to show single-step length preservation

### Technical Challenge Encountered

The `step_preserves_length_bounded` proof encounters difficulties with Coq's simplification tactics:
- After `unfold CPU.step` and `simpl`, the goal expands into complex nested expressions involving `firstn`, `skipn`, `app`
- The `CPU.write_reg` definition expands differently depending on the structure of the register list
- Simply rewriting with `length_write_reg` doesn't work because the pattern doesn't match after simplification
- Need to manually reason about list lengths through the app/firstn/skipn operations

### Viable Approach

The proof strategy is sound but requires more manual list reasoning:

```coq
(* After unfold CPU.step, destruct instr, simpl, unfold CPU.write_reg *)
(* Goal becomes: length (firstn r regs ++ [v] ++ skipn (S r) regs) = n *)
(* Can prove using: *)
repeat rewrite app_length.
repeat rewrite firstn_length.
repeat rewrite skipn_length.
rewrite Nat.min_l by lia.
(* Then arithmetic with lia *)
```

However, this approach requires careful attention to:
- When to apply `simpl` vs when to keep things abstract
- Managing hypotheses after simplification destroys structure
- The record construction at the end of CPU.step that wraps everything

## Alternative Approach: Admit Helper, Proceed with Dependent Lemmas

Since `length_run_n_eq_bounded` is blocking progress on multiple other lemmas, an alternative strategy is:

1. **Accept current admit of `length_run_n_eq_bounded`** with clear TODO
2. **Use it to prove dependent lemmas** that have more direct value
3. **Return to prove `length_run_n_eq_bounded` later** once the dependent proofs demonstrate its utility

### Lemmas That Can Now Be Attempted (with `length_run_n_eq_bounded` available):

#### 1. TODOs in `loop_iteration_no_match` (Lines 1933, 1947, 1950, 1954, 1957, 1965, 1970, 1976)

These are register tracking subgoals that need `length=10` to apply `read_reg_write_reg_diff`:

**Subgoal 1 (PC = 4)**:
```coq
(* Line 1933 - TEMP1 preservation through Jz *)
(* After Jz when not taken, only PC is updated *)
unfold CPU.step, CPU.Jz. simpl.
(* Use read_reg_write_reg_diff with TEMP1 != PC *)
apply read_reg_write_reg_diff.
- discriminate. (* TEMP1 = 8, PC = 0 *)
- apply length_run_n_eq_bounded. exact Hlen3.
- unfold CPU.REG_PC. apply length_run_n_eq_bounded. exact Hlen3. 
```

**Subgoal 2 (REG_Q preserved)** - Similar approach tracking through 6 steps

**Subgoal 3 (REG_SYM preserved)** - Similar approach

**Subgoal 4 (REG_ADDR incremented)** - Track preservation 0-3, show increment at step 4

#### 2. `transition_FindRule_step2b_temp5` (Line 1463)

Shows TEMP1 preserved through AddConst step. Similar pattern to above.

#### 3. `loop_exit_match` (Line 1992)

When TEMP1 = 0, the Jz is taken and PC jumps to 12. Can prove using:
- `step_JumpZero_taken` lemma (need to verify this exists or create it)
- Register tracking with `length_run_n_eq_bounded`

## Recommendation

Given the user's "CONTINUE" directive, the most productive path forward is:

1. **Document the `step_preserves_length_bounded` approach** as partially implemented with known challenges
2. **Use admitted `length_run_n_eq_bounded`** to unblock and prove the dependent lemmas
3. **Demonstrate value** by completing 1-2 of the TODOs in `loop_iteration_no_match`
4. **Return to `length_run_n_eq_bounded`** once the dependent work shows the approach is correct

This provides tangible progress on multiple fronts rather than getting stuck on a single difficult lemma.

## Next Concrete Steps

1. Prove TODO at line 1933 (TEMP1 preservation through Jz)
2. Prove TODO at line 1947 (length = 10 for cpu4)
3. Prove TODO at line 1950 (TEMP1 preservation through AddConst)
4. Prove TODO at line 1954 (length = 10 for cpu5)

These can be done in sequence, each building confidence in the approach.
