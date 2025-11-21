# Analysis of Admitted Lemmas in ThieleUniversalBridge.v

This document tracks the three remaining admitted lemmas in
`thielemachine/verification/ThieleUniversalBridge.v` and outlines strategies for
closing them. The helper lemmas `transition_FindRule_Found_step`,
`transition_FindRule_Next_step2b`, `transition_FindRule_Next_step3b`, and
`loop_iteration_run_equations` have been discharged, so the focus now is on the
non-match iteration, the matching exit, and the final composition theorem.

## Overview

All remaining lemmas involve symbolic execution through CPU states with
`run_n`/`decode_instr` kept opaque (see line ~752) to prevent expensive
unfolding. The loop lemmas reuse the explicit six-step run-equations proved
earlier.

## Admitted Lemmas

### 1. loop_iteration_no_match (Line 1794)
**Location:** Outside transparent section

**Goal:** Prove the FindRule loop invariant (`FindRule_Loop_Inv`) is preserved
when the scanned rule does not match `(q, sym)`.

**Key challenges:**
- Long invariant threading (PC, Q, SYM, ADDR, checked-rule index)
- Requires TEMP1 non-zero throughout the six-step body

**Suggested approach:**
- Rewrite `run_n` prefixes using `loop_iteration_run_equations`
- Split the invariant into sub-goals (PC, registers, index bump) and reuse
  `transition_FindRule_Next` once step3b lands

### 2. loop_exit_match (Line 1824)
**Location:** Outside transparent section

**Goal:** When a matching rule is found, show the loop branches to PC 12 with the
expected `(q, sym)` registers and rule address.

**Key challenges:**
- Guarded jump reasoning mirroring the non-match case
- Recovering the `(q, sym)` payload for ApplyRule

**Suggested approach:**
- Instantiate the decode hypotheses for the guard-true path
- Reuse the step0–step3 prefix equalities to avoid recomputation

### 3. transition_FindRule_to_ApplyRule (Line 1847)
**Location:** Outside transparent section

**Goal:** Compose the FindRule loop with the ApplyRule entry, producing a state
at PC 12 for the matching rule.

**Key challenges:**
- Depends on loop_iteration_no_match and loop_exit_match
- Requires threading the rule lookup `(nth 0 (tm_rules tm) …)` into the final
  state

**Suggested approach:**
- After steps 2 and 3 are closed, instantiate the rule lookup and reuse the
  concrete run-equations instead of `vm_compute`

## Recommended Proving Order

1. `loop_iteration_no_match`
2. `loop_exit_match`
3. `transition_FindRule_to_ApplyRule`

## Key Techniques Needed

1. Temporary transparency: open `run_n`/`decode_instr` locally if needed, then
   restore opacity.
2. Helper lemmas: step_LoadIndirect, step_CopyReg, step_SubReg, step_Jz,
   step_AddConst, step_Jnz.
3. Register tracking: length_write_reg, length_write_reg_ge,
   length_run_n_ge, read_reg_write_reg_same, read_reg_write_reg_diff.
4. run_n manipulation: run_n_S, run_n_1, run_n_0, run_n_unfold_3.
5. Avoid substitution: keep let-bound `cpu` names aligned with decode
   hypotheses.

## Memory/Performance Considerations

- Prefer the explicit decode hypotheses over `vm_compute` to keep proof terms
  small.
- Use the run-equations to avoid repeated unfolding of `run_n` chains.
- Insert intermediate assertions (PC, register lengths) to control rewriting
  and prevent timeouts.
