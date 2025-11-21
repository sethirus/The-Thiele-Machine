# Analysis of Admitted Lemmas in ThieleUniversalBridge.v

This document analyzes the 7 admitted lemmas in `thielemachine/verification/ThieleUniversalBridge.v` and outlines strategies for proving them.

## Overview

All 7 lemmas involve symbolic execution through CPU states with the challenge that `run_n` and `decode_instr` are made opaque at line 752 to prevent memory explosions during proof search. Three lemmas are in a section where they're temporarily made transparent (lines 1315-1436), but even there the proofs are non-trivial.

## Admitted Lemmas

### 1. transition_FindRule_Next_step2b (Line 1321)
**Location:** In transparent section (after line 1315)
**What it proves:** After 6 CPU steps through the FindRule loop (non-matching path), PC returns to 4
**Challenge:** 
- Needs to step through 6 instructions 
- Must track that TEMP1 != 0 throughout (guard false case)
- Pattern matching with let-bound `cpu` variable

**Strategy:**
- Use run1_decode lemma repeatedly
- Use step helper lemmas (step_LoadIndirect, step_CopyReg, step_SubReg, step_Jz, step_AddConst, step_Jnz)
- Keep cpu as let-binding instead of substituting
- Track register length preservation through steps

### 2. transition_FindRule_Next_step3b (Line 1335)
**Location:** In transparent section
**What it proves:** After 6 CPU steps, ADDR register is incremented by RULE_SIZE
**Challenge:** Similar to #1 but proves register value instead of PC
**Strategy:** Same as #1, but use register preservation lemmas

### 3. transition_FindRule_Found_step (Line 1352)
**Location:** In transparent section
**What it proves:** After 4 CPU steps (matching path), PC jumps to 12
**Challenge:** 
- Shorter than #1 and #2 (only 4 steps)
- Guard is true (TEMP1 = 0), so Jz branch is taken
**Strategy:**
- Use step_BranchZero_taken lemma
- Track register length through first 3 steps

### 4. loop_iteration_run_equations (Line 1504)
**Location:** OUTSIDE transparent section (opaque run_n/decode_instr)
**What it proves:** Relationship between run1 applications and CPU.step with decode_instr
**Challenge:** 
- run_n is opaque, so can't unfold it
- Must use only run_n_S, run_n_1, run_n_0 lemmas
- Pattern matching becomes very complex

**Strategy:**
- Either: Make run_n/decode_instr temporarily transparent in proof
- Or: Restructure to avoid needing this lemma (use direct symbolic execution in callers)
- Or: Prove helper lemmas about run_n and run1 relationships when decode_instr is known

### 5. loop_iteration_no_match (Line 1536)
**Location:** OUTSIDE transparent section
**What it proves:** Loop iteration preserves FindRule_Loop_Inv invariant
**Challenge:**
- Depends on loop_iteration_run_equations (currently admitted)
- Very long proof (originally ~350 lines before admission)
- Tracks multiple invariants (PC, Q register, SYM register, ADDR register, checked rules)

**Strategy:**
- First prove loop_iteration_run_equations
- Use symbolic execution with helper lemmas
- Break into sub-lemmas for each invariant component

### 6. loop_exit_match (Line 1566)
**Location:** OUTSIDE transparent section  
**What it proves:** When matching rule found, loop exits with correct state
**Challenge:**
- Similar to #5 but for exit case
- Originally ~170 lines before admission

**Strategy:**
- Similar to #5
- Use step_BranchZero_taken for the Jz branch

### 7. transition_FindRule_to_ApplyRule (Line 1589)
**Location:** OUTSIDE transparent section
**What it proves:** Main theorem composing the loop lemmas
**Challenge:**
- Depends on #5 and #6
- High-level composition lemma

**Strategy:**
- Prove #5 and #6 first
- Should be straightforward once dependencies are proved

## Recommended Proving Order

1. **First:** #3 (transition_FindRule_Found_step) - shortest, in transparent section
2. **Second:** #1 and #2 (transition_FindRule_Next_step2b/3b) - in transparent section, similar structure
3. **Third:** #4 (loop_iteration_run_equations) - foundational for others
4. **Fourth:** #5 and #6 (loop_iteration_no_match, loop_exit_match) - depend on #4
5. **Finally:** #7 (transition_FindRule_to_ApplyRule) - composition

## Key Techniques Needed

1. **Temporary transparency**: Use `Transparent run_n decode_instr` at proof start, `Opaque` at end
2. **Helper lemmas**: step_LoadIndirect, step_CopyReg, step_SubReg, step_Jz, step_AddConst, step_Jnz
3. **Register tracking**: length_write_reg, read_reg_write_reg_same, read_reg_write_reg_diff
4. **run_n manipulation**: run_n_S, run_n_1, run_n_0, run_n_unfold_3
5. **Avoid substitution**: Keep let-bound variables to maintain hypothesis alignment

## Memory/Performance Considerations

- Original proofs before admission were causing OOM or timeouts
- Keep proofs incremental with explicit intermediate assertions
- Seal proof terms at checkpoints using helper lemmas
- Avoid vm_compute on large symbolic states
- Use explicit decode_instr hypotheses instead of computation
