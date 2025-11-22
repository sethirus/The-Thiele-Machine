# ThieleUniversalBridge.v Lemma Status Report

## Overview

This document tracks the status of admitted lemmas in `ThieleUniversalBridge.v` and their dependencies.

## File Compilation Status

✅ **File compiles successfully end-to-end** using Coq 8.18.0

## Critical Blocker: `length_run_n_eq_bounded`

**Location**: Line 907-919

**Status**: ADMITTED (fundamental blocker)

**What it proves**: If a CPU state starts with exactly 10 registers, running `n` steps preserves exactly 10 registers.

**Why it's needed**: 
- The universal program uses registers 0-9 (REG_PC through REG_TEMP2)
- Many proofs need to use `read_reg_write_reg_diff` which requires knowing register indices are in bounds
- Without exact length tracking, we can't apply register manipulation lemmas

**What's required to prove it**:
1. Analyze all instructions in the universal program (UTM_Program.program_instrs)
2. Show each instruction writes to a register r where r < 10
3. Use the fact that `write_reg r v st` where `r < length st.(regs)` preserves the length
4. Apply this analysis inductively across all `n` steps

**Proof strategy**:
- Extract the list of all instructions from the encoded program
- For each instruction type, show it writes to a register < 10
- Build a lemma that tracks register file length through a single step when the instruction is well-formed
- Apply inductively

**Current blocker**: This requires significant work to enumerate and analyze the entire program.

## Dependent Lemmas (Blocked by `length_run_n_eq_bounded`)

### 1. `transition_FindRule_step2b_temp5` (Line 1463-1472)
**Dependency chain**: Needs `length_run_n_eq_bounded`  
**Status**: ADMITTED  
**Purpose**: Shows TEMP1 preserved through AddConst step (checkpoint helper)

### 2. `loop_iteration_run_equations` (Line 1792-1820)
**Dependency chain**: Partially independent but needs careful tactic management  
**Status**: ADMITTED (attempted, needs precise tactic application)  
**Purpose**: Establishes that run1 applications match explicit CPU.step applications  
**Note**: This lemma should be provable without length_run_n_eq_bounded, but requires careful handling of let-bindings and rewriting order.

### 3. `loop_iteration_no_match` TODOs (Lines 1933, 1947, 1950, 1954, 1957, 1965, 1970, 1976)
**Dependency chain**: All four register tracking subgoals need `length_run_n_eq_bounded`  
**Status**: Proof architecture complete, 1/5 subgoals fully proved, 4 subgoals have TODOs  
**Blocked subgoals**:
- Subgoal 1 (Line 1933, 1950, 1953, 1954, 1957): PC = 4, TEMP1 tracking - needs length=10 to apply `read_reg_write_reg_diff`
- Subgoal 2 (Line 1965): REG_Q preserved - needs register inequality proofs
- Subgoal 3 (Line 1970): REG_SYM preserved - needs register inequality proofs  
- Subgoal 4 (Line 1976): REG_ADDR incremented - needs register tracking

**Completed**: Subgoal 5 (rules accumulator) - fully proved using case analysis

### 4. `loop_exit_match` (Line 1992-2015)
**Dependency chain**: Likely needs `length_run_n_eq_bounded` for register tracking  
**Status**: ADMITTED  
**Purpose**: When a matching rule is found, loop exits to PC=12

### 5. `transition_FindRule_to_ApplyRule` (Line 2018-2037)
**Dependency chain**: Depends on `loop_exit_match` and likely `length_run_n_eq_bounded`  
**Status**: ADMITTED  
**Purpose**: Main loop theorem composing iteration lemmas

## Other Admitted Lemmas (Checkpoint Helpers)

### `transition_FindRule_Next_step2b` (Lines 1576-1612)
**Status**: Multiple checkpoint admits within the proof  
**Purpose**: Proves the Next transition maintains invariants  
**Issue**: Uses checkpoint method but some sub-proofs cause term expansion

**Specific admits**:
- Line 1576: TODO checkpoint
- Line 1579: TODO checkpoint  
- Line 1582: TODO checkpoint
- Line 1585: TODO checkpoint
- Line 1590: Extract to checkpoint (causes term expansion)
- Line 1595: Extract to checkpoint (causes term expansion)
- Line 1600: Extract to checkpoint (causes term expansion)
- Line 1611: Final step causes issues with simpl/cbv

## Lemmas That Could Be Proved Next

### Priority 1: `loop_iteration_run_equations`
- **Mostly independent** of length_run_n_eq_bounded
- Requires careful tactic application with let-bindings
- Would complete the run equation infrastructure

### Priority 2: Checkpoint helpers in `transition_FindRule_Next_step2b`
- Some can likely be extracted and sealed
- Would reduce term expansion issues
- Helps with the checkpoint method strategy

### Priority 3: `length_run_n_eq_bounded`
- This is the fundamental blocker
- Requires enumerating all instructions in the program
- Once proved, unblocks most other lemmas

## Proof Techniques Available

1. **Checkpoint Method**: Extract sub-proofs into sealed lemmas (already used successfully)
2. **Register tracking**: Use `read_reg_write_reg_diff` and `read_reg_write_reg_same`
3. **Length preservation**: `length_write_reg` when r < length
4. **Induction**: On step count for run_n lemmas

## Next Steps Recommendation

1. **Short term**: Prove `loop_iteration_run_equations` with careful tactic work
2. **Medium term**: Work on checkpoint helpers to reduce term expansion
3. **Long term**: Tackle `length_run_n_eq_bounded` by:
   - Extracting the concrete instruction list from the program
   - Proving a "well-formed instruction" predicate
   - Showing all program instructions satisfy it
   - Using this to prove length preservation

## File Statistics

- **Total lines**: 2037
- **Admitted lemmas**: 5 major lemmas + multiple checkpoint helpers
- **Compilation time**: ~3 minutes (mostly kernel verification of sealed checkpoints)
- **Successfully uses**: Checkpoint Method to avoid OOM errors during Qed
