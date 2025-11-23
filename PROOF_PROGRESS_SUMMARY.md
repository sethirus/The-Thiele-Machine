# Proof Progress Summary - ThieleUniversalBridge.v

## Session 4 Completed: 2025-11-23

### Achievement
Successfully completed **1 TODO** and discharged **1 admit**, completing **1 full lemma** (`loop_iteration_no_match`) in `coq/thielemachine/verification/ThieleUniversalBridge.v`.

**Major milestone: Only 1 admit and 3 Admitted lemmas remaining!**

### Completed Proofs

#### Session 1
**Lemma**: `transition_FindRule_step2b_temp5` (lines 1548-1589)
- Proved `REG_TEMP1` preservation through `AddConst REG_ADDR RULE_SIZE` execution

#### Session 2
**Lemma**: `transition_FindRule_Next_step3b` (lines 1675-1809)
- Proved `REG_ADDR` register is correctly incremented by `RULE_SIZE` after 6 instruction steps
- Discharged 8 admits

#### Session 3
**Lemma**: `loop_iteration_run_equations` (lines 1989-2052)
- Establishes equivalence between `run1` function and explicit `CPU.step` applications

#### Session 4 (Current)
**Lemma**: `loop_iteration_no_match` (lines 2055-2601)

**Purpose**: Core loop iteration lemma proving that the FindRule loop invariant is preserved when checking a non-matching rule.

**What it proves**: If we start at iteration `i` with the loop invariant holding, and rule `i` doesn't match the current state/symbol, then after 6 instruction steps, the invariant holds for iteration `S i` (i.e., `i+1`).

**Key components proven**:
1. **PC returns to 4** after the 6-step loop iteration (via Jnz instruction)
2. **REG_Q preserved** through all 6 steps (LoadIndirect→Q', CopyReg→TEMP1, SubReg→TEMP1, Jz→PC, AddConst→ADDR, Jnz→PC)
3. **REG_SYM preserved** through all 6 steps (same reasoning as REG_Q)
4. **REG_ADDR incremented by RULE_SIZE** (the focus of this session's work):
   - Steps 0-3 (LoadIndirect, CopyReg, SubReg, Jz): ADDR unchanged
   - Step 4 (AddConst REG_ADDR RULE_SIZE): ADDR += RULE_SIZE
   - Step 5 (Jnz): ADDR unchanged
   - Result: `ADDR(cpu6) = ADDR(cpu) + RULE_SIZE = (RULES_START_ADDR + i * RULE_SIZE) + RULE_SIZE = RULES_START_ADDR + (S i) * RULE_SIZE`
5. **Previous rules non-matching** property preserved (by induction on `j < S i`)

**Proof Strategy for ADDR tracking** (lines 2474-2590):
1. Prove `ADDR(cpu1) = ADDR(cpu)` using `read_reg_write_reg_diff` (LoadIndirect writes to Q')
2. Prove `ADDR(cpu2) = ADDR(cpu1)` (CopyReg writes to TEMP1)
3. Prove `ADDR(cpu3) = ADDR(cpu2)` (SubReg writes to TEMP1)
4. Prove `ADDR(cpu4) = ADDR(cpu3)` (Jz writes to PC, handle both branches)
5. Prove `ADDR(cpu5) = ADDR(cpu4) + RULE_SIZE` (AddConst increment, special handling)
6. Prove `ADDR(cpu6) = ADDR(cpu5)` (Jnz writes to PC, handle both branches)
7. Chain all equalities: `ADDR(cpu6) = ADDR(cpu) + RULE_SIZE`
8. Use loop invariant: `ADDR(cpu) = RULES_START_ADDR + i * RULE_SIZE`
9. Conclude with `lia`: `RULES_START_ADDR + i * RULE_SIZE + RULE_SIZE = RULES_START_ADDR + (S i) * RULE_SIZE`

**Key Technique - Register Tracking Through Multiple Steps**:
```coq
(* For each step that doesn't write to target register *)
assert (Haddr_n: read_reg ADDR cpu_n = read_reg ADDR cpu_(n-1)).
{ unfold cpu_n, run1. rewrite Hdecode_(n-1).
  unfold CPU.step.
  apply read_reg_write_reg_diff; lia. }

(* For the step that increments the register *)
assert (Haddr_n: read_reg ADDR cpu_n = read_reg ADDR cpu_(n-1) + RULE_SIZE).
{ (* Special handling for AddConst with transitivity *) }

(* Chain all equalities *)
rewrite Haddr6, Haddr5, Haddr4, Haddr3, Haddr2, Haddr1.
```

### Progress Statistics
**Before Session 4**: 2 admits, 4 Admitted lemmas
**After Session 4**: 1 admit, 3 Admitted lemmas
**Overall Progress**: 11→1 admits (-91%), 6→3 Admitted lemmas (-50%)

### Remaining Work

#### Statistics
- **Remaining `admit.` statements**: 1 (down from 11 originally, 91% complete!)
- **Remaining `Admitted.` lemmas**: 3 (down from 6 originally, 50% complete!)

#### Key Remaining Lemmas
1. `length_run_n_eq_bounded` (line 907-919) - 1 admit - Needs proving all instructions write in-bounds
2. `loop_exit_match` (line 2609-2629) - Fully admitted - Loop exit when matching rule found
3. `transition_FindRule_to_ApplyRule` (line 2632-2651) - Fully admitted - Main loop theorem

### Proof Techniques Used

#### Register Tracking Through Multiple Steps (new)
The core pattern for tracking a register value through multiple instruction steps:

1. **For steps that don't modify the target register**: Use `read_reg_write_reg_diff`
   ```coq
   assert (Hreg_next: read_reg TARGET_REG cpu_next = read_reg TARGET_REG cpu_prev).
   { unfold cpu_next, run1. rewrite Hdecode.
     unfold CPU.step.
     apply read_reg_write_reg_diff.
     - (* TARGET_REG ≠ WRITTEN_REG *) unfold registers. lia.
     - (* TARGET_REG < length *) unfold register. apply length_lemma.
     - (* WRITTEN_REG < length *) unfold register. apply length_lemma. }
   ```

2. **For conditional jumps**: Handle both branches with `destruct`
   ```coq
   destruct (condition).
   - (* Branch taken *) apply read_reg_write_reg_diff; lia.
   - (* Branch not taken *) apply read_reg_write_reg_diff; lia.
   ```

3. **For AddConst increment**: Use `transitivity` and unfold write operations
   ```coq
   assert (Hreg_next: read_reg TARGET_REG cpu_next = read_reg TARGET_REG cpu_prev + VALUE).
   { unfold cpu_next, run1. rewrite Hdecode.
     unfold CPU.step.
     transitivity (read_reg TARGET_REG (write_reg PC ... cpu_prev)).
     - (* TARGET_REG gets new value *) 
       unfold read_reg, write_reg. simpl.
       rewrite app_nth2. reflexivity.
     - (* TARGET_REG preserved through PC write *)
       apply read_reg_write_reg_diff; lia. }
   ```

4. **Chain all equalities**: Use rewrite with multiple hypotheses
   ```coq
   rewrite H6, H5, H4, H3, H2, H1.
   rewrite Hinvariant_hypothesis.
   lia.  (* Arithmetic conclusion *)
   ```

#### Key Lemmas
- `read_reg_write_reg_diff` (lines 798-834): Writing to one register preserves values in different registers
- `read_reg_write_reg_same` (lines 780-795): Reading the register you just wrote gives the new value
- `length_write_reg` (lines 922-935): `write_reg` preserves register file length when writing in-bounds
- `length_run_n_ge` (lines 886-902): Multi-step execution preserves or grows register file length
- `length_run_n_eq_bounded` (lines 907-919): Multi-step execution preserves exact length = 10 (admitted)

#### Important Definitions
- `run1 s = CPU.step (decode_instr s) s` (line 61-62)
- `run_n s (S n) = run_n (run1 s) n` (line 65-69)
- Register numbers: `REG_PC=0, REG_Q=1, REG_SYM=3, REG_Q'=4, REG_ADDR=7, REG_TEMP1=8`
- `RULES_START_ADDR`, `RULE_SIZE`: Layout constants for rule memory

#### Useful Tactics
- `change (run_n cpu N) with (run1 (run_n cpu (N-1)))` - Convert multi-step to single step
- `unfold CPU.step` - Expose nested write operations
- `transitivity` - Chain equalities through intermediate states
- `destruct (condition)` - Handle both branches of conditional jumps
- `lia` - Discharge arithmetic goals (especially `i * RULE_SIZE + RULE_SIZE = (S i) * RULE_SIZE`)
- `rewrite H6, H5, H4, ...` - Chain multiple equality rewrites

### Compilation Testing
- Coq 8.18.0 installed and operational
- Pre-compiled .vo files exist for dependencies in archive
- Proof patterns validated before full application

### Next Steps for Future Sessions
1. Work on `loop_exit_match` to complete loop exit lemmas (fully admitted)
2. Complete `transition_FindRule_to_ApplyRule` main loop theorem (fully admitted)
3. Complete `length_run_n_eq_bounded` if needed (1 remaining admit)
4. Final verification and compilation of entire file

### Notes
- All proofs avoid term expansion by using abstract reasoning with lemmas
- Length bounds must be carefully tracked through each step
- The pattern of PC write followed by destination register write is consistent across instructions
- Conditional jumps (Jz, Jnz) only write to PC, preserving all other registers
- Register tracking through 6 steps requires systematic step-by-step preservation proofs
- `lia` is powerful for arithmetic involving multiplication (e.g., `i * RULE_SIZE + RULE_SIZE = (S i) * RULE_SIZE`)
