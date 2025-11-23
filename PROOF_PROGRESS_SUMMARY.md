# Proof Progress Summary - ThieleUniversalBridge.v

## Session 2 Completed: 2025-11-23

### Achievement
Successfully completed **8 TODOs** and discharged **8 admits**, completing **1 full lemma** (`transition_FindRule_Next_step3b`) in `coq/thielemachine/verification/ThieleUniversalBridge.v`.

### Completed Proofs

#### Session 1 (Previous)
**Lemma**: `transition_FindRule_step2b_temp5` (lines 1548-1589)
- Proved `REG_TEMP1` preservation through `AddConst REG_ADDR RULE_SIZE` execution

#### Session 2 (Current)
**Lemma**: `transition_FindRule_Next_step3b` (lines 1675-1809)

**Purpose**: Proves that the `REG_ADDR` register is correctly incremented by `RULE_SIZE` after 6 instruction steps in the FindRule loop.

**Sub-proofs completed** (8 admits discharged):
1. **Lines 1692-1693**: Length checkpoint - applied `transition_FindRule_step3b_len_cpu`
2. **Lines 1695-1696**: Length checkpoint - applied `transition_FindRule_step3b_len3`  
3. **Lines 1698-1699**: Length checkpoint - applied `transition_FindRule_step3b_len4`
4. **Lines 1701-1702**: Length checkpoint - applied `transition_FindRule_step3b_len5`
5. **Lines 1704-1722**: ADDR preservation through Jz - Jz only writes PC, so ADDR is preserved
6. **Lines 1724-1748**: ADDR increment through AddConst - Shows ADDR = old_ADDR + RULE_SIZE
7. **Lines 1750-1791**: TEMP1 preservation through Jz and AddConst - Both preserve TEMP1
8. **Lines 1796-1809**: Final ADDR preservation through Jnz - Jnz only writes PC

**Key Techniques**:
- Applied checkpoint lemmas that were already proven
- Used `read_reg_write_reg_diff` to show register preservation
- Used `read_reg_write_reg_same` to show ADDR gets the new value in AddConst
- Handled both branches of conditional jumps (Jz, Jnz)
- Tracked register values through multiple instruction steps

**Proof Pattern for ADDR increment** (lines 1724-1748):
```coq
(* AddConst ADDR RULE_SIZE increments ADDR *)
change (run_n cpu 5) with (run1 (run_n cpu 4)).
rewrite run1_decode, Hdec4.
unfold CPU.step.
(* Show ADDR write sets new value, then show ADDR preserved through PC write *)
transitivity (read_reg ADDR (write_reg PC ... cpu)).
- (* ADDR gets old_value + RULE_SIZE *)
  unfold read_reg, write_reg. simpl.
  rewrite app_nth2. reflexivity.
- (* ADDR preserved through PC write *)
  apply read_reg_write_reg_diff.
```

### Remaining Work

#### Statistics
- **Remaining `admit.` statements**: 3 (down from 11)
- **Remaining `Admitted.` lemmas**: 5 (down from 6)

#### Key Remaining Lemmas
1. `length_run_n_eq_bounded` (line 907-919) - 1 admit - Needs proving all instructions write in-bounds
2. `loop_iteration_run_equations` (line 1877-1905) - 1 admit - Needs proving run equations
3. `loop_iteration_no_match` (line 1907-2342) - 1 admit - Needs proving ADDR tracking in loop
4. `loop_exit_match` (line 2350-2370) - Fully admitted - Loop exit when matching rule found
5. `transition_FindRule_to_ApplyRule` (line 2373-2392) - Fully admitted - Main loop theorem

### Proof Techniques Used

#### Key Lemmas for Register Preservation
- `read_reg_write_reg_diff` (lines 798-834): Shows writing to one register preserves values in different registers
- `read_reg_write_reg_same` (lines 780-795): Shows reading the register you just wrote gives the new value
- `length_write_reg` (lines 922-935): Shows `write_reg` preserves register file length when writing in-bounds
- `length_run_n_ge` (lines 886-902): Shows multi-step execution preserves or grows register file length

#### Important Definitions
- `run1 s = CPU.step (decode_instr s) s` (line 61-62)
- `run_n s (S n) = run_n (run1 s) n` (line 65-69)
- Register numbers: `REG_PC=0, REG_Q=1, REG_SYM=3, REG_Q'=4, REG_ADDR=7, REG_TEMP1=8`

#### Useful Tactics
- `change (run_n cpu N) with (run1 (run_n cpu (N-1)))` - Convert multi-step to single step
- `unfold CPU.step` - Expose nested write operations
- `transitivity` - Chain equalities through intermediate states
- `destruct (condition)` - Handle both branches of conditional jumps
- `lia` - Discharge arithmetic goals about register numbers

#### Pattern for Conditional Jumps (Jz, Jnz)
```coq
unfold CPU.step.
destruct (read_reg REG condition =? 0).
- (* Branch taken *) apply read_reg_write_reg_diff; lia.
- (* Branch not taken *) apply read_reg_write_reg_diff; lia.
```

### Next Steps for Future Sessions
1. Complete `loop_iteration_no_match` ADDR tracking proof (1 admit remaining)
2. Complete `loop_iteration_run_equations` (1 admit remaining)
3. Work on `loop_exit_match` to complete loop exit lemmas
4. Progress through remaining loop lemmas toward the main theorem

### Notes
- All proofs avoid term expansion by using abstract reasoning with lemmas
- Length bounds (>= 10) are maintained throughout to ensure register access is valid
- The pattern of PC write followed by destination register write is consistent across instructions
- Conditional jumps (Jz, Jnz) only write to PC, preserving all other registers
