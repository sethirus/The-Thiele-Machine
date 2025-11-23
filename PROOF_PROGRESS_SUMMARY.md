# Proof Progress Summary - ThieleUniversalBridge.v

## Session Completed: 2025-11-23

### Achievement
Successfully completed **1 TODO** and discharged **1 admit** in `coq/thielemachine/verification/ThieleUniversalBridge.v`.

### Completed Proof
**Lemma**: `transition_FindRule_step2b_temp5` (lines 1548-1589)

**Purpose**: Proves that register `REG_TEMP1` is preserved from step 3 through steps 4 and 5 in the FindRule loop transition.

**Key Insight**: The `AddConst REG_ADDR RULE_SIZE` instruction writes to:
- `REG_PC` (register 0)
- `REG_ADDR` (register 7)

But NOT to `REG_TEMP1` (register 8), so the value is preserved.

**Proof Strategy**:
1. Unfold `run_n cpu 5` to `run1 (run_n cpu 4)`
2. Rewrite with the decode hypothesis to get `CPU.step (AddConst REG_ADDR RULE_SIZE) (run_n cpu 4)`
3. Unfold `CPU.step` to expose the nested `write_reg` operations
4. Use `read_reg_write_reg_diff` lemma to show preservation through:
   - First the ADDR write (TEMP1 ≠ ADDR, so preserved)
   - Then the PC write (TEMP1 ≠ PC, so preserved)
5. Apply the hypothesis `Htemp4` to conclude

**Impact**: This checkpoint lemma is used by `transition_FindRule_Next_step2b`, which should now work correctly.

### Remaining Work

#### Statistics
- **Remaining `admit.` statements**: 11
- **Remaining `Admitted.` lemmas**: 6

#### Key Remaining Lemmas
1. `length_run_n_eq_bounded` (line 907-919) - Needs proving all instructions write in-bounds
2. `transition_FindRule_Next_step3b` (line 1643-1697) - Has multiple admits for checkpoints
3. `loop_iteration_run_equations` (line 1877-1905) - Needs proving run equations
4. `loop_iteration_no_match` (line 1907-2342) - Needs proving ADDR tracking and other register preservation
5. `loop_exit_match` (line 2350-2370) - Loop exit when matching rule found
6. `transition_FindRule_to_ApplyRule` (line 2373-2392) - Main loop theorem

### Proof Techniques Used

#### Key Lemmas for Register Preservation
- `read_reg_write_reg_diff` (lines 798-834): Shows that writing to one register preserves values in different registers
- `length_write_reg` (lines 922-935): Shows that `write_reg` preserves register file length when writing in-bounds

#### Important Definitions
- `run1 s = CPU.step (decode_instr s) s` (line 61-62)
- `run_n s (S n) = run_n (run1 s) n` (line 65-69)
- Register numbers: `REG_PC=0, REG_Q=1, REG_SYM=3, REG_Q'=4, REG_ADDR=7, REG_TEMP1=8`

#### Useful Tactics
- `change (run_n cpu N) with (run1 (run_n cpu (N-1)))` - Convert multi-step to single step
- `unfold CPU.step` - Expose nested write operations
- `transitivity` - Chain equalities through intermediate states
- `lia` - Discharge arithmetic goals about register numbers

### Next Steps for Future Sessions
1. Complete `transition_FindRule_Next_step3b` by filling in the checkpoint admits
2. Work on `loop_iteration_no_match` to complete the ADDR tracking proof
3. Progress through remaining loop lemmas toward the main theorem

### Notes
- The proof avoids term expansion by using abstract reasoning with `read_reg_write_reg_diff` rather than computing with `vm_compute`
- Length bounds (>= 10) are maintained throughout to ensure register access is valid
- The pattern of PC write followed by destination register write is consistent across instructions
