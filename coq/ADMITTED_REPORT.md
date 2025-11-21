# Admitted Lemmas Report - ThieleUniversalBridge.v

**Generated**: 2025-11-21  
**File**: `coq/thielemachine/verification/ThieleUniversalBridge.v`

## Summary

- **Total Admitted**: 6 lemmas
- **Total Axioms**: 0
- **File Compilation**: ✅ SUCCESS

## Admitted Lemmas Detail

### 1. `transition_FindRule_Next_step2b` (Line 1369)
**Status**: Admitted  
**Complexity**: Medium  
**Challenge**: Requires register preservation proof showing TEMP1 register unchanged through Jz and AddConst instructions

**What's needed**: 
- Prove `read_reg TEMP1 (run_n cpu 5) =? 0 = false` from `read_reg TEMP1 (run_n cpu 3) =? 0 = false`
- Track through step 4 (Jz - modifies PC only) and step 5 (AddConst - modifies ADDR only)
- Use `read_reg_write_reg_diff` lemmas to show TEMP1 preservation

**Estimated effort**: 30-40 lines of register preservation reasoning

---

### 2. `transition_FindRule_Next_step3b` (Line 1384)
**Status**: Admitted  
**Complexity**: Medium  
**Challenge**: Similar to step2b, requires register preservation but for ADDR register

**What's needed**:
- Similar pattern to step2b
- Track ADDR register through multiple steps

**Estimated effort**: 30-40 lines

---

### 3. `loop_iteration_run_equations` (Line 1600)
**Status**: Admitted  
**Complexity**: High  
**Challenge**: run_n is opaque in this section; requires proving 6 equality lemmas of form `run1 cpuN = cpuN+1`

**What's needed**:
- Make run_n temporarily transparent within proof
- Prove each `cpuN = run_n cpu N` by reflexivity
- Apply decode hypotheses after rewriting
- Manage opacity carefully to avoid term explosion

**Estimated effort**: 40-60 lines

---

### 4. `loop_iteration_no_match` (Line 1625)
**Status**: Admitted  
**Complexity**: High  
**Challenge**: High-level loop invariant preservation across iteration

**What's needed**:
- Prove loop state preservation when no match found
- Compositional reasoning about multiple steps
- Invariant tracking (register values, PC location, etc.)

**Estimated effort**: 60-100 lines

---

### 5. `loop_exit_match` (Line 1653)
**Status**: Admitted  
**Complexity**: High  
**Challenge**: Loop exit condition reasoning when match is found

**What's needed**:
- Prove correct exit from loop
- Show final state matches expected configuration
- Relate loop exit condition to correctness invariants

**Estimated effort**: 50-80 lines

---

### 6. `transition_FindRule_to_ApplyRule` (Line 1675)
**Status**: Admitted  
**Complexity**: Medium-High  
**Challenge**: Compositional state transition between FindRule and ApplyRule phases

**What's needed**:
- Compose multiple smaller lemmas
- Show state transformation preserves necessary invariants
- Bridge between two major proof sections

**Estimated effort**: 30-50 lines

---

## Proof Strategy Recommendations

### Immediate Actions (Easiest First)
1. **Complete `transition_FindRule_Found_step`** - ✅ DONE (Line 1398-1419)
   - This was successfully completed using definitional equality pattern
   - 13 lines, clean proof

2. **Work on `transition_FindRule_Next_step2b`** (Line 1333-1369)
   - Proof structure 90% complete
   - Only needs register preservation sub-proof
   - Next easiest target

3. **Work on `transition_FindRule_Next_step3b`** (Line 1371-1384)
   - Similar to step2b
   - Can reuse patterns from step2b

### Medium Term
4. **`transition_FindRule_to_ApplyRule`** (Line 1630-1675)
   - Compositional reasoning
   - Depends on completing earlier lemmas

5. **`loop_iteration_run_equations`** (Line 1555-1600)
   - Requires opacity management
   - Foundational for loop lemmas

### Long Term
6. **`loop_iteration_no_match`** (Line 1580-1625)
   - Complex loop invariant tracking
   - Depends on loop_iteration_run_equations

7. **`loop_exit_match`** (Line 1628-1653)
   - Loop termination reasoning
   - Depends on loop invariants

## Available Helper Lemmas

From the file analysis, these lemmas are available:

- `run1_decode`: Relates `decode_instr (run1 cpu)` to `CPU.step`
- `read_reg_write_reg_eq`: Reading register just written returns written value
- `read_reg_write_reg_diff`: Reading different register preserves old value
- `CPU.step_jz_true`: Jz instruction semantics when condition true
- `CPU.step_jz_false`: Jz instruction semantics when condition false
- `CPU.step_jnz_false`: Jnz instruction semantics when condition false
- `CPU.step_jnz_true`: Jnz instruction semantics when condition true

## Key Insights

1. **Working Pattern Exists**: The proved lemma demonstrates that using `change` + reflexivity + direct lemma application avoids term matching issues

2. **Register Preservation is Tractable**: While it requires explicit reasoning, the `read_reg_write_reg_diff` lemmas provide the necessary tools

3. **Opacity Management**: Can use `Transparent run_n` locally within proofs, then restore `Opaque run_n`

4. **Incrementalstrategy**: Complete simpler lemmas first to build confidence and reusable patterns

## Progress Tracking

- ✅ **1/7 Complete**: `transition_FindRule_Found_step`
- 🔄 **1/7 Partial**: `transition_FindRule_Next_step2b` (90% done)
- ⏸️ **5/7 Remaining**: step3b, loop_run_equations, loop_no_match, loop_exit, transition_to_ApplyRule

**Overall Progress**: 14% complete (1 fully proved, 1 partially proved)
