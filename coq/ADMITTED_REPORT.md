# Admitted Lemmas Report - ThieleUniversalBridge.v

**Generated**: 2025-11-21
**File**: `coq/thielemachine/verification/ThieleUniversalBridge.v`

## Summary

- **Total Admitted**: 3 lemmas
- **Total Axioms**: 0
- **File Compilation**: ✅ SUCCESS

## Admitted Lemmas Detail

### 1. `loop_iteration_no_match` (Line 1794)
**Status**: Admitted
**Complexity**: High
**Challenge**: Prove the FindRule loop invariant is preserved when the scanned
rule does not match the current `(q, sym)` pair.

**What's needed**:
- Thread the explicit six-step run equations through the invariant
- Show TEMP1 stays non-zero across the body
- Rebuild `FindRule_Loop_Inv` with the incremented rule index

**Estimated effort**: 60–100 lines


### 2. `loop_exit_match` (Line 1824)
**Status**: Admitted
**Complexity**: High
**Challenge**: Establish the first branch into the ApplyRule block when a
matching rule is found.

**What's needed**:
- Use the decode hypotheses to show the guarded jump reaches PC 12
- Recover the `(q, sym)` registers and the computed rule address
- Prepare the state for the ApplyRule payload

**Estimated effort**: 50–80 lines


### 3. `transition_FindRule_to_ApplyRule` (Line 1847)
**Status**: Admitted
**Complexity**: Medium–High
**Challenge**: Compose the FindRule exit with the ApplyRule entry to obtain a
CPU state at PC 12 for the matching rule.

**What's needed**:
- Close `loop_exit_match` and the invariant-preservation lemma
- Instantiate the rule lookup with the head symbol
- Reuse the concrete decode/run equations to avoid `vm_compute`

**Estimated effort**: 30–50 lines

---

## Progress Tracking

- ✅ `transition_FindRule_Found_step` proved (guard-true Jz branch)
- ✅ `transition_FindRule_Next_step2b` proved (PC jump for non-zero TEMP1)
- ✅ `transition_FindRule_Next_step3b` proved (ADDR bump for non-zero TEMP1)
- ✅ `loop_iteration_run_equations` proved (explicit six-step chain for the
  non-match iteration)
- ⏸️ Remaining admits: loop_iteration_no_match, loop_exit_match,
  transition_FindRule_to_ApplyRule

**Overall Progress**: 4/7 previously listed admits closed; 3 remain in the
bridge file.
