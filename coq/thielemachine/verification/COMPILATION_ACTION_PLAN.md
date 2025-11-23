# ThieleUniversalBridge Compilation Status and Action Plan

## Current Status (2025-11-23)

### Proof Completeness
- **Lines**: 2876
- **Admitted lemmas**: 0 (all proofs complete with Qed)
- **Axioms**: 1 (`universal_program_bounded_writes` at line 908)
- **Proof structure**: Complete, using checkpoint method

### Compilation Status
**DOES NOT COMPILE** - Times out after 300+ seconds

**Timeout location**: During Qed of `transition_FindRule_step2b_temp5` (line ~1623)
- Proof script executes quickly
- Timeout occurs during proof term checking/kernel verification
- This is a known issue documented in BRIDGE_DIAGNOSIS.md

### What I've Tried
1. ✅ Installed Coq 8.18.0
2. ✅ Compiled dependencies successfully
3. ✅ Attempted full compilation - timed out
4. ✅ Applied `abstract` tactic to problematic lemma - still times out
5. ⏹️ Need more aggressive optimizations

## Root Cause Analysis

The timeout is NOT in proof script execution - it's in **proof term checking** during Qed.

**Why this happens**:
1. Complex symbolic execution creates large proof terms
2. Multiple `run_n` applications expand CPU state
3. Register tracking through `write_reg` creates nested structures
4. Kernel has to type-check the entire term

**Documentation confirms**:
- BRIDGE_DIAGNOSIS.md: "120s+ timeout during batch compilation"
- "The bridge file still exhausts the 120s timeout during batch compilation"
- "Manual interrupt required after hanging in guarded replay"

## Action Plan to Complete

### Phase 1: Aggressive Proof Term Reduction (HIGH PRIORITY)
Target lemmas causing timeouts:

1. **transition_FindRule_step2b_temp5** (line 1582-1623)
   - Currently: abstract wrapped - NOT SUFFICIENT
   - Needed: Break into smaller sub-lemmas
   - Strategy: Extract register preservation facts into separate sealed lemmas

2. **transition_FindRule_Next_step2b** (line 1625-1667)
   - Uses checkpoint method - may need more granular checkpoints
   - Break assertion proofs into sealed lemmas

3. **Later FindRule lemmas** (lines 1668+)
   - Apply same techniques preemptively

### Phase 2: Compilation Testing Strategy

Test incrementally:
```bash
# Test just up to problematic lemma
coqc -Q ... ThieleUniversalBridge.v 2>&1 | tee log.txt

# Monitor which lemma is being processed:
tail -f log.txt | grep "Lemma\|Qed"
```

Kill and optimize if timeout > 60s on any single Qed.

### Phase 3: Alternative Approaches

If proof term reduction doesn't work:

1. **Split file**: Break ThieleUniversalBridge into multiple files
   - Part 1: Definitions and basic lemmas
   - Part 2: Transition lemmas (with imports)
   - Part 3: Main theorems

2. **Proof by reflection**: For repetitive register tracking
   - Write OCaml tactic plugin
   - Automate register preservation proofs

3. **Axiom the problematic lemmas temporarily**:
   - Get rest of file compiling
   - Come back to prove axiomatized lemmas later

### Phase 4: Replace Axiom (LOWER PRIORITY)

The axiom `universal_program_bounded_writes` can be proved but doesn't affect compilation:
1. Enumerate all instructions in UTM_Program
2. Show each writes to register < 10
3. Prove inductively

This is lower priority since it doesn't block compilation.

## Recommended Next Steps

1. **Immediate**: Break transition_FindRule_step2b_temp5 into sub-lemmas
   - Lemma for ADDR write preservation
   - Lemma for PC write preservation
   - Main lemma combines them

2. **Test**: Compile after each change to measure improvement

3. **Document**: Track which optimizations help

4. **Iterate**: Apply to remaining problematic lemmas

## Timeline Estimate

- **Proof term reduction**: 2-4 hours (iterative)
- **Testing/validation**: 1-2 hours
- **Documentation**: 30 min

**Total**: 4-7 hours of focused work

## Success Criteria

1. ✅ File compiles in < 10 minutes
2. ✅ No timeouts on any individual lemma Qed
3. ✅ All proofs remain complete (no new Admitted)
4. ✅ Proof structure remains maintainable

##Notes

The infrastructure created earlier (module extraction, profiling) will be valuable for:
- Testing optimizations incrementally
- Measuring compilation time improvements
- Tracking which sections take longest

However, the actual fix requires hands-on proof term optimization, not just infrastructure.
