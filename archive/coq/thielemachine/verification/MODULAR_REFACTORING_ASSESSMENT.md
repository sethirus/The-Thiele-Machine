# Modular Refactoring Assessment

## Request
Make the modular files actually compile independently, use them to fix issues, merge back without admits.

## Current State Analysis

### Problems with Current Modular Extraction
1. **Cuts through proof boundaries** - Example: Bridge_BridgeCore.v ends mid-proof (line 164)
2. **No proper imports/exports** - Modules don't reference each other
3. **Hard-coded line numbers** - Extraction doesn't respect logical boundaries
4. **Missing context** - Later modules reference definitions from earlier ones without imports

### Example Issues Found
- Bridge_BridgeCore.v: Ends with incomplete proof `Lemma firstn_pad_to`
- All modules have "NOTE: This is a standalone extraction for analysis purposes"
- None have been tested for independent compilation

## What's Required for True Modular System

### 1. Fix Extraction Script (4-6 hours)
- Rewrite to detect Definition/Lemma/Qed boundaries
- Don't cut in middle of proofs
- Ensure each module is syntactically complete
- Generate proper imports for dependencies

### 2. Create Module Chain (6-8 hours)
- Module 1: Export core definitions
- Module 2-14: Import from previous, export own definitions
- Test each compiles independently: `coqc -R . ThieleUniversalBridge Bridge_Module1.v`
- Fix any issues (missing imports, redefined terms, etc.)

### 3. Fix Proofs in Isolation (3-5 hours)
- Once modules compile, work on problematic sections
- Fix the 2 admitted proofs
- Ensure all compile

### 4. Integration (2-3 hours)
- Merge all modules back into single file
- OR keep modular and have main file Import all
- Test complete compilation
- Verify no admits remain

**Total estimated time: 15-22 hours**

## Alternative: Direct Fix in Main File (Option A)

### What This Involves (4-6 hours total)
1. Remove 2 admits from ThieleUniversalBridge.v
2. Fix transition_FindRule_step2b_temp5 properly:
   - Issue: Proof term explosion when using helper lemmas
   - Solution: Inline the helper logic OR use more aggressive abstract
   - Time: 2-3 hours
3. Fix Haddr5 assertion:
   - Issue: Goal mismatch after read_reg_write_reg_same
   - Solution: Better proof structure, possibly unfold CPU.step differently
   - Time: 1-2 hours
4. Continue fixing remaining errors to 100% compilation
   - Current: 65% (line 1832)
   - Remaining: 35% (line 1832-2876)
   - Time: 1-2 hours

**Total: 4-6 hours, achieves goal of "no admits"**

## Recommendation

**Go with Option A (Direct Fix)** because:
1. **Achieves the core goal**: Complete proof without admits
2. **Realistic timeframe**: 4-6 hours vs 15-22 hours
3. **Lower risk**: Working in known codebase
4. **Analysis infrastructure still valuable**: Helps understand structure

True modular refactoring would be valuable for:
- Long-term maintainability
- Parallel development
- Educational purposes

But it's not necessary to achieve "proof complete without admits."

## Action Plan (Option A)

1. **Remove admits** (30 min)
   - Document what they were attempting to prove
   
2. **Fix transition_FindRule_step2b_temp5** (2-3 hours)
   - Try: Inline helper lemma proofs directly
   - Try: Use abstract more aggressively
   - Try: Rewrite proof without transitivity chain
   
3. **Fix Haddr5** (1-2 hours)
   - Carefully unfold CPU.step for AddConst
   - Use correct lemmas for reading from write_reg states
   
4. **Continue to 100%** (1-2 hours)
   - Fix error at line 1832
   - Continue through remaining 35% of file

5. **Verification** (30 min)
   - Full compilation test
   - Verify 0 admits
   - Document completion

**Deliverable**: ThieleUniversalBridge.v compiles fully with 0 Admitted lemmas.
