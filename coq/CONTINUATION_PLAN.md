# Continuation Plan for ThieleUniversalBridge.v Proofs

## Current Status

File compiles successfully with documented admits. Previous work identified `length_run_n_eq_bounded` as the critical blocker.

## Infrastructure Lemmas Added

### Session 1: Basic Infrastructure
**`nth_write_diff`** (generic, polymorphic):
- Proves: `nth r (firstn r' l ++ [v] ++ skipn (S r') l) d = nth r l d` when `r <> r'`
- Works on expanded forms from `unfold CPU.write_reg`

**`nth_nat_write_diff`** (specialized):
- Same functionality, specialized for `list nat` with default value 0
- Directly applicable to CPU register tracking

### Session 2: Nested Write Pattern
**`nth_double_write_diff`** ✅ NEW:
- Handles nested writes: PC write followed by register write (common CPU.step pattern)
- Proves preservation through two consecutive writes
- Type: `forall (l : list nat) (r r1 r2 v1 v2 : nat)`
- Automatically handles intermediate length tracking

**`solve_reg_preservation`** Ltac ✅ NEW:
- Automated tactic for register preservation goals
- Recognizes both single and double write patterns
- Automatically applies correct lemma with `lia` for side conditions

## Example Usage

### Single Write:
```coq
(* Goal: nth 8 (firstn 7 regs ++ [v] ++ skipn 8 regs) 0 = nth 8 regs 0 *)
solve_reg_preservation.
(* Automatically applies nth_nat_write_diff with proofs *)
```

### Nested Write (CPU.step pattern):
```coq
(* Goal: nth 8 (firstn 7 (firstn 0 regs ++ [v1] ++ skipn 1 regs) ++ [v2] ++ ...) 0 = nth 8 regs 0 *)
solve_reg_preservation.
(* Automatically applies nth_double_write_diff with proofs *)
```

## Status

✅ All infrastructure lemmas proven  
✅ Ltac automation implemented  
✅ File compiles successfully (~3 minutes)  
✅ Detailed TODO documentation added to source code
✅ Comprehensive usage guide created (INFRASTRUCTURE_USAGE_GUIDE.md)

## Next Steps - Ready for Application

With infrastructure complete and usage guide in place, the remaining work is straightforward:

1. **Apply to TODO at line 2021** (Jz - single write pattern)
   - Follow Pattern 1 from usage guide
   - Use `nth_nat_write_diff` lemma
   - Estimated effort: 5-10 lines of proof

2. **Apply to TODO at line 2043** (AddConst - double write pattern)
   - Follow Pattern 2 from usage guide  
   - Use `nth_double_write_diff` lemma
   - Estimated effort: 10-15 lines of proof

3. **Apply to remaining TODOs** in `loop_iteration_no_match`
   - Use same patterns adapted to each instruction type
   - Infrastructure handles all register tracking mechanics

## Documentation Created

1. **INFRASTRUCTURE_USAGE_GUIDE.md** ✅ NEW:
   - Complete reference for all infrastructure lemmas
   - Step-by-step proof patterns with examples
   - Specific strategies for each TODO location
   - Common pitfalls and solutions
   - Full example proof for TODO at line 2043

2. **Enhanced TODO comments in source** ✅ NEW:
   - Lines 2017-2031: Detailed proof strategy for Jz TODO
   - Lines 2037-2055: Detailed proof strategy for AddConst TODO
   - Includes exact lemma applications and side condition management

## Recommendation

**Immediate Next Steps:**

1. ✅ **DONE**: Create `nth_write_diff` and `nth_nat_write_diff` infrastructure lemmas
2. ✅ **DONE**: Create `nth_double_write_diff` for nested write pattern (CPU.step common case)
3. ✅ **DONE**: Create Ltac tactic `solve_reg_preservation` to automate application
4. **IN PROGRESS**: Prove one TODO completely using infrastructure + automation
5. **TODO**: Apply systematically to remaining TODOs

## Progress Summary

**Latest Session:**
- Added `nth_double_write_diff` lemma for nested writes ✅
- Implemented `solve_reg_preservation` Ltac tactic ✅
- File compiles successfully ✅
- Infrastructure complete and ready to use ✅

**What Remains:**
- Apply infrastructure to complete 8 TODOs in loop_iteration_no_match
- Validate approach with at least one complete proof
- Document patterns and best practices

The infrastructure work is now complete. All tools are in place to systematically complete the register tracking proofs.
