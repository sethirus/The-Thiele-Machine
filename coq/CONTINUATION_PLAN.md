# Continuation Plan for ThieleUniversalBridge.v Proofs

## Current Status

File compiles successfully with documented admits. Previous work identified `length_run_n_eq_bounded` as the critical blocker.

## Infrastructure Lemmas Added (Latest Session)

**Created foundational lemmas that work on expanded nth/firstn/skipn forms:**

1. **`nth_write_diff`** (generic version for any type A):
   - Proves: `nth r (firstn r' l ++ [v] ++ skipn (S r') l) d = nth r l d` when `r <> r'`
   - Works directly on the expanded form that results from `unfold CPU.write_reg`
   - Can be applied after `simpl` expands definitions

2. **`nth_nat_write_diff`** (specialized for nat lists):
   - Same as above but specifically for `list nat` with default value 0
   - Directly applicable to register tracking problems

**Purpose**: These lemmas provide the "bridge" between abstract CPU operations and their expanded list forms, enabling proofs to proceed after Coq's simplification tactics expand definitions.

**Status**: Both lemmas proven and file compiles successfully.

## Work Attempted in This Session

Attempted to use the new infrastructure lemmas to prove TODOs:

### Success:
- ✅ Infrastructure lemmas `nth_write_diff` and `nth_nat_write_diff` proven
- ✅ File compiles with infrastructure in place
- ✅ Demonstrated viable path forward

### Challenges:
- Pattern matching still requires precise alignment with expanded forms
- After `unfold CPU.step, CPU.write_reg. simpl.`, the resulting expression structure needs exact matching
- Nested register writes (PC first, then target register) create complex nested firstn/skipn expressions

### Example of Remaining Challenge:

After simpl, goals look like:
```coq
nth 8 (firstn 7 (firstn 0 regs ++ [v1] ++ skipn 1 regs) ++ [v2] ++ skipn 8 (...)) 0
```

The infrastructure lemmas can prove this, but require:
1. Identifying the exact structure
2. Applying lemmas in the right order (outer write first, then inner)
3. Providing length proofs for intermediate expressions

## Viable Path Forward

### Option 1: Complete Infrastructure (Recommended)

Add more specialized lemmas that handle common patterns:

```coq
(* Preservation through nested writes *)
Lemma nth_double_write_diff : forall l r r1 r2 v1 v2,
  r <> r1 -> r <> r2 ->
  r < length l -> r1 < length l -> r2 < length l ->
  nth r (firstn r2 (firstn r1 l ++ [v1] ++ skipn (S r1) l) ++ [v2] ++ 
         skipn (S r2) (firstn r1 l ++ [v1] ++ skipn (S r1) l)) 0 =
  nth r l 0.
```

This would directly match the pattern from CPU.step (PC write followed by register write).

### Option 2: Tactic Automation

Create custom Ltac tactics that:
1. Recognize register tracking goals
2. Automatically apply infrastructure lemmas
3. Discharge side conditions (inequalities, length bounds)

Example:
```coq
Ltac solve_register_preservation :=
  match goal with
  | |- nth ?r (firstn ?r' _ ++ _ ++ skipn _ _) _ = nth ?r _ _ =>
    apply nth_nat_write_diff; [lia | lia | lia]
  end.
```

### Option 3: Abstract Earlier

Instead of `unfold CPU.step. simpl.`, use:
```coq
assert (CPU.read_reg r (CPU.step instr st) = CPU.read_reg r st).
{ apply read_reg_write_reg_diff. ... }
```

Then apply this abstract lemma before any unfolding.

## Recommendation

**Immediate Next Steps:**

1. ✅ **DONE**: Create `nth_write_diff` and `nth_nat_write_diff` infrastructure lemmas
2. **TODO**: Create `nth_double_write_diff` for nested write pattern (CPU.step common case)
3. **TODO**: Create Ltac tactic `solve_reg_preservation` to automate application
4. **TODO**: Prove one TODO completely using infrastructure + automation
5. **TODO**: Apply systematically to remaining TODOs

This layered approach (infrastructure → automation → application) will make the proofs maintainable and reusable.

## Progress Summary

**Latest Session:**
- Created foundational infrastructure lemmas ✅
- File compiles successfully ✅
- Identified precise pattern matching requirements ✅
- Documented clear path forward ✅

**What Remains:**
- Additional specialized infrastructure for nested writes
- Tactical automation for common patterns
- Systematic application to all 8 TODOs

The foundational work is complete. The remaining work is to build on this foundation with specialized lemmas and automation.
