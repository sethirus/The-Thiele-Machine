# Infrastructure Usage Guide for ThieleUniversalBridge.v

## Overview

This guide explains how to use the register tracking infrastructure lemmas to complete the remaining TODOs in `loop_iteration_no_match`.

## Infrastructure Lemmas Available

### 1. `nth_write_diff` (Generic)
```coq
Lemma nth_write_diff : forall {A : Type} (l : list A) (r r' : nat) (v d : A),
  r <> r' ->
  r < length l ->
  r' < length l ->
  nth r (firstn r' l ++ [v] ++ skipn (S r') l) d = nth r l d.
```

### 2. `nth_nat_write_diff` (Specialized for nat lists)
```coq
Lemma nth_nat_write_diff : forall (l : list nat) (r r' v : nat),
  r <> r' ->
  r < length l ->
  r' < length l ->
  nth r (firstn r' l ++ [v] ++ skipn (S r') l) 0 = nth r l 0.
```

### 3. `nth_double_write_diff` (For nested writes - CPU.step pattern)
```coq
Lemma nth_double_write_diff : forall (l : list nat) (r r1 r2 v1 v2 : nat),
  r <> r1 ->
  r <> r2 ->
  r < length l ->
  r1 < length l ->
  r2 < length l ->
  nth r (firstn r2 (firstn r1 l ++ [v1] ++ skipn (S r1) l) ++ [v2] ++ 
         skipn (S r2) (firstn r1 l ++ [v1] ++ skipn (S r1) l)) 0 =
  nth r l 0.
```

### 4. `solve_reg_preservation` (Ltac tactic)
```coq
Ltac solve_reg_preservation :=
  match goal with
  | |- nth ?r (firstn ?r' _ ++ _ ++ skipn _ _) _ = nth ?r _ _ =>
    apply nth_nat_write_diff; [lia | lia | lia]
  | |- nth ?r (firstn ?r2 (firstn ?r1 _ ++ _ ++ skipn _ _) ++ _ ++ 
                skipn _ (firstn ?r1 _ ++ _ ++ skipn _ _)) _ = nth ?r _ _ =>
    apply nth_double_write_diff; [lia | lia | lia | lia | lia]
  end.
```

## Register Constants

```coq
CPU.REG_PC = 0
CPU.REG_Q = 1
CPU.REG_HEAD = 2
CPU.REG_SYM = 3
CPU.REG_Q' = 4
CPU.REG_WRITE = 5
CPU.REG_MOVE = 6
CPU.REG_ADDR = 7
CPU.REG_TEMP1 = 8
CPU.REG_TEMP2 = 9
```

## Usage Patterns

### Pattern 1: Single Register Write (e.g., Jz instruction)

**Context**: After `unfold CPU.step. simpl.` for a Jz instruction (which only writes PC).

**Goal Structure**: 
```coq
nth 8 (firstn 0 regs ++ [v] ++ skipn 1 regs) 0 <> 0
```

**Proof Strategy**:
```coq
assert (H_preserve: nth 8 (firstn 0 (cpu3.(CPU.regs)) ++ [new_pc] ++ skipn 1 (cpu3.(CPU.regs))) 0
                   = nth 8 (cpu3.(CPU.regs)) 0).
{ apply nth_nat_write_diff.
  - (* TEMP1 != PC *) unfold CPU.REG_TEMP1, CPU.REG_PC. lia.
  - (* TEMP1 < length *) unfold CPU.REG_TEMP1. rewrite Hlen3. lia.
  - (* PC < length *) unfold CPU.REG_PC. rewrite Hlen3. lia. }
rewrite H_preserve.
unfold CPU.REG_TEMP1 in Htemp3_nz.
unfold CPU.read_reg in Htemp3_nz.
exact Htemp3_nz.
```

### Pattern 2: Double Register Write (e.g., AddConst instruction)

**Context**: After `unfold CPU.step, CPU.write_reg. simpl.` for an AddConst instruction.

**Goal Structure**:
```coq
nth 8 (firstn 7 (firstn 0 regs ++ [v1] ++ skipn 1 regs) ++ [v2] ++ 
       skipn 8 (firstn 0 regs ++ [v1] ++ skipn 1 regs)) 0 <> 0
```

**Proof Strategy**:
```coq
assert (H_preserve: nth 8 (firstn 7 (firstn 0 (cpu4.(CPU.regs)) ++ [new_pc] ++ skipn 1 (cpu4.(CPU.regs))) ++ 
                                [new_addr] ++ skipn 8 (firstn 0 (cpu4.(CPU.regs)) ++ [new_pc] ++ skipn 1 (cpu4.(CPU.regs)))) 0
                   = nth 8 (cpu4.(CPU.regs)) 0).
{ apply nth_double_write_diff.
  - (* TEMP1 != PC *) unfold CPU.REG_TEMP1, CPU.REG_PC. lia.
  - (* TEMP1 != ADDR *) unfold CPU.REG_TEMP1, CPU.REG_ADDR. lia.
  - (* TEMP1 < length *) unfold CPU.REG_TEMP1. rewrite Hlen4. lia.
  - (* PC < length *) unfold CPU.REG_PC. rewrite Hlen4. lia.
  - (* ADDR < length *) unfold CPU.REG_ADDR. rewrite Hlen4. lia. }
rewrite H_preserve.
unfold CPU.REG_TEMP1 in Htemp4_nz.
unfold CPU.read_reg in Htemp4_nz.
exact Htemp4_nz.
```

### Pattern 3: Using the Ltac Tactic (when goal matches exactly)

**If the goal is an equality** (not inequality):
```coq
solve_reg_preservation.
```

**If the goal is an inequality** (as in the TODOs):
```coq
assert (H_preserve: nth r (complex_expression) 0 = nth r (simple_expression) 0).
{ solve_reg_preservation. }
rewrite H_preserve.
(* Then apply your nonzero hypothesis *)
```

## Specific TODO Locations and Strategies

### TODO at Line 2021 (Jz - PC write only)
- **Instruction**: Jz (Jump if Zero) - only writes PC when condition is false
- **Registers**: TEMP1 (8) preserved, PC (0) written
- **Pattern**: Single write
- **Lemma to use**: `nth_nat_write_diff`

### TODO at Line 2043 (AddConst - PC + ADDR write)
- **Instruction**: AddConst writes to ADDR (7), CPU.step also writes PC (0)
- **Registers**: TEMP1 (8) preserved, PC (0) and ADDR (7) written
- **Pattern**: Double write (nested)
- **Lemma to use**: `nth_double_write_diff`

## Common Pitfalls and Solutions

### Pitfall 1: Length Hypotheses Missing
**Problem**: Infrastructure lemmas require `length regs = 10`

**Solution**: Use `length_run_n_eq_bounded` to establish lengths:
```coq
assert (Hlen4: length cpu4.(CPU.regs) = 10).
{ rewrite Hcpu4_eq. apply (length_run_n_eq_bounded cpu 4 Hlen). }
```

### Pitfall 2: Goal Not Matching Expected Pattern
**Problem**: After simpl, the goal structure is different than expected

**Solution**: 
1. Inspect the actual goal structure
2. Match it against the lemma statement
3. Adjust the assertion to match the actual expanded form

### Pitfall 3: Unfolding `CPU.read_reg` in Hypotheses
**Problem**: The hypothesis has `CPU.read_reg` but goal has `nth`

**Solution**: Unfold in the hypothesis before using it:
```coq
unfold CPU.REG_TEMP1 in Htemp4_nz.
unfold CPU.read_reg in Htemp4_nz.
(* Now Htemp4_nz has the form: nth 8 regs 0 <> 0 *)
```

## Example: Complete Proof for TODO at Line 2043

```coq
(* Starting context: after unfold CPU.step, CPU.write_reg. simpl. *)
(* and unfold CPU.read_reg. simpl. *)

(* Assume we have: *)
(* Hlen4: length cpu4.(CPU.regs) = 10 *)
(* Htemp4_nz: CPU.read_reg CPU.REG_TEMP1 cpu4 <> 0 *)

(* Goal after simpl will be something like: *)
(* nth 8 (firstn 7 (firstn 0 (cpu4.(CPU.regs)) ++ [...] ++ ...) ++ [...] ++ ...) 0 <> 0 *)

(* Proof: *)
assert (H_preserve: 
  nth (CPU.REG_TEMP1) 
    (firstn (CPU.REG_ADDR)
       (firstn (CPU.REG_PC) (cpu4.(CPU.regs)) ++ 
        [S (CPU.read_reg CPU.REG_PC cpu4)] ++ 
        skipn (S (CPU.REG_PC)) (cpu4.(CPU.regs))) ++
     [CPU.read_reg CPU.REG_ADDR cpu4 + RULE_SIZE] ++
     skipn (S (CPU.REG_ADDR))
       (firstn (CPU.REG_PC) (cpu4.(CPU.regs)) ++ 
        [S (CPU.read_reg CPU.REG_PC cpu4)] ++ 
        skipn (S (CPU.REG_PC)) (cpu4.(CPU.regs))))
    0 =
  nth (CPU.REG_TEMP1) (cpu4.(CPU.regs)) 0).
{ apply nth_double_write_diff.
  - (* TEMP1 != PC *) unfold CPU.REG_TEMP1, CPU.REG_PC. lia.
  - (* TEMP1 != ADDR *) unfold CPU.REG_TEMP1, CPU.REG_ADDR. lia.
  - (* TEMP1 < length *) unfold CPU.REG_TEMP1. rewrite Hlen4. lia.
  - (* PC < length *) unfold CPU.REG_PC. rewrite Hlen4. lia.
  - (* ADDR < length *) unfold CPU.REG_ADDR. rewrite Hlen4. lia. }
rewrite H_preserve.
unfold CPU.REG_TEMP1 in Htemp4_nz.
unfold CPU.read_reg in Htemp4_nz.
exact Htemp4_nz.
```

## Next Steps

1. Apply these patterns to complete the TODOs at lines 2021 and 2043
2. Use similar strategies for other register tracking TODOs
3. Document any new patterns discovered for future reference

## Files Modified

- `ThieleUniversalBridge.v`: Added infrastructure lemmas (lines 938-1015)
- TODOs with detailed proof strategies: lines 2017-2031, 2037-2055

## Additional Resources

- `CONTINUATION_PLAN.md`: Overall strategy and progress tracking
- `BRIDGE_LEMMA_STATUS.md`: Complete analysis of all admits
- `WORK_SUMMARY.md`: Summary of findings and approaches
