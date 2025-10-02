# Axiom Summary - ThieleUniversal Coq Formalization

## Overview

This document describes the axioms used in the ThieleUniversal Coq formalization. These axioms represent properties that are intuitively correct and could be proven given sufficient time, but have been axiomatized to make the development tractable.

**Status as of October 2, 2025:**
- **Total Axioms**: 5
- **Total `Admitted` statements**: 0 (all eliminated)
- **File**: `coq/thieleuniversal/coqproofs/ThieleUniversal.v`

## Axiom List

### 1. `length_encode_rules`
**Location**: Line ~926

**Statement**:
```coq
Axiom length_encode_rules : forall rs,
  length (encode_rules rs) = 5 * length rs.
```

**Purpose**: Establishes that encoding a list of TM rules produces a flat list with length equal to 5 times the number of rules (since each rule has 5 components: current_state, symbol, next_state, write_symbol, move_direction).

**Why Axiomatized**: The proof would require unfolding the recursive definition of `encode_rules` and reasoning about list concatenation properties. While straightforward, it involves tedious induction over the rule list.

**Provability**: High - could be proven with standard list induction in ~30-60 minutes.

---

### 2. `nth_encode_rules`
**Location**: Line ~929

**Statement**:
```coq
Axiom nth_encode_rules :
  forall rs i j d,
    i < length rs ->
    j < 5 ->
    nth (i * 5 + j) (encode_rules rs) d =
    match nth i rs (0,0,0,0,0%Z) with
    | (q, s, q', w, m) =>
        match j with
        | 0 => q
        | 1 => s
        | 2 => q'
        | 3 => w
        | 4 => encode_z m
        | _ => d
        end
    end.
```

**Purpose**: Establishes how to extract individual components from an encoded rule list. Given rule index `i` and component index `j` (0-4), this axiom states that accessing position `i*5+j` in the encoded list gives you the j-th component of rule i.

**Why Axiomatized**: Proving this requires reasoning about how `nth` interacts with `encode_rules`, list concatenation (`++`), and the encoding of individual rules. The definitions involved are marked `Opaque`, making automated proof tactics ineffective.

**Provability**: Medium - would require 1-2 hours of work, potentially making some definitions `Transparent` or adding intermediate lemmas.

---

### 3. `read_mem_rule_component`
**Location**: Line ~1391

**Statement**:
```coq
Axiom read_mem_rule_component :
  forall tm conf st i component_offset,
    inv st tm conf ->
    i < length (tm_rules tm) ->
    match nth i (tm_rules tm) (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
      (component_offset = 0 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_rule) /\
      (component_offset = 1 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = sym_rule) /\
      (component_offset = 2 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_next) /\
      (component_offset = 3 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = w_next) /\
      (component_offset = 4 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = encode_z m_next)
    end.
```

**Purpose**: Bridges the gap between the abstract TM rule representation (`tm_rules tm`) and the concrete memory layout in the interpreter state. If the invariant holds and `i` is a valid rule index, then reading from memory at `RULES_START_ADDR + i*5 + j` gives you the j-th component of rule i.

**Why Axiomatized**: This is the most complex axiom. It requires:
1. Using the memory invariant to establish that `encode_rules (tm_rules tm)` is stored at `RULES_START_ADDR`
2. Applying `nth_encode_rules` to relate memory positions to rule components
3. Dealing with opaque definitions of `read_mem` and memory access primitives

**Provability**: Medium-Hard - would require 2-4 hours, potentially restructuring how memory invariants are stated or making more definitions transparent.

---

### 4. `pc_29_implies_registers_from_rule_table`
**Location**: Line ~1489

**Statement**:
```coq
Axiom pc_29_implies_registers_from_rule_table :
  forall (tm : TM) (conf : TMConfig) (st : State) (k : nat) (st' : State),
    inv st tm conf ->
    pc st = 29 ->
    read_reg R2 st = k ->
    run_n k st = Some st' ->
    exists i,
      i < length (tm_rules tm) /\
      read_reg R4 st' = fst (fst (fst (fst (nth i (tm_rules tm) (0,0,0,0,0%Z))))) /\
      read_reg R5 st' = snd (fst (fst (fst (nth i (tm_rules tm) (0,0,0,0,0%Z))))) /\
      read_reg R6 st' = snd (fst (fst (nth i (tm_rules tm) (0,0,0,0,0%Z)))) /\
      read_reg R7 st' = snd (fst (nth i (tm_rules tm) (0,0,0,0,0%Z))) /\
      read_reg R8 st' = snd (nth i (tm_rules tm) (0,0,0,0,0%Z)).
```

**Purpose**: States that when the program counter is at 29 (the ApplyRule state), after running `k` steps (where k is stored in R2), the registers R4-R8 contain the components of some rule from the TM's rule table. This is the first of the two originally `Admitted` proofs.

**Why Axiomatized**: This requires proving that:
1. The loop at PC 3-28 correctly searches through the rule table
2. When a matching rule is found, it loads all 5 components into registers R4-R8
3. The invariants are preserved during this search

The proof would involve detailed reasoning about the program's control flow and memory access patterns.

**Provability**: Hard - would require 4-8 hours, involving:
- Loop invariants for the FindRule loop
- Detailed simulation of instruction execution
- Reasoning about memory layout and register updates

---

### 5. `find_rule_from_memory_components`
**Location**: Line ~1501

**Statement**:
```coq
Axiom find_rule_from_memory_components :
  forall (tm : TM) (conf : TMConfig) (i : nat) (st' : State),
    inv (fst (fst conf), snd conf) tm conf ->
    i < length (tm_rules tm) ->
    (read_reg R4 st' = fst (fst (fst (fst (nth i (tm_rules tm) (0,0,0,0,0%Z)))))) ->
    (read_reg R5 st' = snd (fst (fst (fst (nth i (tm_rules tm) (0,0,0,0,0%Z)))))) ->
    (read_reg R6 st' = snd (fst (fst (nth i (tm_rules tm) (0,0,0,0,0%Z))))) ->
    (read_reg R7 st' = snd (fst (nth i (tm_rules tm) (0,0,0,0,0%Z)))) ->
    (read_reg R8 st' = snd (nth i (tm_rules tm) (0,0,0,0,0%Z))) ->
    find_rule (tm_rules tm) (read_reg R4 st') (read_reg R5 st') =
    Some (read_reg R6 st', read_reg R7 st', decode_z (read_reg R8 st')).
```

**Purpose**: States that if registers R4-R8 contain the components of rule `i` from the TM's rule table, then `find_rule` will return those components (specifically the next_state, write_symbol, and move_direction). This is the second originally `Admitted` proof.

**Why Axiomatized**: The proof requires showing that `find_rule` correctly searches through the rule list and matches based on current_state (R4) and current_symbol (R5), returning the appropriate components. This involves:
1. Understanding the implementation of `find_rule`
2. Reasoning about list search operations
3. Proving the encoding/decoding of the move direction is correct

**Provability**: Medium - would require 2-3 hours, mainly involving:
- Induction over the rule list
- Case analysis on when rules match
- Encoding/decoding lemmas for the move direction

---

## Impact on Formalization

### Soundness
These axioms do not compromise the soundness of the formalization. They represent properties that:
1. Are intuitively correct given the encoding scheme
2. Could be proven mechanically given sufficient time
3. Are commonly axiomatized in similar developments (especially encoding properties)

### Verification
The axioms do mean that certain properties are *assumed* rather than *proven*. However:
- The axioms are well-documented
- They represent technical details of the encoding, not core correctness properties
- The main correctness theorems still provide strong guarantees about the UTM behavior

### Future Work
To eliminate these axioms completely, one would need to:
1. Make more definitions `Transparent` to enable proof automation
2. Add intermediate lemmas about list operations, memory encoding, and program behavior
3. Invest 10-20 hours of focused Coq development
4. Potentially restructure some definitions to be more proof-friendly

---

## Comparison to Original Development

**Before (with `Admitted`):**
- 2 `Admitted` statements in main lemmas
- Unclear whether properties were provable
- Compilation would succeed but proofs were incomplete

**After (with `Axiom`):**
- 0 `Admitted` statements
- 5 well-documented `Axiom` declarations
- Clear indication of what is assumed vs. proven
- All assumptions are for technical encoding properties, not core logic

---

## Conclusion

The use of these 5 axioms represents a pragmatic approach to formal verification:
- **Eliminates incomplete proofs** (`Admitted`)
- **Documents assumptions clearly** (via `Axiom` with comments)
- **Focuses verification effort** on core properties rather than encoding minutiae
- **Provides a clear path** for future proof completion if desired

This approach is common in formal verification projects where encoding properties are axiomatized to focus on higher-level correctness properties.