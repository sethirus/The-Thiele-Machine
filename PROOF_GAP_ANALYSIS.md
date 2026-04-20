# Proof Gap Analysis — Thiele Machine Hardware Bisimulation
*Produced by deep audit of `coq/kami_hw/` as of 2026-04-15.*

---

## Executive Summary

**Zero `Admitted.` statements exist anywhere in `coq/`.** All 46 opcode bridges are
`Qed`. The repository comment in `RTLGapRegistry.v` that says "7 opcodes without any
hardware-level proofs" is **stale** — it predates the final round of proofs in
`GraphReconstructionBridge.v` (last updated 2026-04-15) and has not been updated.

However, **two real architectural gaps remain** that are not proof gaps in the Coq
sense but are genuine divergences between the hardware and the full kernel spec under
non-trivial coupling data. These are documented below with full precision.

---

## 1. The Stale File: `RTLGapRegistry.v`

`RTLGapRegistry.v` lists 7 opcodes as having no hardware-level proofs:

```
TENSOR_SET, TENSOR_GET, COMPOSE, MORPH_TENSOR, CALL, RET, CHSH_TRIAL
```

This was accurate when written. It is no longer accurate. `GraphReconstructionBridge.v`
§18 (lines 2827–2875) states explicitly:

> Admitted count: 0. All 46 opcode bridges are fully proven (Qed).

Every one of the 7 listed opcodes now has a named `Qed` theorem:

| Opcode | Theorem | Condition |
|---|---|---|
| `TENSOR_SET` | `driven_step_tensor_set_full` | `tensor_indices_ok i j = true` |
| `TENSOR_GET` | `driven_step_tensor_get_full` | `tensor_indices_ok i j = true`, graph entry exists |
| `CALL` | `driven_step_call` | `WellFormedSnapshot`, `pc < MEM_SIZE` |
| `RET` | `driven_step_ret` | `WellFormedSnapshot` |
| `CHSH_TRIAL` | `driven_step_chsh_trial` | `chsh_bits_ok = true` |
| `COMPOSE` | `driven_step_compose` | `extended_hw_invariant` |
| `MORPH_TENSOR` | `driven_step_morph_tensor` | `extended_hw_invariant` |

**Action needed: update `RTLGapRegistry.v`** to reflect the current proof state, or
retire the file and point to `GraphReconstructionBridge.v` §18 as the definitive record.

---

## 2. Full Proof Coverage Breakdown (46 opcodes)

### Group A — Unconditional (31 opcodes)

All opcodes satisfying `SupportedOpcode` are covered by `driven_step_supported` in
`EmbedStep.v`. These 31 opcodes have no preconditions beyond well-typed state. The
precise list is in `EmbedStep.v`.

### Group B — Conditional with simple runtime precondition (11 opcodes)

These have `Qed` proofs under preconditions that are checked at runtime (either
enforced by the hardware or by the calling contract):

- **PNEW**: `pt_well_formed` + fresh slot available
- **PSPLIT**: `pt_well_formed` + space available
- **PMERGE**: `pt_well_formed` + modules exist
- **CALL**: `WellFormedSnapshot` + `pc < MEM_SIZE`
- **RET**: `WellFormedSnapshot`
- **CHSH_TRIAL**: `chsh_bits_ok = true`
- **LASSERT**: `flen = lassert_hw_flen`
- **MORPH_ASSERT**: `morph_table_wf`
- **MORPH_GET**: `extended_hw_invariant`
- **MORPH_DELETE**: `morph_table_wf`
- **MORPH / MORPH_ID**: `extended_hw_invariant` + modules exist

### Group C — TENSOR_SET / TENSOR_GET (2 opcodes)

Covered by `driven_step_tensor_set_full` and `driven_step_tensor_get_full`.  
Precondition: `tensor_indices_ok i j = true` (a bounds check on the tensor indices).  
This is a well-defined runtime precondition with no architectural ambiguity.

### Group D — COMPOSE and MORPH_TENSOR (2 opcodes) — the architectural gap

These have `Qed` proofs under `extended_hw_invariant`. **What this invariant
actually requires is the critical point.**

---

## 3. The Architectural Gap: COMPOSE and MORPH_TENSOR

### What `extended_hw_invariant` requires

Defined in `GraphReconstructionBridge.v` line 771:

```coq
Definition extended_hw_invariant (ks : KamiSnapshot) : Prop :=
  pt_well_formed ks /\
  morph_table_wf (snap_rich_state ks) /\
  coupling_zero_empty (snap_rich_state ks) /\
  coupling_desc_all_zero (snap_rich_state ks) /\
  coupling_desc_safe ks.
```

The load-bearing condition is `coupling_desc_all_zero`:

```coq
Definition coupling_desc_all_zero (rs : RichSnapshotState) : Prop :=
  forall i entry, rs.(rich_morph_table) i = Some entry ->
    morph_entry_coupling_desc entry = 0.
```

**Plain English**: every morphism currently in the table must have `coupling_desc = 0`,
meaning no morphism has any coupling data attached.

### Why MORPH_TENSOR violates this invariant in the post-state

Looking at `Abstraction.v` (the kernel spec), `instr_morph_tensor` is implemented as:

```coq
let '(rs', _) := rich_state_add_morph_with_coupling rs
                   new_ms.(morph_source) new_ms.(morph_target)
                   new_ms.(morph_coupling).(coupling_pairs)
                   new_ms.(morph_coupling).(coupling_label) false in
```

`rich_state_add_morph_with_coupling` calls `rich_state_add_coupling_data`, which
allocates a new coupling descriptor at `rich_next_coupling_desc_id` (≥ 1). The newly
created morphism gets `coupling_desc_addr = desc_id > 0`. This **breaks**
`coupling_desc_all_zero` in the post-state.

### Why COMPOSE has the same problem

From `Abstraction.v`, `instr_compose` computes:

```coq
let composed_pairs := relational_compose pairs1 pairs2 in
...
let '(rs', new_id) := rich_state_add_morph_with_coupling rs ... composed_pairs ...
```

Same result: if inputs carry non-empty coupling, the composed morphism gets
`coupling_desc_addr > 0`, breaking `coupling_desc_all_zero`.

### The divergence

The **hardware** (`ThieleCPUCore.v`) always passes `coupling_desc = 0` when creating
morphisms via COMPOSE and MORPH_TENSOR. The hardware does not propagate coupling data
through these operations — it always outputs a morphism with empty coupling.

The **kernel** (Abstraction.v) tracks and propagates full coupling data.

Under `extended_hw_invariant` (all existing morphisms have empty coupling), there is
no divergence: `relational_compose [] [] = []`, so both sides produce empty coupling,
and the proofs are valid. The first COMPOSE or MORPH_TENSOR on an all-empty-coupling
state is fully proven.

But after that first operation (if the result has coupling data), `extended_hw_invariant`
no longer holds, and no proof covers subsequent operations on those morphisms.

### Concrete failure scenario

1. Execute MORPH (creates morphisms M1, M2 — empty coupling, invariant holds).
2. Execute MORPH_TENSOR on M1, M2 → creates M3 with `coupling_pairs = M1_pairs ++ M2_pairs`.
   - If M1 and M2 have empty coupling: `M3` also has empty coupling. Invariant still holds. Proof covers this.
   - If M1 or M2 had non-empty coupling: M3 gets non-empty coupling. Invariant broken.
3. Execute COMPOSE on M3, M4 (any morphism) →
   - **Hardware**: creates M5 with `coupling_desc = 0` (empty).
   - **Kernel**: creates M5 with `coupling_desc = desc_id > 0` (from relational composition).
   - These differ. No proof covers this case. **Gap.**

Currently, the only way to reach non-empty coupling in the first place is through
`rich_state_add_morph_with_coupling`. Since all morphisms start with empty coupling,
the invariant holds at initialization. It is preserved by every opcode *except*
MORPH_TENSOR and COMPOSE when they produce non-empty coupling. So in the current
opcode set, the invariant can only be broken by those same two opcodes. This is circular:
to exercise the gap, you must first execute MORPH_TENSOR or COMPOSE — but the first
execution is proven (from empty coupling, result is also empty if both inputs are
empty... but MORPH_TENSOR's tensor product of two identity morphisms may not be
empty, depending on the module sizes).

### Precise scope of the gap

The bisimulation gap manifests when:
- A program executes MORPH_TENSOR on morphisms where
  `f_pairs ++ g_pairs ≠ []` (non-trivial tensor coupling), AND
- Any subsequent COMPOSE or MORPH_TENSOR operates on the resulting morphism.

Programs that use MORPH_TENSOR only as a terminal operation (result is not composed
further) do not exercise the gap.

---

## 4. What Remains To Be Done

### Option A — Close the gap in RTL (full closure)

Modify `ThieleCPUCore.v` to propagate coupling data through COMPOSE and MORPH_TENSOR:
- COMPOSE must compute and store `relational_compose(pairs(m1), pairs(m2))`
- MORPH_TENSOR must store `f.pairs ++ g.pairs` (concatenation of tensor factors)

This requires a non-trivial RTL extension (coupling data lives in memory arrays, not
registers). A coupling data store and relational composition unit would need to be added
to the hardware.

Once done, the `extended_hw_invariant` precondition can be replaced by `extended_hw_invariant`
being universally maintained as a true invariant, and the `Hcdaz` assumption in the
COMPOSE/MORPH_TENSOR proofs can be discharged by the step invariance lemma instead of
assumed as a precondition.

### Option B — Restrict the proven execution model (partial closure)

Formally restrict the machine's use contract to programs that never have non-empty
coupling in any morphism that will be composed further. Prove this program property
implies `extended_hw_invariant` holds at every COMPOSE/MORPH_TENSOR call site.

This is a weaker but sound result: "the hardware is correct for programs in class X."

### Option C — Document as known architectural limitation

Accept that version 1 of the Thiele CPU does not implement relational coupling
propagation in COMPOSE and MORPH_TENSOR. Document `extended_hw_invariant` as the
precise contract boundary. Mark the architectural extension as future work.

### Immediate housekeeping (no RTL change needed)

1. **Update `RTLGapRegistry.v`** — replace the stale 7-gap header with the current
   state: TENSOR_SET/GET/CALL/RET/CHSH_TRIAL are fully proven; COMPOSE and MORPH_TENSOR
   are proven under `extended_hw_invariant`; the architectural limitation is documented.

2. **Update the thesis** — the current text says "all 46 in silicon, 39/46
   bisimulation proofs" which is now inaccurate. The correct statement is: all 46
   have Qed bisimulation proofs, of which 44 have clean preconditions and 2
   (COMPOSE, MORPH_TENSOR) are proven under `extended_hw_invariant` with the
   architectural limitation that coupling propagation is not implemented in RTL.

---

## 5. Summary Table

| Group | Count | Proof State | Precondition |
|---|---|---|---|
| Unconditional (`SupportedOpcode`) | 31 | Qed, no conditions | None |
| Simple runtime precondition | 11 | Qed | Runtime-checkable |
| Tensor index bounds | 2 | Qed | `tensor_indices_ok i j` |
| `extended_hw_invariant` | 2 | Qed, with architectural gap | All morphisms have empty coupling |
| **Total** | **46** | **0 Admitted** | |

The architectural gap in COMPOSE and MORPH_TENSOR is the only remaining divergence
between the hardware and the Coq spec. It is not an `Admitted` theorem gap — both
theorems are `Qed`. It is a real semantic gap that is excluded by the precondition
`coupling_desc_all_zero`, which the hardware maintains trivially by never writing
non-zero coupling descriptors, but which the kernel spec can violate if programs
build morphisms with coupling data and then compose them.
