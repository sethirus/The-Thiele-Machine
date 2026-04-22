# Proof Gap Analysis — Thiele Machine Hardware Bisimulation
*Produced by deep audit of `coq/kami_hw/` as of 2026-04-15. Gap closed 2026-04-21.*

---

## Status: CLOSED

The two architectural gaps described in this document (COMPOSE and MORPH_TENSOR
coupling propagation) were closed on 2026-04-21 via the `coupling_wf` migration.

**What was done:**

1. `extended_hw_invariant` previously included `coupling_desc_all_zero` — requiring
   all morphisms to have empty coupling. This invariant was NOT preserved by COMPOSE
   or MORPH_TENSOR success paths, making the proof conditional on empty-only coupling.

2. `coupling_desc_all_zero` was replaced by `coupling_wf`:
   ```coq
   coupling_wf = coupling_desc_bounded /\ coupling_pairs_in_range /\ coupling_pairs_fully_populated
   ```
   This invariant IS preserved by all 46 `kami_step` operations including COMPOSE
   and MORPH_TENSOR success paths (proved in `coupling_wf_kami_step_preserved`).

3. `Abstraction.v` `instr_compose` was updated to use `normalize_coupling` on the
   composed pairs before calling `rich_state_add_morph_with_coupling`, aligning the
   hardware's stored coupling data with what `graph_add_morphism` (kernel) stores.

4. `driven_step_compose` was proved to full VMState equality under the new invariant.

**Current state:** All 46 opcodes have `Qed` proofs under `extended_hw_invariant`
(now using `coupling_wf`). The invariant is proved to be preserved by all 46 opcodes,
meaning it holds for all states reachable from a valid initial state. There are no
remaining semantic gaps between hardware and kernel.

---

## Historical Analysis (preserved for reference)

The sections below describe the gap as it existed before 2026-04-21.

---

## Executive Summary (historical)

**Zero `Admitted.` statements exist anywhere in `coq/`.** All 46 opcode bridges are
`Qed`. The repository comment in `RTLGapRegistry.v` that says "7 opcodes without any
hardware-level proofs" is **stale** — it predates the final round of proofs in
`GraphReconstructionBridge.v` (last updated 2026-04-15) and has not been updated.

However, **two real architectural gaps remained** that were not proof gaps in the Coq
sense but were genuine divergences between the hardware and the full kernel spec under
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

---

## 2. Full Proof Coverage Breakdown (46 opcodes)

### Group A — Unconditional (31 opcodes)

All opcodes satisfying `SupportedOpcode` are covered by `driven_step_supported` in
`EmbedStep.v`. These 31 opcodes have no preconditions beyond well-typed state.

### Group B — Conditional with simple runtime precondition (11 opcodes)

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
Precondition: `tensor_indices_ok i j = true`.

### Group D — COMPOSE and MORPH_TENSOR (2 opcodes) — gap now closed

Previously proved only under `coupling_desc_all_zero`. Now proved under `coupling_wf`
which is an inductive invariant preserved by all 46 operations.

---

## 3. The Architectural Gap (historical — now closed)

The gap was: `coupling_desc_all_zero` required all morphisms to have empty coupling.
COMPOSE and MORPH_TENSOR success paths created morphisms with non-empty coupling,
breaking the invariant. The proofs were valid only when all inputs had empty coupling.

**Resolution:** Replaced `coupling_desc_all_zero` with `coupling_wf`. Added
`normalize_coupling` to `Abstraction.v` `instr_compose`. Proved
`coupling_wf_kami_step_preserved` covering all 46 operations. The gap is closed.

---

## 4. Summary Table (current)

| Group | Count | Proof State | Precondition |
|---|---|---|---|
| Unconditional (`SupportedOpcode`) | 31 | Qed, no conditions | None |
| Simple runtime precondition | 11 | Qed | Runtime-checkable |
| Tensor index bounds | 2 | Qed | `tensor_indices_ok i j` |
| `extended_hw_invariant` (coupling_wf) | 2 | Qed, invariant preserved | `coupling_wf` — holds in all reachable states |
| **Total** | **46** | **0 Admitted, 0 gaps** | |
