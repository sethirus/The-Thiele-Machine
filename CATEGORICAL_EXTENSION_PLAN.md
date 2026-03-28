# Categorical Extension Plan for the Thiele Machine (v2 — Complete)

## Implementation Status (as of 2026-03-24)

| Phase | Description | Status |
|-------|-------------|--------|
| Phase 0 | Standalone relational_compose proofs | ✅ Complete |
| Phase 1 | Data structures (VMState.v, graph ops, cascade delete) | ✅ Complete |
| Phase 2 | 7 new instructions, vm_step, vm_apply, all match cases | ✅ Complete |
| Phase 3 | Conservation proofs, LocalInfoLoss, KernelNoether orbit equiv | ✅ Complete |
| Phase 4 | Category laws (CategoryLaws.v, CategoryBridge.v, CategoryMonoidal.v) | ✅ Complete |
| Phase 5 | OCaml extraction (extracted_vm_runner.ml); Python fallback thiele_vm.py; forge.py + cosim.py opcode tables | ✅ Complete |
| Phase 6 | Kami/Bluespec hardware (ThieleTypes.v, ThieleCPUCore.v, Abstraction.v, VerilogRefinement.v) | ✅ Complete |
| Phase 7 | ThieleMachineComplete inline ✅; MasterSummary categorical imports ✅; Python tests ✅; RTL test gate ✅ | ✅ Complete |

**Coq kernel state**: zero Admitted, zero `make` errors.
All 47 `vm_instruction` constructors fully handled across every exhaustive match and proof.

**All work complete** — confirmed across two CI runs.

**2026-03-24 baseline**: **593 passed, 1 skipped, 0 failed** (Phases 0–7 done).

**2026-03-24 post-completion** (items 44 + 47 closed): **602 passed, 1 skipped, 0 failed** (+9 net; RTL cosim tests gated on iverilog availability).
- `tests/test_rtl_morph_opcodes.py`: +20 RTL cosim tests for MORPH opcodes (all pass)
- `coq/kernel/PartitionSeparation.v`: categorical separation proof (Section 10)
- `coq/kami_hw/VerilogRefinement.v`: ListNotations fix for standalone coqc compilation
- `thielecpu/hardware/rtl/thiele_cpu_kami.v`: regenerated with MORPH opcodes 0x27–0x2D
- `tests/test_verilog_cosim.py`: renamed stale `test_all_38_opcodes_in_cosim` → `test_all_47_opcodes_in_cosim`

Fixes applied (confirmed, not asserted):
1. `build/thiele_vm.py`: added 7 MORPH opcodes to `_parse_instruction_dict` ✅
2. `coq/kernel/MasterSummary.v`: added CategoryLaws/CategoryBridge/CategoryMonoidal imports + 6 export aliases ✅
3. `tests/test_completeness_gate.py`: updated RTL opcode test — MORPH now asserted present ✅
4. `tests/test_categorical_opcodes.py`: 28 integration tests written, all passing ✅
5. `scripts/forge.py`: added MORPH opcodes 0x27–0x2D to OPCODES dict ✅
6. `rtl_harness/cosim.py`: added 7 MORPH opcodes, re-exported through `thielecpu/hardware/cosim.py` ✅
7. `thielecpu/generated/generated_core.py`: regenerated with 47 opcodes (forge.py output) ✅
8. `tests/test_verilog_cosim.py`: updated hardcoded opcode count 40→47, expanded expected_names ✅
9. `artifacts/final_claim_audit/`: MasterSummary artifact checksums refreshed via generate script ✅

---

## Executive Summary

This document specifies the **complete** set of changes needed to add native categorical
computation to the Thiele Machine — objects, morphisms, identity, composition, tensor
products, assertions, inspection, deletion, and cascade semantics — from Coq kernel
through hardware.

**7 new opcodes** (not 3): MORPH, COMPOSE, MORPH_ID, MORPH_DELETE, MORPH_ASSERT,
MORPH_TENSOR, MORPH_GET.

**Estimated total work**: ~4,000 lines of Coq, ~200 lines OCaml, ~150 lines Python,
~200 lines Kami.

---

## Part 1: Design Decisions (Gap Resolutions)

### Gap 1: Where does the morphism ID go?

**Decision**: New morphism-creating instructions write the result ID to a **destination
register** (first parameter). This matches TENSOR_GET and provides explicit control.

```
MORPH dst src_mod dst_mod coupling cost   → regs[dst] := new_morphism_id
COMPOSE dst m1 m2 cost                     → regs[dst] := composed_morphism_id
MORPH_ID dst module cost                   → regs[dst] := identity_morphism_id
MORPH_TENSOR dst f g cost                  → regs[dst] := tensor_morphism_id
```

### Gap 2: PSPLIT/PMERGE and dangling morphisms

**Decision**: **Cascade delete**. When a module is destroyed (by PSPLIT or PMERGE), all
morphisms referencing it as source or target are automatically removed from `pg_morphisms`.

Rationale:
- Explicit cleanup (user must MORPH_DELETE first) is too burdensome
- Redirecting morphisms to new modules is complex and may not preserve well-formedness
- Cascade delete is consistent: when an object dies, its arrows die
- Programs can rebuild necessary morphisms to the new modules

Implementation:
```coq
Definition graph_cascade_delete_morphisms (g : PartitionGraph) (mid : ModuleID) : PartitionGraph :=
  {| pg_next_id := g.(pg_next_id);
     pg_modules := g.(pg_modules);
     pg_next_morph_id := g.(pg_next_morph_id);
     pg_morphisms := filter (fun '(_, ms) =>
       negb (Nat.eqb ms.(morph_source) mid) &&
       negb (Nat.eqb ms.(morph_target) mid)) g.(pg_morphisms) |}.
```

Updated `graph_pmerge` and `graph_psplit` call `graph_cascade_delete_morphisms` on
removed modules before creating new ones.

### Gap 3: Coupling well-formedness

**Decision**: Enforce at vm_step time. Invalid couplings cause error.

```coq
Definition coupling_wf (g : PartitionGraph) (src dst : ModuleID) (c : CouplingData) : Prop :=
  match graph_lookup g src, graph_lookup g dst with
  | Some src_mod, Some dst_mod =>
      (* All pairs reference valid cells in source and target regions *)
      forall a b, In (a, b) c.(coupling_pairs) ->
        In a src_mod.(module_region) /\ In b dst_mod.(module_region)
  | _, _ => False
  end.

Definition coupling_wf_dec (g : PartitionGraph) (src dst : ModuleID) (c : CouplingData) : bool :=
  (* Computable version for vm_apply *)
  ...
```

MORPH succeeds only if `coupling_wf_dec` returns true. Otherwise: `vm_err := true`,
`csr_err := ERR_COUPLING_INVALID`.

### Gap 4: Morphism deletion

**Decision**: Add `MORPH_DELETE` instruction.

```
MORPH_DELETE morph_id cost
```

Removes the morphism from `pg_morphisms`. Fails (with error) if `morph_id` doesn't exist.
This allows explicit cleanup and bounded morphism storage.

### Gap 5: Assertions over morphisms

**Decision**: Add `MORPH_ASSERT` instruction (cert-setter).

```
MORPH_ASSERT morph_id property cert cost
```

- `property`: string encoding the assertion (e.g., "isomorphism", "injection", "commutes:0:1")
- `cert`: certificate (SAT/UNSAT proof)
- On success: Updates `csr_cert_addr` with checksum, records assertion
- On failure: `vm_err := true`

This is a **cert-setter** (cost >= 1 via `S cost`). It creates certified knowledge about
morphism structure, which requires paying mu under NoFI.

### Gap 6: Monoidal structure (tensor on morphisms)

**Decision**: Add `MORPH_TENSOR` instruction.

```
MORPH_TENSOR dst f_id g_id cost
```

Given:
- f : A → B (morphism f_id)
- g : C → D (morphism g_id)

Produces:
- f ⊗ g : A∪C → B∪D

Requirements (checked at runtime):
1. Regions of A and C are disjoint
2. Regions of B and D are disjoint
3. Module with region A∪C exists (find via `graph_find_region`)
4. Module with region B∪D exists (find via `graph_find_region`)

Coupling of f⊗g = disjoint union of f's coupling and g's coupling.

On any failure: `vm_err := true`, `csr_err := ERR_TENSOR_INVALID`.

This requires the user to PMERGE source and target modules first, then MORPH_TENSOR.
This is explicit and avoids having morphism instructions implicitly create modules.

### Gap 7: Morphism inspection

**Decision**: Add `MORPH_GET` instruction.

```
MORPH_GET dst morph_id selector cost
```

Selectors:
- 0: `morph_source` → dst
- 1: `morph_target` → dst
- 2: `length(coupling_pairs)` → dst
- 3: `morph_is_identity` (0 or 1) → dst

For full coupling inspection, use MORPH_ASSERT to check properties, or add a separate
MORPH_GET_COUPLING instruction later (with index parameter for specific pairs).

### Gap 8: Interaction with module_mu_tensor

**Decision**: Morphism operations do NOT directly modify per-module tensors.

The per-module `module_mu_tensor` (4x4 metric) is written via TENSOR_SET and read via
TENSOR_GET. Morphisms are a separate layer (arrows) on top of objects (modules). The
connection is:
- `morphism_distance` (path length through arrows) is related to but distinct from
  `edge_length` (derived from structural mass)
- A future MORPH_METRIC instruction could compute coupling-weighted distances

---

## Part 2: Complete Instruction Set (7 new opcodes)

| Mnemonic | Opcode | Parameters | Semantics | Result |
|----------|--------|------------|-----------|--------|
| `MORPH` | 0x27 | dst, src_mod, dst_mod, coupling, cost | Create morphism | ID → regs[dst] |
| `COMPOSE` | 0x28 | dst, m1, m2, cost | Compose morphisms (type-checked) | ID → regs[dst] |
| `MORPH_ID` | 0x29 | dst, module, cost | Create identity morphism | ID → regs[dst] |
| `MORPH_DELETE` | 0x2A | morph_id, cost | Delete morphism | — |
| `MORPH_ASSERT` | 0x2B | morph_id, property, cert, cost | Assert property (cert-setter) | checksum → csr_cert_addr |
| `MORPH_TENSOR` | 0x2C | dst, f, g, cost | Parallel composition | ID → regs[dst] |
| `MORPH_GET` | 0x2D | dst, morph_id, selector, cost | Read morphism field | value → regs[dst] |

### Cost Classification

| Instruction | Reversible? | Creates Info? | `instruction_cost` | `is_cert_setterb` |
|-------------|-------------|---------------|--------------------|--------------------|
| MORPH | Yes | No | `cost` | false |
| COMPOSE | Yes | No | `cost` | false |
| MORPH_ID | Yes | No | `cost` | false |
| MORPH_DELETE | Yes | No | `cost` | false |
| MORPH_ASSERT | No | **Yes** | `S cost` (≥1) | **true** |
| MORPH_TENSOR | Yes | No | `cost` | false |
| MORPH_GET | Yes (read-only) | No | `cost` | false |

Only MORPH_ASSERT is a cert-setter because it creates certified knowledge about structure.
All other operations are reversible structure manipulation (like PNEW/PSPLIT/PMERGE).

---

## Part 3: Data Structures

### New Types (VMState.v)

```coq
Definition MorphismID := nat.

(* Well-formed coupling requires all pairs to reference valid region cells *)
Record CouplingData := {
  coupling_pairs : list (nat * nat);
  coupling_label : string
}.

Record MorphismState := {
  morph_source : ModuleID;
  morph_target : ModuleID;
  morph_coupling : CouplingData;
  morph_is_identity : bool
}.

(* Extended PartitionGraph *)
Record PartitionGraph := {
  pg_next_id       : ModuleID;
  pg_modules       : list (ModuleID * ModuleState);
  pg_next_morph_id : MorphismID;                      (* NEW *)
  pg_morphisms     : list (MorphismID * MorphismState) (* NEW *)
}.
```

### New Graph Operations (VMState.v)

```coq
(* Lookup *)
Definition graph_lookup_morphism (g : PartitionGraph) (mid : MorphismID)
  : option MorphismState := assoc_lookup mid g.(pg_morphisms).

(* Add morphism (returns new graph and assigned ID) *)
Definition graph_add_morphism (g : PartitionGraph) (src dst : ModuleID)
    (c : CouplingData) (is_id : bool) : PartitionGraph * MorphismID :=
  let new_id := g.(pg_next_morph_id) in
  let ms := {| morph_source := src; morph_target := dst;
               morph_coupling := c; morph_is_identity := is_id |} in
  ({| pg_next_id := g.(pg_next_id);
      pg_modules := g.(pg_modules);
      pg_next_morph_id := S new_id;
      pg_morphisms := (new_id, ms) :: g.(pg_morphisms) |}, new_id).

(* Add identity morphism *)
Definition graph_add_identity (g : PartitionGraph) (mid : ModuleID)
  : option (PartitionGraph * MorphismID) :=
  match graph_lookup g mid with
  | None => None
  | Some ms =>
      let diag := map (fun x => (x, x)) ms.(module_region) in
      let c := {| coupling_pairs := diag; coupling_label := "id" |} in
      Some (graph_add_morphism g mid mid c true)
  end.

(* Delete morphism *)
Definition graph_delete_morphism (g : PartitionGraph) (morph_id : MorphismID)
  : option PartitionGraph :=
  if existsb (fun '(id, _) => Nat.eqb id morph_id) g.(pg_morphisms)
  then Some {| pg_next_id := g.(pg_next_id);
               pg_modules := g.(pg_modules);
               pg_next_morph_id := g.(pg_next_morph_id);
               pg_morphisms := filter (fun '(id, _) => negb (Nat.eqb id morph_id))
                                      g.(pg_morphisms) |}
  else None.

(* Compose morphisms (type-checked) *)
Definition graph_compose_morphisms (g : PartitionGraph) (m1 m2 : MorphismID)
  : option (PartitionGraph * MorphismID) :=
  match graph_lookup_morphism g m1, graph_lookup_morphism g m2 with
  | Some f, Some h =>
      if Nat.eqb f.(morph_target) h.(morph_source)
      then
        let composed_pairs := relational_compose
          f.(morph_coupling).(coupling_pairs)
          h.(morph_coupling).(coupling_pairs) in
        let c := {| coupling_pairs := composed_pairs;
                    coupling_label := f.(morph_coupling).(coupling_label) ++ ";" ++
                                      h.(morph_coupling).(coupling_label) |} in
        Some (graph_add_morphism g f.(morph_source) h.(morph_target) c false)
      else None (* Type mismatch: f.target ≠ h.source *)
  | _, _ => None (* Morphism not found *)
  end.

(* Tensor morphisms (monoidal) *)
Definition graph_tensor_morphisms (g : PartitionGraph) (f_id g_id : MorphismID)
  : option (PartitionGraph * MorphismID) :=
  match graph_lookup_morphism g f_id, graph_lookup_morphism g g_id with
  | Some f, Some h =>
      match graph_lookup g f.(morph_source), graph_lookup g f.(morph_target),
            graph_lookup g h.(morph_source), graph_lookup g h.(morph_target) with
      | Some a_mod, Some b_mod, Some c_mod, Some d_mod =>
          (* Check disjointness *)
          if nat_list_disjoint a_mod.(module_region) c_mod.(module_region) &&
             nat_list_disjoint b_mod.(module_region) d_mod.(module_region)
          then
            let ac_region := nat_list_union a_mod.(module_region) c_mod.(module_region) in
            let bd_region := nat_list_union b_mod.(module_region) d_mod.(module_region) in
            match graph_find_region g ac_region, graph_find_region g bd_region with
            | Some ac_id, Some bd_id =>
                let tensor_pairs := f.(morph_coupling).(coupling_pairs) ++
                                    h.(morph_coupling).(coupling_pairs) in
                let c := {| coupling_pairs := tensor_pairs;
                            coupling_label := f.(morph_coupling).(coupling_label) ++ "⊗" ++
                                              h.(morph_coupling).(coupling_label) |} in
                Some (graph_add_morphism g ac_id bd_id c false)
            | _, _ => None (* Union modules don't exist *)
            end
          else None (* Regions not disjoint *)
      | _, _, _, _ => None (* Modules not found *)
      end
  | _, _ => None (* Morphisms not found *)
  end.

(* Cascade delete: remove all morphisms referencing a module *)
Definition graph_cascade_delete_morphisms (g : PartitionGraph) (mid : ModuleID)
  : PartitionGraph :=
  {| pg_next_id := g.(pg_next_id);
     pg_modules := g.(pg_modules);
     pg_next_morph_id := g.(pg_next_morph_id);
     pg_morphisms := filter (fun '(_, ms) =>
       negb (Nat.eqb ms.(morph_source) mid) &&
       negb (Nat.eqb ms.(morph_target) mid)) g.(pg_morphisms) |}.

(* Relational composition of coupling pairs *)
Definition relational_compose (r1 r2 : list (nat * nat)) : list (nat * nat) :=
  flat_map (fun '(a, b) =>
    map (fun '(b', c) => (a, c)) (filter (fun '(b', _) => Nat.eqb b b') r2)
  ) r1.
```

### Updated Existing Operations

```coq
(* graph_pmerge now cascades deletes *)
Definition graph_pmerge (g : PartitionGraph) (m1 m2 : ModuleID)
  : option (PartitionGraph * ModuleID) :=
  (* ... existing logic to merge regions ... *)
  let g1 := graph_cascade_delete_morphisms g m1 in
  let g2 := graph_cascade_delete_morphisms g1 m2 in
  (* ... continue with merge on g2 ... *)

(* graph_psplit now cascades deletes *)
Definition graph_psplit (g : PartitionGraph) (mid : ModuleID) (left right : list nat)
  : option (PartitionGraph * ModuleID * ModuleID) :=
  (* ... existing validation ... *)
  let g1 := graph_cascade_delete_morphisms g mid in
  (* ... continue with split on g1 ... *)
```

### Extended well_formed_graph

```coq
Definition well_formed_graph (g : PartitionGraph) : Prop :=
  (* Existing: all module IDs < pg_next_id *)
  (forall mid ms, In (mid, ms) g.(pg_modules) -> mid < g.(pg_next_id)) /\
  (* NEW: all morphism IDs < pg_next_morph_id *)
  (forall morph_id ms, In (morph_id, ms) g.(pg_morphisms) ->
    morph_id < g.(pg_next_morph_id)) /\
  (* NEW: all morphism sources/targets exist *)
  (forall morph_id ms, In (morph_id, ms) g.(pg_morphisms) ->
    graph_lookup g ms.(morph_source) <> None /\
    graph_lookup g ms.(morph_target) <> None) /\
  (* NEW: all couplings are well-formed *)
  (forall morph_id ms, In (morph_id, ms) g.(pg_morphisms) ->
    coupling_wf g ms.(morph_source) ms.(morph_target) ms.(morph_coupling)).
```

---

## Part 4: Instruction Definitions (VMStep.v)

### New Constructors

```coq
Inductive vm_instruction :=
  (* ... existing 40 constructors ... *)
  (* Categorical instructions *)
  | instr_morph (dst : nat) (src dst_mod : ModuleID) (coupling : CouplingData) (mu_delta : nat)
  | instr_compose (dst : nat) (m1 m2 : MorphismID) (mu_delta : nat)
  | instr_morph_id (dst : nat) (module : ModuleID) (mu_delta : nat)
  | instr_morph_delete (morph_id : MorphismID) (mu_delta : nat)
  | instr_morph_assert (morph_id : MorphismID) (property : string)
                       (cert : lassert_certificate) (mu_delta : nat)
  | instr_morph_tensor (dst : nat) (f g : MorphismID) (mu_delta : nat)
  | instr_morph_get (dst : nat) (morph_id : MorphismID) (selector : nat) (mu_delta : nat).
```

### instruction_cost

```coq
Definition instruction_cost (instr : vm_instruction) : nat :=
  match instr with
  (* ... existing arms ... *)
  | instr_morph _ _ _ _ cost => cost
  | instr_compose _ _ _ cost => cost
  | instr_morph_id _ _ cost => cost
  | instr_morph_delete _ cost => cost
  | instr_morph_assert _ prop _ cost => String.length prop + S cost  (* cert-setter *)
  | instr_morph_tensor _ _ _ cost => cost
  | instr_morph_get _ _ _ cost => cost
  end.
```

### is_cert_setterb

```coq
Definition is_cert_setterb (instr : vm_instruction) : bool :=
  match instr with
  (* ... existing arms ... *)
  | instr_morph _ _ _ _ _ => false
  | instr_compose _ _ _ _ => false
  | instr_morph_id _ _ _ => false
  | instr_morph_delete _ _ => false
  | instr_morph_assert _ _ _ _ => true   (* CERT-SETTER *)
  | instr_morph_tensor _ _ _ _ => false
  | instr_morph_get _ _ _ _ => false
  end.
```

### vm_step Constructors

```coq
(* MORPH: Create morphism *)
| step_morph : forall s dst src dst_mod coupling cost graph' morph_id regs',
    coupling_wf_dec s.(vm_graph) src dst_mod coupling = true ->
    (graph', morph_id) = graph_add_morphism s.(vm_graph) src dst_mod coupling false ->
    regs' = write_reg s.(vm_regs) dst morph_id ->
    vm_step s (instr_morph dst src dst_mod coupling cost)
      (advance_state_rm s (instr_morph dst src dst_mod coupling cost)
                        graph' s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))

| step_morph_failure : forall s dst src dst_mod coupling cost,
    (graph_lookup s.(vm_graph) src = None \/
     graph_lookup s.(vm_graph) dst_mod = None \/
     coupling_wf_dec s.(vm_graph) src dst_mod coupling = false) ->
    vm_step s (instr_morph dst src dst_mod coupling cost)
      (advance_state s (instr_morph dst src dst_mod coupling cost)
                     s.(vm_graph) (csr_set_err s.(vm_csrs) ERR_COUPLING_INVALID) true)

(* COMPOSE: Type-checked composition *)
| step_compose : forall s dst m1 m2 cost graph' result_id regs',
    graph_compose_morphisms s.(vm_graph) m1 m2 = Some (graph', result_id) ->
    regs' = write_reg s.(vm_regs) dst result_id ->
    vm_step s (instr_compose dst m1 m2 cost)
      (advance_state_rm s (instr_compose dst m1 m2 cost)
                        graph' s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))

| step_compose_failure : forall s dst m1 m2 cost,
    graph_compose_morphisms s.(vm_graph) m1 m2 = None ->
    vm_step s (instr_compose dst m1 m2 cost)
      (advance_state s (instr_compose dst m1 m2 cost)
                     s.(vm_graph) (csr_set_err s.(vm_csrs) ERR_COMPOSE_TYPE) true)

(* MORPH_ID: Identity morphism *)
| step_morph_id : forall s dst mid cost graph' morph_id regs',
    graph_add_identity s.(vm_graph) mid = Some (graph', morph_id) ->
    regs' = write_reg s.(vm_regs) dst morph_id ->
    vm_step s (instr_morph_id dst mid cost)
      (advance_state_rm s (instr_morph_id dst mid cost)
                        graph' s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))

| step_morph_id_failure : forall s dst mid cost,
    graph_add_identity s.(vm_graph) mid = None ->
    vm_step s (instr_morph_id dst mid cost)
      (advance_state s (instr_morph_id dst mid cost)
                     s.(vm_graph) (csr_set_err s.(vm_csrs) 1) true)

(* MORPH_DELETE: Delete morphism *)
| step_morph_delete : forall s morph_id cost graph',
    graph_delete_morphism s.(vm_graph) morph_id = Some graph' ->
    vm_step s (instr_morph_delete morph_id cost)
      (advance_state s (instr_morph_delete morph_id cost)
                     graph' s.(vm_csrs) s.(vm_err))

| step_morph_delete_failure : forall s morph_id cost,
    graph_delete_morphism s.(vm_graph) morph_id = None ->
    vm_step s (instr_morph_delete morph_id cost)
      (advance_state s (instr_morph_delete morph_id cost)
                     s.(vm_graph) (csr_set_err s.(vm_csrs) 1) true)

(* MORPH_ASSERT: Assert property (cert-setter) *)
| step_morph_assert_sat : forall s morph_id property model cost csrs',
    graph_lookup_morphism s.(vm_graph) morph_id <> None ->
    check_morphism_property s.(vm_graph) morph_id property model = true ->
    csrs' = csr_set_cert_addr s.(vm_csrs) (checksum_of property) ->
    vm_step s (instr_morph_assert morph_id property (lassert_cert_sat model) cost)
      (advance_state s (instr_morph_assert morph_id property (lassert_cert_sat model) cost)
                     s.(vm_graph) csrs' s.(vm_err))

| step_morph_assert_failure : forall s morph_id property cert cost,
    (graph_lookup_morphism s.(vm_graph) morph_id = None \/
     check_morphism_property_cert s.(vm_graph) morph_id property cert = false) ->
    vm_step s (instr_morph_assert morph_id property cert cost)
      (advance_state s (instr_morph_assert morph_id property cert cost)
                     s.(vm_graph) (csr_set_err s.(vm_csrs) 1) true)

(* MORPH_TENSOR: Parallel composition *)
| step_morph_tensor : forall s dst f g cost graph' result_id regs',
    graph_tensor_morphisms s.(vm_graph) f g = Some (graph', result_id) ->
    regs' = write_reg s.(vm_regs) dst result_id ->
    vm_step s (instr_morph_tensor dst f g cost)
      (advance_state_rm s (instr_morph_tensor dst f g cost)
                        graph' s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))

| step_morph_tensor_failure : forall s dst f g cost,
    graph_tensor_morphisms s.(vm_graph) f g = None ->
    vm_step s (instr_morph_tensor dst f g cost)
      (advance_state s (instr_morph_tensor dst f g cost)
                     s.(vm_graph) (csr_set_err s.(vm_csrs) ERR_TENSOR_INVALID) true)

(* MORPH_GET: Read morphism field *)
| step_morph_get : forall s dst morph_id selector cost ms value regs',
    graph_lookup_morphism s.(vm_graph) morph_id = Some ms ->
    value = morph_get_field ms selector ->
    regs' = write_reg s.(vm_regs) dst value ->
    vm_step s (instr_morph_get dst morph_id selector cost)
      (advance_state_rm s (instr_morph_get dst morph_id selector cost)
                        s.(vm_graph) s.(vm_csrs) regs' s.(vm_mem) s.(vm_err))

| step_morph_get_failure : forall s dst morph_id selector cost,
    graph_lookup_morphism s.(vm_graph) morph_id = None ->
    vm_step s (instr_morph_get dst morph_id selector cost)
      (advance_state s (instr_morph_get dst morph_id selector cost)
                     s.(vm_graph) (csr_set_err s.(vm_csrs) 1) true)
```

### Helper: morph_get_field

```coq
Definition morph_get_field (ms : MorphismState) (selector : nat) : nat :=
  match selector with
  | 0 => ms.(morph_source)
  | 1 => ms.(morph_target)
  | 2 => length ms.(morph_coupling).(coupling_pairs)
  | 3 => if ms.(morph_is_identity) then 1 else 0
  | _ => 0
  end.
```

---

## Part 5: Category Law Proofs (CategoryLaws.v)

### Foundational Lemmas

```coq
(* Relational composition is associative *)
Theorem relational_compose_assoc :
  forall r1 r2 r3,
    relational_compose (relational_compose r1 r2) r3 =
    relational_compose r1 (relational_compose r2 r3).
Proof.
  (* Induction on r1, then r2, membership reasoning *)
Admitted. (* TODO: straightforward, ~50 lines *)

(* Diagonal is left identity *)
Theorem relational_compose_diagonal_left :
  forall region r,
    (forall a b, In (a, b) r -> In a region) ->
    relational_compose (diagonal region) r = r.
Proof.
  (* diagonal region = [(x,x) | x ∈ region] *)
Admitted. (* TODO: ~30 lines *)

(* Diagonal is right identity *)
Theorem relational_compose_diagonal_right :
  forall region r,
    (forall a b, In (a, b) r -> In b region) ->
    relational_compose r (diagonal region) = r.
Proof.
Admitted. (* TODO: ~30 lines *)
```

### Category Structure

```coq
(* Composition is associative at the graph level *)
Theorem graph_compose_assoc :
  forall g f_id g_id h_id g1 fg_id g2 fgh_id1 g3 gh_id g4 fgh_id2,
    graph_compose_morphisms g f_id g_id = Some (g1, fg_id) ->
    graph_compose_morphisms g1 fg_id h_id = Some (g2, fgh_id1) ->
    graph_compose_morphisms g g_id h_id = Some (g3, gh_id) ->
    graph_compose_morphisms g3 f_id gh_id = Some (g4, fgh_id2) ->
    morph_coupling (graph_lookup_morphism g2 fgh_id1) =
    morph_coupling (graph_lookup_morphism g4 fgh_id2).
Proof.
  (* Reduces to relational_compose_assoc *)
Admitted.

(* Left identity law *)
Theorem graph_compose_id_left :
  forall g mid f_id g1 id_id f_state g2 composed_id,
    graph_add_identity g mid = Some (g1, id_id) ->
    graph_lookup_morphism g1 f_id = Some f_state ->
    f_state.(morph_source) = mid ->
    graph_compose_morphisms g1 id_id f_id = Some (g2, composed_id) ->
    morph_coupling (graph_lookup_morphism g2 composed_id) =
    morph_coupling (graph_lookup_morphism g1 f_id).
Proof.
  (* Reduces to relational_compose_diagonal_left *)
Admitted.

(* Right identity law *)
Theorem graph_compose_id_right :
  forall g mid f_id g1 id_id f_state g2 composed_id,
    graph_add_identity g mid = Some (g1, id_id) ->
    graph_lookup_morphism g1 f_id = Some f_state ->
    f_state.(morph_target) = mid ->
    graph_compose_morphisms g1 f_id id_id = Some (g2, composed_id) ->
    morph_coupling (graph_lookup_morphism g2 composed_id) =
    morph_coupling (graph_lookup_morphism g1 f_id).
Proof.
  (* Reduces to relational_compose_diagonal_right *)
Admitted.
```

### Monoidal Structure

```coq
(* Tensor is bifunctorial: (f⊗g);(f'⊗g') = (f;f')⊗(g;g') when types match *)
Theorem graph_tensor_bifunctor :
  forall g f_id f'_id g_id g'_id
         g1 fg_id g2 f'g'_id g3 seq_id
         g4 ff'_id g5 gg'_id g6 tensor_id,
    (* f⊗g, then f'⊗g' *)
    graph_tensor_morphisms g f_id g_id = Some (g1, fg_id) ->
    graph_tensor_morphisms g1 f'_id g'_id = Some (g2, f'g'_id) ->
    graph_compose_morphisms g2 fg_id f'g'_id = Some (g3, seq_id) ->
    (* f;f', then g;g', then tensor *)
    graph_compose_morphisms g f_id f'_id = Some (g4, ff'_id) ->
    graph_compose_morphisms g4 g_id g'_id = Some (g5, gg'_id) ->
    graph_tensor_morphisms g5 ff'_id gg'_id = Some (g6, tensor_id) ->
    (* Couplings are equal *)
    morph_coupling (graph_lookup_morphism g3 seq_id) =
    morph_coupling (graph_lookup_morphism g6 tensor_id).
Proof.
  (* Interchange law for monoidal categories *)
Admitted.
```

---

## Part 6: Error Codes (ThieleTypes.v)

```coq
Definition ERR_COUPLING_INVALID : word WordSz := ... (* 0x0BADC0DE or new *)
Definition ERR_COMPOSE_TYPE    : word WordSz := ... (* Type mismatch *)
Definition ERR_TENSOR_INVALID  : word WordSz := ... (* Tensor precondition failed *)
Definition ERR_MORPH_NOT_FOUND : word WordSz := ... (* Morphism ID not found *)
```

---

## Part 7: Cascading Behavior Summary

| Operation | Effect on Morphisms |
|-----------|---------------------|
| PNEW | None (new module has no morphisms yet) |
| PSPLIT mid | **Cascade delete**: all morphisms with source=mid or target=mid removed |
| PMERGE m1 m2 | **Cascade delete**: all morphisms with source∈{m1,m2} or target∈{m1,m2} removed |
| PDISCOVER | None (only adds axioms to module) |
| MORPH | Adds new morphism |
| COMPOSE | Adds new morphism (composed) |
| MORPH_ID | Adds new morphism (identity) |
| MORPH_DELETE | Removes specified morphism |
| MORPH_TENSOR | Adds new morphism (tensor product) |

### Cascade Delete Theorem

```coq
Theorem cascade_preserves_wf :
  forall g mid,
    well_formed_graph g ->
    well_formed_graph (graph_cascade_delete_morphisms g mid).
Proof.
  (* All remaining morphisms still have valid source/target
     since we only removed those referencing mid *)
Admitted.

Theorem psplit_preserves_wf :
  forall g mid left right g' left_id right_id,
    well_formed_graph g ->
    graph_psplit g mid left right = Some (g', left_id, right_id) ->
    well_formed_graph g'.
Proof.
  (* Uses cascade_preserves_wf plus existing psplit proofs *)
Admitted.

Theorem pmerge_preserves_wf :
  forall g m1 m2 g' merged_id,
    well_formed_graph g ->
    graph_pmerge g m1 m2 = Some (g', merged_id) ->
    well_formed_graph g'.
Proof.
  (* Uses cascade_preserves_wf twice plus existing pmerge proofs *)
Admitted.
```

---

## Part 8: Full Layer-by-Layer Changes

### Coq Kernel (~2,500 lines)

| File | Changes | Lines |
|------|---------|-------|
| VMState.v | New types, extended PartitionGraph, 8 new graph ops, cascade delete | ~500 |
| VMStep.v | 7 new instructions, 14 step constructors, cost/cert arms | ~250 |
| SimulationProof.v | 7 new vm_apply arms | ~70 |
| MuLedgerConservation.v | 7 new proof cases | ~20 |
| MuCostModel.v | 7 new mu_cost_of_instr arms | ~15 |
| KernelPhysics.v | 7 new instr_targets arms | ~20 |
| Locality.v | 7 new instr_targets + cascade preservation | ~100 |
| PhysicsClosure.v | 7 new vm_step induction cases | ~50 |
| RevelationRequirement.v | 6 non-cert + 1 cert-setter proofs | ~20 |
| CategoryLaws.v | **NEW** — relational composition, category laws | ~500 |
| CategoryMonoidal.v | **NEW** — tensor bifunctor, coherence | ~300 |
| CategoryBridge.v | **NEW** — bridge to ThieleProc, KernelNoether | ~250 |
| PartitionSeparation.v | Extended separation proof | ~50 |
| Various | Downstream fixes for PartitionGraph record change | ~150 |
| ThieleMachineComplete.v | Parallel update | ~700 |

### OCaml Extraction (~200 lines)

| File | Changes |
|------|---------|
| extracted_vm_runner.ml | 7 new parse clauses, morphism serialization/deserialization |

### Python Codegen (~150 lines)

| File | Changes |
|------|---------|
| forge.py | 7 new OPCODES entries |
| forge_vm.py | 7 new CONSTRUCTOR_FIELD_MAP entries, new dataclasses |

### Kami Hardware (~200 lines)

| File | Changes |
|------|---------|
| ThieleTypes.v | 7 new OP_* constants, 4 new ERR_* codes |
| ThieleCPUCore.v | 7 new opcode dispatch cases |
| Abstraction.v | snap_morph_ops counter, 7 new kami_step arms |
| VerilogRefinement.v | 7 new simulation proofs |

---

## Part 9: Implementation Phases

> **Last updated: 2026-03-24** — All phases 0–7 complete. 602 passed, 1 skipped, 0 failed (641 collected). Zero Admitted kernel-wide.
> **Status: COMPLETE** — No remaining work. All 47 opcodes verified across Coq / OCaml / Python / RTL / test layers.
> **Physics scope documented** — Two structural gaps in EinsteinEquations4D.v documented honestly; core theorems unaffected.

### Phase 0: Standalone Proofs (non-breaking) ✅ DONE
1. ✅ Create CategoryLaws.v with relational_compose (no kernel imports)
2. ✅ Prove associativity and diagonal-identity lemmas
3. ✅ Verify compiles independently

### Phase 1: Data Structures (~500 lines) ✅ DONE
4. ✅ Add MorphismID, CouplingData, MorphismState to VMState.v
5. ✅ Extend PartitionGraph with pg_next_morph_id, pg_morphisms
6. ✅ Add all 8 graph operations
7. ✅ Implement coupling_wf and coupling_wf_dec
8. ✅ Implement graph_cascade_delete_morphisms
9. ✅ Update graph_psplit and graph_pmerge to call cascade delete
10. ✅ Extend well_formed_graph
11. ✅ Prove preservation lemmas for all operations
    - graph_add_morphism_preserves_module_count
    - graph_delete_morphism_preserves_module_count
    - graph_add_identity_preserves_module_count
    - graph_compose_morphisms_preserves_module_count
    - graph_tensor_morphisms_preserves_module_count
12. ✅ Fix ALL downstream compilation failures

### Phase 2: Instructions (~250 lines) ✅ DONE
13. ✅ Add 7 constructors to vm_instruction (VMStep.v)
14. ✅ Add 7 arms to instruction_cost (MORPH_ASSERT uses S cost)
15. ✅ Add 7 arms to is_cert_setterb (MORPH_ASSERT = true)
16. ✅ Add 14 vm_step constructors (success + failure for each)
17. ✅ Add 7 arms to vm_apply in SimulationProof.v
18. ✅ Fix ALL exhaustive match failures:
    - ThreeLayerIsomorphism.v: instruction_exhaustive (+7 arms)
    - LocalInfoLoss.v: instr_mu_cost (+7 arms)
    - KernelNoether.v: vm_step_orbit_equiv (+14 eapply cases with change normalization)
    - ThieleMachineComplete.v: non_cert_setter_preserves_cert (removed invalid morph_assert ref)
19. ✅ Verify `make -C coq` compiles — zero errors, zero Admitted

### Phase 3: Conservation Proofs (~200 lines) ✅ DONE
20. ✅ Extend vm_apply_mu for 7 new instructions
21. ✅ Extend mu_cost_of_instr / instr_mu_cost for 7 new instructions
22. ✅ Extend instr_targets for 7 new instructions
23. ✅ Prove non-cert-setter preservation for 6 instructions
24. ✅ Prove MORPH_ASSERT cert-setter properties
25. ✅ Extend closure/module-count proofs for cascade delete
    - other_instr_module_count_unchanged (+7 morph cases)
    - cost_bounds_info_loss (+7 morph cases)
26. ✅ Verified zero Admitted across all kernel files

### Phase 4: Category Proofs (~800 lines) ✅ COMPLETE
27. ✅ Create CategoryLaws.v with standalone relational_compose proofs (no kernel imports)
    - relational_compose_assoc, relational_compose_diagonal_left/right, coupling_equiv
    - compatibility lemmas, empty laws, union spec
    - CONFIRMED: 376 lines, .vo compiled, zero Admitted
28. ✅ Create CategoryBridge.v — prove compose_assoc, compose_id_left, compose_id_right
    using actual kernel graph operations (graph_compose_morphisms, graph_add_identity)
    - CONFIRMED: 311 lines, .vo compiled, zero Admitted
29. ✅ Create CategoryMonoidal.v with tensor bifunctor proof (graph_tensor_morphisms is bifunctor)
    - CONFIRMED: 191 lines, .vo compiled, zero Admitted
30. ✅ LocalMorphismSemantics.v created (locality bridge for split subsystems, zero Admitted)
31. ✅ CategoryBridge.v connects to NoFreeInsight policy: categorical_extension_nofi_consistent proven

### Phase 5: Extraction & Runtime (~200 lines) ✅ COMPLETE
32. ✅ OCaml extraction rebuilt: Extraction.vo compiled, thiele_core.ml regenerated
33. ✅ extracted_vm_runner.ml updated: 7 MORPH parse clauses at lines 391-404 (CONFIRMED by grep)
    - Coq_instr_morph, Coq_instr_compose, Coq_instr_morph_id, Coq_instr_morph_delete,
      Coq_instr_morph_assert, Coq_instr_morph_tensor, Coq_instr_morph_get all present
34. ✅ forge.py: 7 OPCODES entries added (0x27–0x2D) — CONFIRMED (lines 51-57 of scripts/forge.py)
35. ✅ forge_vm.py: 7 CONSTRUCTOR_FIELD_MAP entries — CONFIRMED at lines 197-211 of scripts/forge_vm.py
    - Instr_morph, Instr_morph_id, Instr_morph_delete, Instr_morph_assert,
      Instr_morph_tensor, Instr_morph_get all present; thielecpu/vm.py regenerated
36. ✅ Regeneration complete: thielecpu/generated/generated_core.py has 47 opcodes (sanity_check passes)
    - forge.py regenerated generated_core.py; rtl_harness/cosim.py updated with 7 MORPH entries
37. ✅ Python integration tests written: tests/test_categorical_opcodes.py
    - 28 tests across TestMorphCreate, TestMorphId, TestMorphCompose, TestMorphDelete,
      TestMorphAssert, TestCascadeDelete, TestMorphTensor, TestMorphGet, TestCategoricalInvariants
    - All 28 pass (confirmed 2026-03-24)
⚠️ CONFIRMED GAP (now fixed 2026-03-24): `build/thiele_vm.py` `_parse_instruction_dict` was missing all 7 MORPH opcodes.
   FIXED: Added MORPH/COMPOSE/MORPH_ID/MORPH_DELETE/MORPH_ASSERT/MORPH_TENSOR/MORPH_GET at lines 229–249

### Phase 6: Hardware (~200 lines) ✅ COMPLETE
38. ✅ 7 OP_* constants in ThieleTypes.v (OP_MORPH=0x27 … OP_MORPH_GET=0x2D) — CONFIRMED lines 132-138
39. ✅ ERR_* codes added: ERR_COUPLING_INVALID, ERR_MORPH_NOT_FOUND, ERR_TENSOR_INVALID — CONFIRMED lines 50-60
40. ✅ Dispatch in ThieleCPUCore.v lines 522-584: all 7 opcodes; MORPH_ASSERT charges S(cost) — CONFIRMED
41. ✅ Abstraction.v lines 1002-1015: all 7 morph kami_step arms; pg_morphisms=[] rationale documented
42. ✅ VerilogRefinement.v lines 792-835: abs_phase1_morphism_none, abs_phase1_compose_none,
    abs_phase1_delete_none lemmas; categorical simulation proofs for all 7 — CONFIRMED
43. ✅ scripts/kami_extract.sh exists
    - Note (2026-03-24): script was in git staging but not working tree; recovered via
      `git show :scripts/kami_extract.sh > scripts/kami_extract.sh`
44. ✅ RTL-specific tests for MORPH opcodes written: tests/test_rtl_morph_opcodes.py
    - 20 tests across 3 classes: TestMorphRTLSmoke (7), TestMorphRTLRegisterWrite (7),
      TestMorphRTLMuAccumulation (6); all 20 pass via Verilog cosimulation
    - Prerequisite fix: VerilogRefinement.v needed explicit `List` import + `Import ListNotations.`
      for standalone coqc compilation used by kami_extract.sh (line 914 uses [] notation)
    - Prerequisite: kami_extract.sh re-run to regenerate thiele_cpu_kami.v with MORPH opcodes
      0x27–0x2D; prior Verilog only had opcodes up to 0x26 (TENSOR_GET)
    - Also fixed stale test name: test_all_38_opcodes_in_cosim → test_all_47_opcodes_in_cosim

### Phase 7: Integration (~700 lines) ✅ DONE
45. ✅ ThieleMachineComplete.v updated: MORPH types inline at line 792, instructions at lines 1348-1354,
    vm_apply arms at lines 1727-1797 — CONFIRMED (grep verified 40 occurrences)
46. ✅ MasterSummary.v updated (2026-03-24):
    - Added `From Kernel Require Import CategoryLaws CategoryBridge CategoryMonoidal.`
    - Added Part IIe section (lines 2529+) with 6 export aliases:
      master_categorical_compose_assoc, master_categorical_id_left,
      master_categorical_id_right, master_categorical_nofi_consistent,
      master_categorical_tensor_bifunctor, master_categorical_monoidal_coherence
    - Uses Definition-alias form to avoid name-shadowing ambiguity; zero Admitted; compiles clean
47. ✅ PartitionSeparation.v categorical separation proof added (2026-03-24):
    - Section 10 added at end of PartitionSeparation module (before End PartitionSeparation)
    - Defines: computationally_equivalent, categorically_distinct
    - Theorem categorical_separation: ∃ s1 s2, computationally_equivalent s1 s2 ∧
      categorically_distinct s1 s2  (s1 has one identity morphism; s2 has none)
    - Corollary categorical_layer_is_nontrivial: the distinction is inhabited
    - Proof: all by reflexivity + discriminate; zero Admitted; compiles clean
48. ✅ Full CI run (2026-03-24): 593 passed, 1 skipped, 0 failed (pre-RTL-test baseline)
    - Fixes applied to reach green: forge.py, rtl_harness/cosim.py, test_verilog_cosim.py,
      thielecpu/generated/generated_core.py, artifacts/final_claim_audit/ checksums
49. ✅ Final audit (2026-03-24): zero Admitted kernel-wide, all tests pass
50. ✅ Post-completion additions (2026-03-24):
    - tests/test_rtl_morph_opcodes.py: 20 new RTL cosim tests (item 44)
    - coq/kernel/PartitionSeparation.v: categorical separation proof (item 47)
    - coq/kami_hw/VerilogRefinement.v: List + ListNotations import for kami_extract.sh
    - thielecpu/hardware/rtl/thiele_cpu_kami.v: regenerated with MORPH opcodes 0x27–0x2D
    - coq/kami_hw/LogicEngineEquivalence.vo + RTLCorrectnessInstantiation.vo: restored
      (deleted from working tree by kami_extract.sh run; rebuilt with coqc)

---

## Part 10: Test Programs

### Coq Test: Basic Category

```coq
Definition category_test : list vm_instruction := [
  (* Create objects *)
  instr_pnew [0; 1; 2] 1;                                    (* Module 0 *)
  instr_pnew [3; 4; 5] 1;                                    (* Module 1 *)
  instr_pnew [6; 7; 8] 1;                                    (* Module 2 *)
  (* Create morphisms *)
  instr_morph 0 0 1 (mk_coupling [(0,3);(1,4);(2,5)] "f") 1; (* f: 0→1, ID in r0 *)
  instr_morph 1 1 2 (mk_coupling [(3,6);(4,7);(5,8)] "g") 1; (* g: 1→2, ID in r1 *)
  (* Compose *)
  instr_compose 2 0 1 1;                                      (* g∘f: 0→2, ID in r2 *)
  (* Create identity *)
  instr_morph_id 3 0 1;                                       (* id_0, ID in r3 *)
  (* Compose with identity (should equal f) *)
  instr_compose 4 3 0 1;                                      (* id_0 ; f, ID in r4 *)
  (* Inspect *)
  instr_morph_get 5 4 0 1;                                    (* r5 = source of composed = 0 *)
  instr_morph_get 6 4 1 1;                                    (* r6 = target of composed = 1 *)
  instr_halt 0
].
```

### Coq Test: Monoidal Structure

```coq
Definition monoidal_test : list vm_instruction := [
  (* Create four modules *)
  instr_pnew [0; 1] 1;                                        (* A: Module 0 *)
  instr_pnew [2; 3] 1;                                        (* B: Module 1 *)
  instr_pnew [4; 5] 1;                                        (* C: Module 2 *)
  instr_pnew [6; 7] 1;                                        (* D: Module 3 *)
  (* Create tensor product modules *)
  instr_pmerge 0 2 1;                                         (* A⊗C: Module 4 *)
  instr_pmerge 1 3 1;                                         (* B⊗D: Module 5 *)
  (* Create morphisms *)
  instr_morph 0 0 1 (mk_coupling [(0,2);(1,3)] "f") 1;       (* f: A→B *)
  instr_morph 1 2 3 (mk_coupling [(4,6);(5,7)] "g") 1;       (* g: C→D *)
  (* Tensor product of morphisms *)
  instr_morph_tensor 2 0 1 1;                                 (* f⊗g: A⊗C → B⊗D *)
  (* Inspect result *)
  instr_morph_get 3 2 0 1;                                    (* source = 4 (A⊗C) *)
  instr_morph_get 4 2 1 1;                                    (* target = 5 (B⊗D) *)
  instr_morph_get 5 2 2 1;                                    (* coupling length = 4 *)
  instr_halt 0
].
```

### Coq Test: Cascade Delete

```coq
Definition cascade_test : list vm_instruction := [
  (* Create modules *)
  instr_pnew [0; 1; 2; 3] 1;                                  (* Module 0 *)
  instr_pnew [4; 5] 1;                                        (* Module 1 *)
  (* Create morphism *)
  instr_morph 0 0 1 (mk_coupling [(0,4);(1,5)] "f") 1;       (* f: 0→1 *)
  (* Split module 0 — should cascade delete morphism f *)
  instr_psplit 0 [0; 1] [2; 3] 1;                            (* 0 becomes 2 and 3 *)
  (* Try to inspect deleted morphism — should fail *)
  instr_morph_get 1 0 0 1;                                    (* Should error: morph 0 deleted *)
  instr_halt 0
].
```

### Python Test: Full Coverage

```python
# tests/test_categorical_ops.py

def test_morph_returns_id_to_register():
    s = run_py([
        {"op": "pnew", "region": [0,1,2], "cost": 1},
        {"op": "pnew", "region": [3,4,5], "cost": 1},
        {"op": "morph", "dst": 5, "src": 0, "dst_mod": 1,
         "coupling": {"pairs": [(0,3),(1,4),(2,5)], "label": "f"}, "cost": 1},
        {"op": "halt", "cost": 0}
    ])
    assert s.vm_regs[5] == 0  # First morphism gets ID 0
    assert len(s.vm_graph.pg_morphisms) == 1

def test_compose_type_checks():
    s = run_py([
        {"op": "pnew", "region": [0,1], "cost": 1},
        {"op": "pnew", "region": [2,3], "cost": 1},
        {"op": "pnew", "region": [4,5], "cost": 1},
        {"op": "morph", "dst": 0, "src": 0, "dst_mod": 1,
         "coupling": {"pairs": [(0,2),(1,3)], "label": "f"}, "cost": 1},
        {"op": "morph", "dst": 1, "src": 1, "dst_mod": 2,
         "coupling": {"pairs": [(2,4),(3,5)], "label": "g"}, "cost": 1},
        {"op": "compose", "dst": 2, "m1": 0, "m2": 1, "cost": 1},
        {"op": "halt", "cost": 0}
    ])
    assert s.vm_regs[2] == 2  # Composed morphism gets ID 2
    assert len(s.vm_graph.pg_morphisms) == 3
    composed = s.vm_graph.pg_morphisms[2][1]
    assert composed.morph_source == 0
    assert composed.morph_target == 2

def test_compose_type_mismatch_errors():
    s = run_py([
        {"op": "pnew", "region": [0,1], "cost": 1},
        {"op": "pnew", "region": [2,3], "cost": 1},
        {"op": "pnew", "region": [4,5], "cost": 1},
        {"op": "morph", "dst": 0, "src": 0, "dst_mod": 1,
         "coupling": {"pairs": [(0,2),(1,3)], "label": "f"}, "cost": 1},
        {"op": "morph", "dst": 1, "src": 2, "dst_mod": 0,
         "coupling": {"pairs": [(4,0),(5,1)], "label": "g"}, "cost": 1},
        {"op": "compose", "dst": 2, "m1": 0, "m2": 1, "cost": 1},  # f.target=1 ≠ g.source=2
        {"op": "halt", "cost": 0}
    ])
    assert s.vm_err == True

def test_morph_delete():
    s = run_py([
        {"op": "pnew", "region": [0,1], "cost": 1},
        {"op": "pnew", "region": [2,3], "cost": 1},
        {"op": "morph", "dst": 0, "src": 0, "dst_mod": 1,
         "coupling": {"pairs": [(0,2),(1,3)], "label": "f"}, "cost": 1},
        {"op": "morph_delete", "morph_id": 0, "cost": 1},
        {"op": "halt", "cost": 0}
    ])
    assert len(s.vm_graph.pg_morphisms) == 0

def test_morph_assert_is_cert_setter():
    s = run_py([
        {"op": "pnew", "region": [0,1], "cost": 1},
        {"op": "morph_id", "dst": 0, "module": 0, "cost": 1},
        {"op": "morph_assert", "morph_id": 0, "property": "isomorphism",
         "cert": {"type": "sat", "model": "trivial"}, "cost": 0},  # cost=0 but S(0)=1
        {"op": "halt", "cost": 0}
    ])
    assert s.vm_mu >= 3  # pnew(1) + morph_id(1) + morph_assert(S(0)+len("isomorphism"))

def test_cascade_delete_on_psplit():
    s = run_py([
        {"op": "pnew", "region": [0,1,2,3], "cost": 1},
        {"op": "pnew", "region": [4,5], "cost": 1},
        {"op": "morph", "dst": 0, "src": 0, "dst_mod": 1,
         "coupling": {"pairs": [(0,4),(1,5)], "label": "f"}, "cost": 1},
        {"op": "psplit", "module": 0, "left": [0,1], "right": [2,3], "cost": 1},
        {"op": "halt", "cost": 0}
    ])
    # Morphism f was deleted because module 0 was split
    assert len(s.vm_graph.pg_morphisms) == 0

def test_morph_tensor():
    s = run_py([
        {"op": "pnew", "region": [0,1], "cost": 1},      # A: 0
        {"op": "pnew", "region": [2,3], "cost": 1},      # B: 1
        {"op": "pnew", "region": [4,5], "cost": 1},      # C: 2
        {"op": "pnew", "region": [6,7], "cost": 1},      # D: 3
        {"op": "pmerge", "m1": 0, "m2": 2, "cost": 1},   # A⊗C: 4
        {"op": "pmerge", "m1": 1, "m2": 3, "cost": 1},   # B⊗D: 5
        {"op": "morph", "dst": 0, "src": 0, "dst_mod": 1,
         "coupling": {"pairs": [(0,2),(1,3)], "label": "f"}, "cost": 1},
        {"op": "morph", "dst": 1, "src": 2, "dst_mod": 3,
         "coupling": {"pairs": [(4,6),(5,7)], "label": "g"}, "cost": 1},
        {"op": "morph_tensor", "dst": 2, "f": 0, "g": 1, "cost": 1},
        {"op": "halt", "cost": 0}
    ])
    assert s.vm_regs[2] == 2  # Tensor morphism ID
    tensor_morph = s.vm_graph.pg_morphisms[2][1]
    assert tensor_morph.morph_source == 4  # A⊗C
    assert tensor_morph.morph_target == 5  # B⊗D
    assert len(tensor_morph.morph_coupling.coupling_pairs) == 4

def test_morph_get():
    s = run_py([
        {"op": "pnew", "region": [0,1,2], "cost": 1},
        {"op": "pnew", "region": [3,4,5], "cost": 1},
        {"op": "morph", "dst": 0, "src": 0, "dst_mod": 1,
         "coupling": {"pairs": [(0,3),(1,4),(2,5)], "label": "f"}, "cost": 1},
        {"op": "morph_get", "dst": 1, "morph_id": 0, "selector": 0, "cost": 1},  # source
        {"op": "morph_get", "dst": 2, "morph_id": 0, "selector": 1, "cost": 1},  # target
        {"op": "morph_get", "dst": 3, "morph_id": 0, "selector": 2, "cost": 1},  # coupling len
        {"op": "morph_get", "dst": 4, "morph_id": 0, "selector": 3, "cost": 1},  # is_identity
        {"op": "halt", "cost": 0}
    ])
    assert s.vm_regs[1] == 0  # source
    assert s.vm_regs[2] == 1  # target
    assert s.vm_regs[3] == 3  # 3 coupling pairs
    assert s.vm_regs[4] == 0  # not an identity
```

---

## Part 11: Risk Assessment (Updated)

| Risk | Severity | Mitigation |
|------|----------|------------|
| PartitionGraph record change breaks 10+ files | High | Phase 1 as atomic commit |
| 7 new vm_instruction constructors break 15+ matches | High | Mechanical; follow patterns |
| Cascade delete breaks existing graph invariants | High | Prove cascade_preserves_wf early |
| MORPH_ASSERT cert-setter status adds complexity | Medium | Follow LASSERT pattern exactly |
| Monoidal proofs (bifunctor, coherence) are hard | Medium | Start with bifunctor only; defer pentagon/triangle |
| ThieleMachineComplete.v update is massive | Medium | Do last; it's independent |
| Hardware Option B (morphism table) is complex | Low | Use Option A; defer Option B |
| relational_compose proofs are tedious | Low | Standard set theory; ~100 lines |

---

## Part 12: What This Enables (Updated)

A Thiele Machine with this extension would be:

1. **A categorical computer** — objects, morphisms, composition as hardware primitives
2. **Type-safe at runtime** — COMPOSE refuses type-mismatched arrows
3. **Monoidal** — MORPH_TENSOR implements the tensor bifunctor
4. **Inspectable** — MORPH_GET reads morphism structure
5. **Manageable** — MORPH_DELETE prevents unbounded growth
6. **Certifiable** — MORPH_ASSERT proves properties of arrows under NoFI
7. **Consistent under mutation** — cascade delete keeps graph well-formed

### Theoretical Implications

- **Programs are diagrams**: A sequence of PNEW + MORPH + COMPOSE literally constructs
  a categorical diagram (commutative or not)
- **String diagram compilation**: Visual string diagrams can compile to MORPH_TENSOR +
  COMPOSE sequences
- **Categorical quantum mechanics**: With the existing CHSH_TRIAL + this categorical
  structure, you have the ingredients for a dagger-compact category (add MORPH_DAGGER
  as future work)

### Next Extensions (Future Work)

| Extension | What It Adds |
|-----------|--------------|
| MORPH_DAGGER | Adjoint/dagger operation for quantum categories |
| MORPH_INVERSE | Explicit inverse (for groupoids) |
| FUNCTOR | Maps between partition categories |
| NAT_TRANSFORM | Higher morphisms between functors |
| Coherence proofs | Pentagon, triangle, unitors for full monoidal category |
| MORPH_GET_COUPLING idx | Read individual coupling pairs |

---

## Appendix: Opcode Byte Assignments

| Opcode | Byte | Binary |
|--------|------|--------|
| MORPH | 0x27 | 0010 0111 |
| COMPOSE | 0x28 | 0010 1000 |
| MORPH_ID | 0x29 | 0010 1001 |
| MORPH_DELETE | 0x2A | 0010 1010 |
| MORPH_ASSERT | 0x2B | 0010 1011 |
| MORPH_TENSOR | 0x2C | 0010 1100 |
| MORPH_GET | 0x2D | 0010 1101 |

Next available: 0x2E
