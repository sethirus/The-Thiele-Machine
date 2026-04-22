# The Thiele Machine — Master Completion Record

> **COMPLETED 2026-04-21.** All 46 opcodes have Qed proofs under zero Admitted.
> The coupling_wf migration closed the final two architectural gaps in
> COMPOSE and MORPH_TENSOR. `make closeout-gate` passes. The repo is done.

---

## Completion Table

| # | Phase | Deliverable | File(s) | Status |
|---|---|---|---|---|
| 1 | Orientation | Read and annotate the seven key files | see §1 | ✓ Done |
| 2 | Proof gap 1 | `driven_step_compose` (full equality, Qed) | `GraphReconstructionBridge.v` | ✓ Done |
| 3 | Proof gap 2 | `driven_step_morph_tensor` (full equality, Qed) | `GraphReconstructionBridge.v` | ✓ Done |
| 4 | Wire gaps | COMPOSE + MORPH_TENSOR in `WFDrivenPrecondition` + `driven_step_wf` | `GraphReconstructionBridge.v` | ✓ Done |
| 5 | EmbedStep doc | §9 comment updated — abstraction boundary documented | `EmbedStep.v` | ✓ Done |
| 6 | Gap registry | Empty registry, rtl_gap_count = 0, all gaps closed | `RTLGapRegistry.v` | ✓ Done |
| 7 | Canonical bundle | `CanonicalCPUProofBundle` includes COMPOSE + MORPH_TENSOR fields | `CanonicalCPUProof.v` | ✓ Done |
| 8 | Extraction anchors | `extraction_compose_anchor` + `extraction_monoidal_coherence_anchor` | `Extraction.v` | ✓ Done |
| 9 | Coq build | `make -j4` — zero Admitted, zero errors | root `Makefile` | ✓ Done |
| 10 | Extraction | OCaml extraction regenerated — `thiele_core.ml` byte-for-byte identical to complete | root `Makefile` | ✓ Done |
| 11 | RTL gate | Yosys synthesis passes | root `Makefile` | ✓ Done |
| 12 | Cosim gate | iverilog cosimulation passes | root `Makefile` | ✓ Done |
| 13 | Closeout | `make closeout-gate` — all closure steps green | root `Makefile` | ✓ Done |

---

## What Was Done — Final State

### coupling_wf Migration (Phase 5+, 2026-04-21)

The original plan described closing COMPOSE and MORPH_TENSOR gaps using
`coupling_desc_all_zero` (all morphisms have empty coupling). This approach
was architecturally wrong: `coupling_desc_all_zero` is NOT preserved by
COMPOSE or MORPH_TENSOR success paths — the very operations being proved.

**Resolution:**
- Replaced `coupling_desc_all_zero` in `extended_hw_invariant` with `coupling_wf`:
  ```
  coupling_wf = coupling_desc_bounded /\ coupling_pairs_in_range /\ coupling_pairs_fully_populated
  ```
- Added `normalize_coupling` to `Abstraction.v` `instr_compose` branch — the hardware
  now stores `nodup(relational_compose pairs1 pairs2)` matching the kernel's
  `graph_add_morphism` exactly.
- Proved `coupling_wf_kami_step_preserved` — `coupling_wf` is an inductive invariant
  preserved by all 46 `kami_step` operations.
- `driven_step_compose` and `driven_step_morph_tensor` both proved to full VMState
  equality under `coupling_wf`. Qed.

### Final Coverage

| Group | Count | State | Notes |
|---|---|---|---|
| Unconditional | 36 | Qed | 30 SupportedOpcode + CALL/RET/CHSH_TRIAL/TENSOR_SET/TENSOR_GET/LASSERT |
| Inductive invariant | 10 | Qed | PNEW/PSPLIT/PMERGE + MORPH family (6) + COMPOSE + MORPH_TENSOR |
| **Total** | **46** | **0 Admitted** | |

The 10 "inductive invariant" proofs hold for every state reachable from a valid
initial state. `coupling_wf_kami_step_preserved` and `morph_table_wf_kami_step_preserved`
prove these invariants are inductive — there are no unreachable-state caveats in practice.

---

## The Architecture (final)

```
Categorical_Engine (Python — origin project)
  AbstractMorphism.apply_element  →  vm_apply
  compose(f,g)                    →  driven_step_compose (Qed)
  IdentityMorphism                →  driven_step_morph_id (Qed)
  monoidal composition            →  CategoryMonoidal.monoidal_coherence (Qed)
  Bell-CHSH 16/5 experiment       →  instr_chsh_trial + TsirelsonQuantumModel.v (Qed)
  Z3 property assertions          →  MORPH_ASSERT (mandatory S cost) (Qed)

VMStep.v / VMState.v            — 46-opcode ISA, zero Admitted
   ↓  SimulationProof.v          — vm_step ≡ vm_apply (Qed)
   ↓  EmbedStep.v                — 36 opcodes under abs_phase1 (Qed)
   ↓  GraphReconstructionBridge.v — 46/46 under abs_full_snapshot (Qed)
   ↓  CanonicalCPUProof.v         — canonical proof bundle + extraction root
   ↓  KamiExtraction.v / Extraction.v
   ↓  build/kami_hw/Target.ml     (OCaml, extracted from Coq)
   ↓  build/kami_hw/PP.ml → thiele_hw.bsv  (Bluespec)
   ↓  bsc → synthesizable Verilog
   ↓  make closeout-gate ✓
```

---

## Key Files

| File | Role | Key theorems |
|---|---|---|
| `coq/kernel/VMStep.v` | 46-opcode ISA specification | `vm_instruction`, `instruction_cost` |
| `coq/kernel/CategoryLaws.v` | Relational algebra | `relational_compose_assoc` |
| `coq/kernel/CategoryMonoidal.v` | Monoidal structure | `monoidal_coherence`, `tensor_bifunctor` |
| `coq/kami_hw/Abstraction.v` | Hardware↔kernel projection | `abs_phase1`, `abs_full_snapshot`, `snap_full_graph` |
| `coq/kami_hw/EmbedStep.v` | 36-opcode bridge (abs_phase1) | `embed_step_compute`, `SupportedOpcode` |
| `coq/kami_hw/GraphReconstructionBridge.v` | 46/46 Qed, coupling_wf | `driven_step_wf`, `coupling_wf_kami_step_preserved` |
| `coq/kami_hw/CanonicalCPUProof.v` | Proof bundle + extraction root | `CanonicalCPUProofBundle`, `canonical_cpu_module` |
| `coq/kami_hw/RTLGapRegistry.v` | Gap accounting (0 gaps) | `rtl_gap_count`, `rtl_coverage_partition` |
| `coq/tests/CloseoutVerification.v` | Verified closeout checklist | All 46 proofs reachable, zero gaps |
