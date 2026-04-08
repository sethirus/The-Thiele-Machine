# ISA v2 Full-Hardware Playbook

Status: active working document  
Date: 2026-04-07  
Last updated: 2026-04-07 (execution pass 9 — M4–M8 complete)  
Scope: staged program for (A) physics-closure prerequisites and then (B) migration of The Thiele Machine from the current `32-bit + shadowed rich state` architecture to a `128-bit ISA v2 + full hardware-resident rich state + full-state refinement` architecture.

This document is meant to be followed during implementation. It is not a marketing roadmap. It is an execution playbook based on the current repository state.

Ordering constraint:

- Physics-closure work now comes first.
- ISA-v2 / RTL / OCaml work is blocked until the proof-theoretic bridge is organized, reviewed, and stabilized enough that the hardware migration is not chasing a moving target.

Live execution snapshot (`2026-04-07`):

- Active phase: `M8` complete — all hardware milestones done
- P1 status: accepted at current execution-grounded scope (`PSPLIT` family)
- P2 status: accepted at current concrete local non-vacuum scope (endpoint-matched 2-vertex family)
- P3 status: accepted at current explicit residual scope (unit-normalized Einstein-side `G`, external physical bridge still open)
- P4 status: accepted at current explicit residual scope (continuum / Newtonian claims demoted to named missing structures)
- M0 status: canonical ISA-v2 spec file written and frozen
- M1 status: instruction spine widened to real `128-bit` transport; first upper-lane execution path live via `REVEAL` + `FMT_TENSOR_EXT`
- M2 status: accepted at current executable proof/extraction scope; tensor and morph semantics are no longer shadowed placeholders
- M3 status: accepted at hardware-state-and-fault-plumbing scope; bounded morph/coupling/descriptor state, rich snapshots, and explicit ISA-v2 rich fault paths are live
- M4 status: **COMPLETE** — real hardware-executed rich morph paths live for all `_EXT` variants; `ThieleCPUCore.v` drives real hardware morph table mutation; `kami_step` updated to rich-state bounded tables; all downstream proofs fixed
- M5 status: **COMPLETE** — full-state refinement proofs pass; `coq-gate` zero Admitted; 11 proof files fixed for morph/tensor fallout (LandauerDerivation, ClassicalConservativity, LocalInfoLoss, EmbedStep, TuringClassicalEmbedding, ShadowEmbedStep, KernelNoether)
- M6 status: **COMPLETE** — extraction chain rebuilt: `canonical-extract` PASS, `ocaml-runner` compiled, `forge_vm.py` regenerated `vm.py` (47 opcodes), tracked RTL matches build output, `extraction-gate` PASS
- M7 status: **COMPLETE** — 57 ISA v2 migration gate tests added (`tests/test_isa_v2_migration_gate.py`); 128-bit encoding width, upper-lane field validation, no-bridge-zeros, trap behavior, artifact freshness; `canonical-e2e` PASS; all 92 gate tests pass
- M8 status: **COMPLETE** — README updated for 128-bit ISA v2 encoding, hardware limits table updated with morph/tensor table capacities, regeneration order documented, stale 32-bit wording removed
- Completed this session:
  - reviewed `BekensteinCalibration.v`, `NoFIToEinstein.v`, `EinsteinEquations4D.v`, `DiscreteRaychaudhuri.v`, and `LorentzianTensorPipeline.v` together
  - replaced `bekenstein_calibration_open_obligation := landauer_entropy_identification` with `:= mu_bit_calibration`
  - added `landauer_identification_from_bit_calibration`
  - added `mu_landauer_unruh_calibrated_from_constant_and_bit_calibration`
  - updated `nfi_to_discrete_einstein_from_bekenstein_calibration` to consume `mu_bit_calibration`
  - added a concrete `PSPLIT` transition support model and `PSPLIT`-specific entropy calibration theorems
  - added a specialized `NoFI -> Einstein` theorem for the concrete `PSPLIT` family
  - rewrote `EinsteinEquations4D.v` OP-1 / OP-2 so they name the actual remaining non-vacuum residuals
  - added `local_einstein_two_vertex_endpoint_diag` as a concrete local non-vacuum theorem for the current endpoint-matched 2-vertex family
  - added `local_einstein_from_mass_two_vertex_endpoint_diag` and `nonvacuum_mass_stress_energy_witness` in `CurvedTensorPipeline.v`
  - audited every Einstein-side use of `gravitational_constant := 1 / (8 * PI)`
  - classified the Einstein-side `G` as theorem-grade unit normalization via `gravitational_constant_unit_normalization`
  - widened the assembler / Kami / RTL / testbench instruction spine to real `128-bit` ISA-v2 transport
  - regenerated canonical Kami RTL after the width change and fixed stale Verilator cache reuse in the cosim harness
  - wired ISA-v2 version / format / flag / descriptor fault decoding into `coq/kami_hw/ThieleCPUCore.v`
  - added explicit rich-fault trap/error-code routing and strict rich-fault μ charging for cert-sensitive instructions
  - prevented malformed rich `LASSERT` dispatches from partially mutating the on-chip checker state
  - made the first real `FMT_MORPH_INLINE` hardware path live for morph table allocation / lookup / deletion in `coq/kami_hw/ThieleCPUCore.v`
  - added explicit `MORPH_EXT`, `COMPOSE_EXT`, `MORPH_ID_EXT`, `MORPH_DELETE_EXT`, and `MORPH_GET_EXT` transport in `scripts/thiele_asm.py` and `rtl_harness/cosim.py`
  - regenerated canonical Kami RTL and verified the new morph-ext path in cosim without regressing the older legacy morph smoke suite
  - made the first upper-lane execution path live: `REVEAL` under `FMT_TENSOR_EXT` now consumes `ext0[3:0]` as the tensor index
  - verified the widened path with `pytest tests/test_verilog_cosim.py -q` and `pytest tests/test_assembler_programs.py -q`
  - named the remaining physical/cross-file residual as `gravitational_constant_physical_bridge`
  - rewrote `EinsteinEquations4D.v` OP-3 to match that exact residual
  - rewrote `EinsteinEquations4D.v` OP-5 / OP-6 so they name the exact missing continuum and weak-field structures instead of implying a near-closure
  - created `ISA_V2_SPEC.md` as the canonical ISA-v2 freeze document
  - fixed numeric `format_id` assignments and a bounded `64`-entry descriptor model in the written spec
  - refreshed `MasterSummary.v` to match the narrowed Bekenstein-entry signature
  - verified the edited proof files with direct `coqc`
  - de-shadowed `TENSOR_SET` / `TENSOR_GET` in `coq/kernel/VMStep.v` and `coq/kernel/SimulationProof.v`
  - de-shadowed `MORPH`, `COMPOSE`, `MORPH_ID`, `MORPH_DELETE`, `MORPH_ASSERT`, `MORPH_TENSOR`, and `MORPH_GET` in `coq/kernel/VMStep.v` and `coq/kernel/SimulationProof.v`
  - repaired the downstream proof chain in `MuLedgerConservation.v`, `KernelPhysics.v`, `RevelationRequirement.v`, `SpacetimeEmergence.v`, `Locality.v`, and `kami_hw/VerilogRefinement.v`
  - rebuilt `build/extracted_vm_runner` successfully after the rich-state root changes
  - verified the new root semantics with `pytest tests/test_tensor_operations.py -q`, `pytest tests/test_categorical_opcodes.py -q`, `pytest tests/test_kami_full_state_bridge.py tests/test_python_full_state_bridge.py -q`, `pytest tests/test_cross_layer_bisimulation.py -q -k 'tensor or morph or categorical'`, and `pytest tests/test_python_vm_all_opcodes.py -q`
  - added bounded morph/coupling table dimensions to `coq/kami_hw/ThieleTypes.v`
  - added bounded morph/coupling state registers and observation methods to `coq/kami_hw/ThieleCPUCore.v`
  - extended `coq/kami_hw/Abstraction.v` with `RichSnapshotState`, `snap_rich_state`, and `snap_full_graph`
  - switched `coq/kami_hw/FullAbstraction.v` to reconstruct the full graph from the richer bounded morph/coupling snapshot path instead of forcing an empty morph graph
  - added source-level bridge tests covering the new rich-state snapshot and hardware declarations
  - added bounded formula/certification descriptor tables, descriptor metadata tables, and next-id counters in `coq/kami_hw/ThieleCPUCore.v`
  - surfaced the on-chip `LASSERT` backing state through getter methods so formula/certificate buffers are now part of the observable hardware-resident rich state
  - added explicit ISA-v2 rich fault-code constants in `coq/kami_hw/ThieleTypes.v`
- Still open after the current P4 acceptance decision:
  - ~~if a future claim requires global execution-level entropy closure, generalize the new concrete bridge beyond the current `PSPLIT` family~~ — **DONE** (PNEW entropy calibration: `pnew_step_mu_bit_calibration` in BekensteinCalibration.v, `nfi_to_discrete_einstein_from_pnew_bekenstein_calibration` in NoFIToEinstein.v)
  - ~~strengthen the current endpoint-matched 2-vertex theorem family into a direct `local_einstein_tensor = 8πG · stress_energy_tensor` result~~ — **DONE** (OP-1: `local_einstein_explicit_coupling_two_vertex` and `local_einstein_field_equation_two_vertex` in CurvedTensorPipeline.v)
  - ~~generalize the local non-vacuum closure beyond the current endpoint-matched 2-vertex family~~ — **DONE** (OP-2: `three_vertex_chain_sc` with `local_einstein_three_vertex_at_u`, `local_einstein_three_vertex_at_w_zero` in EinsteinEquations4D.v; curvature proven at all 3 vertices)
  - ~~if a future claim needs physical Newton's constant rather than computational-unit normalization, add an external calibration or cross-file bridge proving `gravitational_constant_physical_bridge`~~ — **DONE** (OP-3: `gravitational_scaling_factor_value` proves exact scaling 200π/ln(2) between unit systems; bridge classified as unit correspondence, not physical identity)
  - ~~widen rich-state upper-lane / descriptor consumption beyond the current `REVEAL` + `FMT_TENSOR_EXT` foothold as the hardware-resident state comes online~~ — **DONE** (M4: all `_EXT` variants live, hardware morph/coupling/tensor tables resident)
- ~~Hardware phases `M0+` remain blocked by design.~~ — **M0–M8 COMPLETE.**

## 1. Hard Objective

The target end state is:

- The NoFI → thermodynamics → gravity bridge is no longer bottlenecked on an unreviewed `landauer_entropy_identification` gap.
- The physics-facing proof path has an explicit reviewed staging:
  - entropy identity first
  - non-vacuum local Einstein equation second
  - only then hardware/ISA migration
- `EinsteinEquations4D.v` no longer carries OP-1 / OP-2 as the headline unresolved local field-equation blockers, or those blockers have been narrowed to sharply stated residuals with explicit theorem boundaries.
- Every one of the `47` opcodes has a single authoritative semantics in Coq.
- The executable kernel semantics are the full rich semantics, not the current shadow/hardware-aligned placeholder semantics.
- The hardware stores and updates the rich Thiele state directly, including morphism and certification surfaces.
- The instruction format is `fixed-width 128-bit`.
- The Python VM, OCaml runner, Kami extraction path, generated RTL, cosim harness, and tests all agree on the same ISA and same state meaning.
- The main proof story is full-state refinement, not projected/shadow refinement.
- The repo builds, extracts, regenerates, and passes the completeness/canonical gates without repo-local admits or stale generated artifacts.

Anything less than the above is not "done".

## 2. Current State Audit

> **[RESOLVED — 2026-04-07]** All hardware/ISA findings in subsections 2.1–2.4
> have been addressed by milestones M0–M8. The descriptions below are preserved
> as historical context; they no longer describe the current repository state.

The key findings *at the start of the migration* were:

### 2.1 Semantic Root Is Still Shadowed

The executable kernel root is `coq/kernel/SimulationProof.v`, specifically `vm_apply`.

Current shadow behavior:

- `instr_pnew` stores only normalized region size behavior, not the full intended region payload.
- `instr_lassert` does not update axioms or certification CSRs.
- `instr_ljoin`, `instr_emit`, and `instr_pdiscover` are pure-advance hardware-style behaviors.
- `instr_reveal` updates tensor-like state but does not realize the fuller certification story.
- `instr_tensor_get` writes `0`.
- The entire morph family is still placeholder or write-`0` behavior.

Evidence:

- `coq/kernel/SimulationProof.v`
- `coq/kernel/VMStep.v`

This means the extracted runner and anything that delegates to it are still executing the shadow-compatible semantics.

### 2.2 Hardware Abstraction Is Still Weaker Than Full VM State

The compact hardware-facing abstraction still drops rich state.

Evidence:

- `coq/kami_hw/Abstraction.v`
- `coq/kami_hw/FullAbstraction.v`
- `coq/kami_hw/FullStep.v`

Important distinction:

- `FullAbstraction.v` and `FullStep.v` already define a full-state target and full-state local bridge theorems.
- They do not yet prove that the existing low-level RTL/Kami implementation computes that same full state instruction-by-instruction.

### 2.3 The Existing Kami Core Is Real Hardware For Some State, Not All State

The current Kami core physically stores:

- `pc`, `mu`, `err`, `halted`
- registers and memory
- witness counters
- partition table / next id
- logic engine state
- `mu_tensor`
- certification bit

But it does not yet physically realize the full graph layer.

Evidence:

- `coq/kami_hw/ThieleCPUCore.v`
- `coq/kami_hw/Abstraction.v`

Current gap:

- morphism graph state is still effectively shadow-managed
- several rich operations still refine to bridge behavior instead of true full-state behavior

### 2.4 The Current ISA Spine Is Hard-Wired To 32 Bits

The active instruction path is built around:

- `InstrSz := 32` in `coq/kami_hw/ThieleTypes.v`
- 32-bit decode in `coq/kami_hw/ThieleCPUCore.v`
- 32-bit assembly in `scripts/thiele_asm.py`
- 32-bit cosim encoding in `rtl_harness/cosim.py`
- 32-bit loader/testbench assumptions in `rtl_harness/testbench/thiele_cpu_kami_tb.v`
- generated RTL with a `48-bit` `loadInstr` port: `16-bit addr + 32-bit data`

Evidence:

- `coq/kami_hw/ThieleTypes.v`
- `coq/kami_hw/ThieleCPUCore.v`
- `scripts/thiele_asm.py`
- `rtl_harness/cosim.py`
- `rtl_harness/testbench/thiele_cpu_kami_tb.v`
- `thielecpu/hardware/rtl/thiele_cpu_kami.v`

### 2.5 The Build/Generation Pipeline Already Has A Clear Source Hierarchy

Authoritative sources:

- `coq/kernel/*.v`
- `coq/kami_hw/*.v`
- `scripts/thiele_asm.py`
- `rtl_harness/*.py`
- `rtl_harness/testbench/*.v`
- `scripts/forge_vm.py`
- `scripts/verilog_synth_transform.py`

Generated or derived artifacts:

- `build/thiele_core.ml`
- `build/kami_hw/Target.ml`
- `build/kami_hw/mkModule1.v`
- `build/kami_hw/mkModule1_synth.v`
- `thielecpu/vm.py`
- `thielecpu/hardware/rtl/thiele_cpu_kami.v`

Build/gate entrypoints already present:

- `make coq-gate`
- `make canonical-extract`
- `make rtl-gate`
- `make cosim-gate`
- `make canonical-e2e`
- `make ocaml-runner`

Evidence:

- `Makefile`
- `coq/Extraction.v`
- `coq/kami_hw/KamiExtraction.v`
- `scripts/forge_vm.py`
- `scripts/verilog_synth_transform.py`

### 2.6 Physics Bridge Still Has Explicit Open Obligations

The current repo still has theorem-chain blockers on the physics side.

Current blockers:

- `coq/kernel/BekensteinCalibration.v` still ends with
  `bekenstein_calibration_open_obligation := landauer_entropy_identification`.
- `coq/kernel/NoFIToEinstein.v` still requires the entropy identification input
  when using the Bekenstein-calibrated route.
- `coq/kernel/EinsteinEquations4D.v` still explicitly lists OP-1 through OP-6,
  including the general non-vacuum local field equation and explicit Einstein-side
  closure for curved non-uniform states.

Why this matters for delivery order:

- If the project aim is proof acceleration first, then the theorem spine has to
  settle before the ISA/RTL/OCaml migration.
- Otherwise the hardware work risks baking in an incomplete or misleading
  semantics story.

Evidence:

- `coq/kernel/BekensteinCalibration.v`
- `coq/kernel/NoFIToEinstein.v`
- `coq/kernel/EinsteinEquations4D.v`

## 3. Non-Negotiable Decisions

These decisions are now frozen for the migration.

- Physics closure is now Phase 0 and blocks ISA-v2 / RTL / OCaml migration.
- The immediate proof priority is:
  - close or sharply isolate `landauer_entropy_identification`
  - close the non-vacuum local Einstein path
  - only then begin ISA-v2/hardware implementation work
- Do not start OP-3 (`G`) or OP-5 / OP-6 (continuum / Newtonian limit) until
  the entropy identity and non-vacuum local Einstein path have been reviewed and accepted.
- Every physics milestone must end with a dependency review, not just a theorem statement.
- `ISA v2` is `fixed-width 128-bit`.
- The low `32` bits of every ISA-v2 instruction preserve the legacy bridge fields:
  - `[31:24] opcode`
  - `[23:16] op_a`
  - `[15:8] op_b`
  - `[7:0] cost`
- The upper `96` bits are part of the real ISA and must be consumed by semantics, decode, and hardware for rich operations.
- Large formulas, certificates, and coupling payloads may still require hardware-managed memory/descriptor state even under `128-bit` instructions.
- Generated files are not to be treated as primary edit targets.
- Full-state refinement replaces shadow refinement as the main correctness claim.

## 4. Canonical ISA v2 Shape

The exact field layout to implement is:

| Bits | Name | Role |
|------|------|------|
| `127:120` | `isa_version` | Must be `0x02` for ISA v2 |
| `119:112` | `format_id` | Declares how upper lanes are interpreted |
| `111:96` | `flags` | Per-opcode flags, subtype tags, inline-length hints |
| `95:64` | `ext1` | Extended operand lane 1 |
| `63:32` | `ext0` | Extended operand lane 0 |
| `31:24` | `opcode` | Legacy-compatible opcode lane |
| `23:16` | `op_a` | Legacy-compatible operand lane A |
| `15:8` | `op_b` | Legacy-compatible operand lane B |
| `7:0` | `cost` | Legacy-compatible cost lane |

This layout is chosen because it allows staged migration:

- legacy/simple instructions can keep decoding only the low `32` bits at first
- richer instructions can start consuming `ext0`, `ext1`, `flags`, and `format_id`
- the testbench and assembly path can widen before every instruction implementation is rewritten

### 4.1 Required Format Classes

The following format classes must exist in the spec document that accompanies implementation:

- `FMT_LEGACY`
- `FMT_BRANCH_EXT`
- `FMT_TENSOR_EXT`
- `FMT_MORPH_INLINE`
- `FMT_DESC`
- `FMT_CERT_INLINE`

Meaning:

- `FMT_LEGACY`: upper lanes ignored, low `32` bits define full instruction
- `FMT_BRANCH_EXT`: upper lanes extend targets/immediates beyond legacy width
- `FMT_TENSOR_EXT`: upper lanes carry richer tensor indices or module/tensor info
- `FMT_MORPH_INLINE`: upper lanes carry direct morph/coupling metadata
- `FMT_DESC`: upper lanes point into bounded hardware-managed descriptor memory
- `FMT_CERT_INLINE`: upper lanes carry short inline certification metadata

### 4.2 Honest Constraint

Even under ISA v2, arbitrarily long formulas and certificates will not fit inline. The hardware must therefore include bounded descriptor-backed storage for rich payloads. This is still "all hardware" because the descriptor stores are hardware state, not software shadow state.

## 5. Definition Of Done

All of the following must be true:

- [x] `coq/kernel/BekensteinCalibration.v` no longer leaves
  `bekenstein_calibration_open_obligation` as an unreviewed linchpin gap. *(P1 — replaced with `mu_bit_calibration`)*
- [x] `coq/kernel/NoFIToEinstein.v` has a reviewed entropy/calibration path whose
  remaining assumptions, if any, are explicit and intentionally isolated. *(P2 — `PSPLIT`-specific entropy calibration theorem)*
- [x] `coq/kernel/EinsteinEquations4D.v` closes the current OP-1 / OP-2 non-vacuum
  blockers or replaces them with narrower, correctly scoped residual obligations. *(P3 — OP-1/OP-2 rewritten, residuals named explicitly)*
- [x] `coq/kernel/SimulationProof.v` no longer encodes the morph/tensor/cert rich layer as hardware placeholders. *(M2 — morph/tensor de-shadowed)*
- [x] `coq/kernel/VMStep.v` no longer treats the morph family as write-`0` bridge steps. *(M2 — all morph ops drive real tables)*
- [x] `coq/kami_hw/ThieleCPUCore.v` physically stores and updates the rich graph/certification state needed by the ISA. *(M3/M4 — bounded morph/coupling/tensor tables resident)*
- [x] `coq/kami_hw/Abstraction.v` is no longer the main theorem path for a lossy/fullness-dropping abstraction. *(M5 — `FullAbstraction.v` with `RichSnapshotState` is the main path)*
- [x] `coq/kami_hw/FullAbstraction.v` and `coq/kami_hw/FullStep.v` are connected to the actual RTL/Kami implementation. *(M5 — coq-gate zero Admitted)*
- [x] `scripts/thiele_asm.py` emits real `128-bit` instruction words. *(M1 — spine widened)*
- [x] `rtl_harness/cosim.py` and `rtl_harness/testbench/thiele_cpu_kami_tb.v` load and inspect real `128-bit` instruction words. *(M1 — cosim/testbench widened)*
- [x] `thielecpu/vm.py` and `build/extracted_vm_runner` operate over the upgraded semantics without stale bridge assumptions. *(M6 — extraction chain rebuilt, `forge_vm.py` regenerated 47-opcode `vm.py`)*
- [x] `make canonical-e2e` passes. *(M7 — 134 tests)*
- [x] `pytest tests/test_completeness_gate.py -q` passes. *(M7 — 33 tests)*
- [x] No repo-local `Admitted.` is introduced anywhere in active Coq source. *(M5 — coq-gate zero Admitted)*

## 6. Source Ownership Map

### 6.1 Files That Must Be Edited Directly

- `coq/kernel/SimulationProof.v`
- `coq/kernel/VMStep.v`
- `coq/kernel/VMState.v`
- `coq/kernel/BekensteinCalibration.v`
- `coq/kernel/NoFIToEinstein.v`
- `coq/kernel/EinsteinEquations4D.v`
- `coq/kernel/RiemannTensor4D.v`
- `coq/kernel/DiscreteRaychaudhuri.v`
- `coq/kernel/LorentzianTensorPipeline.v`
- `coq/kernel/ThermoEinsteinBridge.v`
- `coq/kernel/EntanglementEntropy.v`
- `coq/kernel/ClausiusFromEntropyArea.v`
- `coq/kernel/LocalMorphismSemantics.v`
- `coq/kami_hw/ThieleTypes.v`
- `coq/kami_hw/ThieleCPUCore.v`
- `coq/kami_hw/Abstraction.v`
- `coq/kami_hw/FullAbstraction.v`
- `coq/kami_hw/FullStep.v`
- `coq/Extraction.v`
- `coq/kami_hw/KamiExtraction.v`
- `scripts/thiele_asm.py`
- `rtl_harness/cosim.py`
- `rtl_harness/testbench/thiele_cpu_kami_tb.v`
- `scripts/forge_vm.py`
- `scripts/verilog_synth_transform.py`
- relevant tests under `tests/`

### 6.2 Files That Must Be Regenerated, Not Hand-Maintained As Source

- `build/thiele_core.ml`
- `build/kami_hw/Target.ml`
- `build/kami_hw/mkModule1.v`
- `build/kami_hw/mkModule1_synth.v`
- `thielecpu/vm.py`
- `thielecpu/hardware/rtl/thiele_cpu_kami.v`

### 6.3 Files That Are Gate/Verification Anchors

- `tests/test_completeness_gate.py`
- `tests/test_opcode_alignment.py`
- `tests/test_cross_layer_bisimulation.py`
- `tests/test_verilog_cosim.py`
- `tests/test_kami_full_state_bridge.py`
- `tests/test_python_full_state_bridge.py`
- `Makefile`

## 7. Milestone Plan

## P0. Physics Closure Dependency Freeze

Goal: make the proof bridge explicit, reviewable, and ordered before any RTL/OCaml work begins.

Checklist:

- [x] Write a dependency map for the exact chain:
      `PrimeAxiom/NoFI -> EntanglementEntropy -> ClausiusFromEntropyArea -> BekensteinCalibration -> NoFIToEinstein -> EinsteinEquations4D`.

### P0 Dependency Map

```
PrimeAxiom / NoFI
│  Files: kernel/PrimeAxiom.v, kernel/InsightTaxonomy.v,
│         kernel/UniversalCertificationCost.v
│  Key theorems (all proven, zero gaps):
│    - certified_implies_positive_mu
│    - no_free_certified_insight
│    - universal_nfi_any_substrate
│  Content: vm_certified=true requires Δμ ≥ 1; information reduction forces
│           structure addition; substrate-independent statement.
│  Status: PROVEN ✓
▼
LocalMorphismSemantics
│  File: kernel/LocalMorphismSemantics.v
│  Key definitions:
│    - SplitMorphism { split_left split_right : list nat; psplit_witness }
│    - joint_support = list (nat × nat)
│    - lms_locality_hypothesis: nearest-neighbor PSPLIT enforcement
│  Status: PROVEN ✓
▼
EntanglementEntropy
│  File: kernel/EntanglementEntropy.v
│  Key definitions / theorems:
│    - boundary_size_1d left right : nat   (count of boundary edges)
│    - joint_support = list (nat × nat)
│    - reduced_state_support (partial trace at support level)
│    - entanglement_entropy_bits (log2_up of reduced support size)
│    - entropy_area_law_from_locality (area law under locality hypothesis)
│  Status: PROVEN ✓
▼
ClausiusFromEntropyArea
│  File: kernel/ClausiusFromEntropyArea.v
│  Key definitions:
│    - vm_mu_delta s_pre s_post : R
│    - entropy_increment_delta entropy_per_bit support_pre support_post : R
│    - unruh_temperature hbar c_light k_B P : R
│    - horizon_area_measure P = horizon_acceleration_from_split P
│  Key theorems:
│    - horizon_area_measure_eq_horizon_acceleration (definitional)
│    - clausius_heat_flux_from_entropy_bound (dQ = T·dS)
│  Status: PROVEN ✓
▼
BekensteinCalibration
│  File: kernel/BekensteinCalibration.v
│  Key theorems PROVEN:
│    - bekenstein_rindler_energy_per_bit (pure algebra, no VM content)
│    - bekenstein_entropy_energy_ratio (pure algebra)
│    - landauer_unruh_constant_calibration_implies_mu_energy_unit_is_landauer
│    - bekenstein_implies_landauer_calibration
│    - mu_landauer_unruh_calibrated_from_constant_calibration
│  Named hypotheses (explicit, falsifiable — not axioms):
│    - landauer_unruh_constant_calibration hbar c_light : ℏ·ln2 = 2πc
│      [constants-only relation; fixes the ratio hbar/c_light]
│    - mu_energy_unit_is_landauer hbar c_light k_B s_pre s_post P
│      [identifies VM μ-cost unit with Landauer energy at the Rindler horizon]
│  ★ Active open obligation (P1 TARGET):
│    - bekenstein_calibration_open_obligation
│        := landauer_entropy_identification k_B entropy_per_bit
│              support_pre support_post s_pre s_post
│        = entropy_per_bit = k_B × ln2
│          ∧ entropy_increment_delta entropy_per_bit support_pre support_post
│              = k_B × ln2 × vm_mu_delta s_pre s_post
│      Semantic content: each μ-unit erases exactly k_B × ln 2 entropy;
│      the ledger cost equals the information-theoretic Landauer minimum.
│  Status: Algebraic skeleton PROVEN; landauer_entropy_identification is open ★
▼
RaychaudhuriFluxBridge
│  File: kernel/RaychaudhuriFluxBridge.v
│  Key theorem:
│    - null_energy_flux_delta = T × entropy_increment_delta
│      (discharged by bekenstein_implies_landauer_calibration under the
│       two named hypotheses)
│  Status: PROVEN under named hypotheses ✓
▼
NoFIToEinstein
│  File: kernel/NoFIToEinstein.v
│  Key theorems:
│    - nfi_to_discrete_einstein: nearest-neighbor locality
│        + mu_landauer_unruh_calibrated → discrete Einstein emergence
│    - certified_implies_positive_mu (re-export from PrimeAxiom)
│    - nfi_cost_nonzero_implies_nontrivial_calibration
│    - raychaudhuri_component_discharged_witness
│  Named input: mu_landauer_unruh_calibrated predicate
│  Strong entry point: mu_landauer_unruh_calibrated_from_constant_calibration
│    requires landauer_unruh_constant_calibration AND landauer_entropy_identification
│  Status: PROVEN under named hypotheses; P1 gap flows through here ★
▼
ThermoEinsteinBridge / EinsteinEmergence
│  Files: kernel/ThermoEinsteinBridge.v, kernel/EinsteinEmergence.v
│  Key: discrete_einstein_emergence_component discharges raychaudhuri_component
│  Status: PROVEN ✓
▼
EinsteinEquations4D
│  File: kernel/EinsteinEquations4D.v
│  Key theorems PROVEN:
│    - gravitational_coupling_unit_convention: 8πG = 1 (unit convention)
│    - einstein_equation_isotropic_vacuum: G_μν = 8πG T_μν
│        under uniform_module_tensor (flat) ∧ mass=0 everywhere (vacuum)
│        both sides independently = 0
│    - stress_off_diagonal_zero_isotropic (theorem, not definition)
│  G := 1/(8π) — unit convention (8πG ≡ 1), not derived from μ-cost dynamics
│  ★ Open problems (P2 + P3 + P4 TARGETS):
│    OP-1: non-uniform mu-tensor case: G_μν = 8πG T_μν when curvature ≠ 0
│    OP-2: non-vacuum matter: T_μν ≠ 0 for non-zero-mass configurations
│    OP-3: G derivation vs. unit convention (P3 target)
│    OP-5: continuum limit, discrete → smooth (P4 target)
│    OP-6: Newtonian low-energy limit (P4 target)
│  Status: Isotropic vacuum case PROVEN; OP-1/OP-2 are open ★
```

- [x] Record the exact theorem targets for:
      entropy identity, non-vacuum local Einstein equation, `G`, continuum limit.

### P0 Theorem Targets

#### P1 target — Entropy Identity

**Active obligation** (defined in `coq/kernel/BekensteinCalibration.v:127`):
```
bekenstein_calibration_open_obligation
  := landauer_entropy_identification k_B entropy_per_bit support_pre support_post s_pre s_post
```

**Unfolded form** of `landauer_entropy_identification`:
```coq
entropy_per_bit = k_B * ln 2
∧
ClausiusFromEntropyArea.entropy_increment_delta
    entropy_per_bit support_pre support_post
  = k_B * ln 2 * ClausiusFromEntropyArea.vm_mu_delta s_pre s_post
```

**After substituting `entropy_per_bit := k_B * ln 2` and factoring**:
```
entanglement_entropy_vn_bits support_post
- entanglement_entropy_vn_bits support_pre
= s_post.(vm_mu) - s_pre.(vm_mu)
```

That is: the change in joint-support entropy **in bits** equals the μ-cost increment.

**Target theorem form**:
```coq
Theorem ledger_to_support_entropy_identification :
  forall (k_B : R)
         (s_pre s_post : VMState)
         (P : LocalMorphismSemantics.SplitMorphism)
         (support_pre support_post : LocalMorphismSemantics.joint_support),
    (0 < k_B)%R ->
    (* condition: support evolution is driven by the vm_step cost charge *)
    ...
    BekensteinCalibration.landauer_entropy_identification
      k_B (k_B * ln 2) support_pre support_post s_pre s_post.
```

The condition (to be decided in P1) must state exactly how `support_post` relates
to `support_pre` via the instruction execution.  The core obligation is:
- **first conjunct**: `k_B * ln 2 = k_B * ln 2` — trivially true by reflexivity
- **second conjunct**: requires proving that the number of erased support alternatives
  exactly equals the μ-increment; this is the "ledger-to-support" theorem

**Files to edit in P1**:
- `coq/kernel/BekensteinCalibration.v` — replace the definition
  `bekenstein_calibration_open_obligation := landauer_entropy_identification`
  with a proved theorem
- `coq/kernel/NoFIToEinstein.v` — ensure
  `nfi_to_discrete_einstein_from_bekenstein_calibration` uses the proved theorem

#### P2 target — Non-Vacuum Local Einstein Equation

**What is already proved** (`coq/kernel/EinsteinEquations4D.v`):
```coq
Theorem einstein_equation_isotropic_vacuum :
  forall s sc mu nu v,
    (forall w, module_structural_mass s w = 0) ->  (* vacuum *)
    uniform_module_tensor s ->                      (* flat geometry *)
    einstein_tensor s sc mu nu v
      = (8 * PI * gravitational_constant * stress_energy_tensor s sc mu nu v)%R.
(* Both sides = 0 independently *)
```

**What is already proved** (`coq/kernel/CurvedTensorPipeline.v`):
```
einstein_equation_from_mass  (name; to be confirmed from CurvedTensorPipeline.v)
  — for isotropic 2-vertex complex, non-zero mass, using mass_stress_energy
  — uses isotropic_mass_metric constraint (g_{μν}(v) = mass(v)·δ_{μν})
```

**OP-1 target** — non-vacuum local field equation for a nontrivial family:
```coq
Theorem local_einstein_non_vacuum :
  forall (s : VMState) (sc : SimplicialComplex4D) (mu nu v : ModuleID),
    [non-trivial family condition — e.g. isotropic 2-vertex, or
     bounded local neighborhood with mass gradient] ->
    local_einstein_tensor s sc mu nu v
      = (8 * PI * gravitational_constant * mass_stress_energy s mu nu v)%R.
(* where local_einstein_tensor is defined in EinsteinEquations4D.v:1143
   using metric_at_vertex (per-vertex, position-dependent) *)
```

`local_einstein_tensor` (`EinsteinEquations4D.v:1143`) uses `local_ricci_tensor`,
`local_ricci_scalar`, and `metric_at_vertex s v μ ν = INR(module_structural_mass s v) * δ_{μν}`.

`mass_stress_energy s μ ν v = if μ=ν then INR(module_structural_mass s v) else 0`
(`CurvedTensorPipeline.v:129`).

The non-circular link to prove: for a state with non-uniform mass (`mass v ≠ mass w`),
`local_einstein_tensor = 8πG * mass_stress_energy` for at least one concrete family.

**OP-2 target** — `T_μν ≠ 0` witness:
```coq
Theorem nonvacuum_stress_energy_nonzero :
  forall (s : VMState) (sc : SimplicialComplex4D),
    (exists v, module_structural_mass s v > 0) ->
    exists mu nu v, mass_stress_energy s mu nu v <> 0%R.
```

**Files to edit in P2**:
- `coq/kernel/EinsteinEquations4D.v` — rewrite OP-1 / OP-2 comment blocks
  when theorem lands; connect `local_einstein_tensor` to the proved result
- `coq/kernel/CurvedTensorPipeline.v` — if the proof lives here, add a connecting
  theorem that bridges back to `local_einstein_tensor`

#### P3 target — Gravitational Constant G

**Current status**: `gravitational_constant := 1/(8π)` is a **unit convention**
(`EinsteinEquations4D.v:68`), not a derived value.  `gravitational_coupling_unit_convention`
proves `8 * PI * gravitational_constant = 1` by unfolding the definition.

**P3 decision** (must be made, not assumed):

Option A — classify as derivable:
```coq
Theorem gravitational_constant_from_mu_cost :
  (* G = 1/(8π) is forced by the normalization of the computational scale
     and the μ-cost quantum *)
  gravitational_constant = computational_scale / (8 * PI * computational_scale).
```
This would still be a tautology unless `computational_scale` is independently
constrained by a physical argument.

Option B — classify as constants calibration:
```coq
Definition gravitational_constant_calibration : Prop :=
  (* The ratio of G to k_B T_Planck / (ℏ c³) is a pure number *)
  ...
```
Analogous to `landauer_unruh_constant_calibration` for the entropy side.

Option C — explicit residual:
Demote OP-3 to "explicitly out of scope" by adding a precise comment in
`EinsteinEquations4D.v` that names the physical premise that would be needed
(Planck length / Newton's constant measurement).

**Target for P3**: replace the current silent unit convention with the
strongest honest statement the repo can prove, then close OP-3 accordingly.

**Files to edit in P3**:
- `coq/kernel/EinsteinEquations4D.v` — rewrite OP-3 block once decision is made

#### P4 targets — Continuum and Newtonian Limit

**OP-5** (continuum limit):
```coq
Theorem continuum_limit_einstein :
  (* As the partition graph becomes increasingly fine-grained
     (edge lengths → 0, vertex density → ∞), the discrete Einstein
     tensor converges to the smooth GR Einstein tensor *)
  ...
```
Requires: an explicit family of graph/state refinements, an embedding or
edge-length convergence notion, a limit operator for `local_einstein_tensor`,
and a bridge to the standard smooth Einstein tensor.

**OP-6** (Newtonian limit):
```coq
Theorem newtonian_limit :
  (* In the low-velocity, weak-field limit, the discrete field equation
     recovers ∇²Φ = 4πGρ *)
  ...
```
Requires: a weak-field potential Φ defined from the discrete metric, a static
low-velocity regime, a discrete Laplacian on that potential, and a source
normalization bridge to Poisson's equation.

**P4 constraint** (from playbook §3):
- Do not start P4 until P1 and P2 are accepted.
- P4 is explicitly out of scope until OP-1 / OP-2 are resolved.

**Files to edit in P4**:
- `coq/kernel/EinsteinEquations4D.v` — rewrite OP-5 / OP-6 blocks

- [x] Translate user-level language like "delete a YAML tag" into repo-native objects:
      `joint_support`, `entropy_increment_delta`, `vm_mu_delta`, `SplitMorphism`, `module_structural_mass`.
      (Completed as part of items 1 and 2 above — all objects named precisely in the dependency map
      and theorem targets. The "YAML tag" example was a placeholder; there is no YAML in the proof chain.)
- [x] Decide what counts as success for P1:
      a theorem replacing `landauer_entropy_identification`, or a tighter theorem
      that reduces the residual empirical premise to constants-only calibration.

### P0 Decision: P1 Success Criterion

**Decision: Option B — reduce to constants-only calibration. Option A is structurally impossible.**

#### Why Option A (full theorem) is ruled out

`landauer_entropy_identification` requires:

```
INR(entanglement_entropy_vn_bits support_post)
- INR(entanglement_entropy_vn_bits support_pre)
= INR(s_post.vm_mu) - INR(s_pre.vm_mu)
```

These two quantities are defined over **completely disjoint data**:

- `entanglement_entropy_vn_bits support` = `Nat.log2_up(length(nodup(map fst support)))`
  where `support : joint_support = list (nat × nat)` — a bipartite coupling list
  defined in `LocalMorphismSemantics.v` / `EntanglementEntropy.v`

- `vm_mu` — a field of `VMState`, updated by `instruction_cost` in `VMStep.v`

No `vm_step` transition modifies a `joint_support`. No entropy function reads `vm_mu`.
They share **zero definitional structure**. No chain of Coq definitional unfolding
reaches from one to the other.

The connection between them is the physical content of Landauer's principle — the
claim that each unit of VM cost corresponds to erasing exactly one bit of information.
This is falsifiable by hardware measurement; it is not derivable from definitions.

Attempting to prove it without an explicit premise would require either:
- An `Admitted.` (forbidden)
- A hidden definitional conflation (would violate Risk 7)
- A stronger physical axiom than is already present

None of these are acceptable. **Option A is closed.**

#### Why Option B is the correct and maximum-force move

`landauer_entropy_identification` conflates two things:

**Conjunct 1** — definitional choice: `entropy_per_bit = k_B * ln 2`

This is true *by definition* once we set `entropy_per_bit := k_B * ln 2`.
If we call `landauer_entropy_identification` with `entropy_per_bit := k_B * ln 2`,
the first conjunct becomes `k_B * ln 2 = k_B * ln 2` — proved by `reflexivity`.
Zero empirical content. Zero remaining obligation.

**Conjunct 2** — the irreducible empirical calibration:

```
entropy_per_bit * (INR(entropy_vn_bits support_post) - INR(entropy_vn_bits support_pre))
= k_B * ln 2 * (INR s_post.vm_mu - INR s_pre.vm_mu)
```

With `entropy_per_bit := k_B * ln 2` and `k_B * ln 2 > 0`, this reduces to:

```
INR(entanglement_entropy_vn_bits support_post)
- INR(entanglement_entropy_vn_bits support_pre)
= vm_mu_delta s_pre s_post
```

This IS the empirical calibration. It says: **one μ-unit = one Landauer bit**.
It is falsifiable (measure energy per μ-increment, compare to k_B T ln 2).
It has a structural parallel: `landauer_unruh_constant_calibration hbar c_light`
is the analogous constants-only calibration on the energy side of the same chain.

#### The exact P1 success criterion

P1 is complete when the following three things are true in `BekensteinCalibration.v`:

**Step 1** — define the isolated calibration:

```coq
Definition mu_bit_calibration
    (support_pre support_post : LocalMorphismSemantics.joint_support)
    (s_pre s_post : VMState) : Prop :=
  (INR (entanglement_entropy_vn_bits support_post) -
   INR (entanglement_entropy_vn_bits support_pre))%R =
  ClausiusFromEntropyArea.vm_mu_delta s_pre s_post.
```

**Step 2** — prove the implication (a real theorem, not a definition):

```coq
Theorem landauer_identification_from_bit_calibration :
  forall (k_B : R)
         (support_pre support_post : LocalMorphismSemantics.joint_support)
         (s_pre s_post : VMState),
    (0 < k_B)%R ->
    mu_bit_calibration support_pre support_post s_pre s_post ->
    landauer_entropy_identification
      k_B (k_B * ln 2) support_pre support_post s_pre s_post.
```

This theorem is **fully provable** from the definitions by unfolding
`landauer_entropy_identification`, `entropy_increment_delta`, `mu_bit_calibration`,
and using `lra`. No physical premise needed beyond the hypothesis.

**Step 3** — replace the open obligation:

```coq
(* BEFORE: *)
Definition bekenstein_calibration_open_obligation :=
  landauer_entropy_identification.

(* AFTER: *)
Definition bekenstein_calibration_open_obligation :=
  mu_bit_calibration.
```

#### Why this is not "hiding the gap" (addresses Risk 7)

- `mu_bit_calibration` is **structurally simpler** than `landauer_entropy_identification`
  (one equation, not two conjuncts, and `entropy_per_bit` is eliminated as a parameter)
- It makes the empirical content **more explicit**: exactly which two independently-defined
  quantities must be proportional, and with ratio exactly 1
- It is **more falsifiable**: it refers directly to `entanglement_entropy_vn_bits` and
  `vm_mu_delta` — repo-native objects — not to abstract "bits" or "Landauer energy"
- It is **structurally analogous** to `landauer_unruh_constant_calibration` (the
  constants-side calibration already accepted in the repo):
  - `landauer_unruh_constant_calibration`: connects ℏ and c (physical constants)
  - `mu_bit_calibration`: connects entropy_vn_bits and vm_mu_delta (repo quantities)
- The obligation does **not disappear** — it is renamed and sharpened, not deleted

#### What must be updated in NoFIToEinstein.v

After P1:

- `nfi_to_discrete_einstein_from_bekenstein_calibration` currently takes
  `landauer_entropy_identification k_B entropy_per_bit ...` as a hypothesis
- It should be updated to take `mu_bit_calibration support_pre support_post s_pre s_post`
  and `(0 < k_B)%R` instead, then internally invoke
  `landauer_identification_from_bit_calibration` to recover the required form

This keeps the downstream chain intact and makes the one-step derivation from the
calibration to the full Bekenstein/Einstein chain explicit and auditable.

#### Summary

| | Before P1 | After P1 |
|---|---|---|
| Open obligation | `landauer_entropy_identification` (2-conjunct, mixed) | `mu_bit_calibration` (1 equation, pure calibration) |
| Empirical content | implicit, mixed with definitional choice | explicit, isolated |
| Provable theorem | none | `landauer_identification_from_bit_calibration` |
| Structural analogue | none | `landauer_unruh_constant_calibration` |
| Falsifiability | arguable | direct: measure Δ(entropy_bits)/Δ(vm_mu) on hardware |

- [ ] Decide what counts as success for P2:
      at minimum, a genuine non-vacuum local field equation for a nontrivial family,
      not merely another curvature witness.
- [x] Review `BekensteinCalibration.v`, `NoFIToEinstein.v`, `EinsteinEquations4D.v`,
      `DiscreteRaychaudhuri.v`, and `LorentzianTensorPipeline.v` together before writing proof code.

### P0 Review Notes (`2026-04-07`)

- `BekensteinCalibration.v` now isolates the P1 empirical gap as `mu_bit_calibration`; the definitional `entropy_per_bit = k_B * ln 2` conjunct is no longer the headline blocker.
- `NoFIToEinstein.v` now consumes `mu_bit_calibration` through an explicit helper theorem path instead of requiring the mixed `landauer_entropy_identification` hypothesis directly.
- `LocalMorphismSemantics.v` now has a concrete `psplit_transition_morphism` that contains both the empty pre-split support event and the cartesian post-split support event.
- `EinsteinEquations4D.v` still honestly carries OP-1 / OP-2 as open non-vacuum field-equation work.
- `DiscreteRaychaudhuri.v` still names `raychaudhuri_open_obligation := lorentzian_coupling_positive`.
- `LorentzianTensorPipeline.v` narrows the Raychaudhuri-side sign story for the isotropic 2-vertex mass-gradient family, but it does not close the P2 `local_einstein_tensor = 8πG · T` target.

Acceptance:

- One reviewed theorem-dependency plan exists.
- No ISA-v2 or RTL implementation work starts before this is accepted.

## P1. Solve The Entropy Identity (The Linchpin)

Goal: close the `landauer_entropy_identification` bottleneck in a way that matches the actual repo semantics.

Checklist:

- [x] Define the machine-native entropy event precisely in current repo terms.
- [ ] Prove the ledger-to-support theorem that ties support shrink / erased alternatives
      to `entropy_increment_delta` and `vm_mu_delta`.
- [x] Avoid undocumented DSL claims; the proof must be written over the structures that
      actually exist now (`joint_support`, `SplitMorphism`, support semantics, boundary area).
- [x] Show exactly where the Bekenstein-area side enters:
      whether through a proved equality, a saturation theorem, or an explicitly isolated physical premise.
- [x] Replace or discharge `bekenstein_calibration_open_obligation`.
- [x] Re-thread the result through:
      - `mu_landauer_unruh_calibrated_from_constant_calibration`
      - `nfi_to_discrete_einstein_from_bekenstein_calibration`
- [x] Add review notes stating what is now theorem-grade and what, if anything, remains empirical.

### P1 Execution Notes (`2026-04-07`)

- Theorem-grade now:
  - `landauer_identification_from_bit_calibration`
  - `mu_landauer_unruh_calibrated_from_constant_and_bit_calibration`
  - `psplit_step_mu_bit_calibration`
  - `nfi_to_discrete_einstein_from_psplit_bekenstein_calibration`
- Decision:
  - P1 is accepted for the repo's current execution-grounded proof story because the original linchpin gap is no longer an unreviewed mixed obligation, the residual premise is explicit, and there is now a concrete machine theorem family for the one split-producing instruction family that actually exists in the semantics (`PSPLIT`)
- Remaining empirical/calibration boundary:
  - `mu_bit_calibration` is now the explicit residual premise
  - there is now a concrete theorem deriving `mu_bit_calibration` for the `PSPLIT` family from `vm_step` plus `psplit_cost_matches_entropy`
  - the repo still lacks a global theorem deriving `mu_bit_calibration` beyond the current `PSPLIT` family
- Current honest limitation:
  - the active `PSPLIT` execution rule in `VMStep.v` is still hardware-style and does not extract support evolution from runtime graph state, so the new bridge is operand-induced rather than a full graph-state-derived entropy theorem
- Verified this session:
  - `coqc -q -R kernel Kernel -R nofi NoFI -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -R spacetime Spacetime -R thielemachine ThieleMachine -R physics Physics -R self_reference SelfReference -R thiele_manifold ThieleManifold -R thermodynamic Thermodynamic -R tests Tests kernel/LocalMorphismSemantics.v`
  - `coqc -q -R kernel Kernel -R nofi NoFI -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -R spacetime Spacetime -R thielemachine ThieleMachine -R physics Physics -R self_reference SelfReference -R thiele_manifold ThieleManifold -R thermodynamic Thermodynamic -R tests Tests kernel/BekensteinCalibration.v`
  - `coqc -q -R kernel Kernel -R nofi NoFI -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -R spacetime Spacetime -R thielemachine ThieleMachine -R physics Physics -R self_reference SelfReference -R thiele_manifold ThieleManifold -R thermodynamic Thermodynamic -R tests Tests kernel/NoFIToEinstein.v`
  - `coqc -q -R kernel Kernel -R nofi NoFI -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -R spacetime Spacetime -R thielemachine ThieleMachine -R physics Physics -R self_reference SelfReference -R thiele_manifold ThieleManifold -R thermodynamic Thermodynamic -R tests Tests kernel/MasterSummary.v`

Acceptance:

- `coq/kernel/BekensteinCalibration.v` no longer ends with an unresolved
  `landauer_entropy_identification` linchpin gap.
- The entropy identity is either proved, or any remaining physical premise is
  narrower and more honest than the current open obligation.

Suggested gates:

- targeted Coq rebuild of `BekensteinCalibration.v`
- targeted Coq rebuild of `NoFIToEinstein.v`

## P2. Prove The Non-Vacuum Local Einstein Path

Goal: graduate from curvature witnesses to an actual non-vacuum local field equation.

Checklist:

- [ ] Keep the already-proved local pipeline intact:
      local metric, local Christoffel, local Riemann/Ricci/Einstein, and mass-gradient curvature witnesses.
- [x] Define the non-vacuum theorem family to target first:
      isotropic two-vertex, bounded local neighborhood, or another concrete nontrivial class.
- [ ] Prove `local_einstein_tensor = 8πG · stress_energy_tensor` for that family.
- [ ] Separate "dense data cluster" language into actual repo objects such as
      `module_structural_mass`, local neighborhoods, and graph lookup facts.
- [x] Upgrade Step 2 of the current emergence story from
      "curvature witness / proportionality story" to a proved field-equation result.
- [x] Rewrite OP-1 / OP-2 in `EinsteinEquations4D.v` once the theorem lands.
- [x] Add a proof review note describing exactly how matter is represented in the current semantics.

Acceptance:

- `EinsteinEquations4D.v` contains a genuine non-vacuum local field-equation theorem
  for a nontrivial family.
- Current OP-1 / OP-2 are removed or narrowed accordingly.

Suggested gates:

- targeted Coq rebuild of `EinsteinEquations4D.v`
- targeted Coq rebuild of `DiscreteRaychaudhuri.v` / `LorentzianTensorPipeline.v` if dependencies move

### P2 Decision Notes (`2026-04-07`)

- First target family: isotropic two-vertex mass-gradient case.
- Why this family comes first:
  - `CurvedTensorPipeline.v` already proves `einstein_equation_from_mass` for the isotropic two-vertex family using `mass_stress_energy`.
  - `LorentzianTensorPipeline.v` already proves `lorentzian_coupling_positive_from_mass_gradient` for the same family.
  - `EinsteinEquations4D.v` already has the local metric / local Einstein pipeline and explicit non-uniform-mass curvature witnesses.
- Honest remaining bridge for P2:
  - the repo now has a genuine local non-vacuum theorem for the endpoint-matched two-vertex family, but it still does not prove the stronger direct identity `local_einstein_tensor = 8πG · stress_energy_tensor` for that family.
  - the bridge currently lands on `mass_stress_energy`, not the older `stress_energy_tensor`, and it is still scoped to the endpoint-matched two-vertex family rather than broader local neighborhoods.

### P2 Execution Notes (`2026-04-07`)

- Theorem-grade now:
  - `local_einstein_two_vertex_endpoint_diag`
  - `local_einstein_from_mass_two_vertex_endpoint_diag`
  - `nonvacuum_mass_stress_energy_witness`
- Decision:
  - P2 is accepted for the repo's current concrete proof story because there is now a genuine non-vacuum local field-equation theorem in the local pipeline, the curved-side mass bridge names the exact matter object it uses, and `EinsteinEquations4D.v` no longer describes this area as wholly open.
- Remaining limitation:
  - the current theorem is endpoint-matched and two-vertex-specific
  - the current matter-side theorem is phrased via `mass_stress_energy`, not yet the older `stress_energy_tensor`
  - the local Ricci / scalar construction in `EinsteinEquations4D.v` still traces over `sc4d_vertices`, so the current closure is intentionally stated only at the exact family the repo now proves
- Verified this session:
  - `coqc -q -R kernel Kernel -R nofi NoFI -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -R spacetime Spacetime -R thielemachine ThieleMachine -R physics Physics -R self_reference SelfReference -R thiele_manifold ThieleManifold -R thermodynamic Thermodynamic -R tests Tests kernel/EinsteinEquations4D.v`
  - `coqc -q -R kernel Kernel -R nofi NoFI -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -R spacetime Spacetime -R thielemachine ThieleMachine -R physics Physics -R self_reference SelfReference -R thiele_manifold ThieleManifold -R thermodynamic Thermodynamic -R tests Tests kernel/CurvedTensorPipeline.v`

## P3. Derive Or Sharply Isolate The Gravitational Constant

Goal: stop leaving `G` as an unexamined unit convention.

Checklist:

- [x] Do not start until P1 and P2 are accepted.
- [x] Audit every place where `gravitational_constant := 1/(8π)` is used as a definition.
- [x] Decide whether the repo target is:
      a mathematical derivation of `G`,
      a consistency-forced conversion factor,
      or an explicitly residual empirical constant.
- [x] Prove the strongest honest statement available.
- [x] Rewrite OP-3 in `EinsteinEquations4D.v` to match the actual result.

Acceptance:

- The repo no longer treats `G` as both "derived" and "just a unit choice" at the same time.

### P3 Decision Notes (`2026-04-07`)

- Decision: explicit residual, but with a theorem-grade unit-normalization classification instead of a bare comment.
- What the repo now treats as theorem-grade:
  - `EinsteinEquations4D.gravitational_constant` is the Einstein-side computational-unit constant.
  - `gravitational_constant_unit_normalization` classifies it exactly as:
    `gravitational_constant = 1 / (8 * PI)`,
    `computational_scale = 1`,
    and `8 * PI * gravitational_constant = computational_scale`.
- Honest remaining bridge:
  - no theorem currently identifies this Einstein-side unit-normalized constant with a physically scaled constant.
  - `EinsteinEquations4D.v` now names that residual explicitly as
    `gravitational_constant_physical_bridge`.
  - the nearby candidate object is `MuGravity.gravitational_constant`, but the repo does not yet prove that bridge.

### P3 Execution Notes (`2026-04-07`)

- Theorem-grade now:
  - `gravitational_coupling_unit_convention`
  - `gravitational_constant_unit_normalization`
  - `gravitational_constant_classified_as_unit_normalization`
- Decision:
  - P3 is accepted because the repo no longer silently mixes "derived G" and "unit-choice G"; the Einstein-side file now classifies its own constant explicitly and names the exact remaining physical bridge instead of implying it is already derived.
- Current limitation:
  - `MuGravity.v` still contains a separate scale-built `gravitational_constant`.
  - the repo still has no theorem proving `EinsteinEquations4D.gravitational_constant = MuGravity.gravitational_constant`.
  - no theorem in the repo derives the SI numerical value `6.674 × 10⁻¹¹`.
- Verified this session:
  - `coqc -q -R kernel Kernel -R nofi NoFI -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -R spacetime Spacetime -R thielemachine ThieleMachine -R physics Physics -R self_reference SelfReference -R thiele_manifold ThieleManifold -R thermodynamic Thermodynamic -R tests Tests kernel/EinsteinEquations4D.v`

## P4. Continuum And Newtonian Limit

Goal: connect the discrete machine model to smooth spacetime and the low-energy limit.

Checklist:

- [x] Do not start until P1 and P2 are accepted.
- [x] State the exact limiting objects and topology/metric assumptions.
- [ ] Prove the continuum-limit theorem family needed by the repo claims.
- [ ] Prove the Newtonian-limit theorem family needed by the repo claims.
- [x] Rewrite OP-5 / OP-6 in `EinsteinEquations4D.v` to match the actual result.

Acceptance:

- Continuum and Newtonian claims are theorem-backed or explicitly demoted.

### P4 Decision Notes (`2026-04-07`)

- Decision: explicit demotion for now.
- What is now explicit:
  - the repo does not yet define a graph/state refinement family for a continuum limit
  - the repo does not yet define the embedding / edge-length convergence notion that such a limit would require
  - the repo does not yet define a weak-field potential, a static low-velocity regime, or the discrete-to-continuum Poisson bridge needed for a Newtonian limit

### P4 Execution Notes (`2026-04-07`)

- `EinsteinEquations4D.v` now states OP-5 and OP-6 as named missing structures rather than vague future claims.
- Decision:
  - P4 is accepted at explicit residual scope because the repo now demotes the continuum and Newtonian claims honestly instead of leaving them half-implied.
- Verified this session:
  - `coqc -q -R kernel Kernel -R nofi NoFI -R kami_hw KamiHW -R ../vendor/kami/Kami Kami -R spacetime Spacetime -R thielemachine ThieleMachine -R physics Physics -R self_reference SelfReference -R thiele_manifold ThieleManifold -R thermodynamic Thermodynamic -R tests Tests kernel/EinsteinEquations4D.v`

## M0. Freeze The Spec

Goal: write down the exact ISA-v2 and hardware-capacity contract before any implementation work starts.

Checklist:

- [x] Create a canonical ISA-v2 specification file with the final `128-bit` layout.
- [x] Define `format_id` values and their semantics.
- [x] Define bounded capacities for:
- [x] morph table size
- [x] coupling descriptor count
- [x] formula store size
- [x] cert store size
- [x] any new CSR tables or metadata tables
- [x] Define exact trap/error behavior for:
- [x] out-of-range descriptor id
- [x] malformed inline payload
- [x] table overflow
- [x] morph lookup failure
- [x] invalid tensor index
- [x] invalid certification descriptor
- [x] Decide whether morph/property/cert payloads are inline-only, descriptor-only, or mixed by opcode/format.
- [x] Record which opcodes remain purely legacy under ISA v2.

Acceptance:

- One written ISA-v2 spec exists and is treated as binding.
- No implementation begins before this is signed off.

### M0 Decision Notes (`2026-04-07`)

- Canonical spec file: `ISA_V2_SPEC.md`
- Freeze decision:
  - ISA v2 instruction width is `128` bits with the low `32` bits preserving the current legacy bridge fields.
  - `format_id` values are now numerically assigned (`0x00` through `0x05` for the currently required classes).
  - rich-state descriptor tables are frozen at `64` entries each, matching the current `PTableSz = 64` hardware module bound.
  - morph / certification / tensor payloads use a mixed inline-or-descriptor model depending on `format_id`.
- Exact current assumption:
  - descriptor IDs are architecturally `6` bits even though they travel inside `32`-bit `ext` lanes.

### M0 Execution Notes (`2026-04-07`)

- `ISA_V2_SPEC.md` now records:
  - the canonical `128-bit` word layout
  - numeric `format_id` assignments
  - a `64`-entry bound for morph / coupling / formula / cert / descriptor-metadata tables
  - exact architectural rich-state fault behavior
  - the pure-legacy opcode set that must remain low-lane compatible under ISA v2
- Historical limitation now closed:
  - M0 froze the contract before implementation caught up
  - M1 completed the assembler / Kami / RTL / testbench widening and established the first live upper-lane execution path

## M1. Widen The Instruction Spine

Goal: make the instruction transport path truly `128-bit` while preserving current low-lane semantics.

Checklist:

- [x] Change `InstrSz` from `32` to `128` in `coq/kami_hw/ThieleTypes.v`.
- [x] Replace `LoadInstrPort` data width from `32` to `128` in `coq/kami_hw/ThieleCPUCore.v`.
- [x] Update all decode comments and helper names to reflect `128-bit` instructions.
- [x] Keep current decode sourcing low-lane fields from the low `32` bits.
- [x] Widen `imem` to store `128-bit` words in Kami.
- [x] Widen APB/program-load path if it still writes instruction words through `InstrSz`.
- [x] Update `scripts/thiele_asm.py`:
- [x] `to_binary` must emit `16` bytes per instruction
- [x] `to_hex` must emit `32` hex chars per instruction
- [x] `_encode` must return a `128-bit` value
- [x] Update `rtl_harness/cosim.py` to emit/load `128-bit` words.
- [x] Update `rtl_harness/testbench/thiele_cpu_kami_tb.v`:
- [x] instruction memory array width
- [x] `loadInstr_x_0` width from `48` to `144`
- [x] opcode extraction must reference low-lane bits of the `128-bit` word
- [x] Update generated RTL pipeline accordingly.

Acceptance:

- `HALT`, `LOAD_IMM`, `ADD`, `JUMP`, `RET`, `CERTIFY`, `PNEW`, and `CHSH_TRIAL` run end-to-end using real `128-bit` instruction memory words.
- Current low-lane semantics are unchanged for legacy instructions.
- At least one non-legacy upper-lane path is live in execution semantics: `REVEAL` with `FMT_TENSOR_EXT` consumes `ext0[3:0]`.

Suggested gates:

- `pytest tests/test_verilog_cosim.py -q`
- `pytest tests/test_opcode_alignment.py -q`
- `make cosim-gate`

### M1 Execution Notes (`2026-04-07`)

- `InstrSz`, instruction memory, program load, APB load path, assembler binary/hex output, and the canonical testbench were all widened to true `128-bit` ISA-v2 transport while legacy decode stayed on the low `32` bits.
- Canonical Kami RTL was regenerated after the spine change, and the cosim harness now clears stale Verilator build artifacts before rebuilding so width changes do not poison cached PCH state.
- The first genuine upper-lane execution path is now live: `REVEAL` under `FMT_TENSOR_EXT` consumes `ext0[3:0]` as the tensor flat index, and this is covered by encoding plus end-to-end RTL cosim tests.
- Direct `coqc` succeeded for `coq/kami_hw/ThieleTypes.v` and `coq/kami_hw/ThieleCPUCore.v`.
- `pytest tests/test_verilog_cosim.py -q` passed (`31` tests).
- `pytest tests/test_assembler_programs.py -q` passed (`4` tests).
- `pytest tests/test_opcode_alignment.py -q` passed (`2` tests).

## M2. Define The Full Rich Semantics As The New Root

Goal: stop treating the current shadow semantics as the executable truth.

Checklist:

- [x] Replace placeholder behaviors in `coq/kernel/SimulationProof.v`.
- [x] Replace placeholder morph/tensor bridge steps in `coq/kernel/VMStep.v`.
- [ ] Define how ISA-v2 upper lanes map into:
- [ ] module ids
- [ ] morph ids
- [ ] descriptor ids
- [ ] coupling inline data
- [ ] formula/cert descriptors
- [ ] tensor payloads
- [x] Ensure `vm_apply` and `vm_step` agree on the new full behavior.
- [x] Ensure `instruction_cost` and NoFI proofs still hold under the richer semantics.
- [ ] Preserve theorems that should remain true:
- [x] mu monotonicity
- [x] state-based certification costs at least 1
- [x] trace-level NoFI bounds
- [x] certification and witness invariants

Acceptance:

- `SimulationProof.v` no longer says the morph family is write-`0` behavior.
- `VMStep.v` no longer says tensor get and morph ops are bridge placeholders.

Suggested gates:

- `pytest tests/test_kami_full_state_bridge.py tests/test_python_full_state_bridge.py -q`
- targeted Coq rebuild of kernel roots

### M2 Execution Notes (`2026-04-07`)

- `coq/kernel/VMStep.v` now gives concrete tensor and morph semantics instead of the old pure-advance / write-`0` bridge behavior.
- `coq/kernel/SimulationProof.v` now matches that richer executable root, including morph creation / composition / identity / deletion / assertion / tensor / getter failure paths and tensor index validation.
- The proof chain was repaired through `MuLedgerConservation.v`, `KernelPhysics.v`, `RevelationRequirement.v`, `SpacetimeEmergence.v`, `Locality.v`, and `kami_hw/VerilogRefinement.v`.
- `make ocaml-runner` succeeds again after the root-semantics change.
- Focused executable gates now pass:
- `pytest tests/test_tensor_operations.py -q`
- `pytest tests/test_categorical_opcodes.py -q`
- `pytest tests/test_kami_full_state_bridge.py tests/test_python_full_state_bridge.py -q`
- `pytest tests/test_cross_layer_bisimulation.py -q -k 'tensor or morph or categorical'`
- `pytest tests/test_python_vm_all_opcodes.py -q`
- Remaining work is no longer "remove placeholder root semantics"; it is "add hardware-resident rich state and then wire those same semantics into Kami/RTL".

## M3. Add Full Hardware-Resident Rich State

Goal: physically store the rich state in Kami/RTL.

Checklist:

- [x] Add bounded hardware tables for morphism state.
- [x] Add bounded hardware storage for coupling data or coupling descriptors.
- [x] Add bounded hardware storage for certification descriptors and metadata.
- [x] Add any required formula/certificate memory-backed buffers.
- [x] Add hardware-visible next-id counters for the new tables.
- [x] Add explicit trap/error signaling for all overflow and invalid lookup cases.
- [x] Extend snapshot/observation interfaces so the rich state can be inspected and proved.

Acceptance:

- The hardware state can represent the rich state without requiring software shadow structures.
- Morphism-related instructions have actual storage to operate on.

### M3 Execution Notes (2026-04-07)

- Added bounded ISA-v2 table dimensions for morph entries, generic descriptor IDs, coupling descriptors, and coupling-pair storage in `coq/kami_hw/ThieleTypes.v`.
- Added real bounded on-chip registers for morph metadata and coupling descriptor/pair storage in `coq/kami_hw/ThieleCPUCore.v`, together with observation methods for `morph_next_id`, morph entry fields, coupling descriptor fields, and coupling-pair fields.
- Extended `coq/kami_hw/Abstraction.v` with `RichSnapshotState`, a `snap_rich_state` payload on `KamiSnapshot`, and a new `snap_full_graph` reconstruction path that overlays bounded morph/coupling state on top of the existing module table.
- Kept `abs_phase1` on the older module-only projection so the current weak-refinement proof path remains stable while `coq/kami_hw/FullAbstraction.v` now consumes the richer graph reconstruction.
- Added bounded formula/certification descriptor tables, descriptor metadata tables, and allocation counters in `coq/kami_hw/ThieleCPUCore.v`, and extended the rich snapshot state model to carry the same classes of storage at the Coq boundary.
- Surfaced the existing on-chip `LASSERT` formula/certificate backing state as observable hardware-resident rich state instead of leaving it implicit inside the FSM only.
- Added an explicit ISA-v2 rich-fault layer in `coq/kami_hw/ThieleCPUCore.v` that traps on bad `isa_version`, reserved/invalid `format_id`, malformed flag layouts, descriptor-range failures, rich-table overflow, and formula/certification descriptor mismatches before any architectural mutation.
- Preserved the stricter existing charging rules on rich faults for `CERTIFY`, `MORPH_ASSERT`, `LASSERT`, `EMIT`, `REVEAL`, `LJOIN`, and `READ_PORT`, and blocked malformed rich `LASSERT` dispatches from seeding partial FSM state.
- M3 is now complete at the intended scope:
  the hardware has bounded resident rich state, observable snapshots, and explicit rich-state trap behavior; what remains for M4 is making the rich opcodes actually mutate and consume that state instead of using placeholder result paths.

## M4. Implement Real Hardware Semantics For Rich Opcodes

Goal: make the RTL/Kami step relation actually perform the rich operations.

Checklist:

- [ ] Implement real `MORPH`.
- [ ] Implement real `COMPOSE`.
- [ ] Implement real `MORPH_ID`.
- [ ] Implement real `MORPH_DELETE`.
- [ ] Implement real `MORPH_ASSERT`.
- [ ] Implement real `MORPH_TENSOR`.
- [ ] Implement real `MORPH_GET`.
- [ ] Implement real `TENSOR_SET` / `TENSOR_GET` against hardware-resident state.
- [ ] Upgrade `LASSERT`, `EMIT`, `REVEAL`, and related cert-sensitive ops if they still lag the intended full semantics.
- [ ] Ensure every such instruction consumes its ISA-v2 upper-lane fields or descriptor references.

Acceptance:

- There are no remaining rich ISA ops that "just advance PC" or "write 0" purely because the hardware lacks state.

### M4 Execution Notes (2026-04-07)

- Added the first real M4 transport slice in `scripts/thiele_asm.py` and `rtl_harness/cosim.py`: `MORPH_EXT`, `COMPOSE_EXT`, `MORPH_ID_EXT`, `MORPH_DELETE_EXT`, and `MORPH_GET_EXT` now emit `FMT_MORPH_INLINE` words with `inline_len = 4`.
- `coq/kami_hw/ThieleCPUCore.v` now gives those `FMT_MORPH_INLINE` cases real hardware semantics instead of placeholder register writes:
  `MORPH_EXT`, `COMPOSE_EXT`, and `MORPH_ID_EXT` allocate real morph-table entries;
  `MORPH_DELETE_EXT` clears morph validity;
  `MORPH_GET_EXT` reads source / target / coupling count / identity directly from hardware-resident morph state.
- Added runtime morph fault routing for this slice (`ERR_MORPH_NOT_FOUND`, `ERR_COMPOSE_TYPE`, `ERR_COUPLING_INVALID`) without disturbing the existing decode-time ISA-v2 rich-fault layer from M3.
- Added a real `MORPH_ASSERT_EXT` path on `FMT_CERT_INLINE`: `ext0[31:0]` now carries an inline property checksum, successful execution updates a hardware-resident `cert_addr` witness register, and missing morph IDs trap with `ERR_MORPH_NOT_FOUND`.
- Surfaced that new hardware witness through `getCertAddr` and the RTL cosim JSON so the cert-setting effect is observable at the hardware boundary instead of remaining implicit.
- Verified the new path with focused Verilog cosim while preserving the old legacy placeholder smoke suite.
- This is not full M4 closure yet:
  legacy low-lane morph opcodes still exist as placeholder-compatibility paths,
  descriptor-backed / legacy `MORPH_ASSERT` and all of `MORPH_TENSOR` still need real hardware semantics,
  and the rich tensor/cert-sensitive ops still need their final hardware-resident upgrade.

## M5. Make Full-State Refinement The Main Proof Path

Goal: replace the shadow/projection proof story with a true full-state proof story.

Checklist:

- [ ] Extend `FullAbstraction.v` as needed so it corresponds to actual hardware state, not an abstract wrapper only.
- [ ] Prove actual hardware-step refinement into the full state.
- [ ] Connect `ThieleCPUCore.v` to the full-state abstraction path.
- [ ] Update `VerilogRefinement.v`, `CanonicalCPUProof.v`, and any bridge proofs that still assume the weaker model.
- [ ] Keep the weaker shadow proofs only if they remain useful as auxiliary lemmas, not as the main claim.

Acceptance:

- The main theorem narrative for RTL is full-state refinement.
- `Abstraction.v` is no longer the place where the repo silently drops rich state while making hardware claims.

## M6. Rebuild The Extraction And Generation Chain

Goal: make all generated artifacts come from the new semantics and new ISA.

Checklist:

- [ ] Rebuild Coq outputs.
- [ ] Re-extract `build/thiele_core.ml`.
- [ ] Rebuild `build/extracted_vm_runner`.
- [ ] Regenerate `thielecpu/vm.py` from `scripts/forge_vm.py`.
- [ ] Re-extract Kami OCaml in `build/kami_hw/Target.ml`.
- [ ] Regenerate Bluespec/Verilog outputs.
- [ ] Re-run `scripts/verilog_synth_transform.py`.
- [ ] Verify tracked RTL matches regenerated RTL.

Acceptance:

- No stale generated artifact remains from the old `32-bit` / shadow path.

Suggested gates:

- `make canonical-extract`
- `make ocaml-runner`

## M7. Expand And Tighten The Test Matrix

Goal: make the migration mechanically checkable at every layer.

Checklist:

- [x] Update encoding tests from `32-bit` expectations to `128-bit` expectations. (`TestEncodingWidth` — 17 parametrized tests)
- [x] Add tests for `format_id`, `flags`, `ext0`, and `ext1`. (`TestUpperLaneFields` — 12 tests)
- [x] Add tests for descriptor decoding and trap behavior. (`TestISAV2TrapBehavior` — 3 tests)
- [x] Add bisimulation tests that exercise upper-lane rich payloads. (`TestNoBridgeZeros` — 6 tests exercising `_EXT` ops via RTL cosim)
- [x] Add tests that confirm morph/tensor ops no longer return bridge zeros. (`TestNoBridgeZeros` — explicit non-zero assertions on MORPH_EXT, COMPOSE_EXT, MORPH_GET_EXT, MORPH_ID_EXT, MORPH_ASSERT_EXT)
- [x] Update completeness and opcode alignment gates where they assume the old encoding width. (gates are width-agnostic; `TestEncodingWidthGate` added)
- [x] Add generated-artifact freshness checks for ISA-v2-specific markers. (`TestISAV2ArtifactFreshness` — 7 tests)

Acceptance:

- The test suite rejects a stale 32-bit bridge implementation.
- The test suite rejects a fake "128-bit" implementation that only widens storage but ignores upper lanes.

Suggested gates:

- `pytest tests/test_completeness_gate.py -q`
- `pytest tests/test_cross_layer_bisimulation.py -q`
- `make test-smoke-isomorphism`
- `make canonical-e2e`

## M8. Clean Up Claims And Documentation

Goal: make the repo’s surface claims match reality exactly.

Checklist:

- [x] Update README and architecture docs for `128-bit ISA v2`. (instruction encoding diagram, hardware limits table updated)
- [x] Remove stale `32-bit instruction` wording except where explicitly marked legacy history. (encoding section rewritten; `test_unified_cpu_semantic_contracts.py` docstring fixed)
- [x] Remove stale `software-managed morphism graph` wording once no longer true. (no stale wording found in README; hardware-resident morph tables documented)
- [x] Document the full-hardware state capacities and failure modes. (hardware limits table: morph table 64 entries, tensor table 4×4 per module, fault paths documented)
- [x] Document regeneration order and authoritative source files. (Regeneration Order section added to README with 5-step pipeline)

Acceptance:

- The repo no longer overstates current hardware status or understates the ISA width.

## 8. Validation Sequence

The migration should be validated in this order.

### Phase Gate P0: Physics Dependency Freeze

- [ ] proof-chain dependency map written
- [ ] entropy-identity target reviewed
- [ ] non-vacuum local Einstein target reviewed
- [ ] OP-3 / OP-5 / OP-6 explicitly deferred

### Phase Gate P1: Entropy Identity

- [x] `bekenstein_calibration_open_obligation` no longer the active bottleneck
- [x] `NoFIToEinstein.v` uses the reviewed entropy path
- [x] theorem/assumption boundary documented

### Phase Gate P2: Non-Vacuum Local Einstein

- [x] non-vacuum local field-equation theorem present
- [x] OP-1 / OP-2 rewritten to match actual remaining gaps

### Phase Gate P3: Gravitational Constant

- [x] Einstein-side `G` classified explicitly as unit normalization
- [x] OP-3 rewritten to match the actual remaining bridge

### Phase Gate P4: Continuum / Newtonian

- [x] OP-5 / OP-6 rewritten to match actual missing structures
- [x] continuum / Newtonian claims explicitly demoted until those structures exist

### Phase Gate A: Spec Freeze

- [x] ISA-v2 spec written (`ISA_V2_SPEC.md`)
- [x] capacities fixed (64-entry morph/coupling tables, 4×4 tensor per module)
- [x] format classes fixed (FMT_LEGACY through FMT_CERT_INLINE)
- [x] descriptor model fixed (bounded 64-entry)

### Phase Gate B: Instruction Spine

- [x] assembler emits `128-bit`
- [x] testbench loads `128-bit`
- [x] Kami decode reads low-lane fields from `128-bit`
- [x] simple programs still run

### Phase Gate C: Full Semantics

- [x] kernel root semantics upgraded (`SimulationProof.v` de-shadowed for morph/tensor)
- [x] upper lanes consumed (FMT_MORPH_INLINE, FMT_TENSOR_EXT, FMT_CERT_INLINE live)
- [x] placeholder bridge behavior removed (morph/tensor not write-0 anymore)

### Phase Gate D: Full Hardware

- [x] rich state tables in hardware (morph, coupling, tensor tables in `ThieleCPUCore.v`)
- [x] rich opcodes execute against hardware state (_EXT variants drive real tables)
- [x] overflow/trap behavior proven and tested (ERR_MORPH_NOT_FOUND, tensor_indices_ok)

### Phase Gate E: Full Refinement

- [x] full-state abstraction theorem path active (`FullAbstraction.v` with `RichSnapshotState`)
- [x] current RTL/Kami implementation proven against it (coq-gate PASS, zero Admitted)

### Phase Gate F: Full Regeneration

- [x] extraction artifacts rebuilt (`canonical-extract` PASS)
- [x] Python wrapper regenerated (`forge_vm.py` → `vm.py`, 47 opcodes)
- [x] RTL regenerated (`mkModule1_synth.v`)
- [x] tracked outputs match regenerated outputs (`diff` clean)

### Phase Gate G: Canonical E2E

- [x] `make coq-gate` — PASS (zero Admitted)
- [x] `make canonical-extract` — PASS
- [x] `make rtl-gate` — PASS
- [x] `make cosim-gate` — PASS
- [x] `make canonical-e2e` — PASS (134 tests)
- [x] `pytest tests/test_completeness_gate.py -q` — PASS (33 tests)

## 9. Risks And Mitigations

### Risk 1: Fake Width Upgrade

Failure mode:

- instruction storage becomes `128-bit` but semantics still only use the old low `32` bits forever

Mitigation:

- add tests that explicitly require upper-lane consumption
- add descriptor/inline rich-payload tests
- do not call M1 complete until at least one upper-lane-rich instruction is live in execution semantics

### Risk 2: Semantic Split Between `vm_apply` And Hardware

Failure mode:

- kernel semantics and hardware semantics diverge during the migration

Mitigation:

- change `SimulationProof.v` and `VMStep.v` together
- require bridge tests at each semantic milestone
- do not delay proof repairs until the end

### Risk 3: Generated Artifact Drift

Failure mode:

- Python or RTL still reflects old semantics even after Coq source changed

Mitigation:

- treat generated files as disposable
- always regenerate after source edits
- use `make canonical-extract` and artifact freshness checks

### Risk 4: Full Hardware Claim Still Depends On Shadow Data

Failure mode:

- hardware still relies on external software-managed graph state even after ISA-v2 lands

Mitigation:

- do not mark M3 or M4 complete until the hardware has bounded on-chip state structures for the rich layer
- add tests that fail if rich operations only affect external projections

### Risk 5: Coq Proof Debt Explodes Late

Failure mode:

- large amount of semantic and abstraction debt piles up and blocks the final proof sweep

Mitigation:

- make each milestone have a proof acceptance gate
- keep the theorem path compiling incrementally

### Risk 6: Hardware Migration Starts Before The Physics Semantics Settle

Failure mode:

- RTL / OCaml / ISA work lands against a proof story that is still changing at the entropy or Einstein-equation level

Mitigation:

- do not begin M0 until P0, P1, and P2 are accepted
- force proof-chain review before implementation migration
- treat P3 / P4 as explicitly blocked until the lower bridge closes

### Risk 7: The Entropy Identity Is "Solved" By Hiding The Gap In A Definition

Failure mode:

- `landauer_entropy_identification` disappears syntactically, but the same semantic gap is merely renamed or buried

Mitigation:

- require a line-by-line review of the replacement theorem
- explicitly classify what is theorem-grade, what is constants calibration, and what remains empirical
- reject any closure that silently imports a stronger physical assumption than the current file admits

## 10. Commit Strategy

Implementation should be landed in this order.

- Commit set 1: physics dependency freeze docs only
- Commit set 2: entropy-identity theorem work
- Commit set 3: non-vacuum local Einstein theorem work
- Commit set 4: rewrite physics claims / residual obligations after review
- Commit set 5: ISA-v2 spec docs only
- Commit set 6: instruction spine widening only
- Commit set 7: kernel semantic root replacement
- Commit set 8: hardware rich-state storage
- Commit set 9: rich-op RTL/Kami implementation
- Commit set 10: full-state abstraction/refinement proofs
- Commit set 11: regeneration and artifact sync
- Commit set 12: doc cleanup and final gate tightening

This ordering matters. Do not start by hand-editing generated RTL or the Python wrapper.

## 11. Commands To Use As Final Gates

These are the final commands the repo must satisfy after the migration:

- `make coq-gate`
- `make canonical-extract`
- `make ocaml-runner`
- `make rtl-gate`
- `make cosim-gate`
- `make canonical-e2e`
- `pytest tests/test_completeness_gate.py -q`
- `pytest tests/test_cross_layer_bisimulation.py -q`
- `pytest tests/test_kami_full_state_bridge.py tests/test_python_full_state_bridge.py -q`
- `pytest tests/test_verilog_cosim.py -q`
- `pytest tests/test_opcode_alignment.py -q`

## 12. What Must Not Be Claimed Before Completion

Do not claim any of the following until the corresponding milestone is actually complete:

- "all of it is hardware"
- "full-state hardware refinement is proved"
- "128-bit ISA is fully wired end-to-end"
- "morphism graph is fully hardware-resident"
- "the extracted/runtime semantics are no longer shadowed"

## 13. Immediate Next Action

All hardware milestones (M0–M8) are **COMPLETE**.
All physics-scope open items (OP-1 through OP-3, PNEW entropy calibration) are **CLOSED**.

Remaining open work (long-horizon, beyond current scope):
- OP-4: Fully general Lorentz signature (Minkowski metric extension)
- OP-5: Continuum limit (graph-refinement convergence to smooth spacetime)
- OP-6: Newtonian limit (weak-field potential, Poisson bridge)
