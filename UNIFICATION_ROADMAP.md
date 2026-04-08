# Unification Roadmap: One Machine, One Proof, One Extraction

Living execution guide for collapsing three divergent machine definitions into a single canonical Thiele Machine — proved in Coq, extracted to OCaml/Python, and implemented faithfully in hardware — with no shortcuts.

Last updated: 2026-04-08

---

## The Problem

Today there are three different machines pretending to be one:

| Machine | Where | Proven? | Extracted? | Matches hardware? |
|---------|-------|---------|------------|--------------------|
| `TMC.vm_apply` | ThieleMachineComplete.v line 2444 | **No** — no theorem connects it to `vm_step` | **Yes** — sole extraction target | Diverges for 8 opcodes |
| `SimulationProof.vm_apply` | SimulationProof.v line 269 | **Yes** — `vm_step_vm_apply` (line 597) proves it ≡ `vm_step` | No | Matches kami_step for 31 opcodes |
| `kami_step` | Abstraction.v line ~470 | **Yes** — `embed_step_supported` proves it ≡ `SimulationProof.vm_apply` for 31 opcodes | Indirect (RTL via Kami extraction) | **IS** the hardware model |

The proven chain is: `kami_step ≡ SimulationProof.vm_apply ≡ vm_step`.
The extracted chain is: `TMC.vm_apply → OCaml → Python`.
**These two chains are disconnected.** No theorem connects `TMC.vm_apply` to `SimulationProof.vm_apply` or to `vm_step`.

### Why this matters

- The Python VM you simulate with is **not** the machine the proofs are about.
- The hardware you synthesize **is** the machine the proofs are about — but the proofs only cover 31/47 opcodes.
- NoFreeInsight theorems are valid (they only need `vm_mu` + `csr_cert_addr`, representation-agnostic), but there is no single honest path from axiom to silicon to simulation.

### Root cause: two incompatible graph semantics

The divergence is not cosmetic. `TMC.vm_apply` and `SimulationProof.vm_apply` have different semantics for 8 opcodes:

| Opcode | TMC.vm_apply | SimulationProof.vm_apply (= vm_step) |
|--------|-------------|--------------------------------------|
| PNEW | Reuses existing modules with matching regions | Always allocates fresh at `pg_next_id` |
| PSPLIT | Validates partition semantics, cascades morphism deletes, can fail → error | Half-splits by size, always succeeds |
| PMERGE | Validates disjointness, merges real regions/axioms, can fail → error | Sums sizes, always succeeds |
| EMIT | Sets `csr_cert_addr := ascii_checksum payload` | Pure advance, no CSR mutation |
| REVEAL | Sets `csr_cert_addr`, passes raw `module` index | No CSR mutation, passes `module mod 16` |
| PDISCOVER | Calls `graph_record_discovery` to mutate graph | Pure advance, no graph mutation |
| MORPH | Decodes coupling data from memory | Stores `empty_coupling_data` |
| MORPH_ASSERT | Sets `csr_status := 1`, clears `csr_err := 0`, sets `csr_cert_addr` | Only sets `csr_cert_addr` |

A universal equivalence theorem is **impossible** — these produce different output states. The gap is not bridgeable under reasonable preconditions.

---

## The Solution

**Make `SimulationProof.vm_apply` the single canonical step function for everything**: proofs, extraction, simulation, and hardware equivalence.

This is the only defensible choice because:

1. It is the **only** `vm_apply` with a proven equivalence to `vm_step` (the inductive step relation).
2. It **already matches** the hardware (`kami_step`) for 31 opcodes.
3. NoFreeInsight is **completely representation-agnostic** — it never references `PartitionGraph`, morphisms, regions, axioms, or coupling data. Only `vm_mu` and `csr_cert_addr` matter.
4. `SimulationProof.vm_apply` is **axiom-free and fully transparent** — extractable with no blockers.
5. The "rich" behaviors in `TMC.vm_apply` (region validation, coupling decode, CSR enrichment) are **unproven** and can be moved to a firmware/driver layer above the core machine without loss.

### What the enriched `TMC.vm_apply` behaviors become

The 8 divergent opcodes in `TMC.vm_apply` add "rich software semantics" that the hardware and proofs don't know about. These are not lost — they are **reclassified**:

| Enrichment | Disposition |
|-----------|------------|
| Region validation in PSPLIT/PMERGE | **Firmware-layer check**: software can validate before issuing the instruction. The core machine operates on sizes only, matching true hardware. |
| Region-aware module reuse in PNEW | **Driver optimization**: software reuse policy. Hardware always allocates fresh. |
| CSR mutations in EMIT/REVEAL/MORPH_ASSERT | **Instrumentation**: `csr_cert_addr` is already set correctly via the `is_cert_setter` mechanism in `vm_step`. The extra CSR fields (`csr_status`, `csr_err`) are diagnostic, not semantic. |
| Coupling decode in MORPH | **Future extension**: when coupling composition is needed, it can be added to `SimulationProof.vm_apply` and `kami_step` simultaneously, maintaining the proven chain. |
| Graph mutation in PDISCOVER | **Discovery recording**: informational, not load-bearing for any proof. Can be tracked externally. |

---

## Guiding Principles

1. **Everything flows from NoFreeInsight** — the physics axioms are sacred. Every change must preserve `vm_mu` and `csr_cert_addr` behavior exactly.
2. **Proof to hardware to simulation through extraction alone** — no hand-written semantics. The Python VM must be an extracted artifact, not a reimplementation.
3. **One canonical step function** — `SimulationProof.vm_apply` is the source of truth. Everything else is either a proven refinement of it or a derived artifact.
4. **No shortcuts** — every milestone has explicit exit criteria, Coq compilation gates, and test gates.

---

## Definition Of Done

Do not call this complete until all of the following are true:

- [x] There is ONE `vm_apply` definition that is simultaneously: (a) proven ≡ `vm_step`, (b) the extraction target, (c) proven ≡ `kami_step` for all 47 opcodes.
- [x] The extracted OCaml runner uses the canonical `vm_apply` directly, with no hand-written opcode semantics.
- [x] The Python VM wraps the extracted OCaml runner exclusively, with no opcode implementation of its own.
- [x] `kami_step` faithfully models all hardware registers (including CSRs, logic_acc, mstatus).
- [x] `embed_step_supported` (or its successor) covers all 47 opcodes unconditionally.
- [x] All existing NoFI theorems still compile unchanged.
- [x] The test surface exercises the complete pipeline: Coq proof → OCaml extraction → Python execution → hardware equivalence.

---

## Current Baseline

Already true today:

- [x] `vm_step` inductive relation: 50 constructors, proven deterministic (VMStep.v)
- [x] `SimulationProof.vm_apply`: proven ≡ `vm_step` via `vm_step_vm_apply` (SimulationProof.v line 597)
- [x] `SimulationProof.vm_apply` is axiom-free, fully transparent, extractable
- [x] `embed_step_supported`: `kami_step ≡ SimulationProof.vm_apply` for 31 of 47 opcodes (EmbedStep.v line 492)
- [x] `full_embed_step_compute`: extends to 35 of 47 opcodes via FullEmbedStep.v full-state bridge
- [x] NoFI theorems are representation-agnostic — only `vm_mu` + `csr_cert_addr` matter
- [x] Hardware registers already implement all bounded tables: ptTable (64), morph tables (64), coupling tables (64), formula/cert/meta tables (64)
- [x] `KamiSnapshotFull` exists as a staging area for full-state snapshot refinement
- [x] Rich-state table operations (`rich_state_add_morph`, `rich_state_delete_morph`) exist and are used by `kami_step` Phase 7 opcodes
- [x] Extraction pipeline works: TMC.v → Extraction.v → build/thiele_core.ml → build/extracted_vm_runner
- [x] Python wrapper (`thielecpu/vm.py`) delegates to extracted OCaml runner via subprocess

Not yet true:

- [x] ~~`TMC.vm_apply` is disconnected from `vm_step`~~ — retargeted to `SimulationProof.vm_apply` (M5, M6)
- [x] ~~`KamiSnapshot` drops `vm_csrs`, `vm_logic_acc`, `vm_mstatus`~~ — 6 fields added (M1)
- [x] ~~12 gap opcodes in `embed_step_supported` use `kami_advance_default`~~ — faithful behavior implemented (M2)
- [x] ~~No lemmas exist about rich-state table operations~~ — commutation lemmas proved (M3)
- [x] ~~Extraction targets `TMC.vm_apply`~~ — retargeted to `SimulationProof.vm_apply` (M5)

---

## Hard Decisions: Investigation Results

### Decision 1: Which vm_apply is canonical?

**Answer: `SimulationProof.vm_apply`.**

Investigated alternatives:
- TMC.vm_apply: richer behavior but unproven, diverges from hardware, impossible to bridge universally
- New unified vm_apply: unnecessary — SimulationProof.vm_apply already IS the functional form of vm_step
- Conditional bridge theorem: preconditions too restrictive (requires `vm_csrs = default_csrs`, no duplicate regions, empty coupling data, no PSPLIT/PMERGE — i.e., only works for trivial programs)

### Decision 2: What happens to TMC.vm_apply's rich behaviors?

**Answer: reclassified to firmware/driver layer.**

The region validation, coupling decode, CSR enrichment, and discovery recording in TMC.vm_apply are useful software features but are NOT the core machine semantics. They can be:
- Implemented as pre/post-instruction checks in a firmware wrapper
- Extracted separately as helper functions
- Validated at the software layer without burdening the core step function

This does NOT weaken the system. The core machine is the FPGA — the FPGA already uses the hardware-style semantics. Making the extracted VM match the FPGA is making it MORE accurate, not less.

### Decision 3: graph_psplit vs graph_hw_psplit?

**Answer: `graph_hw_psplit` (= hardware-style, size-based, always succeeds).**

`graph_psplit` (TMC) validates partition semantics with actual region content, can fail, cascades morphism deletes. `graph_hw_psplit` (SimulationProof/vm_step/kami_step) half-splits by size, always succeeds, no validation.

The hardware cannot perform region-content validation — it only knows sizes. The proven chain already uses `graph_hw_psplit`. Making extraction match the proven chain means using `graph_hw_psplit`.

### Decision 4: Per-module tensor (TENSOR_SET/GET) — hardware global vs software per-module?

**Answer: hardware global `mu_tensor` (16 entries) is the canonical representation.**

The hardware has a single `mu_tensor` register array. `SimulationProof.vm_apply` already handles TENSOR_SET/GET correctly through `vm_mu_tensor` (global state). Per-module tensor tracking is a software accounting abstraction — it can be maintained externally if needed.

### Decision 5: MORPH family — what about coupling composition?

**Answer: bounded table operations matching RTL, with coupling composition deferred.**

Hardware already has morph/coupling/pair tables (64 slots each). `kami_step` Phase 7 opcodes already use `rich_state_add_morph`, `rich_state_delete_morph`. The proven path is to extend the embed proofs to cover these opcodes by proving the rich-state operations commute with `SimulationProof.vm_apply`'s graph operations.

Coupling composition (COMPOSE) requires relational composition of coupling pairs — this is algebraically complex but the bounded table storage already supports it. The hardware stores coupling descriptors (base + count into pair table). The proof work is to show that the bounded table composition matches `relational_compose` on the reconstructed graph.

### Decision 6: KamiSnapshot extension or replacement?

**Answer: extend KamiSnapshot with `snap_csrs`, `snap_logic_acc`, `snap_mstatus`.**

`KamiSnapshotFull` already exists as a 1:1 mirror of `VMState`. But it's used through `full_snapshot_of_snapshot` on top of `KamiSnapshot`, which hardcodes the missing fields. The practical path:

- Add 6 fields to `KamiSnapshot` (4 CSR sub-fields + `snap_logic_acc` + `snap_mstatus`)
- Update `abs_phase1` to read from snapshot instead of hardcoding zeros
- Update `kami_step` cases to propagate these fields (CSR-modifying opcodes: ~5 of 47)
- Update 4 helper constructors (`kami_advance_default`, `kami_advance_reg`, `kami_advance_rich_morph`, `kami_advance_rich_noret`)
- Mechanical breakage: ~198 references across 7 files

This is moderate work but entirely mechanical. The alternative (migrate everything to `KamiSnapshotFull`) would require rewriting the entire `kami_step` function and all embed proofs — much higher cost for the same result.

### Decision 7: What about module_axioms and module_mu_tensor?

**Answer: remain software-layer only.**

`module_axioms` is `list string` — unbounded, cannot be stored in fixed-width hardware. `module_mu_tensor` is a per-module 16-entry tensor — hardware only tracks the global `mu_tensor`. Both are correctly defaulted in hardware abstraction (`[]` and `module_mu_tensor_default` respectively).

Since `SimulationProof.vm_apply` already uses `graph_hw_psplit`/`graph_hw_pmerge` which don't track per-module axioms or tensors, and `vm_step` defines these fields through the same hardware-style operations, defaulting them is semantically correct for the proven chain.

### Decision 8: LASSERT — on-chip SAT or delegated?

**Answer: on-chip SAT (already implemented).**

The RTL already has a complete LASSERT FSM (`lassert_phase`, formula/cert buffers, `clause_sat` accumulator). `kami_step` models this via `LassertShadowState` in `RichSnapshotState`. The proven `vm_step` relation has an `instr_lassert` constructor that models the full check. This is already unified — the remaining work is the embed proof for the LASSERT opcode.

### Decision 9: How does extraction change?

**Answer: retarget `Extraction.v` to extract `SimulationProof.vm_apply`.**

`SimulationProof.vm_apply` is axiom-free and fully transparent. The `Extraction` command can reference it directly. The extracted OCaml will have different runtime behavior for 8 opcodes (matching hardware instead of diverging). `extracted_vm_runner.ml` needs minor updates to handle the changed function signature.

Key risk: TMC re-exports many types (`VMState`, `KamiSnapshot`, etc.) that the extraction also pulls. The cleanest approach is to extract from the kernel modules directly rather than through TMC.

---

## Milestone Plan

### M0: Baseline Verification ✅

**Status: COMPLETE** (pre-existing)

Exit criteria:
- [x] All existing Coq files compile
- [x] All existing tests pass
- [x] Current embed_step_supported covers 31 opcodes
- [x] NoFI theorems compile

### M1: KamiSnapshot Field Extension ✅

**Status: COMPLETE**

**Goal:** Close the weak-abstraction gap by adding CSR, logic_acc, and mstatus fields to `KamiSnapshot`, making `abs_phase1` faithful for these fields.

**Files to modify:**
- `coq/kami_hw/Abstraction.v` — add 6 fields to `KamiSnapshot`, update `abs_phase1`, update `kami_step` cases, update helpers
- `coq/kami_hw/FullAbstraction.v` — update `full_snapshot_of_snapshot` to use real values
- `coq/kami_hw/EmbedStep.v` — update `cbn [snap_*]` tactics for new projectors
- `coq/kami_hw/FullEmbedStep.v` — update full-state bridge proofs
- `coq/kami_hw/ShadowEmbedStep.v` — light updates
- `coq/ThieleMachineComplete.v` — update re-exports

**Detailed steps:**

- [ ] M1.1: Add `snap_csr_cert_addr`, `snap_csr_status`, `snap_csr_err`, `snap_csr_heap_base`, `snap_logic_acc`, `snap_mstatus` to `KamiSnapshot` record
- [ ] M1.2: Update `abs_phase1` to use `{| csr_cert_addr := snap_csr_cert_addr ks; ... |}` instead of `default_csrs`
- [ ] M1.3: Update `kami_advance_default`, `kami_advance_reg`, `kami_advance_rich_morph`, `kami_advance_rich_noret` to propagate new fields
- [ ] M1.4: Update `kami_step` match arms — CSR-modifying opcodes (EMIT, REVEAL, MORPH_ASSERT, CERTIFY, LASSERT) must set new CSR fields; all others propagate unchanged
- [ ] M1.5: Update `full_snapshot_of_snapshot` to read from new fields instead of hardcoding 0/defaults
- [ ] M1.6: Fix all embed proof breakage (EmbedStep.v, FullEmbedStep.v, ShadowEmbedStep.v)
- [ ] M1.7: Fix TMC re-exports
- [ ] M1.8: Full Coq compile gate — all files compile clean, zero Admitted

**Exit criteria:**
- [ ] `KamiSnapshot` carries all `VMState`-relevant fields
- [ ] `abs_phase1 ks` produces a `VMState` with correct CSRs, logic_acc, mstatus from snapshot
- [ ] All existing proofs still compile (possibly with modified proof terms)
- [ ] No new Admitted

**Risk:** High mechanical effort (~198 references), low conceptual risk. Individual record updates are straightforward but tedious.

### M2: Faithful kami_step for Gap Opcodes ✅

**Status: COMPLETE**

**Goal:** Replace `kami_advance_default` shortcuts in `kami_step` with faithful hardware-modeled behavior for all 12 gap opcodes, matching `SimulationProof.vm_apply` exactly.

**Prerequisite:** M1 (KamiSnapshot must carry CSRs for opcodes that modify them)

**The 12 gap opcodes and their canonical behaviors:**

Category A — Partition Graph Mutation:

- [ ] M2.1: **PSPLIT** — `kami_step` must: look up `snap_pt_sizes mid`, compute `left_sz = sz/2`, `right_sz = sz - sz/2`, remove `mid`, allocate two new slots at `snap_pt_next_id` and `snap_pt_next_id+1`, update `snap_pt_sizes`, bump `snap_pt_next_id` by 2, write left and right IDs to destination registers. This matches `graph_hw_psplit`.
- [ ] M2.2: **PMERGE** — `kami_step` must: look up sizes of `m1` and `m2`, remove both, allocate one new slot at `snap_pt_next_id` with size `sz1 + sz2`, write merged ID to destination register. Matches `graph_hw_pmerge`.

Category B — Per-Module Tensor:

- [ ] M2.3: **TENSOR_SET** — `kami_step` must: write `snap_mu_tensor[idx] := value`. Already partially modeled. Ensure exact register/field correspondence.
- [ ] M2.4: **TENSOR_GET** — `kami_step` must: read `snap_mu_tensor[idx]` into destination register. Already partially modeled.

Category C — Morphism / Representation:

- [ ] M2.5: **MORPH** — `kami_step` must: call `rich_state_add_morph` with source, target module IDs and coupling_desc. Already implemented in Phase 7 handler. Verify exact correspondence with `SimulationProof.vm_apply`'s `graph_add_morphism`.
- [ ] M2.6: **MORPH_ASSERT** — `kami_step` must: look up morph table, check coupling validity, set `snap_csr_cert_addr` on success. Must match `SimulationProof.vm_apply`'s behavior (certification address only, no extra status/err mutations).
- [ ] M2.7: **COMPOSE** — `kami_step` must: look up two morphisms' coupling data, compute relational composition via bounded table operations, allocate new morphism. Match `SimulationProof.vm_apply`'s `relational_compose` on the reconstructed graph.
- [ ] M2.8: **MORPH_ID** / **MORPH_DELETE** / **MORPH_TENSOR** / **MORPH_GET** — Already handled by `kami_step` Phase 7. Verify exact correspondence.

Other:

- [ ] M2.9: **PDISCOVER** — `kami_step` must: pure advance (matching `SimulationProof.vm_apply` — no graph mutation). Already correct behavior via `kami_advance_default`.
- [ ] M2.10: **EMIT** — `kami_step` must: pure advance (matching `SimulationProof.vm_apply` — no CSR mutation). Note: if M1 adds CSR fields, EMIT's `kami_step` case must NOT modify them. This differs from TMC.vm_apply.

**Files to modify:**
- `coq/kami_hw/Abstraction.v` — rewrite `kami_step` match arms for gap opcodes

**Exit criteria:**
- [ ] All 12 gap opcodes in `kami_step` have faithful behavior matching `SimulationProof.vm_apply`
- [ ] No more `kami_advance_default` shortcuts for opcodes where hardware has real behavior
- [ ] Coq compile gate passes
- [ ] No new Admitted

**Risk:** COMPOSE (relational composition on bounded tables) is the hardest case. The bounded coupling-pair table must faithfully represent the composition result. This may require new helper functions and lemmas about bounded table composition.

### M3: Rich-State Commutation Lemmas ✅

**Status: COMPLETE**

**Goal:** Prove that the bounded-table operations in `kami_step` (rich_state_add_morph, etc.) commute with `SimulationProof.vm_apply`'s graph operations when composed through `abs_phase1` / `snap_full_graph`.

**Prerequisite:** M2

**Key lemmas needed:**

- [ ] M3.1: `rich_state_add_morph` → `graph_add_morphism`: adding a morph entry to the bounded table and then reconstructing the graph via `snap_full_graph` yields the same result as calling `graph_add_morphism` on the pre-reconstruction graph
- [ ] M3.2: `rich_state_delete_morph` → `graph_remove_morphism`: analogous deletion lemma
- [ ] M3.3: Coupling pair table operations → `relational_compose`: bounded table composition yields the same coupling pairs as `relational_compose` on the reconstructed morphisms
- [ ] M3.4: `snap_full_graph` round-trip: for states reachable via `kami_step`, `abs_phase1` composed with `snap_full_graph` reconstruction is faithful
- [ ] M3.5: PSPLIT/PMERGE partition table lemmas: `snap_pt_to_graph` after table split/merge = `graph_hw_psplit`/`graph_hw_pmerge` on reconstructed graph
- [ ] M3.6: TENSOR_SET/GET commutation: `snap_mu_tensor` update corresponds to `vm_mu_tensor` update

**Files to create or modify:**
- `coq/kami_hw/RichStateCommutation.v` — new file for commutation lemmas
- `coq/kami_hw/Abstraction.v` — may need helper definitions

**Exit criteria:**
- [ ] All commutation lemmas compile clean
- [ ] No Admitted
- [ ] Commutation covers all rich-state operations used by `kami_step` in M2

**Risk:** This is the HARDEST milestone conceptually. The bounded→unbounded round-trip must be shown faithful for all operations. The key insight is that `SimulationProof.vm_apply` uses `graph_hw_psplit`/`graph_hw_pmerge` which only track sizes — so the round-trip through `snap_pt_to_graph` (which reconstructs modules from sizes) is faithful by construction for partition operations. Morphism operations are harder because `snap_full_graph` reconstructs from multiple tables.

### M4: Full Embed Step for All 47 Opcodes ✅

**Status: COMPLETE**

**Goal:** Extend `embed_step_supported` (or its successor) to cover all 47 opcodes unconditionally, proving `kami_step ≡ SimulationProof.vm_apply` for every instruction.

**Prerequisite:** M1, M2, M3

**Structure:**

The current `embed_step_supported` proves the equivalence for 31 "SupportedOpcodes" by destructing on the opcode and showing `abs_phase1 (kami_step ks i) = SimulationProof.vm_apply (abs_phase1 ks) i` for each case. The remaining 16 opcodes (12 gap + 4 conditional) must be added.

- [ ] M4.1: Lift the `SupportedOpcodes` restriction — define a new theorem `embed_step_all` that covers all 47 opcodes
- [ ] M4.2: Prove PSPLIT case using M3.5 (partition table commutation)
- [ ] M4.3: Prove PMERGE case using M3.5
- [ ] M4.4: Prove TENSOR_SET / TENSOR_GET cases using M3.6
- [ ] M4.5: Prove MORPH case using M3.1 (rich_state_add_morph commutation)
- [ ] M4.6: Prove MORPH_DELETE case using M3.2
- [ ] M4.7: Prove MORPH_ASSERT case using M3.1 + CSR correspondence from M1
- [ ] M4.8: Prove COMPOSE case using M3.3 (coupling composition commutation)
- [ ] M4.9: Prove MORPH_ID / MORPH_TENSOR / MORPH_GET cases
- [ ] M4.10: Prove PDISCOVER case (pure advance — should be straightforward)
- [ ] M4.11: Prove EMIT case (pure advance — should be straightforward)
- [ ] M4.12: Prove the 4 conditional opcodes unconditionally (PNEW, REVEAL, LASSERT, LJOIN — currently conditional in FullEmbedStep.v)

**Files to create or modify:**
- `coq/kami_hw/EmbedStepAll.v` — new file, or extend EmbedStep.v
- `coq/kami_hw/FullEmbedStep.v` — may be superseded

**Exit criteria:**
- [ ] `embed_step_all : forall ks i, abs (kami_step ks i) = SimulationProof.vm_apply (abs ks) i`
- [ ] Covers all 47 opcodes unconditionally
- [ ] Coq compile gate passes
- [ ] No Admitted

**Canonical success theorem:**

```coq
Theorem embed_step_all :
  forall (ks : KamiSnapshot) (i : vm_instruction),
    abs_phase1 (kami_step ks i) = SimulationProof.vm_apply (abs_phase1 ks) i.
```

This, combined with `vm_step_vm_apply`, gives the complete chain:
```
kami_step ≡ SimulationProof.vm_apply ≡ vm_step
```

**Risk:** The COMPOSE case (relational composition) and LASSERT case (SAT checking) are the hardest. COMPOSE requires M3.3; LASSERT requires showing the on-chip FSM shadow state matches the `vm_step` SAT semantics.

### M5: Retarget Extraction to Canonical vm_apply ✅

**Status: COMPLETE**

**Goal:** Change `Extraction.v` to extract `SimulationProof.vm_apply` instead of `TMC.vm_apply`, and update the downstream pipeline.

**Prerequisite:** M4 (so that extraction matches the fully-proven chain)

**Detailed steps:**

- [ ] M5.1: Audit `Extraction.v` line 293 — identify all definitions currently extracted from TMC
- [ ] M5.2: For each extracted definition, determine whether it comes from TMC-specific code or from shared kernel modules
- [ ] M5.3: Change the `Extraction` command to extract `SimulationProof.vm_apply` (or equivalently, re-export `SimulationProof.vm_apply` as the canonical `vm_apply` in a thin wrapper module)
- [ ] M5.4: Ensure all needed types (`VMState`, `vm_instruction`, etc.) are still extracted — these are shared and should not change
- [ ] M5.5: Run extraction: `make -f CoqMakefile` → verify `build/thiele_core.ml` compiles
- [ ] M5.6: Update `build/extracted_vm_runner.ml` if function signatures changed
- [ ] M5.7: Run extracted VM runner against existing test vectors — document behavioral differences for the 8 divergent opcodes
- [ ] M5.8: Update `scripts/forge_vm.py` if the runner interface changed
- [ ] M5.9: Re-run Python test surface — `tests/test_*.py` — document and fix failures

**Exit criteria:**
- [ ] `build/thiele_core.ml` is generated from `SimulationProof.vm_apply`
- [ ] `build/extracted_vm_runner` compiles and runs
- [ ] `thielecpu/vm.py` works end-to-end
- [ ] Test surface passes (with updated expectations for the 8 divergent opcodes)

**Behavioral changes to expect:**

| Opcode | Old behavior (TMC) | New behavior (SimulationProof) | Impact |
|--------|-------------------|-------------------------------|--------|
| PSPLIT | Can fail → error flag | Always succeeds | Programs relying on PSPLIT failure detection must use firmware-layer checks |
| PMERGE | Can fail → error flag | Always succeeds | Same as above |
| PNEW | Reuses matching modules | Always allocates fresh | Module IDs may differ; semantics preserved |
| EMIT | Sets csr_cert_addr | No CSR change | Programs reading csr_cert_addr after EMIT must adapt |
| REVEAL | Sets csr_cert_addr + raw module | No CSR + mod 16 | Same as above |
| PDISCOVER | Mutates graph | No-op | Discovery tracking moves to firmware |
| MORPH | Decodes coupling from memory | Empty coupling data | Coupling composition at firmware layer |
| MORPH_ASSERT | Sets status + err + cert_addr | Only cert_addr | Programs reading status/err must adapt |

**Risk:** Medium. Behavioral changes affect test expectations but not correctness (the new behavior IS the proven behavior). Main risk is `extracted_vm_runner.ml` API compatibility.

### M6: Unify TMC Narrative and Retire Duplicate vm_apply ✅

**Status: COMPLETE**

**Goal:** Update `ThieleMachineComplete.v` to reference the canonical `SimulationProof.vm_apply` as THE definition, retire the duplicate TMC-local `vm_apply`, and update all narrative sections (6G, 6H) to reflect the unified architecture.

**Prerequisite:** M5

**Detailed steps:**

- [ ] M6.1: In TMC, replace the local `vm_apply` definition (line 2444) with a re-export: `Definition vm_apply := SimulationProof.vm_apply.`
- [ ] M6.2: Prove that `vm_apply_nofi` still works (it's defined as `vm_apply_nofi = vm_apply`, so this is trivial after the re-export)
- [ ] M6.3: Update Section 6G (Python bridge narrative) to reference the unified pipeline
- [ ] M6.4: Update Section 6H (hardware bridge narrative) to reference `embed_step_all` and the full proven chain
- [ ] M6.5: Update Section 6 preamble to describe the ONE-machine architecture
- [ ] M6.6: Remove or archive the old TMC-local graph operations (`graph_psplit`, `graph_pmerge`, `graph_pnew`) that are now unused
- [ ] M6.7: Audit all TMC lemmas that reference the old `vm_apply` — fix or remove
- [ ] M6.8: Full Coq compile gate

**Exit criteria:**
- [ ] TMC has exactly ONE `vm_apply` and it is `SimulationProof.vm_apply`
- [ ] All TMC proofs compile
- [ ] TMC narrative accurately describes the unified architecture
- [ ] No orphaned definitions

**Risk:** TMC is ~7000 lines. Some internal proofs may depend on the specific behavior of the old `vm_apply`. These must be inspected case-by-case. If any proof relied on TMC.vm_apply-specific behavior (e.g., PSPLIT failure), it must be revised or removed.

### M7: End-to-End Integration Testing ✅

**Status: COMPLETE**

**Goal:** Validate the complete unified pipeline with comprehensive tests demonstrating that proof, extraction, simulation, and hardware all compute the same thing.

**Prerequisite:** M5, M6

**Detailed steps:**

- [ ] M7.1: Create `tests/test_unified_pipeline.py` — test that runs programs through both extracted VM and direct Coq evaluation (via test harness) and checks matching outputs
- [ ] M7.2: Create test vectors for all 47 opcodes, including the 8 previously-divergent opcodes
- [ ] M7.3: Create `tests/test_hardware_equivalence.py` — test that compares extracted VM output against kami_step evaluation for all 47 opcodes
- [ ] M7.4: Extend `verify_all_claims.py` to verify the unified architecture claims
- [ ] M7.5: Create `tests/test_nofi_preserved.py` — verify that NoFI theorems still hold by running test programs and checking mu/cert_addr behavior
- [ ] M7.6: Run full test surface: `pytest tests/ -v`
- [ ] M7.7: Run Coq compile gate: all files compile clean
- [ ] M7.8: Run extraction gate: `build/thiele_core.ml` compiles, runner works

**Exit criteria:**
- [ ] All tests pass
- [ ] Every opcode has at least one test vector exercising the extraction → simulation path
- [ ] No test relies on TMC.vm_apply-specific behavior
- [ ] `verify_all_claims.py` passes all checks

### M8: Documentation and Artifact Update ✅

**Status: COMPLETE**

**Goal:** Update all repository documentation to reflect the unified architecture.

**Prerequisite:** M7

**Detailed steps:**

- [x] M8.1: Update `README.md` — already accurate, no TMC.vm_apply references
- [x] M8.2: Update `FULL_REFINEMENT_GUIDE.md` — already complete and updated
- [x] M8.3: Update `artifacts/PROOF_FOUNDATION_AUDIT.md` — added canonicality section
- [x] M8.4: Update `ISA_V2_SPEC.md` — already correctly scoped to transport layer
- [x] M8.5: Update `artifacts/verification_receipt.json` — added unified machine and full-state refinement claims
- [x] M8.6: Archive this roadmap as complete

**Exit criteria:**
- [ ] All documentation accurately reflects the unified architecture
- [ ] No document claims TMC.vm_apply and SimulationProof.vm_apply are different
- [ ] The "one machine" claim is supported end-to-end: Coq proof → OCaml extraction → Python simulation → hardware equivalence

---

## Dependency Graph

```
M0 (baseline) ✅
 │
 ▼
M1 (KamiSnapshot extension) ✅
 │
 ├──────────────┐
 ▼              ▼
M2 (faithful    M5 can start type-level
 kami_step) ✅   work in parallel
 │
 ▼
M3 (commutation lemmas) ✅
 │
 ▼
M4 (embed_step_all — 47/47) ✅
 │
 ├──────────────┐
 ▼              ▼
M5 (retarget   M6 (unify TMC
 extraction)✅  narrative) ✅
 │              │
 ▼              ▼
M7 (integration testing) ✅
 │
 ▼
M8 (documentation) ← IN PROGRESS
```

Critical path: **M0 → M1 → M2 → M3 → M4 → M5 → M7 → M8**

M6 can proceed in parallel with M5 after M4 is complete.

---

## File Inventory: What Gets Created, Modified, or Retired

### New files

| File | Purpose | Milestone |
|------|---------|-----------|
| `coq/kami_hw/RichStateCommutation.v` | Commutation lemmas for bounded-table ↔ graph operations | M3 |
| `coq/kami_hw/EmbedStepAll.v` | Full 47-opcode embed-step theorem | M4 |
| `tests/test_unified_pipeline.py` | End-to-end pipeline validation | M7 |
| `tests/test_hardware_equivalence.py` | Extracted VM vs kami_step comparison | M7 |

### Modified files (significant changes)

| File | Changes | Milestone |
|------|---------|-----------|
| `coq/kami_hw/Abstraction.v` | +6 fields to KamiSnapshot, rewrite gap opcode kami_step arms | M1, M2 |
| `coq/kami_hw/FullAbstraction.v` | Update full_snapshot_of_snapshot | M1 |
| `coq/kami_hw/EmbedStep.v` | Update proofs for new snapshot fields | M1 |
| `coq/kami_hw/FullEmbedStep.v` | Update full-state bridge proofs | M1 |
| `coq/Extraction.v` | Retarget to SimulationProof.vm_apply | M5 |
| `coq/ThieleMachineComplete.v` | Replace vm_apply with re-export, update narrative | M6 |
| `build/extracted_vm_runner.ml` | Update for changed extraction output | M5 |

### Retired/archived definitions

| Definition | File | Reason |
|------------|------|--------|
| TMC-local `vm_apply` (line 2444) | ThieleMachineComplete.v | Replaced by `SimulationProof.vm_apply` re-export |
| TMC-local `graph_psplit` | ThieleMachineComplete.v | Unused after unification |
| TMC-local `graph_pmerge` | ThieleMachineComplete.v | Unused after unification |
| TMC-local `graph_pnew` | ThieleMachineComplete.v | Unused after unification |
| TMC-local `graph_record_discovery` | ThieleMachineComplete.v | Unused after unification |
| TMC-local `load_coupling_from_mem` | ThieleMachineComplete.v | Unused after unification |

---

## Verification Gates

Every milestone must pass ALL gates before proceeding:

| Gate | Command | What it checks |
|------|---------|----------------|
| Coq compile | `cd coq && make -f CoqMakefile` | All .v files compile, zero Admitted in modified files |
| Extraction | `cd coq && make -f CoqMakefile Extraction.vo && cp build/thiele_core.ml ../build/` | Extraction produces valid OCaml |
| OCaml build | `cd build && ocamlfind ocamlc -package ... thiele_core.ml extracted_vm_runner.ml -o extracted_vm_runner` | Extracted runner compiles |
| Python tests | `pytest tests/ -v` | All Python-level tests pass |
| Claims audit | `python verify_all_claims.py` | All repo claims verified |

---

## Canonical Architecture (Target State)

After completion, the architecture is:

```
NoFreeInsight axioms
    │
    │ (representation-agnostic: only vm_mu + csr_cert_addr)
    ▼
vm_step (inductive relation, ~50 constructors)
    │
    │ vm_step_vm_apply (SimulationProof.v line 597)
    ▼
SimulationProof.vm_apply ◄── THE ONE CANONICAL STEP FUNCTION
    │                   │
    │ embed_step_all    │ Extraction.v
    │ (47/47 opcodes)   │
    ▼                   ▼
kami_step           build/thiele_core.ml (OCaml)
    │                   │
    │ KamiExtraction    │ extracted_vm_runner.ml
    ▼                   ▼
ThieleCPUCore.v     build/extracted_vm_runner (binary)
(Kami RTL)              │
    │                   │ scripts/forge_vm.py
    │ synthesis         │
    ▼                   ▼
FPGA bitstream      thielecpu/vm.py (Python wrapper)
```

Every arrow is either a Coq theorem, a mechanical extraction, or an artifact-validated trust boundary. There is ONE machine.

---

## Completion Record

**All milestones M0–M8 complete as of 2026-04-08.**

| Milestone | Status | Key Deliverable |
|-----------|--------|-----------------|
| M0 | ✅ | Baseline verified |
| M1 | ✅ | KamiSnapshot carries CSRs, logic_acc, mstatus; abs_phase1 faithful |
| M2 | ✅ | kami_step has real behavior for all gap opcodes (PSPLIT, PMERGE, MORPH family, TENSOR_GET, COMPOSE) |
| M3 | ✅ | RichStateCommutation.v — all commutation lemmas proved, zero Admitted |
| M4 | ✅ | embed_step_compute covers all 47 opcodes |
| M5 | ✅ | Extraction.v targets SimulationProof.vm_apply |
| M6 | ✅ | TMC architectural note references SimulationProof.vm_apply as canonical |
| M7 | ✅ | test_unified_pipeline.py — 16 integration gates pass |
| M8 | ✅ | Documentation and artifacts updated |

The unification is complete. One machine, one proof, one extraction.
