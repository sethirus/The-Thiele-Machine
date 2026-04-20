# The Thiele Machine — Master Completion Plan

> **One sentence:** Close the two remaining COMPOSE / MORPH_TENSOR proof gaps in
> `GraphReconstructionBridge.v`, wire them through `CanonicalCPUProof.v` and
> `Extraction.v`, update the gap registry, and run `make closeout-gate` to
> produce a fully certified 46-opcode monoidal-category machine extracted from a
> coherent proof chain.

---

## Running Status Table

Every row maps to exactly one concrete deliverable.
Change the **Status** cell as you finish each item.

| # | Phase | Deliverable | File(s) | Status |
|---|---|---|---|---|
| 1 | Orientation | Read and annotate the seven key files | see §1 | ☐ Not started |
| 2 | Proof gap 1 | `driven_step_compose` (full equality, Qed) | `GraphReconstructionBridge.v` | ☐ Not started |
| 3 | Proof gap 2 | `driven_step_morph_tensor` (full equality, Qed) | `GraphReconstructionBridge.v` | ☐ Not started |
| 4 | Wire gaps | Add COMPOSE + MORPH_TENSOR arms to `WFDrivenPrecondition` + `driven_step_wf` | `GraphReconstructionBridge.v` | ☐ Not started |
| 5 | EmbedStep doc | Update §9 comment in `EmbedStep.v` (no code change) | `EmbedStep.v` | ☐ Not started |
| 6 | Gap registry | Remove 7 MORPH gaps; update `rtl_gap_count` to 5 | `RTLGapRegistry.v` | ☐ Not started |
| 7 | Canonical bundle | Add 4 fields to `CanonicalCPUProofBundle` record | `CanonicalCPUProof.v` | ☐ Not started |
| 8 | Extraction anchors | Add `extraction_compose_anchor` + `extraction_monoidal_coherence_anchor` | `Extraction.v` | ☐ Not started |
| 9 | Coq build | `make coq-gate` — zero Admitted, zero errors | root `Makefile` | ☐ Not started |
| 10 | Extraction | `make canonical-extract` — regenerate `thiele_core.ml` + `Target.ml` | root `Makefile` | ☐ Not started |
| 11 | RTL gate | `make rtl-gate` — Yosys synthesis passes | root `Makefile` | ☐ Not started |
| 12 | Cosim gate | `make cosim-gate` — iverilog cosimulation passes | root `Makefile` | ☐ Not started |
| 13 | Closeout | `make closeout-gate` — all 10 closure steps green | root `Makefile` | ☐ Not started |

---

## The Architecture in One Picture

```
Categorical_Engine (Python — origin project)
  AbstractMorphism.apply_element  →  vm_apply
  compose(f,g) + Z3 postcondition →  driven_step_compose (Coq Qed)
  IdentityMorphism                →  driven_step_morph_id (Coq Qed ✓)
  monoidal composition (felt)     →  CategoryMonoidal.monoidal_coherence (Coq Qed ✓)
  Bell-CHSH 16/5 experiment       →  instr_chsh_trial + TsirelsonQuantumModel.v (Coq Qed ✓)
  Z3 property assertions          →  MORPH_ASSERT (mandatory S cost) (Coq Qed ✓)

VMStep.v / VMState.v            — 46-opcode ISA, zero Admitted
   ↓  SimulationProof.v          — vm_step ≡ vm_apply (Qed)
   ↓  EmbedStep.v                — 39 opcodes under abs_phase1 (Qed)
   ↓  GraphReconstructionBridge.v — 45/46 under abs_full_snapshot (Qed)
      ← COMPOSE: field-only, needs driven_step_compose (gap 1)
      ← MORPH_TENSOR: field-only, needs driven_step_morph_tensor (gap 2)
   ↓  CanonicalCPUProof.v         — canonical proof bundle + extraction root
   ↓  KamiExtraction.v / Extraction.v
   ↓  build/kami_hw/Target.ml     (OCaml, extracted from Coq)
   ↓  build/kami_hw/PP.ml → thiele_hw.bsv  (Bluespec)
   ↓  bsc → coq/kami_hw/coq/build/kami_hw/mkModule1_synth.v  (synthesizable Verilog)
   ↓  make rtl-gate / cosim-gate / closeout-gate
```

---

## Exact Proof State Right Now

### What is already fully Qed (do not touch)

| Theorem | File | Line | Precondition |
|---|---|---|---|
| `driven_step_morph` | `GraphReconstructionBridge.v` | 1466 | `extended_hw_invariant` + modules exist |
| `driven_step_morph_id` | `GraphReconstructionBridge.v` | 2035 | `extended_hw_invariant` + module exists |
| `driven_step_morph_delete` | `GraphReconstructionBridge.v` | 1401 | `morph_table_wf` |
| `driven_step_morph_assert` | `GraphReconstructionBridge.v` | 1233 | `morph_table_wf` |
| `driven_step_morph_get` | `GraphReconstructionBridge.v` | 1308 | `extended_hw_invariant` |
| `coupling_data_round_trip` | `GraphReconstructionBridge.v` | 683 | — |
| `coupling_desc_all_zero` + `extended_hw_invariant` | `GraphReconstructionBridge.v` | 765–774 | — |
| `monoidal_coherence` | `CategoryMonoidal.v` | — | — |
| `relational_compose_assoc` | `CategoryLaws.v` | — | — |
| `tensor_bifunctor` | `CategoryMonoidal.v` | — | — |

### What needs to be written (the actual work)

| Theorem | Currently | Needs | Key lemmas to apply |
|---|---|---|---|
| `driven_step_compose` | `driven_step_compose_fields` (5 fields only, L2111) | Full VMState equality (Qed) | `coupling_data_round_trip` + `coupling_desc_all_zero` → composed coupling = `[]` both sides |
| `driven_step_morph_tensor` | `driven_step_morph_tensor_fields` (4 fields only, L2190) | Full VMState equality (Qed) | `abs_full_snapshot_of_snapshot` graph agreement + `coupling_data_round_trip` + error-path agreement |

### What needs updating (no new proofs)

| Item | File | Change |
|---|---|---|
| `WFDrivenPrecondition` COMPOSE arm | `GraphReconstructionBridge.v` L2306 | `False` → `extended_hw_invariant ks` |
| `WFDrivenPrecondition` MORPH_TENSOR arm | `GraphReconstructionBridge.v` L2308 | `False` → `extended_hw_invariant ks` |
| `driven_step_wf` dispatch | `GraphReconstructionBridge.v` L2319 | Add 2 arms for COMPOSE, MORPH_TENSOR |
| §9 comment in `EmbedStep.v` | `EmbedStep.v` | Clarify: gaps are correct for `abs_phase1`; full coverage is in `GraphReconstructionBridge.v` |
| `rtl_gap_registry` | `RTLGapRegistry.v` | Remove 7 MORPH gap entries |
| `rtl_gap_count` | `RTLGapRegistry.v` L167 | `= 12` → `= 5` |
| `MORPH_not_in_hardware` etc. | `RTLGapRegistry.v` L211–217 | Remove or replace with `morph_family_fully_bridged` |
| `CanonicalCPUProofBundle` record | `CanonicalCPUProof.v` | Add 4 fields |
| `extraction_compose_anchor` | `Extraction.v` | New theorem |
| `extraction_monoidal_coherence_anchor` | `Extraction.v` | New theorem |

---

## Phase 1 — Orientation (read before touching anything)

Seven files. Read them in this order. Understand them before writing proof code.

1. **`coq/kami_hw/GraphReconstructionBridge.v` L683–774** — `coupling_data_round_trip`, `coupling_desc_all_zero`, `extended_hw_invariant`. These are the load-bearing lemmas for Phases 2 and 3.

2. **`coq/kami_hw/GraphReconstructionBridge.v` L2111–2230** — `driven_step_compose_fields` and `driven_step_morph_tensor_fields`. These are the partial proofs you will extend. Read every line. Understand why each field closes.

3. **`coq/kami_hw/GraphReconstructionBridge.v` L900–950** — `coupling_zero_empty` and the lemma that says all coupling pairs are `[]` under `coupling_desc_all_zero`. This is the critical step that makes COMPOSE's coupling gap disappear.

4. **`coq/kami_hw/Abstraction.v` L490–540** — `abs_phase1`, `abs_full_snapshot`, `snap_full_graph`. Understand the difference between these three projections. `abs_phase1` has `vm_graph := snap_pt_to_graph` (no morphisms). `abs_full_snapshot` has `vm_graph := snap_full_graph` (full morphism state). The morph proofs live in the `abs_full_snapshot` world.

5. **`coq/kami_hw/GraphReconstructionBridge.v` L1466–1600** — `driven_step_morph`. This is the template. Your proofs for COMPOSE and MORPH_TENSOR follow the same structure: unfold `kami_step`, unfold `vm_apply`, use rich-state lemmas, close field by field with `reflexivity` or `f_equal`.

6. **`coq/kernel/CategoryMonoidal.v`** — `monoidal_coherence`, `tensor_bifunctor`, `coupling_tensor`. These are the algebraic theorems that give MORPH_TENSOR its semantic meaning.

7. **`coq/kernel/CategoryLaws.v`** — `relational_compose`, `relational_compose_assoc`. These underlie COMPOSE.

---

## Phase 2 — `driven_step_compose` (the first gap)

**File:** `coq/kami_hw/GraphReconstructionBridge.v`  
**Insert after:** `driven_step_compose_fields` (line ~2188)

### Why the gap exists
`driven_step_compose_fields` proves all fields *except* `vm_graph` and `vm_regs` because:
- `vm_regs`: the new morphism ID written to `dst` might differ if the graph-side new_id differs from the hardware-side `rich_next_morph_id`
- `vm_graph`: the new morphism's `coupling_pairs` come from `relational_compose(e1_pairs, e2_pairs)` on the kernel side; from `rich_state_add_morph_with_coupling(... composed_pairs ...)` on the hardware side

### Why the gap closes under `extended_hw_invariant`
`extended_hw_invariant` includes `coupling_desc_all_zero`:
```
coupling_desc_all_zero rs := forall i, morph_entry_coupling_desc (rich_morph_table rs i) = 0
```
And `coupling_data_round_trip` + `coupling_zero_empty` (line ~900) prove:
```
coupling_zero_empty: coupling_desc_table rs desc_id = None ->
  snapshot_coupling_pairs_from_desc rs desc_id = []
```
So under `coupling_desc_all_zero`:
- For any existing morphism `e`, `snapshot_coupling_pairs_from_desc rs e.coupling_desc = []`
- Therefore `relational_compose [] [] = []`
- And `rich_state_add_morph_with_coupling rs ... [] ... false` stores `coupling_pairs = []`
- The new morphism ID on both sides is `rich_next_morph_id rs` (same value) → `vm_regs` closes

### Proof skeleton
```coq
Theorem driven_step_compose :
  forall ks dst m1_id m2_id cost,
    extended_hw_invariant ks ->
    (* morphisms exist *)
    (exists e1, rich_morph_table (snap_rich_state ks) m1_id = Some e1) ->
    (exists e2, rich_morph_table (snap_rich_state ks) m2_id = Some e2) ->
    (* endpoint matches *)
    morph_entry_target (force rich_morph_table m1_id) =
    morph_entry_source (force rich_morph_table m2_id) ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_compose dst m1_id m2_id cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_compose dst m1_id m2_id cost).
Proof.
  intros ks dst m1_id m2_id cost Hinv [e1 He1] [e2 He2] Hep.
  (* 1. Unfold both sides *)
  unfold kami_step. unfold vm_apply. cbn [abs_full_snapshot full_snapshot_of_snapshot].
  (* 2. Apply coupling_data_round_trip twice:
        e1.coupling_pairs = [] and e2.coupling_pairs = []  *)
  have He1_cz := coupling_desc_all_zero_gives_empty Hinv m1_id He1.
  have He2_cz := coupling_desc_all_zero_gives_empty Hinv m2_id He2.
  (* 3. relational_compose [] [] = [] *)
  rewrite He1_cz, He2_cz.
  cbn [relational_compose].
  (* 4. Both sides call rich_state_add_morph with the same args;
        new_id = rich_next_morph_id (snap_rich_state ks) on both sides *)
  apply driven_step_compose_fields.   (* closes all other fields *)
  (* 5. vm_graph: snap_full_graph of advanced state = graph_add_morphism result *)
  apply morph_add_graph_commutes; assumption.
  (* 6. vm_regs: dst ← new_id, same new_id on both sides *)
  rewrite snap_morph_next_id_agrees; reflexivity.
Qed.
```

The helper lemmas `coupling_desc_all_zero_gives_empty` and `snap_morph_next_id_agrees` are either already proven or are one-line consequences of the existing lemmas.

---

## Phase 3 — `driven_step_morph_tensor` (the second gap)

**File:** `coq/kami_hw/GraphReconstructionBridge.v`  
**Insert after:** `driven_step_morph_tensor_fields` (line ~2226)

### Why the gap exists
`driven_step_morph_tensor_fields` proves all fields except `vm_graph`, `vm_regs`, `vm_err` because:
- Hardware calls `graph_tensor_morphisms (snap_full_graph ks)` — the *same* function as `vm_apply`
- But `snap_full_graph ks` must equal `vm_graph (abs_full_snapshot (full_snapshot_of_snapshot ks))` — this requires `abs_full_snapshot_of_snapshot` coherence
- `vm_err`: depends on whether `graph_tensor_morphisms` returns `None` (disjointness fails) or `Some` — same condition on same input → same error flag

### Why the gap closes under `extended_hw_invariant`
Under `extended_hw_invariant`, `abs_full_snapshot_of_snapshot ks` is well-defined and:
```
abs_full_snapshot_of_snapshot_vm_graph :
  extended_hw_invariant ks ->
  (abs_full_snapshot (full_snapshot_of_snapshot ks)).vm_graph = snap_full_graph ks
```
This is proven (or follows directly) from `FullAbstraction.v` + `RichStateCommutation.v`.

Given that, both hardware and kernel call `graph_tensor_morphisms` on the *identical* graph with the *identical* morphism IDs. The results are definitionally equal. The coupling pairs follow the same `coupling_data_round_trip` argument as in Phase 2 (under `coupling_desc_all_zero`, new tensor coupling = `coupling_tensor [] [] = []`).

### Proof skeleton
```coq
Theorem driven_step_morph_tensor :
  forall ks dst f_id g_id cost,
    extended_hw_invariant ks ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_morph_tensor dst f_id g_id cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_morph_tensor dst f_id g_id cost).
Proof.
  intros ks dst f_id g_id cost Hinv.
  (* 1. Establish graph equality *)
  have Hgraph : (abs_full_snapshot (full_snapshot_of_snapshot ks)).vm_graph =
                snap_full_graph ks
    := abs_full_snapshot_of_snapshot_vm_graph Hinv.
  (* 2. Unfold both sides; rewrite hardware graph with Hgraph *)
  unfold kami_step, vm_apply. cbn.
  rewrite <- Hgraph.
  (* 3. graph_tensor_morphisms called on same graph with same ids *)
  destruct (graph_tensor_morphisms _ f_id g_id) as [[g' new_ms] |] eqn:Htensor.
  - (* Success path: both sides store new morphism, write new_id to dst *)
    apply driven_step_morph_tensor_fields.
    + (* vm_graph: snap_full_graph of advanced state = g' *)
      apply tensor_morph_graph_commutes; [assumption | exact Htensor].
    + (* vm_regs: new_id same on both sides *)
      rewrite snap_morph_next_id_agrees; reflexivity.
    + (* vm_err: success on both sides *)
      reflexivity.
  - (* Error/None path: both sides set vm_err = true *)
    apply driven_step_morph_tensor_fields.
    + (* vm_graph: unchanged on both sides *)
      reflexivity.
    + (* vm_regs: no dst write on error *)
      reflexivity.
    + (* vm_err: both sides propagate the None result *)
      reflexivity.
Qed.
```

---

## Phase 4 — Wire into `WFDrivenPrecondition` and `driven_step_wf`

**File:** `coq/kami_hw/GraphReconstructionBridge.v` — Lines 2306–2319

Two changes:

**Change A** — `WFDrivenPrecondition`:
```coq
(* Before *)
| instr_compose _ _ _ _ => False  (* §16: driven_step_compose_fields *)
| instr_morph_tensor _ _ _ _ => False  (* §16: driven_step_morph_tensor_fields *)

(* After *)
| instr_compose _ _ _ _ => extended_hw_invariant ks
| instr_morph_tensor _ _ _ _ => extended_hw_invariant ks
```

**Change B** — `driven_step_wf` dispatch:
```coq
(* Add two new arms before the terminal contradiction *)
- (* instr_compose *)
  exact (driven_step_compose ks _ _ _ _ Hpre).
- (* instr_morph_tensor *)
  exact (driven_step_morph_tensor ks _ _ _ _ Hpre).
```

Update the coverage comment at line ~2232:
```
(* 46/46 opcodes fully addressed under WFDrivenPrecondition.
   All 7 MORPH family opcodes are now Qed with full VMState equality. *)
```

---

## Phase 5 — EmbedStep.v documentation update

**File:** `coq/kami_hw/EmbedStep.v` — §9 comment block (lines ~430–500)

Replace the heading "irreducible gaps" with an accurate characterization:

```coq
(** §9  Abstraction-boundary documentation for MORPH family opcodes

    These seven opcodes pass [False] in [embed_step_compute] because
    [EmbedStep.v] works under the WEAKER [abs_phase1] abstraction, which
    projects [vm_graph := snap_pt_to_graph] (partition state only, no
    morphism state).  Under [abs_phase1], MORPH opcodes change [vm_graph]
    in ways [abs_phase1] cannot represent — so [False] is *correct* here.

    This is NOT a proof failure.  It is a correct documentation of the
    abstraction boundary.

    FULL COVERAGE lives in [GraphReconstructionBridge.v] under the
    stronger [abs_full_snapshot] abstraction:

      MORPH         — driven_step_morph         (Qed)
      MORPH_ID      — driven_step_morph_id      (Qed)
      MORPH_DELETE  — driven_step_morph_delete  (Qed)
      MORPH_ASSERT  — driven_step_morph_assert  (Qed)
      MORPH_GET     — driven_step_morph_get     (Qed)
      COMPOSE       — driven_step_compose       (Qed)  ← Phase 2
      MORPH_TENSOR  — driven_step_morph_tensor  (Qed)  ← Phase 3

    All preconditions are [extended_hw_invariant], a structural invariant
    maintained by the hardware initialization procedure. *)
```

No code changes to `SupportedOpcode` — the definition is correct for its abstraction level.

---

## Phase 6 — RTLGapRegistry.v

**File:** `coq/kami_hw/RTLGapRegistry.v`

### Remove from `rtl_gap_registry` list
Remove these 7 entries: `gap_MORPH`, `gap_COMPOSE`, `gap_MORPH_ID`, `gap_MORPH_DELETE`, `gap_MORPH_ASSERT`, `gap_MORPH_TENSOR`, `gap_MORPH_GET`

### Update `rtl_gap_count`
```coq
(* Before *)
Theorem rtl_gap_count : List.length rtl_gap_registry = 12.

(* After *)
Theorem rtl_gap_count : List.length rtl_gap_registry = 5.
```

The 5 remaining conditional gaps: `gap_TENSOR_SET`, `gap_TENSOR_GET`, `gap_CALL`, `gap_RET`, `gap_CHSH_TRIAL`. These are correct — they have field-only or preconditioned proofs, not unconditional full-state equality.

### Replace the `MORPH_not_in_hardware` block with a closure theorem
```coq
(** The MORPH family is fully bridged. Replace the old
    irreducibility claims with a positive closure statement. *)
Theorem morph_family_fully_bridged :
  ~ In gap_MORPH rtl_gap_registry /\
  ~ In gap_COMPOSE rtl_gap_registry /\
  ~ In gap_MORPH_ID rtl_gap_registry /\
  ~ In gap_MORPH_DELETE rtl_gap_registry /\
  ~ In gap_MORPH_ASSERT rtl_gap_registry /\
  ~ In gap_MORPH_TENSOR rtl_gap_registry /\
  ~ In gap_MORPH_GET rtl_gap_registry.
Proof. repeat split; intro H; exact (rtl_coverage_partition H). Qed.
```

---

## Phase 7 — CanonicalCPUProof.v

**File:** `coq/kami_hw/CanonicalCPUProof.v`

### Add 4 fields to `CanonicalCPUProofBundle` record

Add after `canonical_nofi_quantitative_state_space` (line ~141):

```coq
  (* Categorical completeness: COMPOSE opcode simulates vm_apply *)
  canonical_compose_step_simulates :
    forall ks dst m1_id m2_id cost,
      extended_hw_invariant ks ->
      abs_full_snapshot (full_snapshot_of_snapshot
        (kami_step ks (instr_compose dst m1_id m2_id cost))) =
      vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
        (instr_compose dst m1_id m2_id cost);

  (* Categorical completeness: MORPH_TENSOR opcode simulates vm_apply *)
  canonical_morph_tensor_step_simulates :
    forall ks dst f_id g_id cost,
      extended_hw_invariant ks ->
      abs_full_snapshot (full_snapshot_of_snapshot
        (kami_step ks (instr_morph_tensor dst f_id g_id cost))) =
      vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
        (instr_morph_tensor dst f_id g_id cost);

  (* Monoidal coherence: tensor of processes is strictly monoidal *)
  canonical_monoidal_coherence :
    forall r1 r2 r3 : list (nat * nat),
      coupling_tensor (coupling_tensor r1 r2) r3 =
      coupling_tensor r1 (coupling_tensor r2 r3) /\
      coupling_tensor [] r1 = r1 /\
      coupling_tensor r1 [] = r1;

  (* Composition associativity: relational composition of couplings *)
  canonical_compose_assoc :
    forall r1 r2 r3 : Coupling,
      relational_compose (relational_compose r1 r2) r3 ≡
      relational_compose r1 (relational_compose r2 r3);
```

### Add to the proof term
```coq
       canonical_compose_step_simulates := driven_step_compose;
       canonical_morph_tensor_step_simulates := driven_step_morph_tensor;
       canonical_monoidal_coherence := CategoryMonoidal.monoidal_coherence;
       canonical_compose_assoc := CategoryLaws.relational_compose_assoc |}.
```

---

## Phase 8 — Extraction.v anchors

**File:** `coq/Extraction.v`

Add before the `Set Extraction Optimize` at end of anchor block:

```coq
(** [extraction_compose_anchor]: pins COMPOSE hardware bridge into extraction root.
    The hardware step for instr_compose simulates vm_apply under extended_hw_invariant. *)
Theorem extraction_compose_anchor :
  forall ks dst m1_id m2_id cost,
    extended_hw_invariant ks ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_compose dst m1_id m2_id cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_compose dst m1_id m2_id cost).
Proof.
  exact driven_step_compose.
Qed.

(** [extraction_morph_tensor_anchor]: pins MORPH_TENSOR hardware bridge. *)
Theorem extraction_morph_tensor_anchor :
  forall ks dst f_id g_id cost,
    extended_hw_invariant ks ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_morph_tensor dst f_id g_id cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_morph_tensor dst f_id g_id cost).
Proof.
  exact driven_step_morph_tensor.
Qed.

(** [extraction_monoidal_coherence_anchor]: pins the monoidal category laws.
    The tensor of processes on this machine is strictly associative with unit []. *)
Theorem extraction_monoidal_coherence_anchor :
  forall r1 r2 r3 : list (nat * nat),
    coupling_tensor (coupling_tensor r1 r2) r3 =
    coupling_tensor r1 (coupling_tensor r2 r3) /\
    coupling_tensor [] r1 = r1 /\
    coupling_tensor r1 [] = r1.
Proof.
  exact CategoryMonoidal.monoidal_coherence.
Qed.
```

---

## Phases 9–13 — Build Gates

Run these in order. Each must pass before the next.

```bash
# Phase 9: All Coq proofs compile, zero Admitted
make coq-gate

# Phase 10: Extract to OCaml / BSV / Verilog
make canonical-extract

# Phase 11: Yosys synthesis
make rtl-gate

# Phase 12: iverilog cosimulation
make cosim-gate

# Phase 13: Full closure — all 10 steps green
make closeout-gate
```

### What the Makefile actually does at each stage

| Command | Steps | Validates |
|---|---|---|
| `make coq-gate` | `make -C coq -j4`; grep for Admitted | Zero admitted, all .vo compile |
| `make canonical-extract` | Coq → `build/thiele_core.ml`, `build/kami_hw/Target.ml`, `Main.ml` → `thiele_hw.bsv` | Extraction freshness |
| `make rtl-gate` | Yosys `read_verilog`, `prep -top mkModule1`, `check`, `stat` | No Yosys errors |
| `make cosim-gate` | `pytest tests/test_verilog_cosim.py::TestCompilation::test_kami_rtl_compiles` | iverilog compiles RTL |
| `make closeout-gate` | 10 steps: coq-gate + canonical-extract + inquisitor + 6 pytest suites + isomorphism-bitlock | Full repo closedness |

---

## What Gets Certified When This Is Done

The extraction chain produces a **single Coq object** — `CanonicalCPUProof.canonical_cpu_module` — that:

1. Is a verified Kami/Bluespec hardware module
2. Simulates `vm_apply` for **all 46 opcodes** under `WFDrivenPrecondition`
3. Carries the full formal proof of:
   - **NoFI**: no information gain without μ cost (→ thermodynamics → Raychaudhuri → discrete GR)
   - **Tsirelson bound**: CHSH ≤ 2√2, with Born rule uniqueness
   - **Monoidal coherence**: tensor of processes is strictly associative
   - **Composition associativity**: relational composition of couplings
   - **COMPOSE + MORPH_TENSOR**: hardware steps are proven correct for categorical operations
4. Extracts to OCaml → Bluespec → **synthesizable Verilog** via `make canonical-extract`
5. Passes `make closeout-gate` — the single command that means the repository is done

The category theory is not decorative. It is the formal statement that this machine **operates in a verified monoidal category of certified processes**, where:
- Objects are partition modules
- Morphisms are `PartitionGraph.morphisms` with proven coupling semantics
- Composition is `instr_compose`, proven correct at the hardware boundary
- Tensor is `instr_morph_tensor`, proven coherent by `monoidal_coherence`
- Identity is `instr_morph_id`, proven correct (`driven_step_morph_id`)
- Certification costs μ (`MORPH_ASSERT`, `LASSERT`) — enforced by hardware

The Categorical Engine was the first sketch. This is the proof.

---

## Key Files Reference

| File | Role | Key theorems |
|---|---|---|
| `coq/kernel/VMStep.v` | 46-opcode ISA specification | `vm_instruction`, `instruction_cost` |
| `coq/kernel/CategoryLaws.v` | Relational algebra | `relational_compose_assoc`, `relational_compose_diagonal_*` |
| `coq/kernel/CategoryMonoidal.v` | Monoidal structure | `monoidal_coherence`, `tensor_bifunctor` |
| `coq/kernel/CategoryBridge.v` | Laws pinned to graph ops | `graph_add_morphism_new_id_lookup`, `graph_compose_morphisms_coupling` |
| `coq/kami_hw/Abstraction.v` | Hardware↔kernel projection | `abs_phase1`, `abs_full_snapshot`, `snap_full_graph`, `kami_advance_rich_morph` |
| `coq/kami_hw/EmbedStep.v` | 39-opcode bridge (abs_phase1) | `embed_step_compute`, `SupportedOpcode` |
| `coq/kami_hw/GraphReconstructionBridge.v` | **The real work — 44/46 Qed + 2 gaps** | `driven_step_wf`, `WFDrivenPrecondition`, `coupling_data_round_trip` |
| `coq/kami_hw/CanonicalCPUProof.v` | Proof bundle + extraction root | `CanonicalCPUProofBundle`, `canonical_cpu_module` |
| `coq/kami_hw/KamiExtraction.v` | Coq → OCaml | `canonical_cpu_module`, `targetB` |
| `coq/Extraction.v` | Full extraction + anchors | All extraction anchors |
| `coq/kami_hw/RTLGapRegistry.v` | Gap accounting | `rtl_gap_registry`, `rtl_gap_count` |
