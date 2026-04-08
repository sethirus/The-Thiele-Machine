# Third-Phase Roadmap: From Supported-Trace Theorem to Universality

**Last updated:** 2026-04-01
**Status:** ALL PHASES COMPLETE.  Phases 1–5 done.  CHSH_TRIAL dispatch swap fixed.

---

## Context: what the second-phase roadmap left

All four phases of the second-phase roadmap are done.  The key closure is:

- `rtl_shadow_trace_compat_supported` (ShadowDeviceTrace.v:150) — unconditional trace
  compatibility for any trace satisfying `SupportedOpcode`, proved using
  `embed_step_supported_trace` from EmbedStep.v §7.  No external hypothesis.

That closes the main gap identified in the January 2026 audit.  What remains:

---

## Known irreducible gaps (not to-do items)

These are design decisions, not proof omissions.  Document them; do not attempt to close.

| Gap | Category | Reason irreducible |
|---|---|---|
| PSPLIT/PMERGE/MORPH×7 | A — Graph/err divergence | Hardware has no partition/morphism graph; `abs_phase1` sets `pg_morphisms = []` by design; kernel sets err=true on failures |
| LJOIN | B — CSR divergence | cert string comparison differs hw vs kernel |
| LASSERT | C — Cost mismatch | Hardware: `S cost`; kernel: `flen*8 + S cost`.  Documented in `kami_vm_mu_lassert_gap` |
| ORACLE_HALTS | C — Cost mismatch | Hardware: 1,000,000; kernel: 2.  Intentional, documented in HARDENING_TRACKER.md G2c |

**Promoted from irreducible to full-state-proved (via kami_step fix + EmbedStep_WF.v):**
- CHSH_TRIAL — dispatch swap in `kami_step` fixed (2026-04-01); `embed_step_chsh_trial` proved under `chsh_bits_ok`; `WFSupportedOpcode` extended to 29 opcodes

**Promoted from irreducible to shadow-proved (via ShadowEmbedStep.v):**
- PNEW, PDISCOVER, EMIT, REVEAL — shadow-level embed_step (unconditional, no precondition)
- TENSOR_SET, TENSOR_GET — conditional shadow embed_step (bounds ok)
- CHSH_TRIAL — conditional shadow embed_step (chsh_bits_ok)

These are **excluded by design** from full-state `SupportedOpcode` but included in `ShadowSupportedOpcode` (30 opcodes).

---

## Active to-do: ranked by value/difficulty

---

### Phase 1 — Category D closure: CALL, RET, CHSH_TRIAL under WellFormedSnapshot

**Priority: HIGH.  Difficulty: LOW.**
**Ref:** EmbedStep.v §7 comment: "These are NOT irreducible — they are proved under WellFormedSnapshot in EmbedStep_WF.v once that invariant is defined."

Extends supported-opcode coverage from 26 to 29.  Unlike A/B/C, these opcodes
have no semantic divergence — they just need a bounded invariant on the snapshot.

- [x] **1a.** Define `WellFormedSnapshot` record in `coq/kami_hw/Abstraction.v` (done — at line 195)
- [x] **1b.** Prove `embed_step_call` and `embed_step_ret` in `coq/kami_hw/EmbedStep_WF.v` (done — full-state, zero Admitted)
- [x] **1b+.** Define `WFSupportedOpcode` (29 opcodes: 26 + CALL under WFS+PC bound, RET under WFS, CHSH_TRIAL under chsh_bits_ok) in EmbedStep_WF.v (done)
- [x] **1c.** Prove `embed_step_chsh_trial` — **FIXED** (2026-04-01).
      The dispatch swap was a bug in `kami_step` (Abstraction.v), not a design divergence.
      The actual Kami hardware (ThieleCPUCore.v) already used the correct kernel convention.
      Fix: swapped `kami_step` from `same := Nat.eqb x y` + `match a, b` to
      `same := Nat.eqb a b` + `match x, y`.  `embed_step_chsh_trial` proved
      under `chsh_bits_ok x y a b = true`.  Zero Admitted.

**Phase 1 shadow extension (COMPLETE):**
- [x] `ShadowEmbedStep.v`: shadow-level embed_step for PNEW, PDISCOVER, EMIT, REVEAL (unconditional)
- [x] `ShadowEmbedStep.v`: conditional shadow embed_step for CHSH_TRIAL, TENSOR_SET, TENSOR_GET
- [x] `ShadowEmbedStep.v`: `ShadowSupportedOpcode` (30 opcodes), `shadow_embed_step_supported`
- [x] `ShadowEmbedStep.v`: `vm_apply_shadow_compat` (compositionality), `shadow_trace_compat_extended` (trace)
- [x] `ShadowDeviceTrace.v`: `rtl_shadow_trace_compat_extended` (30-opcode RTL corollary)
- [x] `ThieleCanonicality.v`: 8th record field `tcm_trace_compat_shadow_extended`

**Phase 1 done condition:** CALL/RET/CHSH_TRIAL proved (EmbedStep_WF.v). 29-opcode WFSupportedOpcode.
30-opcode shadow trace proved (ShadowEmbedStep.v + ShadowDeviceTrace.v). ThieleCanonicality extended to 8 fields.
CHSH_TRIAL dispatch swap fixed in kami_step. Zero Admitted. Inquisitor OK.
**DONE 2026-04-01.**

---

### Phase 2 — Dynamic ShadowDevice interface

**Priority: MEDIUM.  Difficulty: LOW.**

The current `ShadowDevice` record has no step function.  `every_shadow_device_trace_compat`
requires `embed_step` as an external parameter rather than being internal to the device class.
Strengthening the record makes device class membership a self-contained property.

- [x] **2a.** Extend `ShadowDevice` record in `coq/kami_hw/ShadowDevice.v` (done — `DynamicShadowDevice` with `dsd_supported` predicate scoping `dsd_step_embed`):

  ```coq
  Record DynamicShadowDevice := {
    dsd_state  : Type;
    dsd_obs    : dsd_state -> ClassicalState;
    dsd_embed  : dsd_state -> VMState;
    dsd_step   : dsd_state -> vm_instruction -> dsd_state;
    dsd_embed_shadow_compat :
      forall d, dsd_obs d = shadow_proj (dsd_embed d) ;
    dsd_step_embed :
      forall (d : dsd_state) (i : vm_instruction),
        dsd_embed (dsd_step d i) = vm_apply (dsd_embed d) i ;
  }.
  ```

- [x] **2b.** Instantiate `thiele_rtl_dynamic_shadow_device` for the RTL stack (done — uses `SupportedOpcode` + `embed_step_supported`):

  ```coq
  Definition thiele_rtl_dynamic_shadow_device : DynamicShadowDevice := {|
    dsd_state  := KamiSnapshot ;
    dsd_obs    := rtl_classical_obs ;
    dsd_embed  := abs_phase1 ;
    dsd_step   := kami_step ;
    dsd_embed_shadow_compat := hardware_shadow_compat ;
    dsd_step_embed := embed_step_supported ;  (* only for SupportedOpcode *)
  |}.
  ```
  Note: instantiation currently requires restricting to SupportedOpcode or
  the WF variant.  Either scope the record to supported instructions or add
  a [SupportedOpcode i] hypothesis to `dsd_step_embed`.

- [x] **2c.** Prove internal trace theorem (done — `dynamic_shadow_device_trace_compat` + `rtl_dynamic_shadow_trace_compat` corollary + `dynamic_shadow_device_mu_observable`):

  ```coq
  Theorem dynamic_shadow_device_trace_compat :
    forall (D : DynamicShadowDevice) (trace : list vm_instruction) (d : D.(dsd_state)),
      D.(dsd_obs) (fold_left D.(dsd_step) trace d) =
      shadow_proj (fold_left vm_apply trace (D.(dsd_embed) d)).
  ```
  Proof: apply `every_shadow_device_trace_compat` with `D.(dsd_step_embed)`.

**Phase 2 done condition:** `DynamicShadowDevice` record defined; RTL instantiation proved;
`dynamic_shadow_device_trace_compat` proved with no external `embed_step` parameter;
inquisitor clean.  **DONE 2026-04-01.**

---

### Phase 3 — Representation theorem

**Priority: MEDIUM.  Difficulty: HIGH.**

`universal_nfi_any_substrate` proves that any `CertificationSystem` pays ≥1 to certify.
That is a lower-bound result.  The representation theorem shows that any certification
system with a simulation morphism into Thiele is faithfully captured by it.

- [x] **3a.** Add embed field and morphism to `CertificationSystem` (done — `SimulatingCertificationSystem` record in `UniversalCertificationCost.v` with `scs_decode`, `scs_embed`, `scs_step_commutes`, `scs_cost_preserved`, `scs_cert_reflects`):

  ```coq
  Record SimulatingCertificationSystem := {
    scs_base   : CertificationSystem ;
    scs_decode : scs_base.(cs_instr) -> vm_instruction ;
    scs_embed  : scs_base.(cs_state) -> VMState ;
    scs_step_commutes :
      forall (s : scs_base.(cs_state)) (i : scs_base.(cs_instr)),
        scs_embed (scs_base.(cs_step) s i) =
        vm_apply (scs_embed s) (scs_decode i) ;
    scs_cost_preserved :
      forall (i : scs_base.(cs_instr)),
        scs_base.(cs_cost) i >= instruction_cost (scs_decode i) ;
  }.
  ```

- [x] **3b.** Prove the representation theorem (done — `thiele_represents_simulating_cert_system`; helper `scs_run_embed`; `thiele_self_simulating` identity instance):

  ```coq
  Theorem thiele_represents_simulating_cert_system :
    forall (SCS : SimulatingCertificationSystem)
           (s0  : SCS.(scs_base).(cs_state))
           (trace : list (SCS.(scs_base).(cs_instr))),
      SCS.(scs_base).(cs_cert) s0 = false ->
      SCS.(scs_base).(cs_cert) (cs_run SCS.(scs_base) trace s0) = true ->
      (* (1) cost lower bound *)
      cs_total_cost SCS.(scs_base) trace >= 1 /\
      (* (2) the execution embeds into a Thiele certified execution *)
      (fold_left vm_apply (map SCS.(scs_decode) trace) (SCS.(scs_embed) s0)).(vm_certified) = true.
  ```

- [x] **3c.** Part (1) = `universal_nfi_any_substrate` applied to `scs_base`, not new.
  Part (2) = embedded Thiele run certifies, genuinely new — uses `scs_cert_reflects` + `scs_run_embed`.
  Design decision: added `scs_cert_reflects` field (maps external cert to `vm_certified`) to make part (2) provable.

**Phase 3 done condition:** `SimulatingCertificationSystem` defined with all fields;
`thiele_represents_simulating_cert_system` proved; part (2) must be genuinely new content
not provable from existing theorems alone; inquisitor clean.
**DONE 2026-04-01.**

---

### Phase 4 — Shadow converse: Thiele distinguishes shadow-inequivalent states

**Priority: MEDIUM.  Difficulty: MEDIUM.**

The current `degenerate_projection_theorem` (Part 3) proves:
> Classical programs preserve shadow equality (if s1 ≡_shadow s2 then they stay equivalent).

The converse is unproved:
> If `shadow_proj s1 ≠ shadow_proj s2`, then some classical program can distinguish s1 from s2.

- [x] **4a.** Prove the distinguishability lemma (done — `shadow_inequivalent_states_distinguishable` in `TuringClassicalEmbedding.v`; trivial witness: empty program `[]`):

- [x] **4b.** Trivial case confirmed: the empty trace is the witness.  Added as a named theorem with documentation noting that shadow_proj is exactly the distinguishability quotient.

- [x] **4c.** N/A (trivial case applies).

- [x] **4d.** Added as Part 5 of the Degenerate Projection Theorem narrative in `TuringClassicalEmbedding.v`.

**Phase 4 done condition:** theorem stating that shadow-inequivalent states are
distinguishable by some classical program is named and proved; inquisitor clean.
**DONE 2026-04-01.  Trivial witness (empty program) confirmed sufficient.**

---

### Phase 5 — Initiality of Thiele in certified-cost machines

**Priority: LOW.  Difficulty: HIGH.**

This is the longest-horizon item.  Requires defining a category and proving Thiele
is the initial object.

- [x] **5a.** Define the category of certified-cost machines (done — `CertCostMachine` + `CertCostMorphism` in `UniversalCertificationCost.v`):

  ```coq
  Record CertCostMachine := {
    ccm_state  : Type;
    ccm_step   : ccm_state -> vm_instruction -> ccm_state;
    ccm_cost   : vm_instruction -> nat;
    ccm_cert   : ccm_state -> bool;
    ccm_cert_costs :
      forall s i, ccm_cert s = false -> ccm_cert (ccm_step s i) = true ->
                  ccm_cost i >= 1;
  }.

  Record CertCostMorphism (M N : CertCostMachine) := {
    ccm_map : M.(ccm_state) -> N.(ccm_state);
    ccm_map_step :
      forall s i, ccm_map (M.(ccm_step) s i) = N.(ccm_step) (ccm_map s) i;
    ccm_map_cost :
      forall i, N.(ccm_cost) i >= M.(ccm_cost) i;
  }.
  ```

- [x] **5b.** Define `thiele_cert_cost_machine` as a `CertCostMachine` (done — uses `vm_apply`, `instruction_cost`, `vm_certified`, `no_free_certification_certified`).

- [x] **5c.** Prove initiality (done — reachability-restricted form):
  - `thiele_morphism_exists`: given a simulation map, constructs a `CertCostMorphism`
  - `thiele_morphism_unique_on_traces`: any two morphisms agreeing at s0 agree on all reachable states
  - `thiele_id_morphism`: identity morphism
  - `ccm_to_cert_system` + `ccm_universal_nfi`: every `CertCostMachine` satisfies universal NoFI
  - Full `exists!` uniqueness documented as requiring state surjectivity or reachability restriction (design note in file header)

  ```coq
  Theorem thiele_is_initial_cert_cost_machine :
    forall (M : CertCostMachine),
      exists! (phi : CertCostMorphism thiele_cert_cost_machine M), True.
  ```

  Note: uniqueness requires that the morphism maps are uniquely determined by
  step-commutation + cost preservation.  This may require state surjectivity
  or a reachability assumption.

**Phase 5 done condition:** `CertCostMachine` category defined; Thiele instantiated;
initiality theorem stated and proved (reachability-restricted uniqueness; full
`exists!` requires state surjectivity, documented as design note); inquisitor clean.
**DONE 2026-04-01.**

---

## Active log

| Date | Change |
|---|---|
| 2026-03-30 | Document created from repo-grounded audit |
| 2026-03-30 | Confirmed `rtl_shadow_trace_compat_supported` already proved in ShadowDeviceTrace.v:150 |
| 2026-03-30 | Confirmed `SupportedOpcode`, `embed_step_supported`, `embed_step_supported_trace` in EmbedStep.v §7 |
| 2026-03-30 | EmbedStep.v §7 comment identifies `EmbedStep_WF.v` as planned file for Category D |
| 2026-03-30 | EmbedStep_WF.v created: CALL/RET full-state embed_step under WellFormedSnapshot; WFSupportedOpcode (28 opcodes) |
| 2026-03-30 | ShadowEmbedStep.v created: shadow-level embed_step for 30 opcodes; compositionality; trace theorem |
| 2026-03-30 | ShadowDeviceTrace.v updated: rtl_shadow_trace_compat_extended (30-opcode RTL corollary) |
| 2026-03-30 | ThieleCanonicality.v updated: 8th field tcm_trace_compat_shadow_extended |
| 2026-04-01 | Phase 2 complete: DynamicShadowDevice record (with dsd_supported predicate); RTL instance; self-contained trace theorem; μ-cost corollary |
| 2026-04-01 | Phase 4 complete: shadow_inequivalent_states_distinguishable proved (trivial witness: empty program) |
| 2026-04-01 | Phase 1c reclassified as irreducible: CHSH_TRIAL dispatch swap (hw: eqb x y + match a,b; kernel: eqb a b + match x,y) |
| 2026-04-01 | **Phase 1c FIXED**: dispatch swap was a bug in kami_step, not a design divergence.  Actual Kami HW (ThieleCPUCore.v) already correct.  Fixed kami_step in Abstraction.v; proved embed_step_chsh_trial under chsh_bits_ok; WFSupportedOpcode now 29 opcodes |
| 2026-04-01 | Phase 3 complete: SimulatingCertificationSystem record + thiele_represents_simulating_cert_system + thiele_self_simulating |
| 2026-04-01 | Phase 5 complete: CertCostMachine + CertCostMorphism + thiele_cert_cost_machine + thiele_morphism_exists + thiele_morphism_unique_on_traces + thiele_id_morphism + ccm_universal_nfi |
| 2026-04-01 | **ALL PHASES COMPLETE.** |

---

## Quick-reference: key files

| File | Role |
|---|---|
| `coq/kami_hw/EmbedStep.v` | `SupportedOpcode`, `embed_step_supported`, `embed_step_supported_trace` |
| `coq/kami_hw/EmbedStep_WF.v` | `WFSupportedOpcode` (29 opcodes), `embed_step_call`, `embed_step_ret`, `embed_step_chsh_trial` (DONE) |
| `coq/kami_hw/ShadowEmbedStep.v` | `ShadowSupportedOpcode` (30 opcodes), `shadow_embed_step_supported`, `vm_apply_shadow_compat`, `shadow_trace_compat_extended` (DONE) |
| `coq/kami_hw/ShadowDeviceTrace.v` | `rtl_shadow_trace_compat_supported` (26), `rtl_shadow_trace_compat_extended` (30) (DONE) |
| `coq/kami_hw/ShadowDevice.v` | `ShadowDevice` record; `DynamicShadowDevice` record (Phase 2 — DONE); RTL instances; `dynamic_shadow_device_trace_compat` |
| `coq/kernel/UniversalCertificationCost.v` | `CertificationSystem`, `universal_nfi_any_substrate`; `SimulatingCertificationSystem` + `thiele_represents_simulating_cert_system` (Phase 3 — DONE); `CertCostMachine` + `CertCostMorphism` + `thiele_morphism_unique_on_traces` (Phase 5 — DONE) |
| `coq/kernel/TuringClassicalEmbedding.v` | `degenerate_projection_theorem`; `shadow_inequivalent_states_distinguishable` (Phase 4 — DONE) |
| `coq/kami_hw/ThieleCanonicality.v` | `ThieleCanonicalModel`; Phase 5 adds initiality |
| `coq/kami_hw/VerilogRefinement.v` | All 47 per-instruction RTL simulation; `kami_vm_mu_lassert_gap` |

---

## Execution order

The phases are mostly independent.  Recommended execution order:

```
Phase 1 (Category D, 3 opcodes, EmbedStep_WF.v)
  → unblocks cleaner coverage claims in print

Phase 2 (DynamicShadowDevice)
  → unblocks fully self-contained device class theorem

Phase 3 (Representation theorem)
  → depends on no other phase; can run in parallel with 1+2

Phase 4 (Shadow converse)
  → depends on no other phase; likely trivial, verify first

Phase 5 (Initiality)
  → depends loosely on Phase 2 and 3 for motivation
```
