# Second-Phase Roadmap: From Degenerate Projection to Universality

**Last updated:** 2026-03-29
**Status:** Phase 1 (hardware shadow bridge) — next up

---

## Guiding sequence

```
model theorem → hardware shadow bridge → device class theorem → canonical representation
```

The degenerate-projection theorem is done. The next climb is:

1. **Close the hardware-shadow bridge** — connect RTL observations to `shadow_proj` formally
2. **Package as a device-class interface** — abstract the RTL instance into a reusable record
3. **Prove the device-class theorem** — any device satisfying the interface is a Thiele-shadow device
4. **Canonicality** — Thiele is the initial/universal certified-cost shadow machine

---

## Audit: what already exists

| Claim | File | Status |
|---|---|---|
| Per-instruction RTL simulation (all 47 opcodes) | `coq/kami_hw/VerilogRefinement.v` | ✅ done |
| Canonical CPU proof bundle | `coq/kami_hw/CanonicalCPUProof.v` | ✅ done |
| Three-layer Coq/RTL/OCaml commuting triangle | `coq/kami_hw/RTLCorrectnessInstantiation.v` | ✅ done |
| OCaml extraction correctness (G1a/b) | HARDENING_TRACKER.md phases G1a/b | ✅ done |
| Substrate-generic NoFI schema | `coq/kernel/UniversalCertificationCost.v` | ✅ done |
| Classical shadow strictly lossy | `coq/kernel/ShadowProjection.v` | ✅ done |
| Degenerate projection theorem | `coq/kernel/TuringClassicalEmbedding.v` | ✅ done |
| RTL observation ↔ shadow_proj bridge | `coq/kami_hw/HardwareShadowBridge.v` | ✅ done |
| Device-class interface + instantiation | `coq/kami_hw/ShadowDevice.v` | ✅ done |
| Device-class theorem | `ShadowDevice.every_shadow_device_satisfies_compat` + `ShadowDeviceTrace.every_shadow_device_trace_compat` | ✅ done |
| Canonicality / initiality | `coq/kami_hw/ThieleCanonicality.v` | ✅ done |

---

## Phase 1: Hardware-shadow bridge

**Goal:** one theorem that turns the RTL simulation story into a shadow story.

**Key insight:** `verilog_sim_rel ks s` is already defined as `abs_phase1 ks = s`.
So the bridge reduces to a composition lemma—no new proof machinery needed.

### Target theorem

```
hardware_shadow_compat :
  forall ks : KamiSnapshot,
    rtl_classical_obs ks = classical_obs (shadow_proj (abs_phase1 ks))
```

Where:
- `rtl_classical_obs : KamiSnapshot -> ClassicalObs` — the RTL-visible observable state
- `classical_obs : ClassicalState -> ClassicalObs` — projection from Thiele's classical shadow
- `shadow_proj : VMState -> ClassicalState` — already defined in `ShadowProjection.v`
- `abs_phase1 : KamiSnapshot -> VMState` — existing Kami → Coq abstraction map

Equivalently (using `verilog_sim_rel`):
```
forall ks s, verilog_sim_rel ks s ->
  rtl_classical_obs ks = classical_obs (shadow_proj s)
```

### What this achieves

- "Hardware only sees the classical shadow" becomes a formal claim, not a synthesis of
  several separate theorems.
- Connects the full per-instruction VerilogRefinement layer to the classical-shadow story.
- Enables the trace-level corollary: entire RTL observable trace = classical-shadow trace
  of the corresponding Thiele execution.

### Files to add or extend

- `coq/kami_hw/HardwareShadowBridge.v` — new file
  - Define `rtl_classical_obs`
  - Prove `hardware_shadow_compat`
  - Prove trace-level corollary `hardware_shadow_trace_compat`

### Falsifier target

> A supported trace where `rtl_classical_obs ks` disagrees with
> `classical_obs (shadow_proj (abs_phase1 ks))`.

**Phase 1 done condition:** the sentence
"hardware observation of any Thiele RTL state is exactly the classical shadow of its
abstract VM state" is a named Coq theorem with zero Admitted.

---

## Phase 2: Device-class interface

**Goal:** extract the minimal abstract interface that the RTL proof already satisfies,
so the shadow theorem can be stated for an open class of devices.

### Approach

Do NOT invent new abstractions speculatively. Extract the interface already implied
by the RTL proof: the smallest record such that your concrete RTL is a provable instance.

### Target record: `ShadowDevice`

```coq
Record ShadowDevice := {
  sd_state    : Type;
  sd_obs      : sd_state -> ClassicalObs;
  sd_embed    : sd_state -> VMState;
  sd_embed_shadow_compat :
    forall d, sd_obs d = classical_obs (shadow_proj (sd_embed d));
  sd_step_simulated :
    (* device stepping is simulated by Thiele stepping on the embedded image *)
    ...
}.
```

### Files to add

- `coq/kami_hw/ShadowDevice.v`
  - Record definition above
  - Instantiate with RTL stack as `thiele_rtl_shadow_device`
  - Prove `thiele_rtl_shadow_device` satisfies the record

### Phase 2 done condition

Your current RTL implementation is a named, proved instance of `ShadowDevice`.

---

## Phase 3: Device-class theorem

**Goal:** any device satisfying the `ShadowDevice` interface is provably a Thiele-shadow
device — not just this one build.

### Target theorem

```
every_shadow_device_refines_thiele :
  forall (D : ShadowDevice) (d : D.(sd_state)),
    D.(sd_obs) d = classical_obs (shadow_proj (D.(sd_embed) d))
```

This follows immediately from the record field `sd_embed_shadow_compat`, so the
interesting content is in the richer step-simulation direction:

```
every_shadow_device_trace_compatible :
  forall (D : ShadowDevice) fuel trace d,
    D.(sd_obs) (sd_run D fuel trace d) =
    classical_obs (shadow_proj (run_vm fuel trace (D.(sd_embed) d)))
```

where `sd_run` is the device-level execution lifted through the embedding.

### Falsifier target

> A device satisfying the `ShadowDevice` interface whose observable trace provably
> diverges from the classical-shadow trace of its embedded Thiele execution.

### Phase 3 done condition

"Any device satisfying the interface is a Thiele-shadow device" is a named Coq theorem.

---

## Phase 4: Canonicality / initiality

**Goal:** Thiele is not just *a* host but *the* canonical host for certified-cost
shadow machines.

This is the hardest phase. The category must be nailed down first.

### Candidate formulation

```
thiele_is_initial_shadow_cert_machine :
  (* Thiele is the initial object in the category of certified-cost shadow machines *)
```

or more concretely:

```
thiele_universal_device_representation :
  forall (D : CertificationBearingDevice),
    exists (repr : D -> VMState),
      (* repr is a shadow-preserving, cost-preserving morphism *)
```

### Prerequisites

- Phase 3 done
- Category of "certified-cost shadow machines" precisely defined
  — at minimum: state, step, shadow map, cost function, certified predicate, morphisms
- Morphism notion that preserves shadow, cost, and certified/uncertified structure

### Phase 4 done condition

"Thiele is the canonical/initial/universal certified-cost shadow machine" is a named
Coq theorem in a well-defined category.

---

## Active log

| Date | Change |
|---|---|
| 2026-03-29 | Document created; audit complete; degenerate_projection_theorem built clean |
| 2026-03-29 | Phase 1 done: `HardwareShadowBridge.v` — `hardware_shadow_compat`, `hardware_shadow_sim_rel`, `hardware_sees_only_classical_shadow`, `hardware_shadow_mu_preserved` |
| 2026-03-29 | Phase 2 done: `ShadowDevice.v` — `ShadowDevice` record, `thiele_rtl_shadow_device`, `every_shadow_device_satisfies_compat`, `shadow_device_mu_cost_observable` |
| 2026-03-29 | Phase 3 done: `ShadowDeviceTrace.v` — `vm_apply_mu_eq_apply_cost`, `every_shadow_device_trace_compat` (induction), `rtl_shadow_trace_compat` (RTL corollary with `embed_step` hypothesis), `shadow_trace_mu_monotone` |
| 2026-03-29 | Phase 4 done: `ThieleCanonicality.v` — `thiele_instruction_cost_is_surjective`, `thiele_cert_cost_complete`, `ThieleCanonicalModel` record, `thiele_canonical_model`; `embed_step` precondition for trace level stated explicitly |
| 2026-03-30 | `EmbedStep.v` §7 added: `SupportedOpcode` predicate, `embed_step_supported`, `embed_step_supported_trace`; Category D gap documented (CALL/RET/CHSH → `EmbedStep_WF.v`) |
| 2026-03-30 | `ShadowDeviceTrace.v` §139 added: `rtl_shadow_trace_compat_supported` — unconditional trace compat for any `SupportedOpcode` trace; zero external hypotheses |
| 2026-03-30 | Third-phase roadmap created: `THIRD_PHASE_ROADMAP.md` — 5 phases, Phase 1 = Category D closure (`EmbedStep_WF.v`) |

---

## Quick reference: key files

| File | Role |
|---|---|
| `coq/kernel/ShadowProjection.v` | `shadow_proj`, lossy shadow theorems |
| `coq/kernel/TuringClassicalEmbedding.v` | `degenerate_projection_theorem`, `D2_classical_shadow_preserved` |
| `coq/kernel/BlindnessRepresentation.v` | `shadow_proj_and_forget_agree` |
| `coq/kami_hw/VerilogRefinement.v` | All 47 per-instruction RTL simulation theorems |
| `coq/kami_hw/Abstraction.v` | `abs_phase1 : KamiSnapshot -> VMState` |
| `coq/kami_hw/CanonicalCPUProof.v` | `canonical_cpu_proof : CanonicalCPUProofBundle` |
| `coq/kami_hw/RTLCorrectnessInstantiation.v` | Three-layer isomorphism |
| `coq/kernel/UniversalCertificationCost.v` | `universal_nfi_any_substrate`, `CertificationSystem` |
| `coq/kami_hw/HardwareShadowBridge.v` | `hardware_shadow_compat`, μ-cost bridge (Phase 1 — done) |
| `coq/kami_hw/ShadowDevice.v` | `ShadowDevice` record + RTL instance + class theorem (Phase 2 — done) |
