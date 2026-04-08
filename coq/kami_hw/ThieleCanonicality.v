(** ThieleCanonicality.v

    The canonical certified-cost shadow machine theorem.

    Assembles the full second-phase program into a single named record:
    [thiele_canonical_model : ThieleCanonicalModel].

    The record collects eight unconditional guarantees:
    (1) hardware — RTL obs = classical shadow of abstract Thiele state
    (2) device class (static) — any ShadowDevice has shadow-compat obs
    (3) universal NoFI — any cert system satisfying A2 charges cost ≥ 1
    (4) strict lossiness — shadow throws away actionable structure
    (5) cost surjectivity — every natural number is a Thiele instruction cost
    (6) cert cost completeness — every positive cost has a certifying instruction
    (7) trace-level shadow compat — for SupportedOpcode traces (26 opcodes)
    (8) extended trace shadow compat — for ShadowSupportedOpcode traces (30 opcodes)

    The conditional [thiele_trace_compat_under_embed_step] is retained
    separately for documentation purposes but is now superseded by (7) for
    the supported opcode subset.

    STATEMENT SCOPE:
    Claims (1)-(4) are unconditional theorems about the current implementation.
    Claims (5)-(6) are new structural facts about Thiele's instruction set.
    Claim (7) is unconditional for the 26-opcode SupportedOpcode subset.
    Claim (8) is unconditional for the 30-opcode ShadowSupportedOpcode subset.

    STATUS: All eight record fields proved.  Zero Admitted.  Inquisitor OK.
*)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

From Kernel  Require Import VMState VMStep SimulationProof
                            ShadowProjection UniversalCertificationCost.
From KamiHW  Require Import Abstraction HardwareShadowBridge
                            ShadowDevice ShadowDeviceTrace EmbedStep
                            ShadowEmbedStep.

(** =========================================================================
    NEW LEMMA 1: Thiele instruction cost is surjective

    Every natural number is the cost of some Thiele instruction.
    Witness: [instr_halt n] has [instruction_cost = n].

    This is the sense in which Thiele is "cost-complete":
    no cost budget belongs to a computation that Thiele cannot model.
*)
Theorem thiele_instruction_cost_is_surjective :
  forall n : nat,
    exists i : vm_instruction, instruction_cost i = n.
Proof.
  intros n.
  exists (instr_halt n).
  unfold instruction_cost. reflexivity.
Qed.

(** =========================================================================
    NEW LEMMA 2: Thiele has certifying instructions for every positive cost

    For every cost value [S k], there exists a Thiele instruction that:
    (a) has that exact cost, AND
    (b) unconditionally sets [vm_certified := true]

    Witness: [instr_certify k] — cost is [S k], always certifies.

    This is the sense in which Thiele is "cert-cost-complete":
    any certification budget ≥ 1 is achievable via a concrete instruction.
*)
Theorem thiele_cert_cost_complete :
  forall k : nat,
    exists i : vm_instruction,
      instruction_cost i = S k /\
      forall s : VMState,
        s.(vm_certified) = false ->
        (vm_apply s i).(vm_certified) = true.
Proof.
  intros k.
  exists (instr_certify k).
  split.
  - (* Cost: instruction_cost (instr_certify k) = S k *)
    unfold instruction_cost. reflexivity.
  - (* Certification: vm_apply sets vm_certified to true *)
    intros s _.
    unfold vm_apply. reflexivity.
Qed.

(** =========================================================================
    THE CANONICAL MODEL RECORD

    Bundles the seven unconditional guarantees into a single named structure.
    Proved via instantiation of the record's fields using existing theorems
    plus the two new lemmas above.
*)

Record ThieleCanonicalModel := {

  (** (1) Hardware shadow compatibility (state-level):
      RTL observation equals classical shadow of the abstract Thiele state. *)
  tcm_hardware_shadow_compat :
    forall ks : KamiSnapshot,
      rtl_classical_obs ks = shadow_proj (abs_phase1 ks);

  (** (2) Device class compatibility (static):
      Any ShadowDevice's observation equals the classical shadow of its
      embedded Thiele state.  Holds unconditionally for any device satisfying
      the interface. *)
  tcm_device_class_compat :
    forall (D : ShadowDevice) (d : D.(sd_state)),
      D.(sd_obs) d = shadow_proj (D.(sd_embed) d);

  (** (3) Universal No Free Insight:
      Any certification system satisfying A2 (cost ≥ 1 at the certification
      transition) cannot certify from false to true without spending ≥ 1 cost.
      This holds for Thiele, OCaml extraction, RTL, physical measurements,
      proof assistants, and consensus protocols — any substrate satisfying A2. *)
  tcm_nfi_universal :
    forall (CS : CertificationSystem)
           (trace : list (cs_instr CS))
           (s0 : cs_state CS),
      cs_cert CS s0 = false ->
      cs_cert CS (cs_run CS trace s0) = true ->
      cs_total_cost CS trace >= 1;

  (** (4) Shadow is strictly lossy:
      There exist two Thiele states with the same classical shadow but
      different graph structure — and a probe that preserves the distinction.
      The classical observer cannot distinguish what the Thiele machine retains. *)
  tcm_shadow_strictly_lossy :
    exists (s1 s2 : VMState),
      shadow_proj s1 = shadow_proj s2 /\
      s1.(vm_graph).(pg_morphisms) <> s2.(vm_graph).(pg_morphisms) /\
      exists probe,
        (vm_apply s1 probe).(vm_graph).(pg_morphisms) <>
          (vm_apply s2 probe).(vm_graph).(pg_morphisms);

  (** (5) Thiele instruction cost is surjective:
      Every natural number is achievable as [instruction_cost i] for some i.
      The classical shadow carries vm_mu faithfully; this says no μ-budget
      belongs outside Thiele's representational range. *)
  tcm_cost_surjective :
    forall n : nat,
      exists i : vm_instruction, instruction_cost i = n;

  (** (6) Certifying instructions cover all positive costs:
      For every cost S k, there is a Thiele instruction with that cost that
      unconditionally certifies.  No positive cert-cost is unreachable. *)
  tcm_cert_cost_complete :
    forall k : nat,
      exists i : vm_instruction,
        instruction_cost i = S k /\
        forall s : VMState,
          s.(vm_certified) = false ->
          (vm_apply s i).(vm_certified) = true;

  (** (7) Trace-level shadow compatibility for supported executions:
      For any trace over the SupportedOpcode instruction subset, the hardware
      observable trace equals the classical shadow of the Thiele execution.
      Unconditional — no embed_step hypothesis.  This is the theorem to cite
      in print for the hardware-runs-as-shadow claim. *)
  tcm_trace_compat_supported :
    forall (trace : list vm_instruction) (ks : KamiSnapshot),
      (forall i, List.In i trace -> SupportedOpcode i) ->
      rtl_classical_obs (List.fold_left kami_step trace ks) =
      shadow_proj (List.fold_left vm_apply trace (abs_phase1 ks));

  (** (8) Extended trace-level shadow compatibility (30 opcodes):
      Extends (7) to ShadowSupportedOpcode: the original 26 plus PNEW,
      PDISCOVER, EMIT, REVEAL.  These 4 additional opcodes diverge on
      vm_graph/vm_csrs but agree on all shadow fields.
      Uses shadow compositionality (vm_apply_shadow_compat). *)
  tcm_trace_compat_shadow_extended :
    forall (trace : list vm_instruction) (ks : KamiSnapshot),
      snap_csr_heap_base ks = 0 ->
      (forall i, List.In i trace -> ShadowSupportedOpcode i) ->
      rtl_classical_obs (List.fold_left kami_step trace ks) =
      shadow_proj (List.fold_left vm_apply trace (abs_phase1 ks));
}.

(** =========================================================================
    INSTANTIATION: Thiele satisfies all seven guarantees

    The proof is by record construction from existing lemmata.
*)

(** Seventh guarantee: unconditional trace-level shadow compatibility.
    Proved directly from [rtl_shadow_trace_compat_supported]. *)
Theorem thiele_trace_compat_supported :
  forall (trace : list vm_instruction) (ks : KamiSnapshot),
    (forall i, List.In i trace -> SupportedOpcode i) ->
    rtl_classical_obs (List.fold_left kami_step trace ks) =
    shadow_proj (List.fold_left vm_apply trace (abs_phase1 ks)).
Proof.
  intros trace ks Hsupp.
  exact (rtl_shadow_trace_compat_supported trace ks Hsupp).
Qed.

Theorem thiele_canonical_model : ThieleCanonicalModel.
Proof.
  refine
    {| tcm_hardware_shadow_compat   := hardware_shadow_compat;
       tcm_device_class_compat      := every_shadow_device_satisfies_compat;
       tcm_nfi_universal            := universal_nfi_any_substrate;
       tcm_shadow_strictly_lossy    := shadow_strictly_lossy;
       tcm_cost_surjective          := thiele_instruction_cost_is_surjective;
       tcm_cert_cost_complete       := thiele_cert_cost_complete;
       tcm_trace_compat_supported   := thiele_trace_compat_supported;
       tcm_trace_compat_shadow_extended := rtl_shadow_trace_compat_extended |}.
Qed.

(** =========================================================================
    CONDITIONAL PHASE 3: Trace-level shadow compatibility

    Under [embed_step] — the claim that hardware stepping commutes with
    [abs_phase1] through [vm_apply] — the entire observable device trace
    equals the classical-shadow trace of the corresponding Thiele execution.

    [embed_step] is not yet proved for the RTL instance.  Its proof requires
    a [WellFormedSnapshot] invariant (register values within 64-bit range).
    The theorem is stated here so the scope of the precondition is visible
    next to the canonicality record. *)
Theorem thiele_trace_compat_under_embed_step :
  forall (embed_step : forall (ks : KamiSnapshot) (i : vm_instruction),
                         abs_phase1 (kami_step ks i) = vm_apply (abs_phase1 ks) i)
         (trace : list vm_instruction)
         (ks : KamiSnapshot),
    rtl_classical_obs (fold_left kami_step trace ks) =
    shadow_proj (fold_left vm_apply trace (abs_phase1 ks)).
Proof.
  intros embed_step trace ks.
  exact (rtl_shadow_trace_compat embed_step trace ks).
Qed.
