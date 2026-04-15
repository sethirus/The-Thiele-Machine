(** ShadowDevice.v

    Abstract interface for devices whose classical observation equals the
    classical shadow of their embedded Thiele VM state.

    Extracts the minimal abstract interface already satisfied by the Thiele
    RTL, then states the class-level theorem.

    DESIGN:

    The [ShadowDevice] record captures the static compatibility invariant:
    for any device state [d], the observable classical state equals the
    classical shadow of the embedded Thiele state.  Step-simulation for
    the RTL instance is separately handled by [VerilogRefinement.v] and
    [CanonicalCPUProof.v]; including it here would duplicate that layer.

    STATUS: Six theorems proved cleanly.  Zero Admitted.
    - [thiele_rtl_shadow_device] : RTL is a [ShadowDevice] instance.
    - [every_shadow_device_satisfies_compat] : class-level theorem.
    - [shadow_device_mu_cost_observable] : μ-cost preserved through interface.
    - [thiele_rtl_dynamic_shadow_device] : RTL is a [DynamicShadowDevice] instance.
    - [dynamic_shadow_device_trace_compat] : self-contained trace theorem.
    - [dynamic_shadow_device_mu_observable] : μ-cost through dynamic interface.
*)

From Coq Require Import List Arith.PeanoNat.
Import ListNotations.

From Kernel  Require Import VMState VMStep SimulationProof ShadowProjection.
From KamiHW  Require Import Abstraction VerilogRefinement HardwareShadowBridge EmbedStep.

(** * ShadowDevice interface

    A [ShadowDevice] is any system with:
    - a device state type [sd_state]
    - a classical observation function [sd_obs]
    - an embedding [sd_embed] into [VMState]
    - a proof that the observation equals the shadow of the embedding *)
Record ShadowDevice := {
  sd_state  : Type ;
  sd_obs    : sd_state -> ClassicalState ;
  sd_embed  : sd_state -> VMState ;
  sd_embed_shadow_compat :
    forall d : sd_state, sd_obs d = shadow_proj (sd_embed d)
}.

(** * RTL instance

    The Thiele hardware stack is a [ShadowDevice]:
    - state is [KamiSnapshot]
    - observation is [rtl_classical_obs]
    - embedding is [abs_phase1]
    - compatibility follows directly from [hardware_shadow_compat] *)
Definition thiele_rtl_shadow_device : ShadowDevice :=
  {| sd_state  := KamiSnapshot ;
     sd_obs    := rtl_classical_obs ;
     sd_embed  := abs_phase1 ;
     sd_embed_shadow_compat := hardware_shadow_compat |}.

(** * Device-class theorem

    Every [ShadowDevice] satisfies the shadow compatibility invariant.
    Follows immediately from the record field — the theorem is here to
    make the class-level statement explicit and separately named.

    Any device satisfying the interface is automatically a
    Thiele-shadow device. *)
Theorem every_shadow_device_satisfies_compat :
  forall (D : ShadowDevice) (d : D.(sd_state)),
    D.(sd_obs) d = shadow_proj (D.(sd_embed) d).
Proof.
  intros D d.
  exact (D.(sd_embed_shadow_compat) d).
Qed.

(** * μ-cost is observable through the interface

    For any [ShadowDevice], the μ-cost in the observation equals [vm_mu]
    of the embedded Thiele state.  Connects the interface to the
    μ-ledger cost chain. *)
Theorem shadow_device_mu_cost_observable :
  forall (D : ShadowDevice) (d : D.(sd_state)),
    (D.(sd_obs) d).(cs_mu) = (D.(sd_embed) d).(vm_mu).
Proof.
  intros D d.
  rewrite D.(sd_embed_shadow_compat).
  unfold shadow_proj.
  reflexivity.
Qed.

(** * RTL instance satisfies the device-class theorem

    Explicit instantiation stating the RTL hardware is covered by the
    class theorem above. *)
Corollary thiele_rtl_satisfies_shadow_compat :
  forall ks : KamiSnapshot,
    (thiele_rtl_shadow_device).(sd_obs) ks =
    shadow_proj ((thiele_rtl_shadow_device).(sd_embed) ks).
Proof.
  intros ks.
  exact (every_shadow_device_satisfies_compat thiele_rtl_shadow_device ks).
Qed.

(* ================================================================= *)
(** ** DynamicShadowDevice: ShadowDevice with a step function        *)
(* ================================================================= *)

(** [DynamicShadowDevice] extends [ShadowDevice] with a step function
    and a proof that the step commutes with [vm_apply] through the
    embedding.  This makes trace compatibility a self-contained
    property of the device class, requiring no external [embed_step]
    parameter.

    DESIGN DECISION: [dsd_step_embed] is scoped to instructions
    satisfying a class-provided predicate [dsd_supported].  This
    avoids requiring the RTL to commute on ALL 47 opcodes (some
    diverge by design — see EmbedStep.v header). *)
Record DynamicShadowDevice := {
  dsd_state     : Type ;
  dsd_obs       : dsd_state -> ClassicalState ;
  dsd_embed     : dsd_state -> VMState ;
  dsd_step      : dsd_state -> vm_instruction -> dsd_state ;
  dsd_supported : vm_instruction -> Prop ;
  dsd_embed_shadow_compat :
    forall d : dsd_state, dsd_obs d = shadow_proj (dsd_embed d) ;
  dsd_step_embed :
    forall (d : dsd_state) (i : vm_instruction),
      dsd_supported i ->
      dsd_embed (dsd_step d i) = vm_apply (dsd_embed d) i
}.

(** * RTL instance of DynamicShadowDevice (26-opcode SupportedOpcode scope).

    Uses [kami_step] as the device step and [SupportedOpcode] from
    EmbedStep.v as the support predicate.  [embed_step_supported]
    provides the step-commutation proof. *)
Definition thiele_rtl_dynamic_shadow_device : DynamicShadowDevice :=
  {| dsd_state     := KamiSnapshot ;
     dsd_obs       := rtl_classical_obs ;
     dsd_embed     := abs_phase1 ;
     dsd_step      := kami_step ;
     dsd_supported := SupportedOpcode ;
     dsd_embed_shadow_compat := hardware_shadow_compat ;
     dsd_step_embed := embed_step_supported |}.

(** * Self-contained trace theorem for any DynamicShadowDevice.

    For a supported trace (all instructions satisfy [dsd_supported]),
    the observation after running the trace equals the classical shadow
    of the corresponding Thiele execution via the embedding.

    No external embed_step parameter needed — everything is in the record. *)
Theorem dynamic_shadow_device_trace_compat :
  forall (D : DynamicShadowDevice)
         (trace : list vm_instruction)
         (d : D.(dsd_state)),
    (forall i, List.In i trace -> D.(dsd_supported) i) ->
    D.(dsd_obs) (fold_left D.(dsd_step) trace d) =
    shadow_proj (fold_left vm_apply trace (D.(dsd_embed) d)).
Proof.
  intros D trace.
  induction trace as [| i rest IH].
  - intros d _. simpl. apply D.(dsd_embed_shadow_compat).
  - intros d Hsupp. simpl.
    rewrite (IH (D.(dsd_step) d i)).
    + rewrite (D.(dsd_step_embed) d i).
      * reflexivity.
      * apply Hsupp. left. reflexivity.
    + intros j Hj. apply Hsupp. right. exact Hj.
Qed.

(** * RTL corollary: no hypotheses beyond SupportedOpcode scope. *)
Corollary rtl_dynamic_shadow_trace_compat :
  forall (trace : list vm_instruction) (ks : KamiSnapshot),
    (forall i, List.In i trace -> SupportedOpcode i) ->
    rtl_classical_obs (fold_left kami_step trace ks) =
    shadow_proj (fold_left vm_apply trace (abs_phase1 ks)).
Proof.
  intros trace ks Hsupp.
  exact (dynamic_shadow_device_trace_compat
           thiele_rtl_dynamic_shadow_device trace ks Hsupp).
Qed.

(** * μ-cost observable through dynamic interface.

    The μ-cost after a supported trace equals the Thiele-computed μ —
    connecting the dynamic device to the cost chain. *)
Corollary dynamic_shadow_device_mu_observable :
  forall (D : DynamicShadowDevice)
         (trace : list vm_instruction)
         (d : D.(dsd_state)),
    (forall i, List.In i trace -> D.(dsd_supported) i) ->
    (D.(dsd_obs) (fold_left D.(dsd_step) trace d)).(cs_mu) =
    (fold_left vm_apply trace (D.(dsd_embed) d)).(vm_mu).
Proof.
  intros D trace d Hsupp.
  rewrite (dynamic_shadow_device_trace_compat D trace d Hsupp).
  unfold shadow_proj. reflexivity.
Qed.
