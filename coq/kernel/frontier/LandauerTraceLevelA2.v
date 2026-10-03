(** * LandauerTraceLevelA2: lifting single-step A2 to multi-step traces

    [LogicalErasureCertFlip.v] establishes the single-step result: given
    the Landauer bridge plus cert-monotonicity, A2 holds for any
    single cert-flip step. This file extends to multi-step traces:
    any trace from an uncertified initial state to a certified final
    state has total cost ≥ 1, with the cost-floor still derived from
    the Landauer bridge rather than stipulated separately.

    The composition uses [universal_nfi_any_substrate] from
    [UniversalCertificationCost.v], whose structure requires a
    [CertificationSystem] record. The file constructs one from the
    single-step setup and instantiates.

    No new bridges, no new axioms: pure composition of existing
    single-step content with existing kernel infrastructure. *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import PrimeAxiom AbstractNoFI.
From Kernel Require Import UniversalCertificationCost.
From Kernel Require Import LogicalErasureCertFlip.

(** ** Trace-level extension of the single-step A2 derivation.

    Given the same Landauer bridge premise as the single-step result, A2 lifts from
    single-step to multi-step. For any Thiele trace from an
    uncertified state to a certified final state, total instruction
    cost ≥ 1.

    The composition is: the single-step `A2_from_physical_reversibility_real`
    discharges the cs_cert_costs field of a CertificationSystem
    instance for the Thiele VM (cert channel = vm_certified). Then
    universal_nfi_any_substrate's induction gives the trace-level
    cost ≥ 1. *)

(** Build a [CertificationSystem] from the single-step Landauer hypotheses. *)
Definition thiele_cert_system_from_landauer_bound
  (mu_per_landauer_bit : nat)
  (Hcal : mu_per_landauer_bit >= 1)
  (HLandauer : forall (P : bool_macro_property) (i : vm_instruction),
       step_collapses_bool_classes P i ->
       instruction_cost i >= mu_per_landauer_bit) :
  CertificationSystem :=
  {|
    cs_state := VMState;
    cs_instr := vm_instruction;
    cs_step  := vm_apply;
    cs_cost  := instruction_cost;
    cs_cert  := (fun s => s.(vm_certified));
    cs_cert_costs :=
      A2_from_physical_reversibility_real
        mu_per_landauer_bit Hcal HLandauer
  |}.

(** ** HEADLINE.

    Trace-level A2: given the Landauer bridge, any Thiele trace from
    an uncertified state s0 to a certified final state has total
    instruction cost ≥ 1.

    Proof composes the single-step result with
    universal_nfi_any_substrate (induction over the trace). No new
    bridges, no new axioms. *)

Theorem trace_level_A2_from_landauer_bound :
  forall (mu_per_landauer_bit : nat) (Hcal : mu_per_landauer_bit >= 1)
         (HLandauer : forall (P : bool_macro_property) (i : vm_instruction),
              step_collapses_bool_classes P i ->
              instruction_cost i >= mu_per_landauer_bit),
    forall (trace : list vm_instruction) (s0 : VMState),
      vm_certified s0 = false ->
      vm_certified
        (cs_run (thiele_cert_system_from_landauer_bound
                   mu_per_landauer_bit Hcal HLandauer) trace s0) = true ->
      cs_total_cost
        (thiele_cert_system_from_landauer_bound
           mu_per_landauer_bit Hcal HLandauer) trace >= 1.
Proof.
  intros mu Hcal HLandauer trace s0 Hf Ht.
  exact (universal_nfi_any_substrate
           (thiele_cert_system_from_landauer_bound mu Hcal HLandauer)
           trace s0 Hf Ht).
Qed.

(** ** Per-step variant: any single-instruction trace [[i]] to a
       certified state pays ≥ 1. (Same as the single-step result in a different
       packaging.) *)

Theorem single_step_A2_from_landauer_bound :
  forall (mu_per_landauer_bit : nat) (Hcal : mu_per_landauer_bit >= 1)
         (HLandauer : forall (P : bool_macro_property) (i : vm_instruction),
              step_collapses_bool_classes P i ->
              instruction_cost i >= mu_per_landauer_bit),
    forall (i : vm_instruction) (s0 : VMState),
      vm_certified s0 = false ->
      vm_certified (vm_apply s0 i) = true ->
      instruction_cost i >= 1.
Proof.
  intros mu Hcal HLandauer i s0 Hf Ht.
  exact (A2_from_physical_reversibility_real mu Hcal HLandauer s0 i Hf Ht).
Qed.

(** ** Unconditional Thiele trace-level A2.

    Directly use Thiele's existing [thiele_certified_system] (which
    satisfies A2 via no_free_certification_certified) to derive the
    trace-level cost ≥ 1 result without going through the Landauer derivation's
    Landauer-bridge hypothesis. This is an alternative route to the
    same conclusion via the existing cost law. *)

Theorem thiele_trace_level_A2 :
  forall (trace : list vm_instruction) (s0 : VMState),
    vm_certified s0 = false ->
    vm_certified (cs_run thiele_certified_system trace s0) = true ->
    cs_total_cost thiele_certified_system trace >= 1.
Proof.
  intros trace s0 Hf Ht.
  exact (universal_nfi_any_substrate thiele_certified_system trace s0 Hf Ht).
Qed.

(** ** Print Assumptions sanity.

    All theorems in this file close under the global context. They
    compose the single-step A2_from_physical_reversibility_real, the Thiele
    cost system construction (thiele_certified_system), and
    universal_nfi_any_substrate. No new bridges, no new axioms.

    The A2 derivation extends from single-step to multi-step traces via
    kernel induction, with no project-local content beyond that. *)
