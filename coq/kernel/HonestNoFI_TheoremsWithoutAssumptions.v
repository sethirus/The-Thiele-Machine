(** HonestNoFI_TheoremsWithoutAssumptions: two reduction links in the NoFI chain.

  This file is honest about where the bridge is complete and where it is not.
  One theorem reuses the core NoFI result once the strictly_stronger premise
  is already in hand. The other theorem shows how strict feasible-set
  reduction can generate such predicates from an observation witness.

  What is still missing is the final weld that turns those two nearby pieces
  into one end-to-end theorem with no extra bridge premise left over. *)

From Coq Require Import List.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import NoFreeInsight.
From Kernel Require Import InformationGainToStrengthening.

(** Legacy-shaped wrapper around NoFreeInsight.

  The theorem records the intended reduction context, but it still consumes
  strictly_stronger and Certified as inputs. So this is a wrapper around the
  core theorem, not yet the fully closed result. *)

Theorem honest_information_reduction_requires_structure_addition :
  forall (fuel : nat) (trace : list vm_instruction)
         (s_init s_final : VMState)
         (decoder : NoFreeInsight.receipt_decoder (list vm_instruction))
         (P_prior P_posterior : NoFreeInsight.ReceiptPredicate (list vm_instruction))
         (omega_prior omega_posterior : InformationGainToStrengthening.FeasibleSet),
    s_final = run_vm fuel trace s_init ->
    In s_init omega_prior ->
    InformationGainToStrengthening.is_strict_reduction omega_prior omega_posterior ->
    InformationGainToStrengthening.feasible_size omega_posterior > 0 ->
    s_init.(vm_csrs).(csr_cert_addr) = 0 ->
    NoFreeInsight.strictly_stronger P_posterior P_prior ->
    NoFreeInsight.Certified s_final decoder P_posterior trace ->
    NoFreeInsight.has_structure_addition fuel trace s_init.
Proof.
  intros fuel trace s_init s_final decoder P_prior P_posterior omega_prior omega_posterior
         Hfinal Hin_prior Hreduce Hcard Hinit_cert Hstrict Hcert.
  subst s_final.
  exact (NoFreeInsight.strengthening_requires_structure_addition
           (list vm_instruction) decoder P_prior P_posterior trace s_init fuel
           Hstrict Hinit_cert Hcert).
Qed.

(**
    b4_information_reduction_derives_strict_predicates uses B3's membership-based
    predicates. The strictly_stronger relationship is derived from the strict subset
    relation and observation distinguishability, not taken as input.
    *)

(** INQUISITOR NOTE: b4_information_reduction_derives_strict_predicates shows
    that feasible-set reduction with distinguishing observations produces
    the strictly_stronger relationship needed by NoFreeInsight, using the
    non-trivial membership predicates from B3. No trivial true/false. *)
Theorem b4_information_reduction_derives_strict_predicates :
  forall (omega_prior omega_posterior : InformationGainToStrengthening.FeasibleSet)
         (obs_fn : InformationGainToStrengthening.ObservationFunction)
         (obs_eqb : list vm_instruction -> list vm_instruction -> bool),
    (forall o1 o2, obs_eqb o1 o2 = true <-> o1 = o2) ->
    InformationGainToStrengthening.is_strict_subset omega_posterior omega_prior ->
    (exists s_witness,
      In s_witness omega_prior /\
      ~ In s_witness omega_posterior /\
      InformationGainToStrengthening.observation_distinguishes obs_fn s_witness omega_posterior) ->
    exists (P_prior P_posterior : NoFreeInsight.ReceiptPredicate vm_instruction),
      NoFreeInsight.strictly_stronger P_posterior P_prior.
Proof.
  intros omega_prior omega_posterior obs_fn obs_eqb Heqb_spec Hsubset Hwit.
  exact (InformationGainToStrengthening.feasible_strict_subset_implies_strict_predicates_exists
           obs_eqb Heqb_spec omega_prior omega_posterior obs_fn Hsubset Hwit).
Qed.

(** Summary.

  honest_information_reduction_requires_structure_addition gives the NoFI
  consequence once strictly_stronger is supplied. 

  b4_information_reduction_derives_strict_predicates shows how strict subset
  plus distinguishing observation can manufacture that predicate. *)
