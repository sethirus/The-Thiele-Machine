(* Instantiate the generic all-host-action contract with the EXISTING host. *)
From Coq Require Import List.
Import ListNotations.
Require Minimal.EarnedCore Minimal.UniversalThiele Audit.EnforcedRefinement.
Module E := Minimal.EarnedCore.
Module U := Minimal.UniversalThiele.
Module R := EnforcedRefinement.

Definition guest_configuration := (list E.instr * E.state)%type.
Definition tick (g : guest_configuration) (_ : unit) : guest_configuration :=
  (fst g,E.step (fst g) (snd g)).
Definition related (g : guest_configuration) (h : U.hstate) : Prop :=
  U.gprog h = fst g /\ U.gst h = snd g /\ U.mrec h = E.cert (snd g).

Lemma repeated_ticks_match_guest : forall n P g,
  R.guest_run tick (repeat tt n) (P,g) = (P,E.run_prog n P g).
Proof.
  induction n; intros P g; cbn; [reflexivity|apply IHn].
Qed.

Theorem existing_host_meets_all_action_contract : forall g h,
  related g h -> forall i,
  exists w, related (R.guest_run tick w g) (U.hexec h i).
Proof.
  intros [P g] h [Hp [Hg Ha]] i; cbn in Hp,Hg,Ha.
  destruct (U.hexec_guest h i) as [k Hk].
  exists (repeat tt k); rewrite repeated_ticks_match_guest.
  unfold related; cbn; split.
  - rewrite U.hexec_gprog; exact Hp.
  - split.
    + rewrite Hk,Hp,Hg; reflexivity.
    + assert (Hag : U.agrees h).
      { unfold U.agrees; rewrite Hg; exact Ha. }
      pose proof (U.record_agreement_step h i Hag) as Hafter.
      unfold U.agrees in Hafter; rewrite Hafter,Hk,Hp,Hg; reflexivity.
Qed.

Theorem every_existing_host_trace_refines : forall tr g h,
  related g h -> exists w, related (R.guest_run tick w g) (U.hrun tr h).
Proof.
  intros tr g h Hr.
  change (exists w, related (R.guest_run tick w g) (R.host_run U.hexec tr h)).
  apply (R.every_host_trace_refines tick U.hexec related
    existing_host_meets_all_action_contract tr g h Hr).
Qed.

Print Assumptions existing_host_meets_all_action_contract.
Print Assumptions every_existing_host_trace_refines.
