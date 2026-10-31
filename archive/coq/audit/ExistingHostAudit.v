From Coq Require Import List.
Import ListNotations.
Require Minimal.EarnedCore Minimal.UniversalThiele
  Kernel.UniversalCertificationCost Kernel.UniversalThieleLinks.
Module E := Minimal.EarnedCore.
Module U := Minimal.UniversalThiele.

(* The combined reading describes own OR guest establishment. It is not the
   guest mirror and must not be substituted for it in provenance claims. *)
Theorem combined_reading_is_not_guest_acceptance :
  let h := U.hrun (map U.OWN
    [E.CHECK E.PZero E.CA; E.COMMIT E.PZero E.CA; E.CERTIFY])
      (U.hload 0 0 [] 0 0) in
  U.hread h = true /\ U.mrec h = false /\ E.cert (U.gst h) = false.
Proof. repeat split; reflexivity. Qed.

(* An arbitrary state constructor is not an authorized clean start. *)
Theorem provenance_needs_a_start_condition :
  let s := E.mkst (E.start_core 0 0) 0 true in
  E.cert (E.run [] s) = true /\ E.total_cost [] = 0 /\ ~ E.clean_start s.
Proof.
  cbn; split; [reflexivity|split; [reflexivity|]].
  unfold E.clean_start; cbn; intros [_ [_ H]]; discriminate.
Qed.

Print Assumptions combined_reading_is_not_guest_acceptance.
Print Assumptions provenance_needs_a_start_condition.
Print Assumptions E.no_forging.
Print Assumptions E.earned_certification_provenance.
Print Assumptions E.certified_run_min_cost.
Print Assumptions U.hexec_gprog.
Print Assumptions U.hexec_guest.
Print Assumptions U.guest_runs_own_program.
Print Assumptions U.record_agreement_step.
Print Assumptions U.record_agreement.
Print Assumptions U.host_mirror_earned.
Print Assumptions U.no_free_host_certification.
Print Assumptions U.no_free_host_certification_program.
Print Assumptions U.host_cost_covers_guest.
Print Assumptions Kernel.UniversalThieleLinks.host_nfi.
Print Assumptions Kernel.UniversalCertificationCost.scs_run_embed.
Print Assumptions Kernel.UniversalCertificationCost.host_represents_simulating_cert_system.
