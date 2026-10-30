(* A mathematical extension used ONLY as a countermodel. ForceMirror is NOT
   an instruction of the repository's original universal host. *)
From Coq Require Import List Bool Arith Lia.
Import ListNotations.
Require Minimal.EarnedCore Minimal.UniversalThiele
  Kernel.UniversalCertificationCost Kernel.UniversalThieleLinks.
Module E := Minimal.EarnedCore.
Module U := Minimal.UniversalThiele.
Module C := Kernel.UniversalCertificationCost.
Module L := Kernel.UniversalThieleLinks.

Inductive extended_move := Existing (i : U.hinstr) | ForceMirror.
Definition extended_step (h : U.hstate) (i : extended_move) :=
  match i with
  | Existing j => U.hexec h j
  | ForceMirror => U.mkh (U.hcore h) (U.hmu h + 1) (U.hcert h)
      (U.gprog h) (U.gst h) true
  end.
Definition extended_cost (i : extended_move) :=
  match i with Existing j => U.hcost j | ForceMirror => 1 end.

Definition extended_system : C.CertificationSystem.
Proof.
  refine (C.mk_cert_system U.hstate extended_move extended_step extended_cost U.mrec _).
  intros h [i|] H0 H1.
  - exact (U.host_mirror_toll h i H0 H1).
  - cbn; lia.
Defined.

Definition original_host_is_simulated : C.SimulatingCertificationSystem extended_system.
Proof.
  refine (@C.Build_SimulatingCertificationSystem extended_system L.host_mirror_cs
    (fun i => [Existing i]) (fun h => h) _ _); intros; reflexivity.
Defined.

Theorem original_traces_are_preserved : forall tr h,
  C.cs_run extended_system (map Existing tr) h = U.hrun tr h.
Proof. induction tr; intro h; cbn; [reflexivity|apply IHtr]. Qed.

Theorem original_costs_are_preserved : forall tr,
  C.cs_total_cost extended_system (map Existing tr) = U.htotal_cost tr.
Proof. induction tr; cbn; [reflexivity|rewrite IHtr; reflexivity]. Qed.

Theorem extension_has_exact_ledger : forall h i,
  U.hmu (extended_step h i) = U.hmu h + extended_cost i.
Proof. intros h [i|]; [apply U.hmu_conservation|reflexivity]. Qed.

Theorem extension_has_permanent_record : forall h i,
  U.mrec h = true -> U.mrec (extended_step h i) = true.
Proof.
  intros h [[j|b]|] Hr; cbn; try exact Hr; try reflexivity.
  destruct (E.err (U.hcore h)); cbn; [exact Hr|rewrite Hr; reflexivity].
Qed.

Definition loaded_empty := U.hload 0 0 [] 0 0.
Definition bypassed := extended_step loaded_empty ForceMirror.

Theorem paid_raise_without_guest_establishment :
  U.mrec bypassed = true /\ E.cert (U.gst bypassed) = false /\
  E.clean_start (U.gst bypassed) /\ U.hmu bypassed = 1 /\
  extended_cost ForceMirror = 1.
Proof. repeat split; reflexivity. Qed.

Theorem empty_guest_cannot_supply_accepting_execution : forall n,
  E.cert (E.run_prog n [] (E.start 0 0)) = false.
Proof. intro n; rewrite E.run_prog_halted; reflexivity. Qed.

Theorem no_original_host_trace_reaches_bypassed : forall tr,
  U.hrun tr loaded_empty <> bypassed.
Proof.
  intros tr H.
  pose proof (U.record_agreement tr loaded_empty (U.hload_agrees 0 0 [] 0 0)) as Ha.
  rewrite H in Ha; unfold U.agrees in Ha; discriminate.
Qed.

Print Assumptions extended_system.
Print Assumptions original_host_is_simulated.
Print Assumptions original_traces_are_preserved.
Print Assumptions original_costs_are_preserved.
Print Assumptions extension_has_exact_ledger.
Print Assumptions extension_has_permanent_record.
Print Assumptions paid_raise_without_guest_establishment.
Print Assumptions empty_guest_cannot_supply_accepting_execution.
Print Assumptions no_original_host_trace_reaches_bypassed.
