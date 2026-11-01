(* A countermodel to reading macro-endpoint simulation as prefix safety.
   Both machines meet the actual abstract CertificationSystem definition. *)
From Coq Require Import List Bool Arith Lia.
Import ListNotations.
Require Kernel.UniversalCertificationCost.
Module C := Kernel.UniversalCertificationCost.

Inductive host_move := Raise | Reset.
Definition hstep (_ : bool) (i : host_move) :=
  match i with Raise => true | Reset => false end.
Definition hprice (i : host_move) := match i with Raise => 1 | Reset => 0 end.

Definition host : C.CertificationSystem.
Proof.
  refine (C.mk_cert_system bool host_move hstep hprice (fun b => b) _).
  intros s [|] H0 H1; cbn in *; [lia|discriminate].
Defined.
Definition guest : C.CertificationSystem.
Proof.
  refine (C.mk_cert_system unit unit (fun s _ => s) (fun _ => 0) (fun _ => false) _).
  intros; discriminate.
Defined.
Definition simulation : C.SimulatingCertificationSystem host.
Proof.
  refine (@C.Build_SimulatingCertificationSystem host guest
    (fun _ => [Raise;Reset]) (fun _ => false) _ _); intros; reflexivity.
Defined.

Theorem every_macro_boundary_matches : forall w,
  C.cs_run host (concat (map (C.scs_decode simulation) w)) false = false.
Proof.
  intro w; change (C.cs_run host (concat (map (C.scs_decode simulation) w))
    (C.scs_embed simulation tt) = false).
  rewrite <- C.scs_run_embed; reflexivity.
Qed.

Theorem macro_prefix_exposes_unmatched_acceptance :
  C.cs_cert guest tt = false /\
  C.cs_cert host (C.cs_run host [Raise] false) = true /\
  C.cs_cert host (C.cs_run host [Raise;Reset] false) = false /\
  C.cs_total_cost host [Raise] = 1.
Proof. repeat split; reflexivity. Qed.

(* The false-to-true-to-false counterexample relies on the abstract model
   not requiring permanence. It cannot be used against a permanent host. *)
Theorem this_host_is_not_permanent :
  ~ (forall s i, C.cs_cert host s = true -> C.cs_cert host (C.cs_step host s i) = true).
Proof. intro H; specialize (H true Reset eq_refl); discriminate. Qed.

Section PermanentBoundary.
Variable machine : C.CertificationSystem.
Hypothesis permanent : forall s i,
  C.cs_cert machine s = true -> C.cs_cert machine (C.cs_step machine s i) = true.
Lemma permanent_trace : forall w s,
  C.cs_cert machine s = true -> C.cs_cert machine (C.cs_run machine w s) = true.
Proof. induction w; intros; cbn; [assumption|apply IHw, permanent; assumption]. Qed.

Theorem false_endpoint_excludes_accepting_prefix : forall prefix suffix s,
  C.cs_cert machine (C.cs_run machine (prefix++suffix) s) = false ->
  C.cs_cert machine (C.cs_run machine prefix s) = false.
Proof.
  intros prefix suffix s H; rewrite C.cs_run_app in H.
  destruct (C.cs_cert machine (C.cs_run machine prefix s)) eqn:Hp; [|reflexivity].
  pose proof (permanent_trace suffix _ Hp); congruence.
Qed.
End PermanentBoundary.

Print Assumptions simulation.
Print Assumptions every_macro_boundary_matches.
Print Assumptions macro_prefix_exposes_unmatched_acceptance.
Print Assumptions this_host_is_not_permanent.
Print Assumptions false_endpoint_excludes_accepting_prefix.
