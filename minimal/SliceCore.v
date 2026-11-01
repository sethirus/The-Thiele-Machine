(* SCOPE NOTE: standalone proof scope.
   Characterizes observation-preserving quotients of arbitrary computing and marking instructions.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

(* Abstract transition system: no product decomposition or base is assumed. *)
Section Observation.
  Context {S C P O : Type}.
  Variable compute : C -> S -> S.
  Variable mark : P -> S -> S.
  Variable observe : S -> O.

  Fixpoint run (w : list C) (s : S) : S :=
    match w with [] => s | c::rest => run rest (compute c s) end.
  Definition ObsEq (s t : S) := forall w, observe (run w s) = observe (run w t).

  Theorem observation_reflexive : forall s, ObsEq s s.
  Proof. intros s w; reflexivity. Qed.
  Theorem observation_symmetric : forall s t, ObsEq s t -> ObsEq t s.
  Proof. intros s t H w; symmetry; apply H. Qed.
  Theorem observation_transitive : forall s t u, ObsEq s t -> ObsEq t u -> ObsEq s u.
  Proof. intros s t u H K w; rewrite H; apply K. Qed.
  Theorem observation_step : forall s t, ObsEq s t -> forall c,
    ObsEq (compute c s) (compute c t).
  Proof. intros s t H c w; exact (H (c::w)). Qed.
  Theorem observation_now : forall s t, ObsEq s t -> observe s = observe t.
  Proof. intros s t H; exact (H []). Qed.

  (* Every output-preserving congruence is contained in behavioral equality. *)
  Theorem observation_greatest (R : S -> S -> Prop) :
    (forall s t, R s t -> observe s = observe t) ->
    (forall s t, R s t -> forall c, R (compute c s) (compute c t)) ->
    forall s t, R s t -> ObsEq s t.
  Proof.
    intros Hout Hstep s t H w. revert s t H.
    induction w as [|c w IH]; intros s t H; simpl.
    - apply Hout; exact H.
    - apply IH; apply Hstep; exact H.
  Qed.

  Inductive Erase : S -> S -> Prop :=
  | er_refl : forall s, Erase s s
  | er_sym : forall s t, Erase s t -> Erase t s
  | er_trans : forall s t u, Erase s t -> Erase t u -> Erase s u
  | er_mark : forall s p, Erase s (mark p s)
  | er_compute : forall s t, Erase s t -> forall c,
      Erase (compute c s) (compute c t).

  Theorem erasure_least (R : S -> S -> Prop) :
    (forall s, R s s) ->
    (forall s t, R s t -> R t s) ->
    (forall s t u, R s t -> R t u -> R s u) ->
    (forall s p, R s (mark p s)) ->
    (forall s t, R s t -> forall c, R (compute c s) (compute c t)) ->
    forall s t, Erase s t -> R s t.
  Proof. intros Hr Hs Ht Hm Hc s t H; induction H; eauto. Qed.

  (* Exact existence criterion for an output-preserving mark-silent quotient,
     expressed relationally so no quotient-type axioms are needed. *)
  Theorem erasure_preserves_iff_marks_invisible :
    (forall s t, Erase s t -> observe s = observe t) <->
    (forall s p, ObsEq s (mark p s)).
  Proof.
    split.
    - intros H s p.
      apply (observation_greatest Erase H).
      + intros; apply er_compute; assumption.
      + apply er_mark.
    - intros H s t E. apply observation_now.
      induction E.
      + apply observation_reflexive.
      + apply observation_symmetric; assumption.
      + eapply observation_transitive; eassumption.
      + apply H.
      + apply observation_step; assumption.
  Qed.

  Definition action := (C + P)%type.
  Fixpoint allrun (w : list action) (s : S) : S :=
    match w with
    | [] => s
    | inl c :: rest => allrun rest (compute c s)
    | inr p :: rest => allrun rest (mark p s)
    end.
  Fixpoint purge (w : list action) : list C :=
    match w with
    | [] => []
    | inl c :: rest => c :: purge rest
    | inr _ :: rest => purge rest
    end.

  Theorem invisible_marks_allow_purge :
    (forall s p, ObsEq s (mark p s)) ->
    forall w s, observe (allrun w s) = observe (run (purge w) s).
  Proof.
    intros H w; induction w as [|[c|p] rest IH]; intros s; simpl.
    - reflexivity.
    - apply IH.
    - rewrite IH. symmetry. apply H.
  Qed.
End Observation.

Section ZeroCost.
  Context {S I A : Type}.
  Variable step : I -> S -> S.
  Variable cost : I -> nat.
  Variable mu : S -> nat.
  Variable record : S -> A.
  Hypothesis accounting : forall i s, mu (step i s) = mu s + cost i.
  Hypothesis charged_change : forall i s, record (step i s) <> record s -> cost i >= 1.
  Theorem zero_cost_preserves_ledger : forall i s, cost i = 0 -> mu (step i s) = mu s.
  Proof. intros i s H; rewrite accounting, H; lia. Qed.
  (* Equality decidability is made explicit; Boolean records satisfy it. *)
  Hypothesis record_eq_dec : forall a b : A, {a=b}+{a<>b}.
  Theorem zero_cost_preserves_record : forall i s, cost i = 0 -> record (step i s) = record s.
  Proof.
    intros i s H; destruct (record_eq_dec (record (step i s)) (record s)); auto.
    specialize (charged_change i s n); lia.
  Qed.
End ZeroCost.

(* Same immediate output, different next output after a record-steered step. *)
Definition steering (s : bool * bool) : bool * bool :=
  (xorb (fst s) (snd s), snd s).
Definition latch (s : bool * bool) : bool * bool := (fst s, true).
Theorem mark_immediately_silent : forall s, fst (latch s) = fst s.
Proof. destruct s; reflexivity. Qed.
Theorem steering_exposes_mark :
  fst (steering (false,false)) <> fst (steering (latch (false,false))).
Proof. discriminate. Qed.
Theorem no_autonomous_working_projection :
  ~ exists f : bool -> bool, forall s, fst (steering s) = f (fst s).
Proof.
  intros [f H]. pose proof (H (false,false)) as H0.
  pose proof (H (false,true)) as H1. simpl in H0,H1. congruence.
Qed.

Theorem factorization_obstruction {S Q A : Type} (q : S -> Q) (r : S -> A) :
  (exists s t, q s = q t /\ r s <> r t) ->
  ~ exists d : Q -> A, forall s, d (q s) = r s.
Proof.
  intros [s [t [Hq Hr]]] [d Hd]. apply Hr.
  rewrite <- (Hd s), <- (Hd t), Hq; reflexivity.
Qed.

Print Assumptions observation_reflexive.
Print Assumptions observation_symmetric.
Print Assumptions observation_transitive.
Print Assumptions observation_step.
Print Assumptions observation_now.
Print Assumptions observation_greatest.
Print Assumptions erasure_least.
Print Assumptions erasure_preserves_iff_marks_invisible.
Print Assumptions invisible_marks_allow_purge.
Print Assumptions zero_cost_preserves_ledger.
Print Assumptions zero_cost_preserves_record.
Print Assumptions mark_immediately_silent.
Print Assumptions steering_exposes_mark.
Print Assumptions no_autonomous_working_projection.
Print Assumptions factorization_obstruction.
