(* SCOPE NOTE (standalone proof scope): maps between pointed deterministic
   transition systems, with explicit access words for constructive existence.
   Uses CanonicalObservation.run; no native instruction semantics or physical
   pricing is asserted. LiftTerminal separately connects trace evaluation to
   the actual neutral lift. *)
From Coq Require Import List.
From Audit Require Import CanonicalObservation.
Import ListNotations.
Module O := CanonicalObservation.

Section Maps.
Context {A B I : Type}.
Variable da : I -> A -> A.
Variable db : I -> B -> B.
Variable a0 : A.
Variable b0 : B.

Definition morphism (f : A -> B) :=
  f a0 = b0 /\ forall i a, f (da i a) = db i (f a).
Definition kernel_inclusion := forall u v,
  O.run da u a0 = O.run da v a0 -> O.run db u b0 = O.run db v b0.

Lemma morphism_runs : forall f, morphism f -> forall w a,
  f (O.run da w a) = O.run db w (f a).
Proof.
  intros f [_ H] w; induction w as [|i w IH]; intro a; cbn; [reflexivity|].
  rewrite IH, H; reflexivity.
Qed.

Theorem morphism_requires_kernel_inclusion :
  (exists f, morphism f) -> kernel_inclusion.
Proof.
  intros [f H] u v E.
  pose proof (morphism_runs f H u a0) as Hu.
  pose proof (morphism_runs f H v a0) as Hv.
  destruct H as [H0 _]; rewrite H0 in Hu, Hv; congruence.
Qed.

Variable access : A -> list I.
Hypothesis reaches : forall a, O.run da (access a) a0 = a.
Definition factor (a : A) := O.run db (access a) b0.

Lemma factor_on_words : kernel_inclusion -> forall w,
  factor (O.run da w a0) = O.run db w b0.
Proof.
  intros H w; unfold factor; apply H; apply reaches.
Qed.

Theorem factor_is_morphism : kernel_inclusion -> morphism factor.
Proof.
  intro H; split.
  - exact (factor_on_words H []).
  - intros i a.
    assert (E : da i a = O.run da (access a ++ [i]) a0).
    { rewrite O.run_append, reaches; reflexivity. }
    rewrite E, factor_on_words by exact H.
    rewrite O.run_append; reflexivity.
Qed.

Theorem reachable_morphism_unique : forall f,
  morphism f -> forall a, f a = factor a.
Proof.
  intros f H a; rewrite <- (reaches a) at 1.
  rewrite morphism_runs by exact H.
  destruct H as [H0 _]; rewrite H0; reflexivity.
Qed.

Theorem morphism_exists_iff_kernel_inclusion :
  (exists f, morphism f) <-> kernel_inclusion.
Proof.
  split; [apply morphism_requires_kernel_inclusion|].
  intro H; exists factor; apply factor_is_morphism; exact H.
Qed.

Theorem unique_factorization_iff_kernel_inclusion :
  (exists f, morphism f /\
    forall g, morphism g -> forall a, g a = f a) <-> kernel_inclusion.
Proof.
  split.
  - intros [f [H _]]; apply morphism_requires_kernel_inclusion; exists f; exact H.
  - intro H; exists factor; split.
    + apply factor_is_morphism; exact H.
    + apply reachable_morphism_unique.
Qed.

Theorem factor_surjective_on_target_reachable : kernel_inclusion ->
  forall b, (exists w, O.run db w b0 = b) -> exists a, factor a = b.
Proof.
  intros H b [w E]; exists (O.run da w a0).
  rewrite factor_on_words by exact H; exact E.
Qed.
End Maps.

Section FreeTrace.
Context {I S : Type}.
Variable step : I -> S -> S.
Variable start : S.

Theorem trace_evaluation_uniquely_preserves_steps :
  exists eval : list I -> S,
    eval [] = start /\
    (forall w i, eval (w ++ [i]) = step i (eval w)) /\
    (forall f : list I -> S, f [] = start ->
      (forall w i, f (w ++ [i]) = step i (f w)) ->
      forall w, f w = eval w).
Proof.
  exists (fun w => O.run step w start); repeat split.
  - intros w i; rewrite O.run_append; reflexivity.
  - intros f H0 Hs w; induction w using rev_ind.
    + exact H0.
    + rewrite Hs, IHw, O.run_append; reflexivity.
Qed.
End FreeTrace.
