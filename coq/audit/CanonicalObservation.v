(* SCOPE NOTE (standalone proof scope): generic deterministic observation
   theorem, not a claim about native instruction semantics or physical cost.
   This is a constructive Moore/Myhill--Nerode style uniqueness argument.
   Access words are supplied data; no choice or quotient axiom is used.
   Minimal means behavioral separation, not infinite cardinal minimality. *)
From Coq Require Import List.
Import ListNotations.

Section Runs.
Context {State Input : Type}.
Variable step : Input -> State -> State.
Fixpoint run (w : list Input) (s : State) : State :=
  match w with [] => s | i::rest => run rest (step i s) end.

Lemma run_append : forall u v s,
  run (u ++ v) s = run v (run u s).
Proof. induction u; intros v s; simpl; [reflexivity|apply IHu]. Qed.
End Runs.

Section CoarsestRelation.
Context {State Input Output : Type}.
Variable step : Input -> State -> State.
Variable observe : State -> Output.

Definition future_equivalent (s t : State) :=
  forall w, observe (run step w s) = observe (run step w t).

Theorem future_equivalence_laws :
  (forall s, future_equivalent s s) /\
  (forall s t, future_equivalent s t -> future_equivalent t s) /\
  (forall s t u, future_equivalent s t -> future_equivalent t u ->
    future_equivalent s u).
Proof.
  unfold future_equivalent; repeat split; intros; congruence.
Qed.

Theorem future_equivalence_preserves_observation : forall s t,
  future_equivalent s t -> observe s = observe t.
Proof. intros s t H; exact (H []). Qed.

Theorem future_equivalence_stable : forall i s t,
  future_equivalent s t -> future_equivalent (step i s) (step i t).
Proof. intros i s t H w; exact (H (i::w)). Qed.

(* Every observation-preserving transition congruence refines this relation.
   No finiteness, decidability, quotient type or effectiveness is assumed. *)
Theorem future_equivalence_coarsest : forall R : State -> State -> Prop,
  (forall s t, R s t -> observe s = observe t) ->
  (forall i s t, R s t -> R (step i s) (step i t)) ->
  forall s t, R s t -> future_equivalent s t.
Proof.
  intros R Hout Hstep s t H w; revert s t H.
  induction w; intros s t H; simpl.
  - apply Hout; exact H.
  - apply IHw; apply Hstep; exact H.
Qed.

Theorem coarsest_relation_unique : forall R : State -> State -> Prop,
  (forall s t, R s t -> observe s = observe t) ->
  (forall i s t, R s t -> R (step i s) (step i t)) ->
  (forall Q : State -> State -> Prop,
    (forall s t, Q s t -> observe s = observe t) ->
    (forall i s t, Q s t -> Q (step i s) (step i t)) ->
    forall s t, Q s t -> R s t) ->
  forall s t, R s t <-> future_equivalent s t.
Proof.
  intros R Hout Hstep Hmax s t; split.
  - apply future_equivalence_coarsest; assumption.
  - apply Hmax.
    + apply future_equivalence_preserves_observation.
    + apply future_equivalence_stable.
Qed.
End CoarsestRelation.

Section Canonical.
Context {A B Input Output : Type}.
Variable stepA : Input -> A -> A.
Variable stepB : Input -> B -> B.
Variable startA : A.
Variable startB : B.
Variable outA : A -> Output.
Variable outB : B -> Output.
Variable accessA : A -> list Input.
Hypothesis reachesA : forall s, run stepA (accessA s) startA = s.
Hypothesis same_behavior : forall w,
  outA (run stepA w startA) = outB (run stepB w startB).
Hypothesis separatesB : forall s t,
  (forall w, outB (run stepB w s) = outB (run stepB w t)) -> s = t.

Definition canonical (s : A) : B := run stepB (accessA s) startB.

Theorem canonical_preserves_future : forall s w,
  outB (run stepB w (canonical s)) = outA (run stepA w s).
Proof.
  intros s w; unfold canonical.
  rewrite <- run_append, <- same_behavior, run_append, reachesA; reflexivity.
Qed.

Theorem canonical_preserves_output : forall s, outB (canonical s) = outA s.
Proof. intro s; exact (canonical_preserves_future s []). Qed.

Theorem canonical_preserves_start : canonical startA = startB.
Proof.
  apply separatesB; intro w.
  rewrite canonical_preserves_future; apply same_behavior.
Qed.

Theorem canonical_preserves_step : forall i s,
  canonical (stepA i s) = stepB i (canonical s).
Proof.
  intros i s; apply separatesB; intro w.
  rewrite canonical_preserves_future.
  symmetry; exact (canonical_preserves_future s (i::w)).
Qed.

Theorem canonical_preserves_run : forall w s,
  canonical (run stepA w s) = run stepB w (canonical s).
Proof.
  induction w; intro s; simpl; [reflexivity|].
  rewrite IHw, canonical_preserves_step; reflexivity.
Qed.

Theorem canonical_merges_exactly_equivalent_states : forall s t,
  canonical s = canonical t <->
  (forall w, outA (run stepA w s) = outA (run stepA w t)).
Proof.
  intros s t; split.
  - intros E w; rewrite <- !canonical_preserves_future, E; reflexivity.
  - intro H; apply separatesB; intro w; rewrite !canonical_preserves_future; apply H.
Qed.

(* Start/step preservation already forces the map on every reachable state.
   This is pointwise uniqueness, requiring no functional extensionality. *)
Theorem canonical_unique : forall f : A -> B,
  f startA = startB ->
  (forall i s, f (stepA i s) = stepB i (f s)) ->
  forall s, f s = canonical s.
Proof.
  intros f Hstart Hstep.
  assert (Hrun : forall w s, f (run stepA w s) = run stepB w (f s)).
  { induction w; intro s; simpl; [reflexivity|rewrite IHw, Hstep; reflexivity]. }
  intro s; rewrite <- (reachesA s) at 1.
  rewrite Hrun, Hstart; reflexivity.
Qed.

Hypothesis reachableB : forall t, exists w, run stepB w startB = t.

Theorem canonical_surjective : forall t, exists s, canonical s = t.
Proof.
  intro t; destruct (reachableB t) as [w Hw].
  exists (run stepA w startA).
  rewrite canonical_preserves_run, canonical_preserves_start; exact Hw.
Qed.

Hypothesis separatesA : forall s t,
  (forall w, outA (run stepA w s) = outA (run stepA w t)) -> s = t.

Theorem canonical_injective : forall s t, canonical s = canonical t -> s = t.
Proof.
  intros s t E; apply separatesA.
  apply canonical_merges_exactly_equivalent_states; exact E.
Qed.

Theorem minimal_realizations_uniquely_isomorphic :
  exists f : A -> B,
    f startA = startB /\
    (forall i s, f (stepA i s) = stepB i (f s)) /\
    (forall s, outB (f s) = outA s) /\
    (forall s t, f s = f t -> s = t) /\
    (forall t, exists s, f s = t) /\
    (forall g : A -> B, g startA = startB ->
      (forall i s, g (stepA i s) = stepB i (g s)) -> forall s, g s = f s).
Proof.
  exists canonical; repeat split.
  - apply canonical_preserves_start.
  - apply canonical_preserves_step.
  - apply canonical_preserves_output.
  - apply canonical_injective.
  - apply canonical_surjective.
  - apply canonical_unique.
Qed.
End Canonical.

Print Assumptions run_append.
Print Assumptions future_equivalence_laws.
Print Assumptions future_equivalence_preserves_observation.
Print Assumptions future_equivalence_stable.
Print Assumptions future_equivalence_coarsest.
Print Assumptions coarsest_relation_unique.
Print Assumptions canonical_preserves_future.
Print Assumptions canonical_preserves_output.
Print Assumptions canonical_preserves_start.
Print Assumptions canonical_preserves_step.
Print Assumptions canonical_preserves_run.
Print Assumptions canonical_merges_exactly_equivalent_states.
Print Assumptions canonical_unique.
Print Assumptions canonical_surjective.
Print Assumptions canonical_injective.
Print Assumptions minimal_realizations_uniquely_isomorphic.
