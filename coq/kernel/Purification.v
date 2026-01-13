(** * Purification from Accounting Constraints *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Local Open Scope R_scope.

Definition bloch_mixed (x y z : R) : Prop := x*x + y*y + z*z <= 1.
Definition bloch_pure (x y z : R) : Prop := x*x + y*y + z*z = 1.

Lemma pure_is_mixed : forall x y z : R,
  bloch_pure x y z -> bloch_mixed x y z.
Proof.
  intros x y z Hpure. unfold bloch_mixed, bloch_pure in *. lra.
Qed.

Definition purity (x y z : R) : R := x*x + y*y + z*z.

Lemma purity_nonneg : forall x y z : R, purity x y z >= 0.
Proof.
  intros. unfold purity. nra.
Qed.

Definition purification_deficit (x y z : R) : R := 1 - purity x y z.

Lemma mixed_has_deficit : forall x y z : R,
  bloch_mixed x y z -> 
  purity x y z <= 1 /\ purification_deficit x y z >= 0.
Proof.
  intros x y z Hmixed.
  unfold bloch_mixed, purity, purification_deficit in *.
  split.
  - exact Hmixed.
  - (* 1 - sum >= 0 follows from sum <= 1 *)
    apply Rge_minus. apply Rle_ge. exact Hmixed.
Qed.

Lemma sq_nonneg : forall x : R, x * x >= 0.
Proof. intro x. nra. Qed.

Theorem purification_principle :
  forall x y z : R,
    bloch_mixed x y z ->
    exists (lambda1 lambda2 : R),
      0 <= lambda1 <= 1 /\
      0 <= lambda2 <= 1 /\
      lambda1 + lambda2 = 1 /\
      (lambda1 - lambda2) * (lambda1 - lambda2) = purity x y z.
Proof.
  intros x y z Hmixed.
  set (r2 := purity x y z).
  assert (Hr2_bound: 0 <= r2 <= 1).
  { unfold r2, purity, bloch_mixed in *.
    split.
    - pose proof (sq_nonneg x). pose proof (sq_nonneg y). pose proof (sq_nonneg z). lra.
    - exact Hmixed. }
  exists ((1 + sqrt r2) / 2), ((1 - sqrt r2) / 2).
  assert (Hsqrt_bound: 0 <= sqrt r2 <= 1).
  { split.
    - apply sqrt_pos.
    - rewrite <- sqrt_1. apply sqrt_le_1; lra. }
  assert (H2ne0: 2 <> 0) by lra.
  assert (Hinv2: /2 <> 0) by (apply Rinv_neq_0_compat; lra).
  split; [| split; [| split]].
  - (* 0 <= (1 + sqrt r2)/2 <= 1 *)
    destruct Hsqrt_bound; split; lra.
  - (* 0 <= (1 - sqrt r2)/2 <= 1 *)
    destruct Hsqrt_bound; split; lra.
  - (* (1 + sqrt r2)/2 + (1 - sqrt r2)/2 = 1 *)
    unfold Rdiv.
    replace ((1 + sqrt r2) * /2 + (1 - sqrt r2) * /2) 
      with ((1 + sqrt r2 + 1 - sqrt r2) * /2) by ring.
    replace (1 + sqrt r2 + 1 - sqrt r2) with 2 by ring.
    apply Rinv_r. lra.
  - (* ((1+s)/2 - (1-s)/2)^2 = r2 *)
    unfold Rdiv.
    replace ((1 + sqrt r2) * /2 - (1 - sqrt r2) * /2) 
      with ((sqrt r2 + sqrt r2) * /2) by ring.
    assert (Heq: (sqrt r2 + sqrt r2) * /2 = sqrt r2).
    { replace ((sqrt r2 + sqrt r2) * / 2) with (sqrt r2 * (2 * / 2)).
      - assert (Htmp: 2 * / 2 = 1) by (apply Rinv_r; lra).
        rewrite Htmp. ring.
      - ring. }
    rewrite Heq.
    rewrite sqrt_sqrt; [reflexivity | destruct Hr2_bound; lra].
Qed.

Corollary pure_needs_no_reference : forall x y z : R,
  bloch_pure x y z ->
  purification_deficit x y z = 0.
Proof.
  intros x y z Hpure.
  unfold purification_deficit, purity, bloch_pure in *.
  lra.
Qed.

Lemma maximally_mixed_needs_full_reference :
  purification_deficit 0 0 0 = 1.
Proof.
  unfold purification_deficit, purity. ring.
Qed.
