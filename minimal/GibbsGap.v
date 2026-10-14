(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file is the Shannon form of the strict concentration in NoisyChairs.v: for a strictly positive spread the relative entropy to the uniform spread is nonnegative and strictly positive off the uniform spread, and equals ln N minus the entropy; it uses the Coq real-number library and stands alone from the certification-system kernel. *)
(* Shannon version, machine-checked over the reals: for a strictly positive spread q on N states
   summing to 1, the relative entropy to the uniform spread, sum q_i ln(N q_i) = ln N - H(q),
   is >= 0, and > 0 as soon as some q_i differs from 1/N.
   With NoisyChairs/Concentrate: a raising kernel sends the uniform spread to a non-uniform one,
   so (when that spread is strictly positive) its Shannon entropy strictly drops below ln N.
   That drop is the quantity Landauer's premise charges heat for. *)
Require Import Reals Lra List.
Import ListNotations.
Local Open Scope R_scope.

Definition Rsum (l : list R) : R := fold_right Rplus 0 l.
Lemma Rsum_map_plus : forall {A} (f g : A -> R) l, Rsum (map (fun x => f x + g x) l) = Rsum (map f l) + Rsum (map g l).
Proof. induction l; simpl. ring. rewrite IHl. ring. Qed.
Lemma Rsum_map_scale : forall {A} (k : R) (f : A -> R) l, Rsum (map (fun x => k * f x) l) = k * Rsum (map f l).
Proof. induction l; simpl. ring. rewrite IHl. ring. Qed.
Lemma Rsum_le : forall {A} (f g : A -> R) l, (forall x, In x l -> f x <= g x) -> Rsum (map f l) <= Rsum (map g l).
Proof. induction l; simpl; intros. lra. assert (f a <= g a) by auto. assert (Rsum (map f l) <= Rsum (map g l)) by auto. lra. Qed.
Lemma Rsum_lt : forall {A} (f g : A -> R) l, (forall x, In x l -> f x <= g x) ->
  (exists x, In x l /\ f x < g x) -> Rsum (map f l) < Rsum (map g l).
Proof.
  induction l; simpl; intros Hle [x [Hx Hlt]]. contradiction.
  destruct Hx as [-> | Hx].
  - assert (Rsum (map f l) <= Rsum (map g l)) by (apply Rsum_le; auto). lra.
  - assert (Rsum (map f l) < Rsum (map g l)) by (apply IHl; auto; exists x; auto). assert (f a <= g a) by auto. lra.
Qed.
Lemma Rsum_map_const : forall {A} (k : R) (l : list A), Rsum (map (fun _ => k) l) = k * INR (length l).
Proof. induction l; simpl. ring. rewrite IHl. destruct l; simpl; try rewrite S_INR; ring. Qed.

(* ln y <= y - 1, and strictly when y <> 1 *)
Lemma ln_le_minus1 : forall y, 0 < y -> ln y <= y - 1.
Proof. intros y Hy. assert (H := exp_ineq1_le (ln y)). rewrite exp_ln in H by auto. lra. Qed.
Lemma ln_lt_minus1 : forall y, 0 < y -> y <> 1 -> ln y < y - 1.
Proof.
  intros y Hy Hne.
  assert (Hl : ln y <> 0). { intro E. apply Hne. rewrite <- (exp_ln y) by auto. rewrite E. apply exp_0. }
  assert (H := exp_ineq1 (ln y) Hl). rewrite exp_ln in H by auto. lra.
Qed.

Section Gibbs.
Variable q : list R.                       (* the spread *)
Let N := INR (length q).
Hypothesis pos : forall x, In x q -> 0 < x.
Hypothesis total : Rsum q = 1.
Hypothesis nonempty : (0 < length q)%nat.

Lemma N_pos : 0 < N.
Proof. unfold N. apply lt_0_INR. auto. Qed.

(* relative entropy to uniform: sum x ln (N x) *)
Definition relent := Rsum (map (fun x => x * ln (N * x)) q).

(* each term: x ln(N x) = - x ln (1/(N x)) >= - x (1/(N x) - 1) = x - 1/N *)
Lemma term_ge : forall x, In x q -> x - / N <= x * ln (N * x).
Proof.
  intros x Hx. assert (Hx0 := pos x Hx). assert (HN := N_pos).
  assert (Hinv : ln (N * x) = - ln (/ (N * x))). { rewrite ln_Rinv. ring. apply Rmult_lt_0_compat; auto. }
  assert (Hl := ln_le_minus1 (/ (N * x)) (Rinv_0_lt_compat _ (Rmult_lt_0_compat _ _ HN Hx0))).
  rewrite Hinv.
  assert (x * ln (/ (N * x)) <= x * (/ (N * x) - 1)) by (apply Rmult_le_compat_l; lra).
  replace (x * (/ (N * x) - 1)) with (/ N - x) in H by (field; lra).
  lra.
Qed.
Lemma term_gt : forall x, In x q -> x <> / N -> x - / N < x * ln (N * x).
Proof.
  intros x Hx Hne. assert (Hx0 := pos x Hx). assert (HN := N_pos).
  assert (Hinv : ln (N * x) = - ln (/ (N * x))). { rewrite ln_Rinv. ring. apply Rmult_lt_0_compat; auto. }
  assert (Hne1 : / (N * x) <> 1).
  { intro E. apply Hne.
    assert (N * x = 1). { rewrite <- (Rinv_inv (N * x)). rewrite E. apply Rinv_1. }
    apply Rmult_eq_reg_l with (r := N); [| lra]. rewrite Rinv_r by lra. auto. }
  assert (Hl := ln_lt_minus1 (/ (N * x)) (Rinv_0_lt_compat _ (Rmult_lt_0_compat _ _ HN Hx0)) Hne1).
  rewrite Hinv.
  assert (x * ln (/ (N * x)) < x * (/ (N * x) - 1)) by (apply Rmult_lt_compat_l; lra).
  replace (x * (/ (N * x) - 1)) with (/ N - x) in H by (field; lra).
  lra.
Qed.

Lemma map_id_list : forall l : list R, map (fun x : R => x) l = l.
Proof. induction l; simpl; auto. rewrite IHl. auto. Qed.
Lemma base_sum : Rsum (map (fun x => x - / N) q) = 0.
Proof.
  transitivity (Rsum (map (fun x : R => x + (-1) * / N) q)).
  { f_equal. apply map_ext. intro. ring. }
  rewrite Rsum_map_plus. rewrite Rsum_map_scale. rewrite Rsum_map_const. rewrite map_id_list.
  rewrite total. unfold N. assert (HN := N_pos). unfold N in HN. field. lra.
Qed.

Theorem gibbs_nonneg : 0 <= relent.
Proof. unfold relent. rewrite <- base_sum. apply Rsum_le. intros. apply term_ge. auto. Qed.

Theorem gibbs_strict : (exists x, In x q /\ x <> / N) -> 0 < relent.
Proof.
  intros [x [Hx Hne]]. unfold relent. rewrite <- base_sum. apply Rsum_lt.
  - intros. apply term_ge. auto.
  - exists x. split; auto. apply term_gt; auto.
Qed.

(* and relent = ln N - H(q) with H(q) = - sum x ln x *)
Definition H := - Rsum (map (fun x => x * ln x) q).
Theorem relent_is_entropy_gap : relent = ln N - H.
Proof.
  unfold relent, H.
  transitivity (Rsum (map (fun x => x * ln N + x * ln x) q)).
  { f_equal. apply map_ext_in. intros x Hx. rewrite ln_mult by (try apply N_pos; apply pos; auto). ring. }
  rewrite Rsum_map_plus.
  transitivity (ln N * Rsum (map (fun x : R => x) q) + Rsum (map (fun x => x * ln x) q)).
  { f_equal. rewrite <- Rsum_map_scale. f_equal. apply map_ext. intro. ring. }
  rewrite map_id_list. rewrite total. ring.
Qed.
End Gibbs.
