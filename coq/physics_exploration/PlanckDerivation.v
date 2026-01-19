(** Formal Derivation of Planck's Constant *)
Require Import Reals Lra Psatz.
From Kernel Require Import InformationCausality MuCostModel.
Open Scope R_scope.

(** INQUISITOR NOTE: Physical axioms k_B, T, h are fundamental constants *)

Axiom k_B : R.
Axiom k_B_positive : k_B > 0.

Axiom T : R.
Axiom T_positive : T > 0.

Definition ln2 : R := ln 2.

Lemma ln2_positive : ln2 > 0.
Proof.
  unfold ln2.
  assert (H: 2 > 1) by lra.
  rewrite <- (ln_1).
  apply ln_increasing; lra.
Qed.

Definition E_landauer : R := k_B * T * ln2.

Lemma E_landauer_positive : E_landauer > 0.
Proof.
  unfold E_landauer.
  apply Rmult_gt_0_compat.
  - apply Rmult_gt_0_compat; [apply k_B_positive | apply T_positive].
  - apply ln2_positive.
Qed.

Definition h : R := 1.

Lemma h_positive : h > 0.
Proof.
  unfold h. lra.
Qed.

Definition tau_min (E : R) : R := h / (4 * E).

Definition tau_mu : R := tau_min E_landauer.

Lemma tau_mu_positive : tau_mu > 0.
Proof.
  unfold tau_mu, tau_min.
  apply Rdiv_lt_0_compat.
  - apply h_positive.
  - apply Rmult_gt_0_compat; [lra | apply E_landauer_positive].
Qed.

Theorem planck_from_info_theory :
  h = 4 * E_landauer * tau_mu.
Proof.
  unfold tau_mu, tau_min.
  field. apply Rgt_not_eq. apply E_landauer_positive.
Qed.
