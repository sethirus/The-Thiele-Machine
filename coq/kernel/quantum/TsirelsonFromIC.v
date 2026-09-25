(** CHSH algebra for the quadratic information-causality condition.

    The protocol bias condition E_I^2 + E_II^2 <= 1, with
    E_I = (E00 + E10)/2 and E_II = (E01 - E11)/2, gives the inequality
    below (Pawlowski et al., https://arxiv.org/abs/0905.2292).
    This file proves its CHSH consequence. The information-theoretic
    protocol derivation and the physical principle are external premises;
    the predicate is not a definition of Information Causality itself. *)

From Coq Require Import Reals Lra Psatz.
From Kernel Require Import TsirelsonFromMu.
Local Open Scope R_scope.

(* SCOPE NOTE: standalone proof scope, standalone correlator algebra with an explicit quadratic premise. *)
Definition ic_quadratic_bound (b : CorrelatorBox) : Prop :=
  (cb_E00 b + cb_E10 b)^2 + (cb_E01 b - cb_E11 b)^2 <= 4.

Theorem tsirelson_bound_from_ic_quadratic :
  forall b : CorrelatorBox,
    ic_quadratic_bound b ->
    Rabs (chsh_S b) <= 2 * sqrt 2.
Proof.
  intros [a b c d] H.
  unfold ic_quadratic_bound, chsh_S in *; simpl in *.
  pose proof (Rle_0_sqr (a+c-(b-d))) as Hnonneg.
  unfold Rsqr in Hnonneg.
  assert (Hsq : (a+b+c-d)^2 <= 8) by nra.
  assert (Hroot : (sqrt 2)^2 = 2) by (rewrite pow2_sqrt; lra).
  assert (Hpos : 0 <= 2 * sqrt 2) by (pose proof (sqrt_pos 2); lra).
  rewrite <- (Rabs_right (2 * sqrt 2)); [|lra].
  apply Rsqr_le_abs_0. unfold Rsqr. nra.
Qed.

Theorem pr_box_violates_ic_quadratic : ~ ic_quadratic_bound pr_box.
Proof. unfold ic_quadratic_bound, pr_box; simpl; lra. Qed.

Theorem deterministic_strategy_satisfies_ic_quadratic :
  forall a0 a1 b0 b1 : R,
    a0*a0 = 1 -> a1*a1 = 1 -> b0*b0 = 1 -> b1*b1 = 1 ->
    ic_quadratic_bound
      {| cb_E00 := a0*b0; cb_E01 := a0*b1;
         cb_E10 := a1*b0; cb_E11 := a1*b1 |}.
Proof.
  intros a0 a1 b0 b1 Ha0 Ha1 Hb0 Hb1.
  change ((a0*b0+a1*b0)^2 + (a0*b1-a1*b1)^2 <= 4).
  replace ((a0*b0+a1*b0)^2 + (a0*b1-a1*b1)^2)
    with (b0*b0*(a0+a1)^2 + b1*b1*(a0-a1)^2) by ring.
  rewrite Hb0, Hb1. nra.
Qed.

Print Assumptions tsirelson_bound_from_ic_quadratic.
Print Assumptions pr_box_violates_ic_quadratic.
Print Assumptions deterministic_strategy_satisfies_ic_quadratic.
