(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file is the time column: a biased walk (Bennett's Brownian computer) produces strictly positive entropy per tick at any nonzero speed, and heat times time is at least the square of the distance; it uses the Coq real-number library and stands alone from the certification-system kernel. *)
(* The time column as a theorem. Bennett's Brownian computer, as a biased walk: at each tick it moves
   forward with probability p and back with probability 1-p. Its speed is v = 2p - 1 (net steps per tick).
   Its entropy production per tick (Schnakenberg's formula for a biased walk, in units of k) is
     sigma(p) = (2p - 1) * ln (p / (1 - p)).
   Theorem: sigma(p) > 0 whenever the speed is not zero, and sigma(1/2) = 0.
   So at any nonzero speed every tick pays heat; only the machine that goes nowhere pays nothing. *)
Require Import Reals Lra.
Local Open Scope R_scope.

Definition sigma (p : R) : R := (2 * p - 1) * ln (p / (1 - p)).

Lemma ratio_gt_1 : forall p, 1/2 < p < 1 -> 1 < p / (1 - p).
Proof. intros p [H1 H2]. apply Rmult_lt_reg_r with (r := 1 - p); [lra|].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra. Qed.
Lemma ratio_lt_1 : forall p, 0 < p < 1/2 -> 0 < p / (1 - p) < 1.
Proof. intros p [H1 H2]. split.
  - apply Rdiv_lt_0_compat; lra.
  - apply Rmult_lt_reg_r with (r := 1 - p); [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra. Qed.

Theorem heat_at_any_speed : forall p, 0 < p < 1 -> p <> 1/2 -> 0 < sigma p.
Proof.
  intros p [Hp0 Hp1] Hne. unfold sigma.
  destruct (Rlt_le_dec p (1/2)) as [Hlt | Hge].
  - (* backwards: both factors negative *)
    assert (Hr := ratio_lt_1 p (conj Hp0 Hlt)).
    assert (ln (p / (1 - p)) < 0).
    { rewrite <- ln_1. apply ln_increasing; lra. }
    assert (2 * p - 1 < 0) by lra.
    nra.
  - assert (1/2 < p) by (destruct (Rle_lt_or_eq_dec _ _ Hge); [auto | exfalso; apply Hne; auto]).
    assert (Hr := ratio_gt_1 p (conj H Hp1)).
    assert (0 < ln (p / (1 - p))).
    { rewrite <- ln_1. apply ln_increasing; lra. }
    assert (0 < 2 * p - 1) by lra.
    nra.
Qed.

Theorem no_heat_at_rest : sigma (1/2) = 0.
Proof. unfold sigma. replace (2 * (1/2) - 1) with 0 by lra. ring. Qed.

(* The exchange rate: heat times time has a floor.
   Speed v in (0,1). Heat per net step of progress = ln((1+v)/(1-v)) (sigma per tick / v).
   Lemma: ln((1+v)/(1-v)) >= v.  Then N net steps cost heat >= N v, take time N / v,
   and heat * time >= N^2. Going slower cuts the heat and lengthens the time; the product never
   goes under the square of the distance travelled. *)
Lemma ln_le_minus1 : forall y, 0 < y -> ln y <= y - 1.
Proof. intros y Hy. assert (H := exp_ineq1_le (ln y)). rewrite exp_ln in H by auto. lra. Qed.

Lemma ln_ratio_ge_v : forall v, 0 < v < 1 -> v <= ln ((1 + v) / (1 - v)).
Proof.
  intros v [H0 H1].
  unfold Rdiv. rewrite ln_mult; [| lra | apply Rinv_0_lt_compat; lra].
  rewrite ln_Rinv by lra.
  assert (0 <= ln (1 + v)). { rewrite <- ln_1. apply Rlt_le. apply ln_increasing; lra. }
  assert (ln (1 - v) <= - v). { assert (Hm := ln_le_minus1 (1 - v)). lra. }
  lra.
Qed.

Definition heat (N v : R) := N * ln ((1 + v) / (1 - v)).
Definition time (N v : R) := N / v.

Theorem heat_time_floor : forall N v, 0 <= N -> 0 < v < 1 -> N * N <= heat N v * time N v.
Proof.
  intros N v HN Hv. unfold heat, time.
  assert (Hl := ln_ratio_ge_v v Hv).
  assert (Hv0 : 0 < v) by lra.
  replace (N * ln ((1 + v) / (1 - v)) * (N / v)) with (N * N * (ln ((1 + v) / (1 - v)) / v)) by (field; lra).
  assert (1 <= ln ((1 + v) / (1 - v)) / v).
  { apply Rmult_le_reg_r with (r := v); auto. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r; lra. }
  nra.
Qed.
