(** NecEChshEquality: where the row-bound form of Tsirelson's bound is
    reached, and the worked tallies of the derivation appendix.

    - Under the row bounds, S^2 = 8 holds only at a = b = c = -d with
      2 a^2 = 1, where (a, b, c, d) = (E00, E01, E10, E11) and
      S = a + b + c - d ([nec_e_equality_forces_point]); that is, at the
      point of the tightness theorem and its negative
      ([nec_e_equality_two_points]).
    - No tally's correlator solves 2 a^2 = 1: a ratio of whole numbers with
      a positive denominator never does ([nec_e_no_rational_half_square]).
    - The worked cascade: correlators (3/5, 3/5, 3/5, -3/5) with the moment
      buckets (0/2, 0/2, 0/2, 0/2, -2/4) pass the full 1+AB check
      ([nec_e_worked_cascade_passes]); with the last bucket 0/2 it fails
      ([nec_e_worked_cascade_fails_at_zero]); the level-1 check passes on the
      same counts ([nec_e_worked_level1_passes]).
    - Interior only: the tally with correlators (3/5, 4/5, 4/5, -3/5) passes
      the level-1 check ([nec_e_singular_level1_passes]) and fails the full
      1+AB check for every choice of buckets, because its H11 is zero
      ([nec_e_singular_full_fails]). *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is about the CHSH check over the real numbers and the integer tallies (it
   imports the machine-free quantum files and NecEChsh.v only). Its link to
   the abstract record (the machine of SmallChshMachine.v as a
   CertificationSystem, with the floor of 3 for a certified run) lives in
   SmallChshLinks.v. *)

From Coq Require Import List Reals Lra Psatz ZArith Bool.
From Kernel Require Import CHSHColumnCheck.
From Kernel Require Import NecEChsh.

Open Scope R_scope.

Theorem nec_e_equality_forces_point : forall a b c d : R,
  a * a + b * b <= 1 -> c * c + d * d <= 1 -> (a + b + c - d) * (a + b + c - d) = 8 ->
  a = b /\ a = c /\ d = - a /\ 2 * (a * a) = 1.
Proof.
  intros a b c d Hr1 Hr2 HS.
  assert (Hsos : (a - b) * (a - b) + (a - c) * (a - c) + (a + d) * (a + d) +
                 (b - c) * (b - c) + (b + d) * (b + d) + (c + d) * (c + d) =
                 4 * (a * a + b * b + c * c + d * d) - (a + b + c - d) * (a + b + c - d))
    by ring.
  assert (H0 : (a - b) * (a - b) + (a - c) * (a - c) + (a + d) * (a + d) +
               (b - c) * (b - c) + (b + d) * (b + d) + (c + d) * (c + d) <= 0) by lra.
  pose proof (Rle_0_sqr (a - b)) as S1. pose proof (Rle_0_sqr (a - c)) as S2.
  pose proof (Rle_0_sqr (a + d)) as S3. pose proof (Rle_0_sqr (b - c)) as S4.
  pose proof (Rle_0_sqr (b + d)) as S5. pose proof (Rle_0_sqr (c + d)) as S6.
  unfold Rsqr in *.
  assert (E1 : (a - b) * (a - b) = 0) by lra.
  assert (E2 : (a - c) * (a - c) = 0) by lra.
  assert (E3 : (a + d) * (a + d) = 0) by lra.
  apply Rmult_integral in E1. apply Rmult_integral in E2. apply Rmult_integral in E3.
  assert (Hab : a = b) by (destruct E1; lra).
  assert (Hac : a = c) by (destruct E2; lra).
  assert (Had : d = - a) by (destruct E3; lra).
  split; [exact Hab | split; [exact Hac | split; [exact Had |]]].
  subst b c d. nra.
Qed.

Theorem nec_e_equality_two_points : forall a b c d : R,
  a * a + b * b <= 1 -> c * c + d * d <= 1 -> (a + b + c - d) * (a + b + c - d) = 8 ->
  (a = / sqrt 2 \/ a = - / sqrt 2) /\ b = a /\ c = a /\ d = - a.
Proof.
  intros a b c d Hr1 Hr2 HS.
  destruct (nec_e_equality_forces_point a b c d Hr1 Hr2 HS) as [Hab [Hac [Had Ha]]].
  split; [| split; [symmetry; exact Hab | split; [symmetry; exact Hac | exact Had]]].
  assert (Hs2 : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  assert (Hpos : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  assert (Hsq : (a * sqrt 2) * (a * sqrt 2) = 1) by nra.
  assert (Hf : (a * sqrt 2 - 1) * (a * sqrt 2 + 1) = 0) by nra.
  apply Rmult_integral in Hf. destruct Hf as [Hf | Hf].
  - left. apply (Rmult_eq_reg_r (sqrt 2)); [| lra].
    rewrite Rinv_l by lra. lra.
  - right. apply (Rmult_eq_reg_r (sqrt 2)); [| lra].
    rewrite Ropp_mult_distr_l_reverse, Rinv_l by lra. lra.
Qed.

Theorem nec_e_no_rational_half_square : forall D N : Z,
  (0 < N)%Z -> 2 * ((IZR D / IZR N) * (IZR D / IZR N)) <> 1.
Proof.
  intros D N HN H.
  assert (HNr : IZR N <> 0) by (apply not_0_IZR; lia).
  assert (H2 : 2 * (IZR D * IZR D) = IZR N * IZR N).
  { replace (2 * (IZR D * IZR D)) with
      ((2 * ((IZR D / IZR N) * (IZR D / IZR N))) * (IZR N * IZR N)) by (field; exact HNr).
    rewrite H. ring. }
  assert (HZ : IZR (N * N) = IZR (2 * (D * D))).
  { rewrite !mult_IZR. lra. }
  apply eq_IZR in HZ.
  pose proof (nec_e_sq2_descent (S (Z.abs_nat D)) N D (Nat.lt_succ_diag_r _) HZ) as HD0.
  subst D. rewrite Rdiv_0_l, Rmult_0_l, Rmult_0_r in H. lra.
Qed.

Close Scope R_scope.
Open Scope Z_scope.

Theorem nec_e_worked_cascade_passes :
  q1ab_g12345_check_z_kernel 3 5 3 5 3 5 (-3) 5 0 2 0 2 0 2 0 2 (-2) 4 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem nec_e_worked_cascade_fails_at_zero :
  q1ab_g12345_check_z_kernel 3 5 3 5 3 5 (-3) 5 0 2 0 2 0 2 0 2 0 2 = false.
Proof. vm_compute. reflexivity. Qed.

(** The worked counts as a tally: 4 same and 1 different gives 3/5, 1 same
    and 4 different gives -3/5. *)
Definition nec_e_worked_tally : WitnessCounts :=
  {| wc_same_00 := 4; wc_diff_00 := 1; wc_same_01 := 4; wc_diff_01 := 1;
     wc_same_10 := 4; wc_diff_10 := 1; wc_same_11 := 1; wc_diff_11 := 4 |}.

Theorem nec_e_worked_level1_passes : column_contractive_check_witness nec_e_worked_tally = true.
Proof. vm_compute. reflexivity. Qed.

(** Correlators (3/5, 4/5, 4/5, -3/5), as 8 same and 2 different (3/5),
    9 and 1 (4/5), and 2 and 8 (-3/5). *)
Definition nec_e_singular_tally : WitnessCounts :=
  {| wc_same_00 := 8; wc_diff_00 := 2; wc_same_01 := 9; wc_diff_01 := 1;
     wc_same_10 := 9; wc_diff_10 := 1; wc_same_11 := 2; wc_diff_11 := 8 |}.

Theorem nec_e_singular_level1_passes : column_contractive_check_witness nec_e_singular_tally = true.
Proof. vm_compute. reflexivity. Qed.

Theorem nec_e_singular_full_fails : forall Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5,
  q1ab_g12345_check_z_kernel 6 10 8 10 8 10 (-6) 10 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 = false.
Proof.
  intros. unfold q1ab_g12345_check_z_kernel.
  assert (H : cleared_g12345_H11_Z 6 10 8 10 8 10 (-6) 10 Ng1 Dg1 Ng2 Dg2 Ng3 Dg3 Ng4 Dg4 Ng5 Dg5 = 0).
  { unfold cleared_g12345_H11_Z. ring. }
  rewrite H. simpl.
  repeat rewrite andb_false_r. repeat rewrite andb_false_l.
  destruct (0 <? 10); destruct (0 <? Dg1); destruct (0 <? Dg2); destruct (0 <? Dg3);
  destruct (0 <? Dg4); destruct (0 <? Dg5); simpl; try reflexivity;
  repeat (match goal with |- context [?x && false] => rewrite (andb_false_r x) end); reflexivity.
Qed.

Close Scope Z_scope.

Print Assumptions nec_e_equality_forces_point.
Print Assumptions nec_e_equality_two_points.
Print Assumptions nec_e_no_rational_half_square.
Print Assumptions nec_e_worked_cascade_passes.
Print Assumptions nec_e_worked_cascade_fails_at_zero.
Print Assumptions nec_e_worked_level1_passes.
Print Assumptions nec_e_singular_level1_passes.
Print Assumptions nec_e_singular_full_fails.
