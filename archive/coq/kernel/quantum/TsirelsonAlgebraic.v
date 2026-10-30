(** TsirelsonAlgebraic: Tsirelson's bound and the arcsine edge in any
    dimension.

    A quantum strategy in any dimension, finite or infinite, with the two
    parties on a tensor product or only commuting with each other, gives an
    algebra of operators and an expectation on it: psi x = Re <v, x v> for
    the shared state v. What the proofs below use of that is only this: the
    algebra has a sum, a product, real multiples and an adjoint; the product
    distributes over sums and real multiples; psi is linear and never
    negative on x* x; each observable is its own adjoint with psi (A A) at
    most 1 (a +-1 measurement, sharp or not); and Alice's observables commute
    with Bob's. No dimension appears anywhere.

    - For Z any real combination of A0, A1, B0, B1, psi (Z Z) is a fixed
      quadratic form in the coefficients, and it is never negative
      ([ta_quad_nonneg]).
    - Two such Z give Tsirelson's sum of squares: the CHSH value of the
      correlators psi (Ai Bj) is at most 2 sqrt 2 in absolute value
      ([ta_tsirelson]).
    - The same form, with the cross moments symmetrized and the diagonal
      raised to 1, is a PSD completion of the correlator table
      ([ta_realizable]), so the correlators satisfy the four arcsine
      inequalities of Landau and Masanes ([ta_arcsine]).
    - With a unit whose expectation is 1, the first level of the
      Navascues-Pironio-Acin hierarchy, marginals included, is PSD
      ([ta_npa_psd]): their necessary condition, in any dimension.
    - The hypotheses are met: the real numbers with a classical +-1 plan are
      an instance ([ta_classical_instance]). *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics. No definition or theorem here mentions a certification
   system, a ledger or a machine step; it imports only the PSD and
   arcsine-boundary files.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. The standalone boundary is stated here rather than inferred from
   an import. *)

From Coq Require Import List Reals Lra Psatz.
From Kernel Require Import ConstructivePSD NPAMomentMatrix ElliptopeCompletion ArcsineBoundary.
Open Scope R_scope.

Section Algebraic.

Variable T : Type.
Variable add : T -> T -> T.
Variable mul : T -> T -> T.
Variable scal : R -> T -> T.
Variable star : T -> T.
Variable psi : T -> R.

Hypothesis mul_add_l : forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Hypothesis mul_add_r : forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Hypothesis mul_scal_l : forall a x y, mul (scal a x) y = scal a (mul x y).
Hypothesis mul_scal_r : forall a x y, mul x (scal a y) = scal a (mul x y).
Hypothesis star_add : forall x y, star (add x y) = add (star x) (star y).
Hypothesis star_scal : forall a x, star (scal a x) = scal a (star x).
Hypothesis psi_add : forall x y, psi (add x y) = psi x + psi y.
Hypothesis psi_scal : forall a x, psi (scal a x) = a * psi x.
Hypothesis psi_pos : forall x, 0 <= psi (mul (star x) x).

Variables A0 A1 B0 B1 : T.
Hypothesis A0_sa : star A0 = A0.
Hypothesis A1_sa : star A1 = A1.
Hypothesis B0_sa : star B0 = B0.
Hypothesis B1_sa : star B1 = B1.
Hypothesis A0_le : psi (mul A0 A0) <= 1.
Hypothesis A1_le : psi (mul A1 A1) <= 1.
Hypothesis B0_le : psi (mul B0 B0) <= 1.
Hypothesis B1_le : psi (mul B1 B1) <= 1.
Hypothesis c00 : mul B0 A0 = mul A0 B0.
Hypothesis c01 : mul B1 A0 = mul A0 B1.
Hypothesis c10 : mul B0 A1 = mul A1 B0.
Hypothesis c11 : mul B1 A1 = mul A1 B1.

(** The correlators. *)
Definition ta_E00 : R := psi (mul A0 B0).
Definition ta_E01 : R := psi (mul A0 B1).
Definition ta_E10 : R := psi (mul A1 B0).
Definition ta_E11 : R := psi (mul A1 B1).

(** Alice's and Bob's own cross moments, symmetrized. *)
Definition ta_X : R := psi (mul A0 A1) + psi (mul A1 A0).
Definition ta_Y : R := psi (mul B0 B1) + psi (mul B1 B0).

Definition ta_Z (v1 v2 v3 v4 : R) : T :=
  add (add (add (scal v1 A0) (scal v2 A1)) (scal v3 B0)) (scal v4 B1).

Lemma ta_Z_sa : forall v1 v2 v3 v4, star (ta_Z v1 v2 v3 v4) = ta_Z v1 v2 v3 v4.
Proof.
  intros. unfold ta_Z. rewrite !star_add, !star_scal, A0_sa, A1_sa, B0_sa, B1_sa. reflexivity.
Qed.

(** psi (Z Z) as a quadratic form in the coefficients. *)
Lemma ta_quad_expand : forall v1 v2 v3 v4,
  psi (mul (ta_Z v1 v2 v3 v4) (ta_Z v1 v2 v3 v4)) =
    psi (mul A0 A0) * (v1 * v1) + psi (mul A1 A1) * (v2 * v2)
  + psi (mul B0 B0) * (v3 * v3) + psi (mul B1 B1) * (v4 * v4)
  + ta_X * (v1 * v2) + ta_Y * (v3 * v4)
  + 2 * ta_E00 * (v1 * v3) + 2 * ta_E01 * (v1 * v4)
  + 2 * ta_E10 * (v2 * v3) + 2 * ta_E11 * (v2 * v4).
Proof.
  intros. unfold ta_Z.
  rewrite !mul_add_l, !mul_add_r, !mul_scal_l, !mul_scal_r, !psi_add, !psi_scal.
  rewrite c00, c01, c10, c11.
  unfold ta_X, ta_Y, ta_E00, ta_E01, ta_E10, ta_E11. ring.
Qed.

Theorem ta_quad_nonneg : forall v1 v2 v3 v4,
  0 <= psi (mul A0 A0) * (v1 * v1) + psi (mul A1 A1) * (v2 * v2)
     + psi (mul B0 B0) * (v3 * v3) + psi (mul B1 B1) * (v4 * v4)
     + ta_X * (v1 * v2) + ta_Y * (v3 * v4)
     + 2 * ta_E00 * (v1 * v3) + 2 * ta_E01 * (v1 * v4)
     + 2 * ta_E10 * (v2 * v3) + 2 * ta_E11 * (v2 * v4).
Proof.
  intros. rewrite <- ta_quad_expand. rewrite <- (ta_Z_sa v1 v2 v3 v4) at 1. apply psi_pos.
Qed.

(** ** Tsirelson's bound *)

Theorem ta_tsirelson : Rabs (ta_E00 + ta_E01 + ta_E10 - ta_E11) <= 2 * sqrt 2.
Proof.
  set (r := / sqrt 2).
  assert (Hs : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  assert (Hss : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  assert (Hr2 : r * r = / 2) by (unfold r; rewrite <- Rinv_mult, Hss; reflexivity).
  assert (Hrs : 2 * r = sqrt 2).
  { unfold r. apply (Rmult_eq_reg_r (sqrt 2)); [| lra].
    rewrite Rmult_assoc, Rinv_l, Hss by lra. ring. }
  assert (F1 : 2 * (r * r) - 1 = 0) by (rewrite Hr2; field).
  pose proof (ta_quad_nonneg 1 0 (- r) (- r)) as Q1.
  pose proof (ta_quad_nonneg 0 1 (- r) r) as Q2.
  pose proof (ta_quad_nonneg 1 0 r r) as Q3.
  pose proof (ta_quad_nonneg 0 1 r (- r)) as Q4.
  set (d := psi (mul A0 A0) + psi (mul A1 A1) + psi (mul B0 B0) + psi (mul B1 B1)).
  assert (Hd : d <= 4) by (unfold d; lra).
  set (S := ta_E00 + ta_E01 + ta_E10 - ta_E11).
  assert (Up : sqrt 2 * S <= d).
  { assert (E : psi (mul A0 A0) * (1 * 1) + psi (mul A1 A1) * (0 * 0)
               + psi (mul B0 B0) * (- r * - r) + psi (mul B1 B1) * (- r * - r)
               + ta_X * (1 * 0) + ta_Y * (- r * - r)
               + 2 * ta_E00 * (1 * - r) + 2 * ta_E01 * (1 * - r)
               + 2 * ta_E10 * (0 * - r) + 2 * ta_E11 * (0 * - r)
               + (psi (mul A0 A0) * (0 * 0) + psi (mul A1 A1) * (1 * 1)
               + psi (mul B0 B0) * (- r * - r) + psi (mul B1 B1) * (r * r)
               + ta_X * (0 * 1) + ta_Y * (- r * r)
               + 2 * ta_E00 * (0 * - r) + 2 * ta_E01 * (0 * r)
               + 2 * ta_E10 * (1 * - r) + 2 * ta_E11 * (1 * r))
               = d * 1 + (psi (mul B0 B0) + psi (mul B1 B1)) * (2 * (r * r) - 1) - (2 * r) * S)
      by (unfold d, S; ring).
    rewrite F1, Hrs in E. lra. }
  assert (Lo : - d <= sqrt 2 * S).
  { assert (E : psi (mul A0 A0) * (1 * 1) + psi (mul A1 A1) * (0 * 0)
               + psi (mul B0 B0) * (r * r) + psi (mul B1 B1) * (r * r)
               + ta_X * (1 * 0) + ta_Y * (r * r)
               + 2 * ta_E00 * (1 * r) + 2 * ta_E01 * (1 * r)
               + 2 * ta_E10 * (0 * r) + 2 * ta_E11 * (0 * r)
               + (psi (mul A0 A0) * (0 * 0) + psi (mul A1 A1) * (1 * 1)
               + psi (mul B0 B0) * (r * r) + psi (mul B1 B1) * (- r * - r)
               + ta_X * (0 * 1) + ta_Y * (r * - r)
               + 2 * ta_E00 * (0 * r) + 2 * ta_E01 * (0 * - r)
               + 2 * ta_E10 * (1 * r) + 2 * ta_E11 * (1 * - r))
               = d * 1 + (psi (mul B0 B0) + psi (mul B1 B1)) * (2 * (r * r) - 1) + (2 * r) * S)
      by (unfold d, S; ring).
    rewrite F1, Hrs in E. lra. }
  assert (H22 : 4 = sqrt 2 * (2 * sqrt 2)) by nra.
  apply Rabs_le. split.
  - apply (Rmult_le_reg_l (sqrt 2)); [exact Hs |]. nra.
  - apply (Rmult_le_reg_l (sqrt 2)); [exact Hs |]. nra.
Qed.

(** ** The arcsine edge *)

(** The correlator table has a PSD completion: the cross moments are the
    symmetrized ones, and raising each diagonal entry to 1 keeps the form
    nonnegative. *)
Theorem ta_realizable : elliptope_realizable ta_E00 ta_E01 ta_E10 ta_E11.
Proof.
  exists (ta_X / 2), (ta_Y / 2). split.
  - exact (completed_matrix_symmetric ta_E00 ta_E01 ta_E10 ta_E11 (ta_X / 2) (ta_Y / 2)).
  - intro v. rewrite completed_quad_expand. cbv zeta.
    set (v0 := v Fin.F1). set (v1 := v (Fin.FS Fin.F1)). set (v2 := v (Fin.FS (Fin.FS Fin.F1))).
    set (v3 := v (Fin.FS (Fin.FS (Fin.FS Fin.F1)))). set (v4 := v (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))).
    pose proof (ta_quad_nonneg v1 v2 v3 v4) as Q.
    assert (S0 : 0 <= v0 * v0) by nra.
    assert (S1 : 0 <= (1 - psi (mul A0 A0)) * (v1 * v1)) by (apply Rmult_le_pos; nra).
    assert (S2 : 0 <= (1 - psi (mul A1 A1)) * (v2 * v2)) by (apply Rmult_le_pos; nra).
    assert (S3 : 0 <= (1 - psi (mul B0 B0)) * (v3 * v3)) by (apply Rmult_le_pos; nra).
    assert (S4 : 0 <= (1 - psi (mul B1 B1)) * (v4 * v4)) by (apply Rmult_le_pos; nra).
    apply Rle_ge.
    assert (E : v0 * v0 + v1 * v1 + v2 * v2 + v3 * v3 + v4 * v4
                + 2 * (ta_X / 2) * (v1 * v2) + 2 * (ta_Y / 2) * (v3 * v4)
                + 2 * ta_E00 * (v1 * v3) + 2 * ta_E01 * (v1 * v4)
                + 2 * ta_E10 * (v2 * v3) + 2 * ta_E11 * (v2 * v4)
              = v0 * v0
                + (psi (mul A0 A0) * (v1 * v1) + psi (mul A1 A1) * (v2 * v2)
                   + psi (mul B0 B0) * (v3 * v3) + psi (mul B1 B1) * (v4 * v4)
                   + ta_X * (v1 * v2) + ta_Y * (v3 * v4)
                   + 2 * ta_E00 * (v1 * v3) + 2 * ta_E01 * (v1 * v4)
                   + 2 * ta_E10 * (v2 * v3) + 2 * ta_E11 * (v2 * v4))
                + (1 - psi (mul A0 A0)) * (v1 * v1) + (1 - psi (mul A1 A1)) * (v2 * v2)
                + (1 - psi (mul B0 B0)) * (v3 * v3) + (1 - psi (mul B1 B1)) * (v4 * v4))
      by field.
    rewrite E. lra.
Qed.

(** Landau and Masanes, in any dimension. *)
Theorem ta_arcsine : am_arcsine_region ta_E00 ta_E01 ta_E10 ta_E11.
Proof. apply am_arcsine. exact ta_realizable. Qed.

(** ** The first NPA level, marginals included *)

Variable one : T.
Hypothesis mul_one_l : forall x, mul one x = x.
Hypothesis mul_one_r : forall x, mul x one = x.
Hypothesis star_one : star one = one.
Hypothesis psi_one : psi one = 1.

Definition ta_npa : NPAMomentMatrix := {|
  npa_EA0 := psi A0;
  npa_EA1 := psi A1;
  npa_EB0 := psi B0;
  npa_EB1 := psi B1;
  npa_E00 := ta_E00;
  npa_E01 := ta_E01;
  npa_E10 := ta_E10;
  npa_E11 := ta_E11;
  npa_rho_AA := ta_X / 2;
  npa_rho_BB := ta_Y / 2;
|}.

Lemma ta_npa_quad : forall (v : Vec5),
  quad5 (nat_matrix_to_fin5 (npa_to_matrix ta_npa)) v =
    let v0 := v Fin.F1 in
    let v1 := v (Fin.FS Fin.F1) in
    let v2 := v (Fin.FS (Fin.FS Fin.F1)) in
    let v3 := v (Fin.FS (Fin.FS (Fin.FS Fin.F1))) in
    let v4 := v (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) in
    v0 * v0 + v1 * v1 + v2 * v2 + v3 * v3 + v4 * v4
    + 2 * v0 * (psi A0 * v1 + psi A1 * v2 + psi B0 * v3 + psi B1 * v4)
    + 2 * (ta_X / 2) * (v1 * v2) + 2 * (ta_Y / 2) * (v3 * v4)
    + 2 * ta_E00 * (v1 * v3) + 2 * ta_E01 * (v1 * v4)
    + 2 * ta_E10 * (v2 * v3) + 2 * ta_E11 * (v2 * v4).
Proof.
  intros. cbv [quad5 sum_fin5 nat_matrix_to_fin5 npa_to_matrix ta_npa fin_to_nat].
  simpl. ring.
Qed.

Lemma ta_W_nonneg : forall v0 v1 v2 v3 v4,
  0 <= v0 * v0 + 2 * v0 * (psi A0 * v1 + psi A1 * v2 + psi B0 * v3 + psi B1 * v4)
     + (psi (mul A0 A0) * (v1 * v1) + psi (mul A1 A1) * (v2 * v2)
        + psi (mul B0 B0) * (v3 * v3) + psi (mul B1 B1) * (v4 * v4)
        + ta_X * (v1 * v2) + ta_Y * (v3 * v4)
        + 2 * ta_E00 * (v1 * v3) + 2 * ta_E01 * (v1 * v4)
        + 2 * ta_E10 * (v2 * v3) + 2 * ta_E11 * (v2 * v4)).
Proof.
  intros. set (W := add (scal v0 one) (ta_Z v1 v2 v3 v4)).
  assert (Hs : star W = W) by (unfold W; rewrite star_add, star_scal, star_one, ta_Z_sa; reflexivity).
  pose proof (psi_pos W) as P. rewrite Hs in P.
  assert (E : psi (mul W W) = v0 * v0 + 2 * v0 * (psi A0 * v1 + psi A1 * v2 + psi B0 * v3 + psi B1 * v4)
                              + psi (mul (ta_Z v1 v2 v3 v4) (ta_Z v1 v2 v3 v4))).
  { unfold W, ta_Z.
    rewrite !mul_add_l, !mul_add_r, !mul_scal_l, !mul_scal_r, !mul_one_l, !mul_one_r, !psi_add, !psi_scal, psi_one.
    ring. }
  rewrite E, ta_quad_expand in P. lra.
Qed.

(** In any dimension, the level-1 moment matrix, with the true marginals,
    is PSD: the NPA test is necessary for quantum behaviour. *)
Theorem ta_npa_psd : npa_psd ta_npa.
Proof.
  split.
  - apply npa_to_matrix_symmetric.
  - intro v. rewrite ta_npa_quad. cbv zeta.
    set (v0 := v Fin.F1). set (v1 := v (Fin.FS Fin.F1)). set (v2 := v (Fin.FS (Fin.FS Fin.F1))).
    set (v3 := v (Fin.FS (Fin.FS (Fin.FS Fin.F1)))). set (v4 := v (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))).
    pose proof (ta_W_nonneg v0 v1 v2 v3 v4) as Q.
    assert (S1 : 0 <= (1 - psi (mul A0 A0)) * (v1 * v1)) by (apply Rmult_le_pos; nra).
    assert (S2 : 0 <= (1 - psi (mul A1 A1)) * (v2 * v2)) by (apply Rmult_le_pos; nra).
    assert (S3 : 0 <= (1 - psi (mul B0 B0)) * (v3 * v3)) by (apply Rmult_le_pos; nra).
    assert (S4 : 0 <= (1 - psi (mul B1 B1)) * (v4 * v4)) by (apply Rmult_le_pos; nra).
    apply Rle_ge.
    assert (E : v0 * v0 + v1 * v1 + v2 * v2 + v3 * v3 + v4 * v4
                + 2 * v0 * (psi A0 * v1 + psi A1 * v2 + psi B0 * v3 + psi B1 * v4)
                + 2 * (ta_X / 2) * (v1 * v2) + 2 * (ta_Y / 2) * (v3 * v4)
                + 2 * ta_E00 * (v1 * v3) + 2 * ta_E01 * (v1 * v4)
                + 2 * ta_E10 * (v2 * v3) + 2 * ta_E11 * (v2 * v4)
              = (v0 * v0 + 2 * v0 * (psi A0 * v1 + psi A1 * v2 + psi B0 * v3 + psi B1 * v4)
                 + (psi (mul A0 A0) * (v1 * v1) + psi (mul A1 A1) * (v2 * v2)
                    + psi (mul B0 B0) * (v3 * v3) + psi (mul B1 B1) * (v4 * v4)
                    + ta_X * (v1 * v2) + ta_Y * (v3 * v4)
                    + 2 * ta_E00 * (v1 * v3) + 2 * ta_E01 * (v1 * v4)
                    + 2 * ta_E10 * (v2 * v3) + 2 * ta_E11 * (v2 * v4)))
                + (1 - psi (mul A0 A0)) * (v1 * v1) + (1 - psi (mul A1 A1)) * (v2 * v2)
                + (1 - psi (mul B0 B0)) * (v3 * v3) + (1 - psi (mul B1 B1)) * (v4 * v4))
      by field.
    rewrite E. lra.
Qed.

End Algebraic.

(** ** The hypotheses are met *)

(** The real numbers, with a classical plan of +-1 answers, satisfy every
    hypothesis of the section. *)
Theorem ta_classical_instance : forall a0 a1 b0 b1 : R,
  a0 * a0 = 1 -> a1 * a1 = 1 -> b0 * b0 = 1 -> b1 * b1 = 1 ->
  Rabs (a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1) <= 2 * sqrt 2.
Proof.
  intros a0 a1 b0 b1 H0 H1 H2 H3.
  refine (ta_tsirelson R Rplus Rmult Rmult (fun x => x) (fun x => x)
            _ _ _ _ _ _ _ _ _ a0 a1 b0 b1 _ _ _ _ _ _ _ _ _ _ _ _);
    intros; try reflexivity; try ring; try nra; lra.
Qed.

Print Assumptions ta_quad_nonneg.
Print Assumptions ta_tsirelson.
Print Assumptions ta_realizable.
Print Assumptions ta_arcsine.
Print Assumptions ta_npa_psd.
Print Assumptions ta_classical_instance.
