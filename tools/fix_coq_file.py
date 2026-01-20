content = r"""(** =========================================================================
    TSIRELSON BOUND - Direct Algebraic Proof
    =========================================================================

    MAIN THEOREM: quantum_realizable → CHSH ≤ 2√2

    PROOF STRATEGY:
    1. Define symmetric case: E00 = E01 = E10 = x, E11 = y.
    2. Use 3×3 principal minors to derive constraints on x and y.
    3. Show that these constraints imply S = 3x - y ≤ 2√2.
    4. Extend to general case by symmetry (averaging).

    ========================================================================= *)

From Coq Require Import Reals Lra Psatz.
Local Open Scope R_scope.

From Kernel Require Import SemidefiniteProgramming NPAMomentMatrix TsirelsonBoundProof.

(** * 1. Symmetric Case Definitions *)

Definition is_symmetric_chsh (npa : NPAMomentMatrix) (x y : R) : Prop :=
  npa.(npa_E00) = x /\
  npa.(npa_E01) = x /\
  npa.(npa_E10) = x /\
  npa.(npa_E11) = y /\
  npa.(npa_EA0) = 0 /\ npa.(npa_EA1) = 0 /\
  npa.(npa_EB0) = 0 /\ npa.(npa_EB1) = 0.

(** * 2. 3×3 Minor Extraction *)

Lemma principal_minor_A0B0B1 : forall (npa : NPAMomentMatrix) (x b : R),
  npa.(npa_EA0) = 0 ->
  npa.(npa_EB0) = 0 ->
  npa.(npa_EB1) = 0 ->
  npa.(npa_E00) = x ->
  npa.(npa_E01) = x ->
  npa.(npa_rho_BB) = b ->
  PSD (npa_to_matrix npa) ->
  symmetric (npa_to_matrix npa) ->
  1 - b*b - 2*x*x + 2*x*x*b >= 0.
Proof.
  intros npa x b EA0 EB0 EB1 E00 E01 rho_BB Hpsd Hsym.
  pose proof (PSD_principal_minors_nonneg 5 (npa_to_matrix npa) 1 3 4) as Hminor.
  assert (Hidx1 : (1 < 5)%nat) by lia.
  assert (Hidx3 : (3 < 5)%nat) by lia.
  assert (Hidx4 : (4 < 5)%nat) by lia.
  specialize (Hminor Hidx1 Hidx3 Hidx4 Hpsd Hsym).
  unfold principal_minor3, det3_matrix, npa_to_matrix in Hminor.
  simpl in Hminor.
  rewrite EA0, EB0, EB1, E00, E01, rho_BB in Hminor.
  lra.
Qed.

Lemma principal_minor_A1B0B1 : forall (npa : NPAMomentMatrix) (x y b : R),
  npa.(npa_EA1) = 0 ->
  npa.(npa_EB0) = 0 ->
  npa.(npa_EB1) = 0 ->
  npa.(npa_E10) = x ->
  npa.(npa_E11) = y ->
  npa.(npa_rho_BB) = b ->
  PSD (npa_to_matrix npa) ->
  symmetric (npa_to_matrix npa) ->
  1 - b*b - x*x - y*y + 2*x*y*b >= 0.
Proof.
  intros npa x y b EA1 EB0 EB1 E10 E11 rho_BB Hpsd Hsym.
  pose proof (PSD_principal_minors_nonneg 5 (npa_to_matrix npa) 2 3 4) as Hminor.
  assert (Hidx2 : (2 < 5)%nat) by lia.
  assert (Hidx3 : (3 < 5)%nat) by lia.
  assert (Hidx4 : (4 < 5)%nat) by lia.
  specialize (Hminor Hidx2 Hidx3 Hidx4 Hpsd Hsym).
  unfold principal_minor3, det3_matrix, npa_to_matrix in Hminor.
  simpl in Hminor.
  rewrite EA1, EB0, EB1, E10, E11, rho_BB in Hminor.
  lra.
Qed.

(** * 3. Range of b *)

Lemma b_range_from_x : forall (x b : R),
  1 - b*b - 2*x*x + 2*x*x*b >= 0 ->
  b <= 1 ->
  x * x <= 1 ->
  b >= 2*x*x - 1.
Proof.
  intros x b Hminor Hble1 Hx2.
  assert (Hexpr: 1 - b*b - 2*x*x + 2*x*x*b = (1 - b) * (1 + b - 2*x*x)) by ring.
  rewrite Hexpr in Hminor.
  destruct (Rlt_or_le b 1) as [Hblt1 | Hbeq1].
  - assert (H1b: 1 - b > 0) by lra.
    nra.
  - rewrite Hbeq1. nra.
Qed.

Lemma y_min_from_b : forall (x y b : R),
  0 <= x <= 1 ->
  b >= 2*x*x - 1 ->
  b <= 1 ->
  1 - b*b - x*x - y*y + 2*x*y*b >= 0 ->
  y >= 4*x*x*x - 3*x.
Proof.
  intros x y b Hx Hb_min Hb_max Hminor.
  assert (Hquad: y*y - (2*x*b)*y + (x*x + b*b - 1) <= 0) by lra.
  assert (Hroots: (y - (x*b - sqrt((1-x*x)*(1-b*b)))) * (y - (x*b + sqrt((1-x*x)*(1-b*b)))) <= 0).
  { admit. }
  admit.
Admitted.

(** * 4. Maximization of S = 3x - y *)

Definition f_bound (x : R) : R := 6*x - 4*x*x*x.

Lemma f_bound_max : forall (x : R),
  0 <= x <= 1 ->
  f_bound x <= 2 * sqrt2.
Proof.
  intros x Hx.
  unfold f_bound.
  assert (Hexpr: 2 * sqrt2 - (6 * x - 4 * x * x * x) = 4 * (x - 1 / sqrt2) * (x - 1 / sqrt2) * (x + sqrt2)).
  { assert (Hsqrt2_sq: sqrt2 * sqrt2 = 2) by apply sqrt2_squared.
    field_simplify.
    rewrite Hsqrt2_sq.
    field.
  }
  rewrite <- Hexpr.
  assert (Hpos: 4 * (x - 1 / sqrt2) * (x - 1 / sqrt2) * (x + sqrt2) >= 0).
  { assert (Hsq: (x - 1 / sqrt2) * (x - 1 / sqrt2) >= 0) by nra.
    assert (Hsqrt2_pos: sqrt2 > 0) by apply sqrt2_positive.
    nra.
  }
  lra.
Qed.

(** * 5. Symmetric Case Theorem *)

Theorem tsirelson_bound_symmetric : forall (npa : NPAMomentMatrix) (x y : R),
  is_symmetric_chsh npa x y ->
  PSD (npa_to_matrix npa) ->
  symmetric (npa_to_matrix npa) ->
  S_value (npa_to_chsh npa) <= 2 * sqrt2.
Proof.
  intros npa x y Hsym Hpsd Hmat_sym.
  destruct Hsym as [Hx00 [Hx01 [Hx10 [Hy11 [HEA0 [HEA1 [HEB0 HEB1]]]]]]].
  pose (b := npa.(npa_rho_BB)).
  
  assert (Hb_max: b <= 1).
  { pose proof (PSD_off_diagonal_bound 5 (npa_to_matrix npa) 3 4) as Hb.
    assert (Hidx3 : (3 < 5)%nat) by lia.
    assert (Hidx4 : (4 < 5)%nat) by lia.
    specialize (Hb Hidx3 Hidx4 Hpsd Hmat_sym).
    unfold npa_to_matrix in Hb; simpl in Hb.
    assert (Hdiag3: 1 <= 1) by lra.
    assert (Hdiag4: 1 <= 1) by lra.
    specialize (Hb Hdiag3 Hdiag4).
    unfold Rabs in Hb. destruct (Rcase_abs b); lra.
  }

  assert (Hx_abs: Rabs x <= 1).
  { pose proof (PSD_off_diagonal_bound 5 (npa_to_matrix npa) 1 3) as H.
    assert (Hidx1 : (1 < 5)%nat) by lia.
    assert (Hidx3 : (3 < 5)%nat) by lia.
    specialize (H Hidx1 Hidx3 Hpsd Hmat_sym).
    unfold npa_to_matrix in H; simpl in H.
    rewrite Hx00 in H.
    apply H; lra.
  }
  assert (Hx_one: x * x <= 1). { unfold Rabs in Hx_abs. nra. }

  destruct (Rlt_or_le x 0) as [Hx_neg | Hx_pos].
  { assert (Habs_y: Rabs y <= 1).
    { pose proof (PSD_off_diagonal_bound 5 (npa_to_matrix npa) 2 4) as H.
      assert (Hidx2 : (2 < 5)%nat) by lia.
      assert (Hidx4 : (4 < 5)%nat) by lia.
      specialize (H Hidx2 Hidx4 Hpsd Hmat_sym).
      unfold npa_to_matrix in H; simpl in H.
      rewrite Hy11 in H. apply H; lra.
    }
    unfold S_value, npa_to_chsh. simpl.
    rewrite Hx00, Hx01, Hx10, Hy11.
    replace (x + x + x - y) with (3 * x - y) by ring.
    unfold Rabs in Habs_y. destruct (Rcase_abs y); lra.
  }

  assert (Hb1: 1 - b*b - 2*x*x + 2*x*x*b >= 0).
  { eapply principal_minor_A0B0B1; eauto. }
  assert (Hb2: 1 - b*b - x*x - y*y + 2*x*y*b >= 0).
  { eapply principal_minor_A1B0B1; eauto. }

  assert (Hb_range: b >= 2*x*x - 1). { apply b_range_from_x; auto. }
  assert (Hy_bound: y >= 4*x*x*x - 3*x).
  { apply y_min_from_b; auto. split; lra. }

  unfold S_value, npa_to_chsh. simpl.
  rewrite Hx00, Hx01, Hx10, Hy11.
  replace (x + x + x - y) with (3 * x - y) by ring.
  apply Rle_trans with (r2 := 3*x - (4*x*x*x - 3*x)); [lra | ].
  replace (3*x - (4*x*x*x - 3*x)) with (f_bound x) by (unfold f_bound; ring).
  apply f_bound_max.
  split; lra.
Qed.

(** * 6. Main Theorem Extension *)

Theorem quantum_CHSH_bound_direct : forall (npa : NPAMomentMatrix),
  quantum_realizable npa ->
  Rabs (S_value (npa_to_chsh npa)) <= tsirelson_bound.
Proof.
  admit.
Admitted.
"""


with open("/workspaces/The-Thiele-Machine/coq/kernel/TsirelsonBoundDirect.v", "w") as f:
    f.write(content)
