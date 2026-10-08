(** SmallChshCheck.v: the integer CHSH check on eight counters, with no
    machine in it.

    A tally is eight counts: for each question pair xy, the rounds whose
    answers matched (same) and the rounds whose answers differed (diff).
    With N = same + diff and D = same - diff for each pair, the check
    small_chsh_check tests seven integer facts, the same seven that
    column_contractive_check_witness of CHSHColumnCheck.v tests on its
    witness counters:

      N00 > 0, N01 > 0, N10 > 0, N11 > 0,
      A := N00^2 N10^2 - D00^2 N10^2 - D10^2 N00^2 >= 0,
      B := N01^2 N11^2 - D01^2 N11^2 - D11^2 N01^2 >= 0,
      C^2 <= A B,  where C := D00 D01 N10 N11 + D10 D11 N00 N01.

    The meaning of a pass, small_chsh_meaning, is stated over the reals
    with no integers in it: every pair was sampled, and the five-by-five
    moment matrix on I, A0, A1, B0, B1 with ones on the diagonal, the
    correlator E_xy = D_xy / N_xy in the cells (A_x, B_y) and (B_y, A_x),
    and zeros everywhere else is symmetric and positive semidefinite.

    Headline results.
      small_chsh_check_iff: the check passes exactly when the meaning holds.
        Both directions are proved; the check is sound and complete for
        this pinned matrix.
      small_chsh_meaning_tsirelson: the meaning forces S^2 <= 8 and
        |S| <= 2 sqrt 2, for S = E00 + E01 + E10 - E11.
      small_chsh_check_tsirelson: the two together.

    The pinned matrix is stricter than the quantum question: a quantum
    point can fail it, and every deterministic plan does. Passing is a
    sufficient condition for the bound, not a test for quantum behaviour.

    Dependencies: the Coq standard library (Reals, ZArith, micromega) and
    three machine-free files of coq/kernel/quantum: ConstructivePSD.v,
    NPAMomentMatrix.v and TsirelsonFromAlgebra.v. The four matrix lemmas
    (the quadratic form of a two-by-two block, contraction gives PSD, PSD
    gives contraction, row bounds from PSD) are stated here under
    small_chsh_ names, so this file needs no machine and no other quantum
    file.                                                        *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is the integer CHSH check and its meaning over the real numbers (it
   imports the machine-free quantum files only). Its link to the abstract
   record (the machine of SmallChshMachine.v as a CertificationSystem, with
   the floor of 3 for a certified run) lives in SmallChshLinks.v. *)

From Coq Require Import Reals Lra Psatz Lia ZArith Bool.
Require Coq.Vectors.Fin.
From Kernel Require Import ConstructivePSD NPAMomentMatrix TsirelsonFromAlgebra.

Local Open Scope R_scope.

(* ================================================================= *)
(* The tally and the integer check.                                  *)
(* ================================================================= *)

Record small_chsh_tally : Type := small_chsh_mk {
  small_chsh_same00 : nat; small_chsh_diff00 : nat;
  small_chsh_same01 : nat; small_chsh_diff01 : nat;
  small_chsh_same10 : nat; small_chsh_diff10 : nat;
  small_chsh_same11 : nat; small_chsh_diff11 : nat
}.

(* D = same - diff and N = same + diff, as integers. *)
Definition small_chsh_d (same diff : nat) : Z := (Z.of_nat same - Z.of_nat diff)%Z.
Definition small_chsh_n (same diff : nat) : Z := (Z.of_nat same + Z.of_nat diff)%Z.

(* The seven integer facts, written exactly as
   column_contractive_check_witness of CHSHColumnCheck.v writes them for
   its witness counters. *)
Definition small_chsh_check (t : small_chsh_tally) : bool :=
  let d00 := small_chsh_d t.(small_chsh_same00) t.(small_chsh_diff00) in
  let n00 := small_chsh_n t.(small_chsh_same00) t.(small_chsh_diff00) in
  let d01 := small_chsh_d t.(small_chsh_same01) t.(small_chsh_diff01) in
  let n01 := small_chsh_n t.(small_chsh_same01) t.(small_chsh_diff01) in
  let d10 := small_chsh_d t.(small_chsh_same10) t.(small_chsh_diff10) in
  let n10 := small_chsh_n t.(small_chsh_same10) t.(small_chsh_diff10) in
  let d11 := small_chsh_d t.(small_chsh_same11) t.(small_chsh_diff11) in
  let n11 := small_chsh_n t.(small_chsh_same11) t.(small_chsh_diff11) in
  let n00sq := (n00 * n00)%Z in
  let n01sq := (n01 * n01)%Z in
  let n10sq := (n10 * n10)%Z in
  let n11sq := (n11 * n11)%Z in
  let d00sq := (d00 * d00)%Z in
  let d01sq := (d01 * d01)%Z in
  let d10sq := (d10 * d10)%Z in
  let d11sq := (d11 * d11)%Z in
  let A := (n00sq * n10sq - d00sq * n10sq - d10sq * n00sq)%Z in
  let B := (n01sq * n11sq - d01sq * n11sq - d11sq * n01sq)%Z in
  let C := (d00 * d01 * n10 * n11 + d10 * d11 * n00 * n01)%Z in
  andb (Z.ltb 0 n00)
  (andb (Z.ltb 0 n01)
  (andb (Z.ltb 0 n10)
  (andb (Z.ltb 0 n11)
  (andb (Z.leb 0 A)
  (andb (Z.leb 0 B)
        (Z.leb (C * C) (A * B))))))).

(* ================================================================= *)
(* The meaning, over the reals.                                      *)
(* ================================================================= *)

(* The correlator of one pair: (same - diff) / (same + diff), read as 0
   when the pair has no rounds. *)
Definition small_chsh_corr (same diff : nat) : R :=
  if Nat.eqb (same + diff) 0 then 0
  else (INR same - INR diff) / INR (same + diff).

Definition small_chsh_e00 (t : small_chsh_tally) : R :=
  small_chsh_corr t.(small_chsh_same00) t.(small_chsh_diff00).
Definition small_chsh_e01 (t : small_chsh_tally) : R :=
  small_chsh_corr t.(small_chsh_same01) t.(small_chsh_diff01).
Definition small_chsh_e10 (t : small_chsh_tally) : R :=
  small_chsh_corr t.(small_chsh_same10) t.(small_chsh_diff10).
Definition small_chsh_e11 (t : small_chsh_tally) : R :=
  small_chsh_corr t.(small_chsh_same11) t.(small_chsh_diff11).

(* The CHSH score of the tally. *)
Definition small_chsh_score (t : small_chsh_tally) : R :=
  CHSH_value (small_chsh_e00 t) (small_chsh_e01 t) (small_chsh_e10 t) (small_chsh_e11 t).

(* Every question pair has at least one round. *)
Definition small_chsh_sampled (t : small_chsh_tally) : Prop :=
  (0 < t.(small_chsh_same00) + t.(small_chsh_diff00))%nat /\
  (0 < t.(small_chsh_same01) + t.(small_chsh_diff01))%nat /\
  (0 < t.(small_chsh_same10) + t.(small_chsh_diff10))%nat /\
  (0 < t.(small_chsh_same11) + t.(small_chsh_diff11))%nat.

(* The pinned five-by-five built from the tally's correlators is
   symmetric and positive semidefinite (npa_psd, NPAMomentMatrix.v). *)
Definition small_chsh_psd (t : small_chsh_tally) : Prop :=
  npa_psd (zero_marginal_npa (small_chsh_e00 t) (small_chsh_e01 t)
                             (small_chsh_e10 t) (small_chsh_e11 t)).

Definition small_chsh_meaning (t : small_chsh_tally) : Prop :=
  small_chsh_sampled t /\ small_chsh_psd t.

(* ================================================================= *)
(* PSD of the pinned matrix is the same as three contraction facts.  *)
(* ================================================================= *)

(* The correlator grid shrinks every vector: two column conditions and
   one determinant condition. *)
Definition small_chsh_contractive (e00 e01 e10 e11 : R) : Prop :=
  1 - e00 * e00 - e10 * e10 >= 0 /\
  1 - e01 * e01 - e11 * e11 >= 0 /\
  (1 - e00 * e00 - e10 * e10) *
    (1 - e01 * e01 - e11 * e11) -
    (e00 * e01 + e10 * e11) * (e00 * e01 + e10 * e11) >= 0.

(* A two-by-two symmetric table with nonnegative diagonal and nonnegative
   determinant gives a nonnegative quadratic form. *)
Lemma small_chsh_psd2_form_nonneg :
  forall a b d u v,
    a >= 0 ->
    d >= 0 ->
    a * d - b * b >= 0 ->
    a * u * u + 2 * b * u * v + d * v * v >= 0.
Proof.
  intros a b d u v Ha Hd Hdet.
  destruct (Req_dec v 0) as [Hv0 | Hv0].
  - subst v. nra.
  - set (t := u / v).
    assert (Hu : u = t * v).
    { unfold t. field. lra. }
    rewrite Hu.
    replace (a * (t * v) * (t * v) + 2 * b * (t * v) * v + d * v * v)
      with ((v * v) * (a * t * t + 2 * b * t + d)) by ring.
    assert (Hv2 : v * v >= 0) by nra.
    assert (Hq : a * t * t + 2 * b * t + d >= 0).
    {
      destruct (Req_dec a 0) as [Ha0 | Ha0].
      * subst a.
        assert (Hb0 : b = 0) by nra.
        subst b.
        nra.
      * assert (Ha_pos : a > 0) by lra.
        replace (a * t * t + 2 * b * t + d) with
          (a * (t + b / a) * (t + b / a) + (a * d - b * b) / a)
          by (field; lra).
        assert (Hsqr : 0 <= (t + b / a) * (t + b / a)) by apply Rle_0_sqr.
        assert (Hs1 : a * (t + b / a) * (t + b / a) >= 0) by nra.
        assert (Hs2 : (a * d - b * b) / a >= 0).
        {
          unfold Rdiv.
          assert (Hainv : / a >= 0) by (left; apply Rinv_0_lt_compat; lra).
          nra.
        }
        nra.
    }
    nra.
Qed.

(* Contraction gives PSD: the quadratic form of the pinned matrix is a
   sum of three squares plus the two-by-two form above. *)
Lemma small_chsh_contractive_implies_psd5 :
  forall e00 e01 e10 e11,
    small_chsh_contractive e00 e01 e10 e11 ->
    PSD5 (nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11))).
Proof.
  intros e00 e01 e10 e11 [Hc0 [Hc1 Hdet]] v.
  unfold PSD5, quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, zero_marginal_npa.
  simpl.
  set (v0 := v Fin.F1).
  set (x0 := v (Fin.FS Fin.F1)).
  set (x1 := v (Fin.FS (Fin.FS Fin.F1))).
  set (y0 := v (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
  set (y1 := v (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))).
  assert (Hblock :
    (1 - e00 * e00 - e10 * e10) * y0 * y0 +
    2 * (-(e00 * e01 + e10 * e11)) * y0 * y1 +
    (1 - e01 * e01 - e11 * e11) * y1 * y1 >= 0).
  {
    apply (small_chsh_psd2_form_nonneg
      (1 - e00 * e00 - e10 * e10)
      (-(e00 * e01 + e10 * e11))
      (1 - e01 * e01 - e11 * e11)
      y0 y1).
    - exact Hc0.
    - exact Hc1.
    - replace
        ((1 - e00 * e00 - e10 * e10) * (1 - e01 * e01 - e11 * e11) -
         (-(e00 * e01 + e10 * e11)) * (-(e00 * e01 + e10 * e11)))
        with
        ((1 - e00 * e00 - e10 * e10) * (1 - e01 * e01 - e11 * e11) -
         (e00 * e01 + e10 * e11) * (e00 * e01 + e10 * e11)) by ring.
      exact Hdet.
  }
  replace
    (v0 * (v0 * 1 + x0 * 0 + x1 * 0 + y0 * 0 + y1 * 0) +
     x0 * (v0 * 0 + x0 * 1 + x1 * 0 + y0 * e00 + y1 * e01) +
     x1 * (v0 * 0 + x0 * 0 + x1 * 1 + y0 * e10 + y1 * e11) +
     y0 * (v0 * 0 + x0 * e00 + x1 * e10 + y0 * 1 + y1 * 0) +
     y1 * (v0 * 0 + x0 * e01 + x1 * e11 + y0 * 0 + y1 * 1))
    with
    (v0 * v0 +
     (x0 + e00 * y0 + e01 * y1) * (x0 + e00 * y0 + e01 * y1) +
     (x1 + e10 * y0 + e11 * y1) * (x1 + e10 * y0 + e11 * y1) +
     (1 - e00 * e00 - e10 * e10) * y0 * y0 +
     2 * (-(e00 * e01 + e10 * e11)) * y0 * y1 +
     (1 - e01 * e01 - e11 * e11) * y1 * y1)
    by ring.
  assert (Hv0_nonneg : 0 <= v0 * v0) by apply Rle_0_sqr.
  assert (Hx0_nonneg : 0 <= (x0 + e00 * y0 + e01 * y1) * (x0 + e00 * y0 + e01 * y1))
    by apply Rle_0_sqr.
  assert (Hx1_nonneg : 0 <= (x1 + e10 * y0 + e11 * y1) * (x1 + e10 * y0 + e11 * y1))
    by apply Rle_0_sqr.
  nra.
Qed.

(* Three test vectors read the contraction facts back out of PSD. *)
Lemma small_chsh_quad_col0 :
  forall e00 e01 e10 e11 : R,
  let M := nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)) in
  let v : Vec5 := fun i =>
    match proj1_sig (Fin.to_nat i) with
    | 1%nat => -e00
    | 2%nat => -e10
    | 3%nat => 1
    | _     => 0
    end in
  quad5 M v = 1 - e00 * e00 - e10 * e10.
Proof.
  intros e00 e01 e10 e11.
  unfold quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, zero_marginal_npa.
  simpl. ring.
Qed.

Lemma small_chsh_quad_col1 :
  forall e00 e01 e10 e11 : R,
  let M := nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)) in
  let v : Vec5 := fun i =>
    match proj1_sig (Fin.to_nat i) with
    | 1%nat => -e01
    | 2%nat => -e11
    | 4%nat => 1
    | _     => 0
    end in
  quad5 M v = 1 - e01 * e01 - e11 * e11.
Proof.
  intros e00 e01 e10 e11.
  unfold quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, zero_marginal_npa.
  simpl. ring.
Qed.

Lemma small_chsh_quad_schur :
  forall e00 e01 e10 e11 t : R,
  let M := nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)) in
  let v : Vec5 := fun i =>
    match proj1_sig (Fin.to_nat i) with
    | 1%nat => -(e00 * t + e01)
    | 2%nat => -(e10 * t + e11)
    | 3%nat => t
    | 4%nat => 1
    | _     => 0
    end in
  quad5 M v =
    (1 - e00*e00 - e10*e10) * t * t
    - 2 * (e00*e01 + e10*e11) * t
    + (1 - e01*e01 - e11*e11).
Proof.
  intros e00 e01 e10 e11 t.
  unfold quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, zero_marginal_npa.
  simpl. ring.
Qed.

(* PSD gives contraction. *)
Theorem small_chsh_psd5_implies_contractive :
  forall e00 e01 e10 e11 : R,
    PSD5 (nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11))) ->
    small_chsh_contractive e00 e01 e10 e11.
Proof.
  intros e00 e01 e10 e11 Hpsd.
  unfold small_chsh_contractive.
  assert (Hc0 : 1 - e00 * e00 - e10 * e10 >= 0).
  {
    pose proof Hpsd (fun i =>
      match proj1_sig (Fin.to_nat i) with
      | 1%nat => -e00
      | 2%nat => -e10
      | 3%nat => 1
      | _     => 0
      end) as Hv1.
    rewrite small_chsh_quad_col0 in Hv1.
    exact Hv1.
  }
  assert (Hc1 : 1 - e01 * e01 - e11 * e11 >= 0).
  {
    pose proof Hpsd (fun i =>
      match proj1_sig (Fin.to_nat i) with
      | 1%nat => -e01
      | 2%nat => -e11
      | 4%nat => 1
      | _     => 0
      end) as Hv2.
    rewrite small_chsh_quad_col1 in Hv2.
    exact Hv2.
  }
  assert (Hdet : (1 - e00 * e00 - e10 * e10) * (1 - e01 * e01 - e11 * e11) -
                 (e00 * e01 + e10 * e11) * (e00 * e01 + e10 * e11) >= 0).
  {
    assert (Hquad : forall t : R,
      (1 - e00*e00 - e10*e10) * t * t
      - 2 * (e00*e01 + e10*e11) * t
      + (1 - e01*e01 - e11*e11) >= 0).
    {
      intro t.
      pose proof Hpsd (fun i =>
        match proj1_sig (Fin.to_nat i) with
        | 1%nat => -(e00 * t + e01)
        | 2%nat => -(e10 * t + e11)
        | 3%nat => t
        | 4%nat => 1
        | _     => 0
        end) as Hvt.
      rewrite small_chsh_quad_schur in Hvt.
      exact Hvt.
    }
    assert (Hform : forall t : R,
      (1 - e01*e01 - e11*e11)
      + 2 * (-(e00*e01 + e10*e11)) * t
      + (1 - e00*e00 - e10*e10) * t * t >= 0).
    { intro t. specialize (Hquad t). lra. }
    apply quadratic_nonneg_discriminant in Hform.
    nra.
  }
  exact (conj Hc0 (conj Hc1 Hdet)).
Qed.

(* The pinned matrix is symmetric and PSD exactly when the correlators
   are a contraction. *)
Theorem small_chsh_psd_iff_contractive :
  forall e00 e01 e10 e11 : R,
    npa_psd (zero_marginal_npa e00 e01 e10 e11) <->
    small_chsh_contractive e00 e01 e10 e11.
Proof.
  intros e00 e01 e10 e11. unfold npa_psd. split.
  - intros [_ Hpsd]. apply small_chsh_psd5_implies_contractive. exact Hpsd.
  - intro Hc. split.
    + apply npa_to_matrix_symmetric.
    + apply small_chsh_contractive_implies_psd5. exact Hc.
Qed.

(* ================================================================= *)
(* Clearing denominators: the integer facts are the contraction facts. *)
(* ================================================================= *)

Lemma small_chsh_scale_nonneg : forall k x, 0 < k -> (0 <= k * x <-> 0 <= x).
Proof.
  intros k x Hk. split; intro H.
  - apply (Rmult_le_reg_l k); [exact Hk | rewrite Rmult_0_r; exact H].
  - apply Rmult_le_pos; lra.
Qed.

Lemma small_chsh_Z_nonneg_iff : forall z : Z, (0 <= z)%Z <-> 0 <= IZR z.
Proof. intro z. split; [apply IZR_le | intro H; apply le_IZR; exact H]. Qed.

(* With positive N's, the three integer inequalities hold exactly when
   the correlators D / N are a contraction. *)
Theorem small_chsh_clear_denominators :
  forall N00 N01 N10 N11 D00 D01 D10 D11 : Z,
    (0 < N00)%Z -> (0 < N01)%Z -> (0 < N10)%Z -> (0 < N11)%Z ->
    let A := (N00 * N00 * (N10 * N10) - D00 * D00 * (N10 * N10)
              - D10 * D10 * (N00 * N00))%Z in
    let B := (N01 * N01 * (N11 * N11) - D01 * D01 * (N11 * N11)
              - D11 * D11 * (N01 * N01))%Z in
    let C := (D00 * D01 * N10 * N11 + D10 * D11 * N00 * N01)%Z in
    ((0 <= A)%Z /\ (0 <= B)%Z /\ (C * C <= A * B)%Z) <->
    small_chsh_contractive (IZR D00 / IZR N00) (IZR D01 / IZR N01)
                           (IZR D10 / IZR N10) (IZR D11 / IZR N11).
Proof.
  intros N00 N01 N10 N11 D00 D01 D10 D11 H00 H01 H10 H11 A B C.
  assert (R00 : 0 < IZR N00) by (apply IZR_lt; exact H00).
  assert (R01 : 0 < IZR N01) by (apply IZR_lt; exact H01).
  assert (R10 : 0 < IZR N10) by (apply IZR_lt; exact H10).
  assert (R11 : 0 < IZR N11) by (apply IZR_lt; exact H11).
  set (e00 := IZR D00 / IZR N00). set (e01 := IZR D01 / IZR N01).
  set (e10 := IZR D10 / IZR N10). set (e11 := IZR D11 / IZR N11).
  set (p := 1 - e00 * e00 - e10 * e10).
  set (q := 1 - e01 * e01 - e11 * e11).
  set (s := e00 * e01 + e10 * e11).
  assert (HA : IZR A = (IZR N00 * IZR N00 * (IZR N10 * IZR N10)) * p).
  { unfold A, p, e00, e10. rewrite !minus_IZR, !mult_IZR. field. lra. }
  assert (HB : IZR B = (IZR N01 * IZR N01 * (IZR N11 * IZR N11)) * q).
  { unfold B, q, e01, e11. rewrite !minus_IZR, !mult_IZR. field. lra. }
  assert (HD : IZR (A * B - C * C) =
     (IZR N00 * IZR N01 * IZR N10 * IZR N11) * (IZR N00 * IZR N01 * IZR N10 * IZR N11)
     * (p * q - s * s)).
  { rewrite minus_IZR, !mult_IZR, HA, HB.
    unfold C. rewrite plus_IZR, !mult_IZR.
    unfold p, q, s, e00, e01, e10, e11. field. lra. }
  assert (KA : 0 < IZR N00 * IZR N00 * (IZR N10 * IZR N10)) by
    (apply Rmult_lt_0_compat; apply Rmult_lt_0_compat; lra).
  assert (KB : 0 < IZR N01 * IZR N01 * (IZR N11 * IZR N11)) by
    (apply Rmult_lt_0_compat; apply Rmult_lt_0_compat; lra).
  assert (KQ : 0 < IZR N00 * IZR N01 * IZR N10 * IZR N11) by
    (repeat apply Rmult_lt_0_compat; lra).
  assert (KD : 0 < (IZR N00 * IZR N01 * IZR N10 * IZR N11) *
                   (IZR N00 * IZR N01 * IZR N10 * IZR N11)) by
    (apply Rmult_lt_0_compat; lra).
  assert (EA : (0 <= A)%Z <-> 0 <= p).
  { rewrite small_chsh_Z_nonneg_iff, HA. apply small_chsh_scale_nonneg. exact KA. }
  assert (EB : (0 <= B)%Z <-> 0 <= q).
  { rewrite small_chsh_Z_nonneg_iff, HB. apply small_chsh_scale_nonneg. exact KB. }
  assert (EC : (C * C <= A * B)%Z <-> 0 <= p * q - s * s).
  { assert (Hz : (C * C <= A * B)%Z <-> (0 <= A * B - C * C)%Z) by lia.
    rewrite Hz, small_chsh_Z_nonneg_iff, HD. apply small_chsh_scale_nonneg. exact KD. }
  unfold small_chsh_contractive. fold e00 e01 e10 e11. fold p q s.
  rewrite EA, EB, EC. split.
  - intros [Hp [Hq Hd]]. split; [lra | split; lra].
  - intros [Hp [Hq Hd]]. split; [lra | split; lra].
Qed.

(* ================================================================= *)
(* The check is exactly its meaning.                                 *)
(* ================================================================= *)

Lemma small_chsh_n_pos_iff : forall same diff,
  (0 < small_chsh_n same diff)%Z <-> (0 < same + diff)%nat.
Proof. intros same diff. unfold small_chsh_n. lia. Qed.

Lemma small_chsh_corr_eq : forall same diff,
  (0 < same + diff)%nat ->
  small_chsh_corr same diff = IZR (small_chsh_d same diff) / IZR (small_chsh_n same diff).
Proof.
  intros same diff H. unfold small_chsh_corr, small_chsh_d, small_chsh_n.
  destruct (Nat.eqb (same + diff) 0) eqn:E; [apply Nat.eqb_eq in E; lia |].
  rewrite minus_IZR, plus_IZR, <- !INR_IZR_INZ, plus_INR. reflexivity.
Qed.

(* The check, with its seven conjuncts taken apart. *)
Lemma small_chsh_check_unfold : forall t,
  small_chsh_check t = true <->
  let d00 := small_chsh_d t.(small_chsh_same00) t.(small_chsh_diff00) in
  let n00 := small_chsh_n t.(small_chsh_same00) t.(small_chsh_diff00) in
  let d01 := small_chsh_d t.(small_chsh_same01) t.(small_chsh_diff01) in
  let n01 := small_chsh_n t.(small_chsh_same01) t.(small_chsh_diff01) in
  let d10 := small_chsh_d t.(small_chsh_same10) t.(small_chsh_diff10) in
  let n10 := small_chsh_n t.(small_chsh_same10) t.(small_chsh_diff10) in
  let d11 := small_chsh_d t.(small_chsh_same11) t.(small_chsh_diff11) in
  let n11 := small_chsh_n t.(small_chsh_same11) t.(small_chsh_diff11) in
  let A := (n00 * n00 * (n10 * n10) - d00 * d00 * (n10 * n10)
            - d10 * d10 * (n00 * n00))%Z in
  let B := (n01 * n01 * (n11 * n11) - d01 * d01 * (n11 * n11)
            - d11 * d11 * (n01 * n01))%Z in
  let C := (d00 * d01 * n10 * n11 + d10 * d11 * n00 * n01)%Z in
  (0 < n00)%Z /\ (0 < n01)%Z /\ (0 < n10)%Z /\ (0 < n11)%Z /\
  ((0 <= A)%Z /\ (0 <= B)%Z /\ (C * C <= A * B)%Z).
Proof.
  intro t. unfold small_chsh_check. cbv zeta.
  rewrite !andb_true_iff, !Z.ltb_lt, !Z.leb_le. tauto.
Qed.

Theorem small_chsh_check_iff : forall t,
  small_chsh_check t = true <-> small_chsh_meaning t.
Proof.
  intro t. rewrite small_chsh_check_unfold. cbv zeta.
  unfold small_chsh_meaning, small_chsh_sampled, small_chsh_psd.
  rewrite <- !small_chsh_n_pos_iff.
  split.
  - intros [H00 [H01 [H10 [H11 Hrest]]]].
    split; [tauto |].
    unfold small_chsh_e00, small_chsh_e01, small_chsh_e10, small_chsh_e11.
    rewrite !small_chsh_corr_eq by (apply small_chsh_n_pos_iff; assumption).
    apply small_chsh_psd_iff_contractive.
    apply (small_chsh_clear_denominators _ _ _ _ _ _ _ _ H00 H01 H10 H11).
    exact Hrest.
  - intros [[H00 [H01 [H10 H11]]] Hpsd].
    do 4 (split; [assumption |]).
    unfold small_chsh_e00, small_chsh_e01, small_chsh_e10, small_chsh_e11 in Hpsd.
    rewrite !small_chsh_corr_eq in Hpsd by (apply small_chsh_n_pos_iff; assumption).
    apply small_chsh_psd_iff_contractive in Hpsd.
    apply (small_chsh_clear_denominators _ _ _ _ _ _ _ _ H00 H01 H10 H11).
    exact Hpsd.
Qed.

(* ================================================================= *)
(* PSD forces the Tsirelson bound.                                   *)
(* ================================================================= *)

(* PSD with a unit diagonal makes the three-by-three minors on rows
   (A0, B0, B1) and (A1, B0, B1) nonnegative, which are the two row
   bounds. *)
(* SAFE: row bounds E00^2 + E01^2 <= 1 and E10^2 + E11^2 <= 1; 2 sqrt 2 follows in small_chsh_check_tsirelson. *)
Theorem small_chsh_psd_row_bounds :
  forall E00 E01 E10 E11 : R,
    npa_psd (zero_marginal_npa E00 E01 E10 E11) ->
    E00 * E00 + E01 * E01 <= 1 /\ E10 * E10 + E11 * E11 <= 1.
Proof.
  intros E00 E01 E10 E11 [Hsym Hpsd].
  set (npa := zero_marginal_npa E00 E01 E10 E11).
  set (M := nat_matrix_to_fin5 (npa_to_matrix npa)).
  split.
  - pose proof (psd_3x3_determinant_nonneg M idx1 idx3 idx4 Hpsd Hsym
      (npa_diagonal_one _ _) (npa_diagonal_one _ _) (npa_diagonal_one _ _)) as Hdet.
    unfold M in Hdet.
    rewrite npa_E00_position in Hdet.
    rewrite npa_E01_position in Hdet.
    rewrite npa_rho_BB_position in Hdet.
    unfold npa in Hdet. simpl in Hdet.
    unfold det3_corr in Hdet.
    lra.
  - pose proof (psd_3x3_determinant_nonneg M idx2 idx3 idx4 Hpsd Hsym
      (npa_diagonal_one _ _) (npa_diagonal_one _ _) (npa_diagonal_one _ _)) as Hdet.
    unfold M in Hdet.
    rewrite npa_E10_position in Hdet.
    rewrite npa_E11_position in Hdet.
    rewrite npa_rho_BB_position in Hdet.
    unfold npa in Hdet. simpl in Hdet.
    unfold det3_corr in Hdet.
    lra.
Qed.

(* S^2 <= 8 and |S| <= 2 sqrt 2 for any correlators whose pinned matrix
   is symmetric and PSD. *)
Theorem small_chsh_psd_tsirelson :
  forall E00 E01 E10 E11 : R,
    npa_psd (zero_marginal_npa E00 E01 E10 E11) ->
    CHSH_value E00 E01 E10 E11 * CHSH_value E00 E01 E10 E11 <= 8 /\
    Rabs (CHSH_value E00 E01 E10 E11) <= 2 * sqrt 2.
Proof.
  intros E00 E01 E10 E11 H.
  destruct (small_chsh_psd_row_bounds _ _ _ _ H) as [Hr1 Hr2].
  pose proof (tsirelson_squared E00 E01 E10 E11 Hr1 Hr2) as Hsq.
  split; [exact Hsq |].
  rewrite <- sqrt8_eq_2sqrt2.
  set (S := CHSH_value E00 E01 E10 E11) in *.
  assert (H8 : 0 <= sqrt 8) by apply sqrt_pos.
  assert (H8sq : sqrt 8 * sqrt 8 = 8) by (apply sqrt_sqrt; lra).
  rewrite <- (Rabs_pos_eq (sqrt 8) H8).
  apply Rsqr_le_abs_0. unfold Rsqr. lra.
Qed.

Theorem small_chsh_meaning_tsirelson : forall t,
  small_chsh_meaning t ->
  small_chsh_score t * small_chsh_score t <= 8 /\
  Rabs (small_chsh_score t) <= 2 * sqrt 2.
Proof.
  intros t [_ Hpsd]. unfold small_chsh_score.
  apply small_chsh_psd_tsirelson. exact Hpsd.
Qed.

(* A passed integer check means the bound. *)
Theorem small_chsh_check_tsirelson : forall t,
  small_chsh_check t = true ->
  small_chsh_score t * small_chsh_score t <= 8 /\
  Rabs (small_chsh_score t) <= 2 * sqrt 2.
Proof.
  intros t H. apply small_chsh_meaning_tsirelson, small_chsh_check_iff, H.
Qed.

Print Assumptions small_chsh_psd_iff_contractive.
Print Assumptions small_chsh_clear_denominators.
Print Assumptions small_chsh_check_iff.
Print Assumptions small_chsh_psd_tsirelson.
Print Assumptions small_chsh_check_tsirelson.
