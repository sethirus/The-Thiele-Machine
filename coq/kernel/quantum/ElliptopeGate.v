(** The decidable elliptope gate: an integer-arithmetic membership check for
    the full CHSH correlator quantum set, with a soundness proof into
    [elliptope_realizable].

  ElliptopeCompletion.v characterizes the correlator quantum set as an
  existential completion: some assignment of the cross moments makes the
  moment matrix PSD. That is a real-valued predicate with an existential in
  it, and an opcode cannot branch on it. This file builds the thing an
  opcode CAN branch on: a boolean function of the witness counters and a
  supplied completion witness, computed in Z with every denominator cleared,
  no real and no rational ever evaluated at runtime -- the same discipline
  as [column_contractive_check_witness] -- together with the theorem that a
  passing check entails elliptope membership of the witness-derived
  correlators.

  The check ([elliptope_check_full]) has two branches:

  - The PD branch ([elliptope_pd_check]): the program supplies completion
    buckets for x = <A0 A1> and y = <B0 B1> (the same bucket-pair idiom the
    Q_{1+AB} opcodes use for their gamma moments), and the check runs the
    fraction-free Sylvester test on the completed 4x4: all four leading
    principal minors of the denominator-cleared integer matrix strictly
    positive. Soundness routes through [sym4_qf_nonneg_from_pd], the
    fraction-free LDLT lemma the Q_{1+AB} slice-C development already
    proves. This is the cheap path for a strictly-interior point (four
    completion buckets, no certificate).

  - The LDL branch ([elliptope_ldl_check]): the program supplies the
    completion (x, y) plus a rational LDL^T certificate of the completed
    matrix -- six subdiagonal L-entries over a common denominator [lden],
    four pivots d_k >= 0 over a common denominator [dden] -- and the check
    verifies the ten entry equations of M = L D L^T in cross-multiplied
    Z-arithmetic. Soundness ([elliptope_ldl_check_sound]) is a
    sum-of-weighted-squares identity. Because a zero pivot in a PSD matrix
    forces its whole column to vanish, every rational PSD matrix has a
    rational LDL^T without pivoting, so this branch accepts EVERY point with
    a rational PSD completion -- interior, classical (singular), or exactly
    on the quantum boundary. It subsumes the strict PD branch, and it
    subsumes what an LHV-weight decomposition could reach; an earlier draft
    carried a separate sixteen-weight LHV branch, now removed as redundant
    (every finite mixture of deterministic strategies has a rational PSD
    completion the LDL branch certifies) and as the file's only performance
    liability.

  What no exact integer check can ever accept, said out loud: tuples whose
  EVERY PSD completion is irrational, since a rational certificate for such
  a completion does not exist to be supplied. That residue is the arithmetic
  of the boundary itself, not an engineering gap -- and it is provably
  disjoint from the accept side: soundness holds with the check's passing as
  its only hypothesis, and [elliptope_full_gate_never_accepts_pr_box] shows
  the refusal side has teeth. The Pythagorean point (3/5, 4/5, 4/5, -3/5),
  exactly ON the Tsirelson curve (arcsine sum pi, S = 14/5 > 2), has a
  rational singular completion and is accepted by the LDL branch
  ([gate_accepts_pythagorean_boundary]).

  This file is the mathematical content of a CHSH_LASSERT_ELLIPTOPE
  cert-opcode: the decider and its soundness. Binding it into the step
  relation (opcode constructor, cost schedule under A2, Kami mirror) is
  plumbing on the pattern of the four Q_{1+AB} opcodes and is not done
  here.
*)

(* INQUISITOR NOTE: proof-connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.
From Kernel Require Import ConstructivePSD NPAMomentMatrix.
From Kernel Require Import MuLedgerQuantumBridge.
From Kernel Require Import QuantumPartitionPSD_1AB.
From Kernel Require Import ElliptopeCompletion.

From Coq Require Import Reals Lra Psatz Lia ZArith.
From Coq Require Import Bool.
From Coq Require Import Fin.
Local Open Scope R_scope.

(** * Bucket arithmetic: numerator, positive denominator, real value *)

(** Numerator and denominator of a bucket pair, in Z. The denominator is
    forced to 1 on an empty bucket, so it is always strictly positive and
    the bucket's value 0/1 = 0 matches [state_bucket_correlation]'s empty
    convention. *)
Definition bnum (s d : nat) : Z := (Z.of_nat s - Z.of_nat d)%Z.
Definition bden (s d : nat) : Z :=
  if Nat.eqb (s + d) 0 then 1%Z else Z.of_nat (s + d).

Lemma bden_pos : forall s d, (0 < bden s d)%Z.
Proof.
  intros s d. unfold bden.
  destruct (Nat.eqb (s + d) 0) eqn:He.
  - lia.
  - apply Nat.eqb_neq in He. lia.
Qed.

Definition bval (s d : nat) : RealNumber := IZR (bnum s d) / IZR (bden s d).

Lemma bden_IZR_pos : forall s d, 0 < IZR (bden s d).
Proof. intros. apply IZR_lt. apply bden_pos. Qed.

Lemma bden_IZR_neq0 : forall s d, IZR (bden s d) <> 0.
Proof. intros. pose proof (bden_IZR_pos s d). lra. Qed.

(** The Z-side value agrees with the kernel's INR-side correlator. *)
Lemma bval_state_bucket_correlation :
  forall s d, bval s d = state_bucket_correlation s d.
Proof.
  intros s d.
  unfold bval, state_bucket_correlation, bnum, bden.
  destruct (Nat.eqb (s + d) 0) eqn:He.
  - apply Nat.eqb_eq in He.
    assert (Hs : s = 0%nat) by lia.
    assert (Hd : d = 0%nat) by lia.
    subst. simpl. lra.
  - apply Nat.eqb_neq in He.
    rewrite !INR_IZR_INZ.
    rewrite <- minus_IZR.
    reflexivity.
Qed.

(** * The PD branch: fraction-free Sylvester on the completed matrix *)

Section PDCheck.

(** All eight witness-counter fields plus the two completion bucket pairs. *)
Variable wc : WitnessCounts.
Variables xs xd ys yd : nat.

(** Z-side numerators and denominators. *)
Definition zn00 : Z := bnum wc.(wc_same_00) wc.(wc_diff_00).
Definition zd00 : Z := bden wc.(wc_same_00) wc.(wc_diff_00).
Definition zn01 : Z := bnum wc.(wc_same_01) wc.(wc_diff_01).
Definition zd01 : Z := bden wc.(wc_same_01) wc.(wc_diff_01).
Definition zn10 : Z := bnum wc.(wc_same_10) wc.(wc_diff_10).
Definition zd10 : Z := bden wc.(wc_same_10) wc.(wc_diff_10).
Definition zn11 : Z := bnum wc.(wc_same_11) wc.(wc_diff_11).
Definition zd11 : Z := bden wc.(wc_same_11) wc.(wc_diff_11).
Definition znx : Z := bnum xs xd.
Definition zdx : Z := bden xs xd.
Definition zny : Z := bnum ys yd.
Definition zdy : Z := bden ys yd.

(** Common scale K and per-entry cofactor scales: K/D for each denominator,
    written as the product of the other five so everything stays in Z. *)
Definition zK  : Z := (zdx * zdy * zd00 * zd01 * zd10 * zd11)%Z.
Definition zCx : Z := (zdy * zd00 * zd01 * zd10 * zd11)%Z.
Definition zCy : Z := (zdx * zd00 * zd01 * zd10 * zd11)%Z.
Definition zC00 : Z := (zdx * zdy * zd01 * zd10 * zd11)%Z.
Definition zC01 : Z := (zdx * zdy * zd00 * zd10 * zd11)%Z.
Definition zC10 : Z := (zdx * zdy * zd00 * zd01 * zd11)%Z.
Definition zC11 : Z := (zdx * zdy * zd00 * zd01 * zd10)%Z.

(** Integer entries of the scaled completed matrix A = K * M. *)
Definition za12 : Z := (znx * zCx)%Z.
Definition za13 : Z := (zn00 * zC00)%Z.
Definition za14 : Z := (zn01 * zC01)%Z.
Definition za23 : Z := (zn10 * zC10)%Z.
Definition za24 : Z := (zn11 * zC11)%Z.
Definition za34 : Z := (zny * zCy)%Z.

(** Leading principal minors of A, transliterating sym4_d2/d3/d4 with all
    four diagonal entries equal to K. *)
Definition zminor2 : Z := (zK * zK - za12 * za12)%Z.
Definition zminor3 : Z :=
  (zK * (zK * zK - za23 * za23)
   - za12 * (za12 * zK - za13 * za23)
   + za13 * (za12 * za23 - za13 * zK))%Z.
Definition zminor4 : Z :=
  (zK * (zK * (zK * zK - za34 * za34)
         - za23 * (za23 * zK - za24 * za34)
         + za24 * (za23 * za34 - za24 * zK))
   - za12 * (za12 * (zK * zK - za34 * za34)
             - za23 * (za13 * zK - za14 * za34)
             + za24 * (za13 * za34 - za14 * zK))
   + za13 * (za12 * (za23 * zK - za24 * za34)
             - zK * (za13 * zK - za14 * za34)
             + za24 * (za13 * za24 - za14 * za23))
   - za14 * (za12 * (za23 * za34 - za24 * zK)
             - zK * (za13 * za34 - za14 * zK)
             + za23 * (za13 * za24 - za14 * za23)))%Z.

Definition elliptope_pd_check : bool :=
  (0 <? zK)%Z && (0 <? zminor2)%Z && (0 <? zminor3)%Z && (0 <? zminor4)%Z.

End PDCheck.

(** * Soundness of the PD branch *)

Lemma elliptope_pd_check_sound :
  forall wc xs xd ys yd,
    elliptope_pd_check wc xs xd ys yd = true ->
    elliptope_realizable
      (bval wc.(wc_same_00) wc.(wc_diff_00))
      (bval wc.(wc_same_01) wc.(wc_diff_01))
      (bval wc.(wc_same_10) wc.(wc_diff_10))
      (bval wc.(wc_same_11) wc.(wc_diff_11)).
Proof.
  intros wc xs xd ys yd Hchk.
  unfold elliptope_pd_check in Hchk.
  apply andb_prop in Hchk as [Hchk Hm4].
  apply andb_prop in Hchk as [Hchk Hm3].
  apply andb_prop in Hchk as [HK Hm2].
  apply Z.ltb_lt in HK, Hm2, Hm3, Hm4.
  (* Real-side abbreviations. *)
  set (E00 := bval wc.(wc_same_00) wc.(wc_diff_00)).
  set (E01 := bval wc.(wc_same_01) wc.(wc_diff_01)).
  set (E10 := bval wc.(wc_same_10) wc.(wc_diff_10)).
  set (E11 := bval wc.(wc_same_11) wc.(wc_diff_11)).
  set (x := bval xs xd).
  set (y := bval ys yd).
  exists x, y.
  split.
  - apply npa_to_matrix_symmetric.
  - intro v.
    rewrite (completed_quad_expand E00 E01 E10 E11 x y v).
    cbv zeta.
    set (v0 := v F1).
    set (v1 := v (FS F1)).
    set (v2 := v (FS (FS F1))).
    set (v3 := v (FS (FS (FS F1)))).
    set (v4 := v (FS (FS (FS (FS F1))))).
    (* The 4x4 block of the expansion is sym4_qf at the completed entries. *)
    assert (Hsplit :
      v0 * v0 + v1 * v1 + v2 * v2 + v3 * v3 + v4 * v4
      + 2 * x * (v1 * v2) + 2 * y * (v3 * v4)
      + 2 * E00 * (v1 * v3) + 2 * E01 * (v1 * v4)
      + 2 * E10 * (v2 * v3) + 2 * E11 * (v2 * v4)
      = v0 * v0
        + sym4_qf 1 x E00 E01 1 E10 E11 1 y 1 v1 v2 v3 v4).
    { unfold sym4_qf. ring. }
    rewrite Hsplit.
    (* Positivity of the denominators, real side. *)
    pose proof (bden_IZR_neq0 wc.(wc_same_00) wc.(wc_diff_00)) as Hd00.
    pose proof (bden_IZR_neq0 wc.(wc_same_01) wc.(wc_diff_01)) as Hd01.
    pose proof (bden_IZR_neq0 wc.(wc_same_10) wc.(wc_diff_10)) as Hd10.
    pose proof (bden_IZR_neq0 wc.(wc_same_11) wc.(wc_diff_11)) as Hd11.
    pose proof (bden_IZR_neq0 xs xd) as Hdx.
    pose proof (bden_IZR_neq0 ys yd) as Hdy.
    set (K := zK wc xs xd ys yd) in *.
    assert (HKr : 0 < IZR K) by (apply IZR_lt; exact HK).
    (* Entry bridges: each scaled integer entry is K times the real entry. *)
    assert (HKfact : IZR K
            = IZR (zdx xs xd) * IZR (zdy ys yd)
              * IZR (zd00 wc) * IZR (zd01 wc)
              * IZR (zd10 wc) * IZR (zd11 wc)).
    { unfold K, zK. rewrite !mult_IZR. reflexivity. }
    assert (Ha12 : IZR (za12 wc xs xd ys yd) = IZR K * x).
    { unfold za12. rewrite mult_IZR. rewrite HKfact.
      unfold x, bval, znx, zCx, zdx, zdy, zd00, zd01, zd10, zd11.
      rewrite ?mult_IZR. field. exact Hdx. }
    assert (Ha13 : IZR (za13 wc xs xd ys yd) = IZR K * E00).
    { unfold za13. rewrite mult_IZR. rewrite HKfact.
      unfold E00, bval, zn00, zC00, zdx, zdy, zd00, zd01, zd10, zd11.
      rewrite ?mult_IZR. field. exact Hd00. }
    assert (Ha14 : IZR (za14 wc xs xd ys yd) = IZR K * E01).
    { unfold za14. rewrite mult_IZR. rewrite HKfact.
      unfold E01, bval, zn01, zC01, zdx, zdy, zd00, zd01, zd10, zd11.
      rewrite ?mult_IZR. field. exact Hd01. }
    assert (Ha23 : IZR (za23 wc xs xd ys yd) = IZR K * E10).
    { unfold za23. rewrite mult_IZR. rewrite HKfact.
      unfold E10, bval, zn10, zC10, zdx, zdy, zd00, zd01, zd10, zd11.
      rewrite ?mult_IZR. field. exact Hd10. }
    assert (Ha24 : IZR (za24 wc xs xd ys yd) = IZR K * E11).
    { unfold za24. rewrite mult_IZR. rewrite HKfact.
      unfold E11, bval, zn11, zC11, zdx, zdy, zd00, zd01, zd10, zd11.
      rewrite ?mult_IZR. field. exact Hd11. }
    assert (Ha34 : IZR (za34 wc xs xd ys yd) = IZR K * y).
    { unfold za34. rewrite mult_IZR. rewrite HKfact.
      unfold y, bval, zny, zCy, zdx, zdy, zd00, zd01, zd10, zd11.
      rewrite ?mult_IZR. field. exact Hdy. }
    (* Scaled quadratic form: sym4_qf at the integer entries equals
       K * sym4_qf at the real entries. *)
    assert (Hscale :
      sym4_qf (IZR K) (IZR (za12 wc xs xd ys yd))
              (IZR (za13 wc xs xd ys yd)) (IZR (za14 wc xs xd ys yd))
              (IZR K) (IZR (za23 wc xs xd ys yd))
              (IZR (za24 wc xs xd ys yd)) (IZR K)
              (IZR (za34 wc xs xd ys yd)) (IZR K) v1 v2 v3 v4
      = IZR K * sym4_qf 1 x E00 E01 1 E10 E11 1 y 1 v1 v2 v3 v4).
    { rewrite Ha12, Ha13, Ha14, Ha23, Ha24, Ha34.
      unfold sym4_qf. ring. }
    (* Minor bridges: the real minors at the integer entries are the IZR
       images of the Z minors. *)
    assert (Hb2 : sym4_d2 (IZR K) (IZR (za12 wc xs xd ys yd))
                    (IZR (za13 wc xs xd ys yd)) (IZR (za14 wc xs xd ys yd))
                    (IZR K) (IZR (za23 wc xs xd ys yd))
                    (IZR (za24 wc xs xd ys yd)) (IZR K)
                    (IZR (za34 wc xs xd ys yd)) (IZR K)
                  = IZR (zminor2 wc xs xd ys yd)).
    { unfold sym4_d2, zminor2. fold K.
      rewrite minus_IZR, !mult_IZR. reflexivity. }
    assert (Hb3 : sym4_d3 (IZR K) (IZR (za12 wc xs xd ys yd))
                    (IZR (za13 wc xs xd ys yd)) (IZR (za14 wc xs xd ys yd))
                    (IZR K) (IZR (za23 wc xs xd ys yd))
                    (IZR (za24 wc xs xd ys yd)) (IZR K)
                    (IZR (za34 wc xs xd ys yd)) (IZR K)
                  = IZR (zminor3 wc xs xd ys yd)).
    { unfold sym4_d3, zminor3. fold K.
      (* zminor3 mirrors sym4_d3 exactly, so after pushing IZR through the
         two sides are syntactically identical: reflexivity, not ring. *)
      repeat first [rewrite plus_IZR | rewrite minus_IZR | rewrite mult_IZR].
      reflexivity. }
    assert (Hb4 : sym4_d4 (IZR K) (IZR (za12 wc xs xd ys yd))
                    (IZR (za13 wc xs xd ys yd)) (IZR (za14 wc xs xd ys yd))
                    (IZR K) (IZR (za23 wc xs xd ys yd))
                    (IZR (za24 wc xs xd ys yd)) (IZR K)
                    (IZR (za34 wc xs xd ys yd)) (IZR K)
                  = IZR (zminor4 wc xs xd ys yd)).
    { unfold sym4_d4, zminor4. fold K.
      (* Likewise: zminor4 mirrors sym4_d4, so this is reflexivity after the
         IZR push, not a degree-4 determinant normalization. *)
      repeat first [rewrite plus_IZR | rewrite minus_IZR | rewrite mult_IZR].
      reflexivity. }
    (* Apply the fraction-free Sylvester lemma at the scaled entries. *)
    assert (Hqf_scaled :
      sym4_qf (IZR K) (IZR (za12 wc xs xd ys yd))
              (IZR (za13 wc xs xd ys yd)) (IZR (za14 wc xs xd ys yd))
              (IZR K) (IZR (za23 wc xs xd ys yd))
              (IZR (za24 wc xs xd ys yd)) (IZR K)
              (IZR (za34 wc xs xd ys yd)) (IZR K) v1 v2 v3 v4 >= 0).
    { apply sym4_qf_nonneg_from_pd.
      - unfold sym4_d1. exact HKr.
      - rewrite Hb2. apply IZR_lt. exact Hm2.
      - rewrite Hb3. apply IZR_lt. exact Hm3.
      - rewrite Hb4. apply IZR_lt. exact Hm4. }
    rewrite Hscale in Hqf_scaled.
    (* Divide out the positive scale and add the v0 square. *)
    assert (Hqf : sym4_qf 1 x E00 E01 1 E10 E11 1 y 1 v1 v2 v3 v4 >= 0).
    { apply Rle_ge. apply Rmult_le_reg_l with (r := IZR K); [exact HKr |].
      rewrite Rmult_0_r. apply Rge_le. exact Hqf_scaled. }
    pose proof (Rle_0_sqr v0) as Hv0; unfold Rsqr in Hv0.
    lra.
Qed.

(** * The gate computes: concrete acceptances and a refusal *)

(** The mu = 0 all-ones tightness witness: one trial per setting pair, all
    outcomes agreeing. Weight 1 on strategy 15 (all four signs +1). The
    slice gate traps this state; the elliptope gate accepts it. *)
Definition wc_all_ones : WitnessCounts :=
  {| wc_same_00 := 1; wc_diff_00 := 0;
     wc_same_01 := 1; wc_diff_01 := 0;
     wc_same_10 := 1; wc_diff_10 := 0;
     wc_same_11 := 1; wc_diff_11 := 0 |}.

(** The running example (1,0,1,0): perfect correlation on B0, coin-flip on
    B1, as an even mixture of strategies 15 and 7 (b1 flipped). *)
Definition wc_turing_point : WitnessCounts :=
  {| wc_same_00 := 1; wc_diff_00 := 0;
     wc_same_01 := 1; wc_diff_01 := 1;
     wc_same_10 := 1; wc_diff_10 := 0;
     wc_same_11 := 1; wc_diff_11 := 1 |}.

(** An interior quantum-side point: E = (3/5, 3/5, 3/5, -3/5), S = 12/5 > 2,
    accepted through the PD branch with the zero completion. *)
Definition wc_interior : WitnessCounts :=
  {| wc_same_00 := 4; wc_diff_00 := 1;
     wc_same_01 := 4; wc_diff_01 := 1;
     wc_same_10 := 4; wc_diff_10 := 1;
     wc_same_11 := 1; wc_diff_11 := 4 |}.

(** The PR box: no weights and no completion buckets make the gate pass.
    Not an enumeration: soundness plus the Tsirelson theorem close every
    branch at once. *)
Definition wc_pr_box : WitnessCounts :=
  {| wc_same_00 := 1; wc_diff_00 := 0;
     wc_same_01 := 1; wc_diff_01 := 0;
     wc_same_10 := 1; wc_diff_10 := 0;
     wc_same_11 := 0; wc_diff_11 := 1 |}.

Lemma state_bucket_correlation_1_0 : state_bucket_correlation 1 0 = 1.
Proof.
  unfold state_bucket_correlation. simpl. lra.
Qed.

Lemma state_bucket_correlation_0_1 : state_bucket_correlation 0 1 = -1.
Proof.
  unfold state_bucket_correlation. simpl. lra.
Qed.

(** * The LDL branch: rational certificates for singular completions *)

(** The PD branch demands strict positivity, so it cannot accept a point
    whose only admissible completions are singular -- and the boundary of
    the quantum set is exactly where that happens. This branch closes the
    gap for every point that has a RATIONAL positive-semidefinite
    completion at all: the program supplies the completion (x, y) plus a
    rational LDL^T certificate of the completed matrix -- six L-entries
    over a common positive denominator [lden], four pivots d_k >= 0 over a
    common positive denominator [dden] -- and the check verifies the ten
    entry equations of M = L D L^T in cross-multiplied Z-arithmetic.
    Soundness is a sum-of-weighted-squares identity: given the equations,
    the quadratic form IS d1 P1^2 + d2 P2^2 + d3 P3^2 + d4 P4^2.

    Completeness scope, exact: every rational symmetric PSD matrix admits
    a rational LDL^T without pivoting (a zero pivot in a PSD matrix forces
    its entire column to vanish, so the factorization never needs a swap),
    so this branch accepts every correlator tuple admitting any rational
    PSD completion -- interior, classical, or exactly on the quantum
    boundary, as [gate_accepts_pythagorean_boundary] computes below. What
    no integer check can ever accept: tuples whose every PSD completion is
    irrational, since an exact rational certificate for such a completion
    does not exist to be supplied. That residue is not an engineering gap;
    it is the arithmetic of the boundary itself. *)

Section LDLCheck.

Variable wc : WitnessCounts.
Variables xs xd ys yd : nat.
Variable lden dden : Z.
Variable lq : nat -> Z.   (* L21 L31 L32 L41 L42 L43 at indices 0..5 *)
Variable dq : nat -> Z.   (* d1 d2 d3 d4 at indices 0..3 *)

(** The ten entry equations of M = L D L^T, denominators cleared. Entry
    order matches the completed matrix: rows (A0, A1, B0, B1); M21 = x,
    M31 = E00, M41 = E01, M32 = E10, M42 = E11, M43 = y; unit diagonal. *)
Definition ldl_equations : bool :=
  (* diagonal 1: d1 = 1 *)
  (dq 0 =? dden)%Z
  (* x = L21 d1 *)
  && (bnum xs xd * lden * dden =? bden xs xd * (lq 0 * dq 0))%Z
  (* diagonal 2: lden^2 dden = L21^2num d1 + lden^2 d2 *)
  && (lden * lden * dden =? lq 0 * lq 0 * dq 0 + lden * lden * dq 1)%Z
  (* E00 = L31 d1 *)
  && (bnum wc.(wc_same_00) wc.(wc_diff_00) * lden * dden
      =? bden wc.(wc_same_00) wc.(wc_diff_00) * (lq 1 * dq 0))%Z
  (* E10 = L31 L21 d1 + L32 d2 *)
  && (bnum wc.(wc_same_10) wc.(wc_diff_10) * (lden * lden) * dden
      =? bden wc.(wc_same_10) wc.(wc_diff_10)
         * (lq 1 * lq 0 * dq 0 + lden * lq 2 * dq 1))%Z
  (* diagonal 3 *)
  && (lden * lden * dden
      =? lq 1 * lq 1 * dq 0 + lq 2 * lq 2 * dq 1 + lden * lden * dq 2)%Z
  (* E01 = L41 d1 *)
  && (bnum wc.(wc_same_01) wc.(wc_diff_01) * lden * dden
      =? bden wc.(wc_same_01) wc.(wc_diff_01) * (lq 3 * dq 0))%Z
  (* E11 = L41 L21 d1 + L42 d2 *)
  && (bnum wc.(wc_same_11) wc.(wc_diff_11) * (lden * lden) * dden
      =? bden wc.(wc_same_11) wc.(wc_diff_11)
         * (lq 3 * lq 0 * dq 0 + lden * lq 4 * dq 1))%Z
  (* y = L41 L31 d1 + L42 L32 d2 + L43 d3 *)
  && (bnum ys yd * (lden * lden) * dden
      =? bden ys yd
         * (lq 3 * lq 1 * dq 0 + lq 4 * lq 2 * dq 1 + lden * lq 5 * dq 2))%Z
  (* diagonal 4 *)
  && (lden * lden * dden
      =? lq 3 * lq 3 * dq 0 + lq 4 * lq 4 * dq 1 + lq 5 * lq 5 * dq 2
         + lden * lden * dq 3)%Z.

Definition elliptope_ldl_check : bool :=
  (0 <? lden)%Z && (0 <? dden)%Z
  && (0 <=? dq 0)%Z && (0 <=? dq 1)%Z && (0 <=? dq 2)%Z && (0 <=? dq 3)%Z
  && ldl_equations.

End LDLCheck.

(** Quotient helpers used by every equation lift. All deterministic:
    no field_simplify, no search. *)
Lemma mul2_neq0 : forall a b : RealNumber, a <> 0 -> b <> 0 -> a * b <> 0.
Proof.
  intros a b Ha Hb Habs.
  apply Rmult_integral in Habs as [H | H]; [exact (Ha H) | exact (Hb H)].
Qed.

Lemma mul3_neq0 : forall a b c : RealNumber,
  a <> 0 -> b <> 0 -> c <> 0 -> a * b * c <> 0.
Proof.
  intros a b c Ha Hb Hc.
  apply mul2_neq0; [apply mul2_neq0; assumption | assumption].
Qed.

Lemma div_eq_intro :
  forall a b c d : RealNumber,
    b <> 0 -> d <> 0 -> a * d = c * b -> a / b = c / d.
Proof.
  intros a b c d Hb Hd H.
  unfold Rdiv.
  apply (Rmult_eq_reg_r (b * d)); [| apply mul2_neq0; assumption].
  assert (HL : a * / b * (b * d) = a * d * (/ b * b)) by ring.
  assert (HR : c * / d * (b * d) = c * b * (/ d * d)) by ring.
  rewrite HL, HR, (Rinv_l b Hb), (Rinv_l d Hd).
  rewrite !Rmult_1_r. exact H.
Qed.

Lemma one_eq_div : forall c d : RealNumber, d <> 0 -> d = c -> 1 = c / d.
Proof.
  intros c d Hd Heq. rewrite <- Heq. symmetry. unfold Rdiv.
  apply Rinv_r. exact Hd.
Qed.

Lemma elliptope_ldl_check_sound :
  forall wc xs xd ys yd lden dden lq dq,
    elliptope_ldl_check wc xs xd ys yd lden dden lq dq = true ->
    elliptope_realizable
      (bval wc.(wc_same_00) wc.(wc_diff_00))
      (bval wc.(wc_same_01) wc.(wc_diff_01))
      (bval wc.(wc_same_10) wc.(wc_diff_10))
      (bval wc.(wc_same_11) wc.(wc_diff_11)).
Proof.
  intros wc xs xd ys yd lden dden lq dq Hchk.
  unfold elliptope_ldl_check in Hchk.
  apply andb_prop in Hchk as [Hbase Heqs].
  apply andb_prop in Hbase as [Hbase Hdq3].
  apply andb_prop in Hbase as [Hbase Hdq2].
  apply andb_prop in Hbase as [Hbase Hdq1].
  apply andb_prop in Hbase as [Hbase Hdq0].
  apply andb_prop in Hbase as [Hlden Hdden].
  unfold ldl_equations in Heqs.
  apply andb_prop in Heqs as [Heqs He10].
  apply andb_prop in Heqs as [Heqs He9].
  apply andb_prop in Heqs as [Heqs He8].
  apply andb_prop in Heqs as [Heqs He7].
  apply andb_prop in Heqs as [Heqs He6].
  apply andb_prop in Heqs as [Heqs He5].
  apply andb_prop in Heqs as [Heqs He4].
  apply andb_prop in Heqs as [Heqs He3].
  apply andb_prop in Heqs as [He1 He2].
  apply Z.ltb_lt in Hlden, Hdden.
  apply Z.leb_le in Hdq0, Hdq1, Hdq2, Hdq3.
  apply Z.eqb_eq in He1, He2, He3, He4, He5, He6, He7, He8, He9, He10.
  set (E00 := bval wc.(wc_same_00) wc.(wc_diff_00)).
  set (E01 := bval wc.(wc_same_01) wc.(wc_diff_01)).
  set (E10 := bval wc.(wc_same_10) wc.(wc_diff_10)).
  set (E11 := bval wc.(wc_same_11) wc.(wc_diff_11)).
  set (x := bval xs xd).
  set (y := bval ys yd).
  set (rl := fun i => IZR (lq i) / IZR lden).
  set (rd := fun k => IZR (dq k) / IZR dden).
  assert (Hldr : 0 < IZR lden) by (apply IZR_lt; exact Hlden).
  assert (Hddr : 0 < IZR dden) by (apply IZR_lt; exact Hdden).
  assert (Hldne : IZR lden <> 0) by lra.
  assert (Hddne : IZR dden <> 0) by lra.
  assert (Hden3 : IZR lden * IZR lden * IZR dden <> 0)
    by (apply mul3_neq0; assumption).
  (* Real forms of the ten equations. *)
  assert (R1 : rd 0%nat = 1).
  { unfold rd. rewrite He1. unfold Rdiv. apply Rinv_r. exact Hddne. }
  assert (Rx : x = rl 0%nat * rd 0%nat).
  { assert (H0 : IZR (bnum xs xd * lden * dden)
               = IZR (bden xs xd * (lq 0%nat * dq 0%nat))) by (now rewrite He2).
    repeat first [rewrite plus_IZR in H0 | rewrite mult_IZR in H0].
    assert (Hcd : rl 0%nat * rd 0%nat
                = IZR (lq 0%nat) * IZR (dq 0%nat) / (IZR lden * IZR dden)).
    { unfold rl, rd. field. split; assumption. }
    rewrite Hcd. unfold x, bval.
    apply div_eq_intro;
      [ exact (bden_IZR_neq0 xs xd)
      | apply mul2_neq0; assumption
      | nra ]. }
  assert (R3 : 1 = rl 0%nat * rl 0%nat * rd 0%nat + rd 1%nat).
  { assert (H0 : IZR (lden * lden * dden)
               = IZR (lq 0%nat * lq 0%nat * dq 0%nat + lden * lden * dq 1%nat))
      by (now rewrite He3).
    repeat first [rewrite plus_IZR in H0 | rewrite mult_IZR in H0].
    assert (Hcd : rl 0%nat * rl 0%nat * rd 0%nat + rd 1%nat
                = (IZR (lq 0%nat) * IZR (lq 0%nat) * IZR (dq 0%nat)
                   + IZR lden * IZR lden * IZR (dq 1%nat))
                  / (IZR lden * IZR lden * IZR dden)).
    { unfold rl, rd. field. split; assumption. }
    rewrite Hcd. apply one_eq_div; [exact Hden3 | nra]. }
  assert (R00 : E00 = rl 1%nat * rd 0%nat).
  { assert (H0 : IZR (bnum wc.(wc_same_00) wc.(wc_diff_00) * lden * dden)
               = IZR (bden wc.(wc_same_00) wc.(wc_diff_00) * (lq 1%nat * dq 0%nat)))
      by (now rewrite He4).
    repeat first [rewrite plus_IZR in H0 | rewrite mult_IZR in H0].
    assert (Hcd : rl 1%nat * rd 0%nat
                = IZR (lq 1%nat) * IZR (dq 0%nat) / (IZR lden * IZR dden)).
    { unfold rl, rd. field. split; assumption. }
    rewrite Hcd. unfold E00, bval.
    apply div_eq_intro;
      [ exact (bden_IZR_neq0 _ _)
      | apply mul2_neq0; assumption
      | nra ]. }
  assert (R10 : E10 = rl 1%nat * rl 0%nat * rd 0%nat + rl 2%nat * rd 1%nat).
  { assert (H0 : IZR (bnum wc.(wc_same_10) wc.(wc_diff_10) * (lden * lden) * dden)
               = IZR (bden wc.(wc_same_10) wc.(wc_diff_10)
                      * (lq 1%nat * lq 0%nat * dq 0%nat + lden * lq 2%nat * dq 1%nat)))
      by (now rewrite He5).
    repeat first [rewrite plus_IZR in H0 | rewrite mult_IZR in H0].
    assert (Hcd : rl 1%nat * rl 0%nat * rd 0%nat + rl 2%nat * rd 1%nat
                = (IZR (lq 1%nat) * IZR (lq 0%nat) * IZR (dq 0%nat)
                   + IZR lden * IZR (lq 2%nat) * IZR (dq 1%nat))
                  / (IZR lden * IZR lden * IZR dden)).
    { unfold rl, rd. field. split; assumption. }
    rewrite Hcd. unfold E10, bval.
    apply div_eq_intro; [ exact (bden_IZR_neq0 _ _) | exact Hden3 | nra ]. }
  assert (R6 : 1 = rl 1%nat * rl 1%nat * rd 0%nat
                   + rl 2%nat * rl 2%nat * rd 1%nat + rd 2%nat).
  { assert (H0 : IZR (lden * lden * dden)
               = IZR (lq 1%nat * lq 1%nat * dq 0%nat + lq 2%nat * lq 2%nat * dq 1%nat
                      + lden * lden * dq 2%nat)) by (now rewrite He6).
    repeat first [rewrite plus_IZR in H0 | rewrite mult_IZR in H0].
    assert (Hcd : rl 1%nat * rl 1%nat * rd 0%nat
                  + rl 2%nat * rl 2%nat * rd 1%nat + rd 2%nat
                = (IZR (lq 1%nat) * IZR (lq 1%nat) * IZR (dq 0%nat)
                   + IZR (lq 2%nat) * IZR (lq 2%nat) * IZR (dq 1%nat)
                   + IZR lden * IZR lden * IZR (dq 2%nat))
                  / (IZR lden * IZR lden * IZR dden)).
    { unfold rl, rd. field. split; assumption. }
    rewrite Hcd. apply one_eq_div; [exact Hden3 | nra]. }
  assert (R01 : E01 = rl 3%nat * rd 0%nat).
  { assert (H0 : IZR (bnum wc.(wc_same_01) wc.(wc_diff_01) * lden * dden)
               = IZR (bden wc.(wc_same_01) wc.(wc_diff_01) * (lq 3%nat * dq 0%nat)))
      by (now rewrite He7).
    repeat first [rewrite plus_IZR in H0 | rewrite mult_IZR in H0].
    assert (Hcd : rl 3%nat * rd 0%nat
                = IZR (lq 3%nat) * IZR (dq 0%nat) / (IZR lden * IZR dden)).
    { unfold rl, rd. field. split; assumption. }
    rewrite Hcd. unfold E01, bval.
    apply div_eq_intro;
      [ exact (bden_IZR_neq0 _ _)
      | apply mul2_neq0; assumption
      | nra ]. }
  assert (R11 : E11 = rl 3%nat * rl 0%nat * rd 0%nat + rl 4%nat * rd 1%nat).
  { assert (H0 : IZR (bnum wc.(wc_same_11) wc.(wc_diff_11) * (lden * lden) * dden)
               = IZR (bden wc.(wc_same_11) wc.(wc_diff_11)
                      * (lq 3%nat * lq 0%nat * dq 0%nat + lden * lq 4%nat * dq 1%nat)))
      by (now rewrite He8).
    repeat first [rewrite plus_IZR in H0 | rewrite mult_IZR in H0].
    assert (Hcd : rl 3%nat * rl 0%nat * rd 0%nat + rl 4%nat * rd 1%nat
                = (IZR (lq 3%nat) * IZR (lq 0%nat) * IZR (dq 0%nat)
                   + IZR lden * IZR (lq 4%nat) * IZR (dq 1%nat))
                  / (IZR lden * IZR lden * IZR dden)).
    { unfold rl, rd. field. split; assumption. }
    rewrite Hcd. unfold E11, bval.
    apply div_eq_intro; [ exact (bden_IZR_neq0 _ _) | exact Hden3 | nra ]. }
  assert (Ry : y = rl 3%nat * rl 1%nat * rd 0%nat
                   + rl 4%nat * rl 2%nat * rd 1%nat + rl 5%nat * rd 2%nat).
  { assert (H0 : IZR (bnum ys yd * (lden * lden) * dden)
               = IZR (bden ys yd
                      * (lq 3%nat * lq 1%nat * dq 0%nat + lq 4%nat * lq 2%nat * dq 1%nat
                         + lden * lq 5%nat * dq 2%nat))) by (now rewrite He9).
    repeat first [rewrite plus_IZR in H0 | rewrite mult_IZR in H0].
    assert (Hcd : rl 3%nat * rl 1%nat * rd 0%nat
                  + rl 4%nat * rl 2%nat * rd 1%nat + rl 5%nat * rd 2%nat
                = (IZR (lq 3%nat) * IZR (lq 1%nat) * IZR (dq 0%nat)
                   + IZR (lq 4%nat) * IZR (lq 2%nat) * IZR (dq 1%nat)
                   + IZR lden * IZR (lq 5%nat) * IZR (dq 2%nat))
                  / (IZR lden * IZR lden * IZR dden)).
    { unfold rl, rd. field. split; assumption. }
    rewrite Hcd. unfold y, bval.
    apply div_eq_intro; [ exact (bden_IZR_neq0 _ _) | exact Hden3 | nra ]. }
  assert (R10d : 1 = rl 3%nat * rl 3%nat * rd 0%nat + rl 4%nat * rl 4%nat * rd 1%nat
                     + rl 5%nat * rl 5%nat * rd 2%nat + rd 3%nat).
  { assert (H0 : IZR (lden * lden * dden)
               = IZR (lq 3%nat * lq 3%nat * dq 0%nat + lq 4%nat * lq 4%nat * dq 1%nat
                      + lq 5%nat * lq 5%nat * dq 2%nat + lden * lden * dq 3%nat))
      by (now rewrite He10).
    repeat first [rewrite plus_IZR in H0 | rewrite mult_IZR in H0].
    assert (Hcd : rl 3%nat * rl 3%nat * rd 0%nat + rl 4%nat * rl 4%nat * rd 1%nat
                  + rl 5%nat * rl 5%nat * rd 2%nat + rd 3%nat
                = (IZR (lq 3%nat) * IZR (lq 3%nat) * IZR (dq 0%nat)
                   + IZR (lq 4%nat) * IZR (lq 4%nat) * IZR (dq 1%nat)
                   + IZR (lq 5%nat) * IZR (lq 5%nat) * IZR (dq 2%nat)
                   + IZR lden * IZR lden * IZR (dq 3%nat))
                  / (IZR lden * IZR lden * IZR dden)).
    { unfold rl, rd. field. split; assumption. }
    rewrite Hcd. apply one_eq_div; [exact Hden3 | nra]. }
  (* Pivot nonnegativity, real side. *)
  assert (Hrd0 : 0 <= rd 0%nat).
  { unfold rd. apply Rmult_le_pos; [apply IZR_le; exact Hdq0 |].
    left. apply Rinv_0_lt_compat. exact Hddr. }
  assert (Hrd1 : 0 <= rd 1%nat).
  { unfold rd. apply Rmult_le_pos; [apply IZR_le; exact Hdq1 |].
    left. apply Rinv_0_lt_compat. exact Hddr. }
  assert (Hrd2 : 0 <= rd 2%nat).
  { unfold rd. apply Rmult_le_pos; [apply IZR_le; exact Hdq2 |].
    left. apply Rinv_0_lt_compat. exact Hddr. }
  assert (Hrd3 : 0 <= rd 3%nat).
  { unfold rd. apply Rmult_le_pos; [apply IZR_le; exact Hdq3 |].
    left. apply Rinv_0_lt_compat. exact Hddr. }
  (* The witness completion. *)
  exists x, y.
  split.
  - apply npa_to_matrix_symmetric.
  - intro v.
    rewrite (completed_quad_expand E00 E01 E10 E11 x y v).
    cbv zeta.
    set (v0 := v F1).
    set (v1 := v (FS F1)).
    set (v2 := v (FS (FS F1))).
    set (v3 := v (FS (FS (FS F1)))).
    set (v4 := v (FS (FS (FS (FS F1))))).
    set (P1 := v1 + rl 0%nat * v2 + rl 1%nat * v3 + rl 3%nat * v4).
    set (P2 := v2 + rl 2%nat * v3 + rl 4%nat * v4).
    set (P3 := v3 + rl 5%nat * v4).
    (* The LDL sum-of-weighted-squares identity, with correction terms
       the ten equations annihilate. Pure ring identity. *)
    assert (Hkey :
      v0 * v0 + v1 * v1 + v2 * v2 + v3 * v3 + v4 * v4
      + 2 * x * (v1 * v2) + 2 * y * (v3 * v4)
      + 2 * E00 * (v1 * v3) + 2 * E01 * (v1 * v4)
      + 2 * E10 * (v2 * v3) + 2 * E11 * (v2 * v4)
      =
      v0 * v0
      + rd 0%nat * (P1 * P1) + rd 1%nat * (P2 * P2)
      + rd 2%nat * (P3 * P3) + rd 3%nat * (v4 * v4)
      + (1 - rd 0%nat) * (v1 * v1)
      + (1 - (rl 0%nat * rl 0%nat * rd 0%nat + rd 1%nat)) * (v2 * v2)
      + (1 - (rl 1%nat * rl 1%nat * rd 0%nat + rl 2%nat * rl 2%nat * rd 1%nat
              + rd 2%nat)) * (v3 * v3)
      + (1 - (rl 3%nat * rl 3%nat * rd 0%nat + rl 4%nat * rl 4%nat * rd 1%nat
              + rl 5%nat * rl 5%nat * rd 2%nat + rd 3%nat)) * (v4 * v4)
      + 2 * (x - rl 0%nat * rd 0%nat) * (v1 * v2)
      + 2 * (E00 - rl 1%nat * rd 0%nat) * (v1 * v3)
      + 2 * (E01 - rl 3%nat * rd 0%nat) * (v1 * v4)
      + 2 * (E10 - (rl 1%nat * rl 0%nat * rd 0%nat + rl 2%nat * rd 1%nat)) * (v2 * v3)
      + 2 * (E11 - (rl 3%nat * rl 0%nat * rd 0%nat + rl 4%nat * rd 1%nat)) * (v2 * v4)
      + 2 * (y - (rl 3%nat * rl 1%nat * rd 0%nat + rl 4%nat * rl 2%nat * rd 1%nat
                  + rl 5%nat * rd 2%nat)) * (v3 * v4)).
    { unfold P1, P2, P3. ring. }
    rewrite Hkey.
    (* The corrections vanish. *)
    assert (Z1 : 1 - rd 0%nat = 0) by lra.
    assert (Z2 : 1 - (rl 0%nat * rl 0%nat * rd 0%nat + rd 1%nat) = 0) by lra.
    assert (Z3 : 1 - (rl 1%nat * rl 1%nat * rd 0%nat + rl 2%nat * rl 2%nat * rd 1%nat
                      + rd 2%nat) = 0) by lra.
    assert (Z4 : 1 - (rl 3%nat * rl 3%nat * rd 0%nat + rl 4%nat * rl 4%nat * rd 1%nat
                      + rl 5%nat * rl 5%nat * rd 2%nat + rd 3%nat) = 0) by lra.
    assert (Z5 : x - rl 0%nat * rd 0%nat = 0) by lra.
    assert (Z6 : E00 - rl 1%nat * rd 0%nat = 0) by lra.
    assert (Z7 : E01 - rl 3%nat * rd 0%nat = 0) by lra.
    assert (Z8 : E10 - (rl 1%nat * rl 0%nat * rd 0%nat + rl 2%nat * rd 1%nat) = 0) by lra.
    assert (Z9 : E11 - (rl 3%nat * rl 0%nat * rd 0%nat + rl 4%nat * rd 1%nat) = 0) by lra.
    assert (Z10 : y - (rl 3%nat * rl 1%nat * rd 0%nat + rl 4%nat * rl 2%nat * rd 1%nat
                       + rl 5%nat * rd 2%nat) = 0) by lra.
    rewrite Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10.
    (* Sum of a square and four weighted squares. *)
    pose proof (Rle_0_sqr v0) as Hv0; unfold Rsqr in Hv0.
    pose proof (Rle_0_sqr P1) as HP1; unfold Rsqr in HP1.
    pose proof (Rle_0_sqr P2) as HP2; unfold Rsqr in HP2.
    pose proof (Rle_0_sqr P3) as HP3; unfold Rsqr in HP3.
    pose proof (Rle_0_sqr v4) as Hv4; unfold Rsqr in Hv4.
    assert (HT0 : 0 <= rd 0%nat * (P1 * P1)) by (apply Rmult_le_pos; assumption).
    assert (HT1 : 0 <= rd 1%nat * (P2 * P2)) by (apply Rmult_le_pos; assumption).
    assert (HT2 : 0 <= rd 2%nat * (P3 * P3)) by (apply Rmult_le_pos; assumption).
    assert (HT3 : 0 <= rd 3%nat * (v4 * v4)) by (apply Rmult_le_pos; assumption).
    lra.
Qed.

(** * The full gate: all three branches *)

Definition elliptope_check_full
  (wc : WitnessCounts) (xs xd ys yd : nat)
  (lden dden : Z) (lq dq : nat -> Z) : bool :=
  elliptope_pd_check wc xs xd ys yd
  || elliptope_ldl_check wc xs xd ys yd lden dden lq dq.

Theorem elliptope_check_full_sound :
  forall wc xs xd ys yd lden dden lq dq,
    elliptope_check_full wc xs xd ys yd lden dden lq dq = true ->
    elliptope_realizable
      (state_bucket_correlation wc.(wc_same_00) wc.(wc_diff_00))
      (state_bucket_correlation wc.(wc_same_01) wc.(wc_diff_01))
      (state_bucket_correlation wc.(wc_same_10) wc.(wc_diff_10))
      (state_bucket_correlation wc.(wc_same_11) wc.(wc_diff_11)).
Proof.
  intros wc xs xd ys yd lden dden lq dq Hchk.
  rewrite <- !bval_state_bucket_correlation.
  unfold elliptope_check_full in Hchk.
  apply orb_prop in Hchk as [Hpd | Hldl].
  - exact (elliptope_pd_check_sound wc xs xd ys yd Hpd).
  - exact (elliptope_ldl_check_sound wc xs xd ys yd lden dden lq dq Hldl).
Qed.

(** * The gate computes: acceptances via LDL / PD certificates *)

(** The mu = 0 all-ones tightness witness (E = (1,1,1,1)): completion
    x = y = 1 gives the rank-one all-ones matrix -- singular, invisible to
    the strict PD branch -- whose rational LDL certificate (pivots 1,0,0,0,
    unit L-column) passes. The slice gate traps this state; the elliptope
    gate accepts it. *)
Definition lq_ones (i : nat) : Z :=
  match i with 0%nat => 1 | 1%nat => 1 | 3%nat => 1 | _ => 0 end%Z.
Definition dq_ones (k : nat) : Z :=
  match k with 0%nat => 1 | _ => 0 end%Z.

Example gate_accepts_all_ones :
  elliptope_check_full wc_all_ones 1 0 1 0 1 1 lq_ones dq_ones = true.
Proof. reflexivity. Qed.

(** The running example (1,0,1,0): completion x = 1, y = 0, rank-two
    singular; LDL certificate pivots (1,0,0,1). *)
Definition lq_tur (i : nat) : Z :=
  match i with 0%nat => 1 | 1%nat => 1 | _ => 0 end%Z.
Definition dq_tur (k : nat) : Z :=
  match k with 0%nat => 1 | 3%nat => 1 | _ => 0 end%Z.

Example gate_accepts_turing_point :
  elliptope_check_full wc_turing_point 1 0 0 0 1 1 lq_tur dq_tur = true.
Proof. reflexivity. Qed.

(** An interior quantum-side point E = (3/5, 3/5, 3/5, -3/5), S = 12/5 > 2,
    strictly inside: the strict PD branch accepts it at the zero
    completion. *)
Example gate_accepts_beyond_classical :
  elliptope_check_full wc_interior 0 0 0 0 1 1 (fun _ => 0%Z) (fun _ => 0%Z) = true.
Proof. reflexivity. Qed.

(** * The boundary computes: a Pythagorean point ON the Tsirelson curve *)

(** E = (3/5, 4/5, 4/5, -3/5): arcsin(3/5) + 2 arcsin(4/5) + arcsin(3/5)
    = 2 (arcsin(3/5) + arcsin(4/5)) = pi, so this rational point lies
    exactly on the quantum boundary, with S = 14/5 > 2: not classical,
    not interior, invisible to both other branches. Its completion at
    x = y = 0 is singular (pivots 1, 1, 0, 0) and rational, and the LDL
    branch accepts it by computation. *)
Definition wc_pythagorean : WitnessCounts :=
  {| wc_same_00 := 4; wc_diff_00 := 1;
     wc_same_01 := 9; wc_diff_01 := 1;
     wc_same_10 := 9; wc_diff_10 := 1;
     wc_same_11 := 1; wc_diff_11 := 4 |}.

Definition lq_pyth (i : nat) : Z :=
  match i with
  | 0%nat => 0
  | 1%nat => 3
  | 2%nat => 4
  | 3%nat => 4
  | 4%nat => (-3)
  | _ => 0
  end%Z.

Definition dq_pyth (k : nat) : Z :=
  match k with
  | 0%nat => 1
  | 1%nat => 1
  | _ => 0
  end%Z.

Example gate_accepts_pythagorean_boundary :
  elliptope_ldl_check wc_pythagorean 0 0 0 0 5 1 lq_pyth dq_pyth = true.
Proof. reflexivity. Qed.

(** The full gate still never accepts the PR box: soundness plus Tsirelson
    close all three branches at once. *)
Theorem elliptope_full_gate_never_accepts_pr_box :
  forall xs xd ys yd lden dden lq dq,
    elliptope_check_full wc_pr_box xs xd ys yd lden dden lq dq = false.
Proof.
  intros xs xd ys yd lden dden lq dq.
  destruct (elliptope_check_full wc_pr_box xs xd ys yd lden dden lq dq)
    eqn:Hgate; [exfalso | reflexivity].
  apply elliptope_check_full_sound in Hgate.
  assert (Hf00 : wc_same_00 wc_pr_box = 1%nat) by reflexivity.
  assert (Hf00d : wc_diff_00 wc_pr_box = 0%nat) by reflexivity.
  assert (Hf01 : wc_same_01 wc_pr_box = 1%nat) by reflexivity.
  assert (Hf01d : wc_diff_01 wc_pr_box = 0%nat) by reflexivity.
  assert (Hf10 : wc_same_10 wc_pr_box = 1%nat) by reflexivity.
  assert (Hf10d : wc_diff_10 wc_pr_box = 0%nat) by reflexivity.
  assert (Hf11 : wc_same_11 wc_pr_box = 0%nat) by reflexivity.
  assert (Hf11d : wc_diff_11 wc_pr_box = 1%nat) by reflexivity.
  rewrite Hf00, Hf00d, Hf01, Hf01d, Hf10, Hf10d, Hf11, Hf11d in Hgate.
  rewrite state_bucket_correlation_1_0, state_bucket_correlation_0_1 in Hgate.
  exact (pr_box_not_elliptope Hgate).
Qed.

(** * Anchor for proof-connectivity audits *)

Definition elliptope_gate_anchor := @elliptope_check_full.
