(** QuantumStrategiesComplex: Tsirelson's bound for quantum strategies with
    complex amplitudes.

    Amplitudes and matrix entries are complex numbers, written by their real
    and imaginary parts. A state psi = psr + i psi_ on a finite joint space is
    a unit vector; an observable A = ar + i ai is Hermitian (ar symmetric, ai
    antisymmetric) and squares to the identity. The correlator is the real
    part of <psi, (A (x) B) psi>, which is real for Hermitian A and B.

    - The correlator is the real inner product of the two vectors
      (A (x) 1) psi and (1 (x) B) psi ([qc_corr_dot]), and both are unit
      vectors ([qc_uvec_unit], [qc_vvec_unit]).
    - Tsirelson's bound: every such strategy has S^2 <= 8
      ([qc_tsirelson]). The proof reads a complex vector on I x J as a real
      vector on (bool x I) x J and applies the four-vector bound
      ([qc_four_vectors]).
    - Every real strategy is a complex one with zero imaginary parts and the
      same S ([qc_of_real_valid]), so the two-qubit strategy reaches 2 sqrt 2
      here too ([qc_tsirelson_reached]).
    - Five unit vectors give a positive semidefinite level-1 moment matrix
      ([qc_gram_psd]), so every strategy with complex amplitudes passes
      npa_psd ([qc_npa_psd]), with its four correlators in the correlator
      entries ([qc_npa_correlators]). *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics. No definition or theorem here mentions a certification
   system, a ledger or a machine step; it imports only FiniteSums.v and
   QuantumStrategies.v.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. The standalone boundary is stated here rather than inferred from
   an import. *)

From Coq Require Import List Reals Lra Psatz Bool Lia.
Import ListNotations.
From Kernel Require Import ConstructivePSD NPAMomentMatrix FiniteSums QuantumStrategies.
Open Scope R_scope.

(** The bound on four unit vectors, for any finite index: if u0, u1, v0, v1
    are unit vectors then (u0.v0 + u0.v1 + u1.v0 - u1.v1)^2 <= 8. *)
Lemma qc_four_vectors : forall (X Y : Type) (LX : list X) (LY : list Y) (u0 u1 v0 v1 : X -> Y -> R),
  qs_dot X Y LX LY u0 u0 = 1 -> qs_dot X Y LX LY u1 u1 = 1 ->
  qs_dot X Y LX LY v0 v0 = 1 -> qs_dot X Y LX LY v1 v1 = 1 ->
  let s := qs_dot X Y LX LY u0 v0 + qs_dot X Y LX LY u0 v1 +
           qs_dot X Y LX LY u1 v0 - qs_dot X Y LX LY u1 v1 in
  s * s <= 8.
Proof.
  intros X Y LX LY u0 u1 v0 v1 Hu0 Hu1 Hv0 Hv1 s.
  set (wp := fun k j => v0 k j + v1 k j). set (wm := fun k j => v0 k j - v1 k j).
  assert (EX : qs_dot X Y LX LY u0 v0 + qs_dot X Y LX LY u0 v1 = qs_dot X Y LX LY u0 wp)
    by (unfold wp; rewrite qs_dot_plus_r; reflexivity).
  assert (EY : qs_dot X Y LX LY u1 v0 - qs_dot X Y LX LY u1 v1 = qs_dot X Y LX LY u1 wm)
    by (unfold wm; rewrite qs_dot_minus_r; reflexivity).
  set (a := qs_dot X Y LX LY u0 wp) in *. set (b := qs_dot X Y LX LY u1 wm) in *.
  assert (HX : a * a <= qs_dot X Y LX LY wp wp).
  { pose proof (qs_dot_cs X Y LX LY u0 wp) as H. rewrite Hu0, Rmult_1_l in H. exact H. }
  assert (HY : b * b <= qs_dot X Y LX LY wm wm).
  { pose proof (qs_dot_cs X Y LX LY u1 wm) as H. rewrite Hu1, Rmult_1_l in H. exact H. }
  assert (HPQ : qs_dot X Y LX LY wp wp + qs_dot X Y LX LY wm wm = 4).
  { unfold wp, wm. rewrite qs_dot_sum_diff, Hv0, Hv1. ring. }
  assert (Es : s = a + b) by (unfold s; lra).
  rewrite Es.
  pose proof (sq_nonneg (a - b)) as HD.
  assert (E : (a + b) * (a + b) = 2 * (a * a) + 2 * (b * b) - (a - b) * (a - b)) by ring.
  rewrite E. nra.
Qed.

(** * The moment matrix of five unit vectors *)

Section Gram.

Variables (X Y : Type) (LX : list X) (LY : list Y).

Let dot := qs_dot X Y LX LY.

(** The level-1 moment matrix whose entries are the inner products of five
    vectors w 0, ..., w 4, in the order psi, A0 psi, A1 psi, B0 psi, B1 psi. *)
Definition qc_gram (w : nat -> X -> Y -> R) : NPAMomentMatrix := {|
  npa_EA0 := dot (w 0%nat) (w 1%nat);
  npa_EA1 := dot (w 0%nat) (w 2%nat);
  npa_EB0 := dot (w 0%nat) (w 3%nat);
  npa_EB1 := dot (w 0%nat) (w 4%nat);
  npa_E00 := dot (w 1%nat) (w 3%nat);
  npa_E01 := dot (w 1%nat) (w 4%nat);
  npa_E10 := dot (w 2%nat) (w 3%nat);
  npa_E11 := dot (w 2%nat) (w 4%nat);
  npa_rho_AA := dot (w 1%nat) (w 2%nat);
  npa_rho_BB := dot (w 3%nat) (w 4%nat);
|}.

Lemma qc_gram_entries : forall w, (forall n, (n <= 4)%nat -> dot (w n) (w n) = 1) ->
  forall i j : Fin5,
  nat_matrix_to_fin5 (npa_to_matrix (qc_gram w)) i j = dot (w (fin_to_nat i)) (w (fin_to_nat j)).
Proof.
  intros w Hw i j.
  assert (H0 : dot (w 0%nat) (w 0%nat) = 1) by (apply Hw; lia).
  assert (H1 : dot (w 1%nat) (w 1%nat) = 1) by (apply Hw; lia).
  assert (H2 : dot (w 2%nat) (w 2%nat) = 1) by (apply Hw; lia).
  assert (H3 : dot (w 3%nat) (w 3%nat) = 1) by (apply Hw; lia).
  assert (H4 : dot (w 4%nat) (w 4%nat) = 1) by (apply Hw; lia).
  unfold nat_matrix_to_fin5, fin_to_nat.
  destruct i using Fin.caseS';
    [| destruct i using Fin.caseS';
       [| destruct i using Fin.caseS';
          [| destruct i using Fin.caseS';
             [| destruct i using Fin.caseS'; [| inversion i]]]]];
  (destruct j using Fin.caseS';
    [| destruct j using Fin.caseS';
       [| destruct j using Fin.caseS';
          [| destruct j using Fin.caseS';
             [| destruct j using Fin.caseS'; [| inversion j]]]]]);
  cbn;
  first [ symmetry; exact H0 | symmetry; exact H1 | symmetry; exact H2
        | symmetry; exact H3 | symmetry; exact H4 | reflexivity
        | apply (qs_dot_sym X Y LX LY) ].
Qed.

(** Five unit vectors give a positive semidefinite moment matrix. *)
Theorem qc_gram_psd : forall w, (forall n, (n <= 4)%nat -> dot (w n) (w n) = 1) ->
  npa_psd (qc_gram w).
Proof.
  intros w Hw. unfold npa_psd. split.
  - intros i j. rewrite !(qc_gram_entries w Hw). apply (qs_dot_sym X Y LX LY).
  - intro v. unfold quad5. rewrite qs_sum_fin5. apply Rle_ge.
    assert (E : sumL qs_fin5_list (fun i => sum_fin5 (fun j =>
                  v i * nat_matrix_to_fin5 (npa_to_matrix (qc_gram w)) i j * v j)) =
                sumL qs_fin5_list (fun i => sumL qs_fin5_list (fun j =>
                  v i * dot (w (fin_to_nat i)) (w (fin_to_nat j)) * v j))).
    { apply sumL_ext. intros i _. rewrite qs_sum_fin5. apply sumL_ext. intros j _.
      rewrite (qc_gram_entries w Hw). reflexivity. }
    rewrite E.
    pose proof (qs_dot_combination X Y LX LY qs_fin5_list v (fun t => w (fin_to_nat t))) as C.
    cbv beta in C. unfold dot. rewrite <- C. apply qs_dot_nonneg.
Qed.

End Gram.

Section Complex.

Variables (I J : Type).
Variable eqI : forall a b : I, {a = b} + {a <> b}.
Variable eqJ : forall a b : J, {a = b} + {a <> b}.
Variables (LI : list I) (LJ : list J).
Hypothesis LI_nodup : NoDup LI.
Hypothesis LJ_nodup : NoDup LJ.

Definition qc_dI (i m : I) : R := if eqI i m then 1 else 0.
Definition qc_dJ (j m : J) : R := if eqJ j m then 1 else 0.

(** A Hermitian involution on the I side, given by its real and imaginary
    parts. *)
Definition qc_obsI (ar ai : I -> I -> R) : Prop :=
  (forall i k, ar i k = ar k i) /\ (forall i k, ai i k = - ai k i) /\
  (forall i m, In i LI -> In m LI ->
     sumL LI (fun k => ar i k * ar k m - ai i k * ai k m) = qc_dI i m) /\
  (forall i m, In i LI -> In m LI ->
     sumL LI (fun k => ar i k * ai k m + ai i k * ar k m) = 0).

Definition qc_obsJ (br bi : J -> J -> R) : Prop :=
  (forall j l, br j l = br l j) /\ (forall j l, bi j l = - bi l j) /\
  (forall j m, In j LJ -> In m LJ ->
     sumL LJ (fun l => br j l * br l m - bi j l * bi l m) = qc_dJ j m) /\
  (forall j m, In j LJ -> In m LJ ->
     sumL LJ (fun l => br j l * bi l m + bi j l * br l m) = 0).

Definition qc_unit (pr pi_ : I -> J -> R) : Prop :=
  sumL LI (fun i => sumL LJ (fun j => pr i j * pr i j + pi_ i j * pi_ i j)) = 1.

(** Real part of conj(x) * a * b * y, written out in real and imaginary
    parts. *)
Definition qc_re4 (xr xi ar ai br bi yr yi : R) : R :=
  let pr := xr * ar + xi * ai in        (* conj(x) * a, real part *)
  let pi_ := xr * ai - xi * ar in       (* conj(x) * a, imaginary part *)
  let qr := pr * br - pi_ * bi in
  let qi := pr * bi + pi_ * br in
  qr * yr - qi * yi.

(** The correlator Re <psi, (A (x) B) psi>. *)
Definition qc_corr (pr pi_ : I -> J -> R) (ar ai : I -> I -> R) (br bi : J -> J -> R) : R :=
  sumL LI (fun i => sumL LJ (fun j => sumL LI (fun k => sumL LJ (fun l =>
    qc_re4 (pr i j) (pi_ i j) (ar i k) (ai i k) (br j l) (bi j l) (pr k l) (pi_ k l))))).

(** (A (x) 1) psi and (1 (x) B) psi, by parts. *)
Definition qc_ur (ar ai : I -> I -> R) (pr pi_ : I -> J -> R) (k : I) (j : J) : R :=
  sumL LI (fun i => ar k i * pr i j - ai k i * pi_ i j).
Definition qc_ui (ar ai : I -> I -> R) (pr pi_ : I -> J -> R) (k : I) (j : J) : R :=
  sumL LI (fun i => ar k i * pi_ i j + ai k i * pr i j).
Definition qc_vr (br bi : J -> J -> R) (pr pi_ : I -> J -> R) (k : I) (j : J) : R :=
  sumL LJ (fun l => br j l * pr k l - bi j l * pi_ k l).
Definition qc_vi (br bi : J -> J -> R) (pr pi_ : I -> J -> R) (k : I) (j : J) : R :=
  sumL LJ (fun l => br j l * pi_ k l + bi j l * pr k l).

(** The real inner product of two complex vectors given by parts. *)
Definition qc_dot (xr xi yr yi : I -> J -> R) : R :=
  sumL LI (fun k => sumL LJ (fun j => xr k j * yr k j + xi k j * yi k j)).

(** Both observables are Hermitian, so the correlator is the real part of
    <(A (x) 1) psi, (1 (x) B) psi>. *)
Lemma qc_corr_dot : forall pr pi_ ar ai br bi,
  (forall i k, ar i k = ar k i) -> (forall i k, ai i k = - ai k i) ->
  qc_corr pr pi_ ar ai br bi =
  qc_dot (qc_ur ar ai pr pi_) (qc_ui ar ai pr pi_) (qc_vr br bi pr pi_) (qc_vi br bi pr pi_).
Proof.
  intros pr pi_ ar ai br bi Hs Ha. unfold qc_corr, qc_dot, qc_ur, qc_ui, qc_vr, qc_vi.
  transitivity (sumL LI (fun k => sumL LJ (fun j => sumL LI (fun i => sumL LJ (fun l =>
    qc_re4 (pr i j) (pi_ i j) (ar i k) (ai i k) (br j l) (bi j l) (pr k l) (pi_ k l)))))).
  - etransitivity.
    { apply sumL_ext. intros i _. apply (sumL_swap J I LJ LI). }
    etransitivity.
    { apply (sumL_swap I I LI LI). }
    apply sumL_ext. intros k _. apply (sumL_swap I J LI LJ).
  - apply sumL_ext. intros k _. apply sumL_ext. intros j _.
    rewrite !sumL_mult, <- sumL_plus. apply sumL_ext. intros i _.
    rewrite <- sumL_plus. apply sumL_ext. intros l _.
    unfold qc_re4. rewrite (Hs k i), (Ha k i). ring.
Qed.

(** The square of the norm of (A (x) 1) psi, one coordinate pair at a time:
    after the Hermitian substitution each term splits into the real part of
    A A, which the involution makes the identity, and its imaginary part,
    which the involution makes zero. *)
Lemma qc_uvec_unit : forall pr pi_ ar ai, qc_obsI ar ai -> qc_unit pr pi_ ->
  qc_dot (qc_ur ar ai pr pi_) (qc_ui ar ai pr pi_) (qc_ur ar ai pr pi_) (qc_ui ar ai pr pi_) = 1.
Proof.
  intros pr pi_ ar ai [Hs [Ha [Hre Him]]] Hunit. unfold qc_dot, qc_ur, qc_ui, qc_unit in *.
  transitivity (sumL LJ (fun j => sumL LI (fun i => pr i j * pr i j + pi_ i j * pi_ i j))).
  - transitivity (sumL LI (fun k => sumL LJ (fun j => sumL LI (fun i => sumL LI (fun m =>
      (ar k i * pr i j - ai k i * pi_ i j) * (ar k m * pr m j - ai k m * pi_ m j) +
      (ar k i * pi_ i j + ai k i * pr i j) * (ar k m * pi_ m j + ai k m * pr m j)))))).
    { apply sumL_ext. intros k _. apply sumL_ext. intros j _.
      rewrite !sumL_mult, <- sumL_plus. apply sumL_ext. intros i _.
      rewrite <- sumL_plus. reflexivity. }
    etransitivity. { apply (sumL_swap I J LI LJ). }
    apply sumL_ext. intros j _.
    etransitivity. { apply (sumL_swap I I LI LI). }
    apply sumL_ext. intros i Hi.
    etransitivity. { apply (sumL_swap I I LI LI). }
    transitivity (sumL LI (fun m => qc_dI i m * (pr m j * pr i j + pi_ m j * pi_ i j))).
    + apply sumL_ext. intros m Hm.
      transitivity (sumL LI (fun k =>
        (ar i k * ar k m - ai i k * ai k m) * (pr m j * pr i j + pi_ m j * pi_ i j) +
        (ar i k * ai k m + ai i k * ar k m) * (pi_ i j * pr m j - pr i j * pi_ m j))).
      * apply sumL_ext. intros k _. rewrite (Hs k i), (Ha k i). ring.
      * transitivity (sumL LI (fun k => ar i k * ar k m - ai i k * ai k m) *
          (pr m j * pr i j + pi_ m j * pi_ i j) +
          sumL LI (fun k => ar i k * ai k m + ai i k * ar k m) *
          (pi_ i j * pr m j - pr i j * pi_ m j)).
        { rewrite <- !sumL_scale_r, <- sumL_plus. reflexivity. }
        rewrite (Hre i m Hi Hm), (Him i m Hi Hm). ring.
    + unfold qc_dI.
      rewrite (sumL_delta I eqI LI i (fun m => pr m j * pr i j + pi_ m j * pi_ i j) LI_nodup Hi).
      reflexivity.
  - rewrite sumL_swap. exact Hunit.
Qed.

Lemma qc_vvec_unit : forall pr pi_ br bi, qc_obsJ br bi -> qc_unit pr pi_ ->
  qc_dot (qc_vr br bi pr pi_) (qc_vi br bi pr pi_) (qc_vr br bi pr pi_) (qc_vi br bi pr pi_) = 1.
Proof.
  intros pr pi_ br bi [Hs [Ha [Hre Him]]] Hunit. unfold qc_dot, qc_vr, qc_vi, qc_unit in *.
  rewrite <- Hunit. apply sumL_ext. intros k _.
  transitivity (sumL LJ (fun j => sumL LJ (fun l => sumL LJ (fun n =>
    (br j l * pr k l - bi j l * pi_ k l) * (br j n * pr k n - bi j n * pi_ k n) +
    (br j l * pi_ k l + bi j l * pr k l) * (br j n * pi_ k n + bi j n * pr k n))))).
  { apply sumL_ext. intros j _. rewrite !sumL_mult, <- sumL_plus. apply sumL_ext. intros l _.
    rewrite <- sumL_plus. reflexivity. }
  etransitivity. { apply (sumL_swap J J LJ LJ). }
  apply sumL_ext. intros l Hl.
  etransitivity. { apply (sumL_swap J J LJ LJ). }
  transitivity (sumL LJ (fun n => qc_dJ l n * (pr k n * pr k l + pi_ k n * pi_ k l))).
  - apply sumL_ext. intros n Hn.
    transitivity (sumL LJ (fun j =>
      (br l j * br j n - bi l j * bi j n) * (pr k n * pr k l + pi_ k n * pi_ k l) +
      (br l j * bi j n + bi l j * br j n) * (pi_ k l * pr k n - pr k l * pi_ k n))).
    + apply sumL_ext. intros j _. rewrite (Hs j l), (Ha j l). ring.
    + transitivity (sumL LJ (fun j => br l j * br j n - bi l j * bi j n) *
        (pr k n * pr k l + pi_ k n * pi_ k l) +
        sumL LJ (fun j => br l j * bi j n + bi l j * br j n) *
        (pi_ k l * pr k n - pr k l * pi_ k n)).
      { rewrite <- !sumL_scale_r, <- sumL_plus. reflexivity. }
      rewrite (Hre l n Hl Hn), (Him l n Hl Hn). ring.
  - unfold qc_dJ.
    rewrite (sumL_delta J eqJ LJ l (fun n => pr k n * pr k l + pi_ k n * pi_ k l) LJ_nodup Hl).
    ring.
Qed.

(** A complex vector on I x J, read as a real vector on (bool x I) x J: the
    first coordinate picks the real part (false) or the imaginary part
    (true). *)
Definition qc_lift (xr xi : I -> J -> R) (bk : bool * I) (j : J) : R :=
  if fst bk then xi (snd bk) j else xr (snd bk) j.

Definition qc_LB : list (bool * I) := list_prod [false; true] LI.

Lemma qc_dot_lift : forall xr xi yr yi,
  qc_dot xr xi yr yi = qs_dot (bool * I) J qc_LB LJ (qc_lift xr xi) (qc_lift yr yi).
Proof.
  intros xr xi yr yi. unfold qc_dot, qs_dot, qc_LB. symmetry.
  transitivity (sumL (list_prod [false; true] LI) (fun p =>
    (fun b k => sumL LJ (fun j => qc_lift xr xi (b, k) j * qc_lift yr yi (b, k) j)) (fst p) (snd p))).
  { apply sumL_ext. intros [b k] _. reflexivity. }
  rewrite (sumL_prod bool I [false; true] LI
    (fun b k => sumL LJ (fun j => qc_lift xr xi (b, k) j * qc_lift yr yi (b, k) j))).
  rewrite !sumL_cons, sumL_nil. unfold qc_lift. cbn [fst snd].
  rewrite Rplus_0_r, <- sumL_plus. apply sumL_ext. intros k _.
  rewrite <- sumL_plus. reflexivity.
Qed.

(** A quantum strategy with complex amplitudes. *)
Record qc_strategy : Type := {
  qc_pr : I -> J -> R; qc_pi : I -> J -> R;
  qc_A0r : I -> I -> R; qc_A0i : I -> I -> R;
  qc_A1r : I -> I -> R; qc_A1i : I -> I -> R;
  qc_B0r : J -> J -> R; qc_B0i : J -> J -> R;
  qc_B1r : J -> J -> R; qc_B1i : J -> J -> R
}.

Definition qc_valid (s : qc_strategy) : Prop :=
  qc_unit (qc_pr s) (qc_pi s) /\
  qc_obsI (qc_A0r s) (qc_A0i s) /\ qc_obsI (qc_A1r s) (qc_A1i s) /\
  qc_obsJ (qc_B0r s) (qc_B0i s) /\ qc_obsJ (qc_B1r s) (qc_B1i s).

Definition qc_S (s : qc_strategy) : R :=
  let c := fun ar ai br bi => qc_corr (qc_pr s) (qc_pi s) ar ai br bi in
  c (qc_A0r s) (qc_A0i s) (qc_B0r s) (qc_B0i s) + c (qc_A0r s) (qc_A0i s) (qc_B1r s) (qc_B1i s) +
  c (qc_A1r s) (qc_A1i s) (qc_B0r s) (qc_B0i s) - c (qc_A1r s) (qc_A1i s) (qc_B1r s) (qc_B1i s).

(** Tsirelson's bound for every strategy with complex amplitudes. *)
Theorem qc_tsirelson : forall s, qc_valid s -> qc_S s * qc_S s <= 8.
Proof.
  intros s [Hu [HA0 [HA1 [HB0 HB1]]]].
  pose proof HA0 as [HA0s [HA0a _]]. pose proof HA1 as [HA1s [HA1a _]].
  unfold qc_S. cbv zeta.
  rewrite !qc_corr_dot by assumption. rewrite !qc_dot_lift.
  set (pr := qc_pr s) in *. set (pi_ := qc_pi s) in *.
  apply qc_four_vectors; rewrite <- qc_dot_lift.
  - apply qc_uvec_unit; assumption.
  - apply qc_uvec_unit; assumption.
  - apply qc_vvec_unit; assumption.
  - apply qc_vvec_unit; assumption.
Qed.

(** * The level-1 moment matrix of a complex strategy *)

(** The five vectors psi, (A0 (x) 1) psi, (A1 (x) 1) psi, (1 (x) B0) psi and
    (1 (x) B1) psi, each read as a real vector on (bool x I) x J. The
    moment matrix holds the real parts of their inner products. *)
Definition qc_vec_n (s : qc_strategy) (n : nat) : bool * I -> J -> R :=
  let pr := qc_pr s in let pi_ := qc_pi s in
  match n with
  | 0%nat => qc_lift pr pi_
  | 1%nat => qc_lift (qc_ur (qc_A0r s) (qc_A0i s) pr pi_) (qc_ui (qc_A0r s) (qc_A0i s) pr pi_)
  | 2%nat => qc_lift (qc_ur (qc_A1r s) (qc_A1i s) pr pi_) (qc_ui (qc_A1r s) (qc_A1i s) pr pi_)
  | 3%nat => qc_lift (qc_vr (qc_B0r s) (qc_B0i s) pr pi_) (qc_vi (qc_B0r s) (qc_B0i s) pr pi_)
  | _ => qc_lift (qc_vr (qc_B1r s) (qc_B1i s) pr pi_) (qc_vi (qc_B1r s) (qc_B1i s) pr pi_)
  end.

Definition qc_npa (s : qc_strategy) : NPAMomentMatrix :=
  qc_gram (bool * I) J qc_LB LJ (qc_vec_n s).

(** Its correlators are the strategy's correlators. *)
Lemma qc_npa_correlators : forall s, qc_valid s ->
  let c := fun ar ai br bi => qc_corr (qc_pr s) (qc_pi s) ar ai br bi in
  npa_E00 (qc_npa s) = c (qc_A0r s) (qc_A0i s) (qc_B0r s) (qc_B0i s) /\
  npa_E01 (qc_npa s) = c (qc_A0r s) (qc_A0i s) (qc_B1r s) (qc_B1i s) /\
  npa_E10 (qc_npa s) = c (qc_A1r s) (qc_A1i s) (qc_B0r s) (qc_B0i s) /\
  npa_E11 (qc_npa s) = c (qc_A1r s) (qc_A1i s) (qc_B1r s) (qc_B1i s).
Proof.
  intros s [_ [[HA0s [HA0a _]] [[HA1s [HA1a _]] _]]] c. unfold c, qc_npa, qc_vec_n. cbn.
  rewrite !qc_corr_dot by assumption. rewrite !qc_dot_lift. repeat split.
Qed.

(** NPA's level-1 condition holds for every strategy with complex
    amplitudes in finite dimension. *)
Theorem qc_npa_psd : forall s, qc_valid s -> npa_psd (qc_npa s).
Proof.
  intros s [Hu [HA0 [HA1 [HB0 HB1]]]]. unfold qc_npa. apply qc_gram_psd.
  intros n Hn. destruct n as [| [| [| [| [| n]]]]]; [| | | | | lia];
    unfold qc_vec_n; cbv zeta; rewrite <- qc_dot_lift.
  - exact Hu.
  - apply qc_uvec_unit; assumption.
  - apply qc_uvec_unit; assumption.
  - apply qc_vvec_unit; assumption.
  - apply qc_vvec_unit; assumption.
Qed.

(** A real strategy is a complex one with zero imaginary parts, and it keeps
    its correlators. *)
Definition qc_of_real (s : qs_strategy I J) : qc_strategy :=
  {| qc_pr := qs_psi I J s; qc_pi := fun _ _ => 0;
     qc_A0r := qs_A0 I J s; qc_A0i := fun _ _ => 0;
     qc_A1r := qs_A1 I J s; qc_A1i := fun _ _ => 0;
     qc_B0r := qs_B0 I J s; qc_B0i := fun _ _ => 0;
     qc_B1r := qs_B1 I J s; qc_B1i := fun _ _ => 0 |}.

Lemma qc_corr_real : forall pr ar br,
  qc_corr pr (fun _ _ => 0) ar (fun _ _ => 0) br (fun _ _ => 0) = qs_corr I J LI LJ pr ar br.
Proof.
  intros pr ar br. unfold qc_corr, qs_corr.
  apply sumL_ext. intros i _. apply sumL_ext. intros j _.
  apply sumL_ext. intros k _. apply sumL_ext. intros l _. unfold qc_re4. ring.
Qed.

Lemma qc_obsI_real : forall A, qs_obsI I eqI LI A -> qc_obsI A (fun _ _ => 0).
Proof.
  intros A [Hs Hinv]. unfold qc_obsI. repeat split.
  - exact Hs.
  - intros. lra.
  - intros i m Hi Hm. transitivity (sumL LI (fun k => A i k * A k m)).
    + apply sumL_ext. intros. ring.
    + rewrite (Hinv i m Hi Hm). reflexivity.
  - intros. transitivity (sumL LI (fun _ : I => 0)); [| apply sumL_zero]. apply sumL_ext. intros. ring.
Qed.

Lemma qc_obsJ_real : forall B, qs_obsJ J eqJ LJ B -> qc_obsJ B (fun _ _ => 0).
Proof.
  intros B [Hs Hinv]. unfold qc_obsJ. repeat split.
  - exact Hs.
  - intros. lra.
  - intros j m Hj Hm. transitivity (sumL LJ (fun l => B j l * B l m)).
    + apply sumL_ext. intros. ring.
    + rewrite (Hinv j m Hj Hm). reflexivity.
  - intros. transitivity (sumL LJ (fun _ : J => 0)); [| apply sumL_zero]. apply sumL_ext. intros. ring.
Qed.

Theorem qc_of_real_valid : forall s,
  qs_valid I J eqI eqJ LI LJ s ->
  qc_valid (qc_of_real s) /\ qc_S (qc_of_real s) = qs_S I J LI LJ s.
Proof.
  intros s [Hu [HA0 [HA1 [HB0 HB1]]]]. split.
  - unfold qc_valid, qc_of_real. cbn [qc_pr qc_pi qc_A0r qc_A0i
      qc_A1r qc_A1i qc_B0r qc_B0i qc_B1r qc_B1i].
    refine (conj _ (conj (qc_obsI_real _ HA0) (conj (qc_obsI_real _ HA1)
      (conj (qc_obsJ_real _ HB0) (qc_obsJ_real _ HB1))))).
    unfold qc_unit. rewrite <- Hu. unfold qs_unit. apply sumL_ext. intros. apply sumL_ext. intros. ring.
  - unfold qc_S, qs_S, qc_of_real. cbn [qc_pr qc_pi qc_A0r qc_A0i
      qc_A1r qc_A1i qc_B0r qc_B0i qc_B1r qc_B1i]. rewrite !qc_corr_real. reflexivity.
Qed.

End Complex.

(** The bound is reached: the two-qubit strategy of QuantumStrategies.v,
    read with complex amplitudes, is valid and has S = 2 sqrt 2. *)
Theorem qc_tsirelson_reached :
  let s := qc_of_real bool bool qs_bell_strategy in
  qc_valid bool bool Bool.bool_dec Bool.bool_dec qs_bits qs_bits s /\
  qc_S bool bool qs_bits qs_bits s = 2 * sqrt 2.
Proof.
  destruct qs_tsirelson_reached as [Hv [_ [_ [_ [_ HS]]]]].
  destruct (qc_of_real_valid bool bool Bool.bool_dec Bool.bool_dec qs_bits qs_bits
    qs_bell_strategy Hv) as [Hcv HcS].
  split; [exact Hcv | rewrite HcS; exact HS].
Qed.

Print Assumptions qc_corr_dot.
Print Assumptions qc_uvec_unit.
Print Assumptions qc_vvec_unit.
Print Assumptions qc_tsirelson.
Print Assumptions qc_of_real_valid.
Print Assumptions qc_npa_correlators.
Print Assumptions qc_npa_psd.
Print Assumptions qc_gram_psd.
Print Assumptions qc_tsirelson_reached.
