(** QuantumStrategies: quantum strategies for the CHSH game, built and
    bounded.

    A strategy is a unit vector psi of a finite-dimensional real joint space
    (rows indexed by a list LI, columns by a list LJ, both without repeats)
    and, on each side, two observables: real symmetric matrices that square
    to the identity. The correlator of A and B is <psi, (A (x) B) psi>.

    - Every correlator is an inner product of two unit vectors,
      (A (x) 1) psi and (1 (x) B) psi ([qs_corr_dot], [qs_uvec_unit],
      [qs_vvec_unit]).
    - Tsirelson's bound: every strategy has S^2 <= 8, where
      S = E00 + E01 + E10 - E11 ([qs_tsirelson]).
    - The bound is reached: on two qubits, the state (|00> + |11>)/sqrt 2 with
      A0 = Z, A1 = X, B0 = (Z + X)/sqrt 2 and B1 = (Z - X)/sqrt 2 is a valid
      strategy whose correlators are 1/sqrt 2, 1/sqrt 2, 1/sqrt 2 and
      -1/sqrt 2, so S = 2 sqrt 2 ([qs_tsirelson_reached]).
    - Every deterministic plan is a quantum strategy: for signs a0, a1, b0, b1
      in {-1, 1}, a product state with observables a_x times the identity and
      b_y times the identity is valid and has correlators a_x b_y
      ([qs_deterministic_plan]).
    - The NPA reading at level 1: the moment matrix of every strategy (its
      marginals, its correlators and its two self-correlations, in the record
      of NPAMomentMatrix.v) passes the book's own test npa_psd
      ([qs_npa_psd]).

    Amplitudes are real. *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics. No definition or theorem here mentions a certification
   system, a ledger or a machine step; it imports only the machine-free
   quantum files ConstructivePSD.v and NPAMomentMatrix.v and the sums of
   FiniteSums.v.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. The standalone boundary is stated here rather than inferred from
   an import. *)

From Coq Require Import List Reals Lra Psatz Bool.
Import ListNotations.
From Kernel Require Import ConstructivePSD.
From Kernel Require Import NPAMomentMatrix.
From Kernel Require Import FiniteSums.
Open Scope R_scope.


Section Strategy.

Variables (I J : Type).
Variable eqI : forall a b : I, {a = b} + {a <> b}.
Variable eqJ : forall a b : J, {a = b} + {a <> b}.
Variables (LI : list I) (LJ : list J).
Hypothesis LI_nodup : NoDup LI.
Hypothesis LJ_nodup : NoDup LJ.

Definition qs_deltaI (i m : I) : R := if eqI i m then 1 else 0.
Definition qs_deltaJ (j m : J) : R := if eqJ j m then 1 else 0.

(** A local observable: a real symmetric matrix that squares to the identity. *)
Definition qs_obsI (A : I -> I -> R) : Prop :=
  (forall i k, A i k = A k i) /\
  (forall i m, In i LI -> In m LI -> sumL LI (fun k => A i k * A k m) = qs_deltaI i m).
Definition qs_obsJ (B : J -> J -> R) : Prop :=
  (forall j l, B j l = B l j) /\
  (forall j m, In j LJ -> In m LJ -> sumL LJ (fun l => B j l * B l m) = qs_deltaJ j m).

(** A unit vector of the joint space. *)
Definition qs_unit (psi : I -> J -> R) : Prop :=
  sumL LI (fun i => sumL LJ (fun j => psi i j * psi i j)) = 1.

(** The correlator <psi, (A (x) B) psi>. *)
Definition qs_corr (psi : I -> J -> R) (A : I -> I -> R) (B : J -> J -> R) : R :=
  sumL LI (fun i => sumL LJ (fun j => sumL LI (fun k => sumL LJ (fun l =>
    psi i j * A i k * B j l * psi k l)))).

(** Inner product on the joint space, and the two vectors (A (x) 1) psi and
    (1 (x) B) psi. *)
Definition qs_dot (u v : I -> J -> R) : R := sumL LI (fun k => sumL LJ (fun j => u k j * v k j)).
Definition qs_uvec (A : I -> I -> R) (psi : I -> J -> R) (k : I) (j : J) : R :=
  sumL LI (fun i => A i k * psi i j).
Definition qs_vvec (B : J -> J -> R) (psi : I -> J -> R) (k : I) (j : J) : R :=
  sumL LJ (fun l => B j l * psi k l).

Lemma qs_corr_dot : forall psi A B,
  qs_corr psi A B = qs_dot (qs_uvec A psi) (qs_vvec B psi).
Proof.
  intros psi A B. unfold qs_corr, qs_dot, qs_uvec, qs_vvec.
  (* right side: sum_k sum_j (sum_i A i k psi i j) (sum_l B j l psi k l) *)
  transitivity (sumL LI (fun k => sumL LJ (fun j => sumL LI (fun i => sumL LJ (fun l =>
    psi i j * A i k * B j l * psi k l))))).
  - etransitivity.
    { apply sumL_ext. intros i _. apply (sumL_swap J I LJ LI). }
    etransitivity.
    { apply (sumL_swap I I LI LI). }
    apply sumL_ext. intros k _. apply (sumL_swap I J LI LJ).
  - apply sumL_ext. intros k _. apply sumL_ext. intros j _.
    rewrite sumL_mult. apply sumL_ext. intros i _. apply sumL_ext. intros l _. ring.
Qed.

Lemma qs_uvec_unit : forall A psi, qs_obsI A -> qs_unit psi ->
  qs_dot (qs_uvec A psi) (qs_uvec A psi) = 1.
Proof.
  intros A psi [Hsym Hinv] Hunit. unfold qs_dot, qs_uvec, qs_unit in *.
  transitivity (sumL LJ (fun j => sumL LI (fun i => psi i j * psi i j))).
  - (* expand the product of the two inner sums *)
    transitivity (sumL LI (fun k => sumL LJ (fun j => sumL LI (fun i => sumL LI (fun m =>
      A i k * psi i j * (A m k * psi m j)))))).
    { apply sumL_ext. intros k _. apply sumL_ext. intros j _. apply sumL_mult. }
    (* move k innermost *)
    etransitivity. { apply (sumL_swap I J LI LJ). }
    apply sumL_ext. intros j _.
    etransitivity. { apply (sumL_swap I I LI LI). }
    apply sumL_ext. intros i Hi.
    etransitivity. { apply (sumL_swap I I LI LI). }
    transitivity (sumL LI (fun m => qs_deltaI i m * (psi m j * psi i j))).
    + apply sumL_ext. intros m Hm.
      rewrite <- (Hinv i m Hi Hm).
      transitivity (sumL LI (fun k => A i k * A k m * (psi m j * psi i j))).
      * apply sumL_ext. intros k _. rewrite (Hsym m k). ring.
      * apply sumL_scale_r.
    + unfold qs_deltaI. rewrite (sumL_delta I eqI LI i (fun m => psi m j * psi i j) LI_nodup Hi).
      reflexivity.
  - rewrite sumL_swap. exact Hunit.
Qed.

Lemma qs_vvec_unit : forall B psi, qs_obsJ B -> qs_unit psi ->
  qs_dot (qs_vvec B psi) (qs_vvec B psi) = 1.
Proof.
  intros B psi [Hsym Hinv] Hunit. unfold qs_dot, qs_vvec, qs_unit in *.
  rewrite <- Hunit. apply sumL_ext. intros k _.
  transitivity (sumL LJ (fun j => sumL LJ (fun l => sumL LJ (fun n =>
    B j l * psi k l * (B j n * psi k n))))).
  { apply sumL_ext. intros j _. apply sumL_mult. }
  etransitivity. { apply (sumL_swap J J LJ LJ). }
  apply sumL_ext. intros l Hl.
  etransitivity. { apply (sumL_swap J J LJ LJ). }
  transitivity (sumL LJ (fun n => qs_deltaJ l n * (psi k n * psi k l))).
  - apply sumL_ext. intros n Hn.
    rewrite <- (Hinv l n Hl Hn).
    transitivity (sumL LJ (fun j => B l j * B j n * (psi k n * psi k l))).
    + apply sumL_ext. intros j _. rewrite (Hsym j l). ring.
    + apply sumL_scale_r.
  - unfold qs_deltaJ. rewrite (sumL_delta J eqJ LJ l (fun n => psi k n * psi k l) LJ_nodup Hl).
    ring.
Qed.

(** Bilinearity and Cauchy-Schwarz for the joint inner product. *)
Lemma qs_dot_plus_r : forall u v w, qs_dot u (fun k j => v k j + w k j) = qs_dot u v + qs_dot u w.
Proof.
  intros u v w. unfold qs_dot. rewrite <- sumL_plus. apply sumL_ext. intros k _.
  rewrite <- sumL_plus. apply sumL_ext. intros j _. ring.
Qed.

Lemma qs_dot_minus_r : forall u v w, qs_dot u (fun k j => v k j - w k j) = qs_dot u v - qs_dot u w.
Proof.
  intros u v w. unfold qs_dot. rewrite <- sumL_minus. apply sumL_ext. intros k _.
  rewrite <- sumL_minus. apply sumL_ext. intros j _. ring.
Qed.

Lemma qs_dot_flat : forall u v,
  qs_dot u v = sumL (list_prod LI LJ) (fun p => u (fst p) (snd p) * v (fst p) (snd p)).
Proof. intros u v. unfold qs_dot. symmetry. apply (sumL_prod I J LI LJ (fun k j => u k j * v k j)). Qed.

Lemma qs_dot_cs : forall u v, qs_dot u v * qs_dot u v <= qs_dot u u * qs_dot v v.
Proof.
  intros u v. rewrite !qs_dot_flat.
  apply (sumL_cauchy_schwarz _ (list_prod LI LJ) (fun p => u (fst p) (snd p)) (fun p => v (fst p) (snd p))).
Qed.

Lemma qs_dot_nonneg : forall u, 0 <= qs_dot u u.
Proof.
  intro u. unfold qs_dot. apply sumL_nonneg. intros k _. apply sumL_nonneg. intros j _. apply sq_nonneg.
Qed.

Lemma qs_dot_sum_diff : forall v w,
  qs_dot (fun k j => v k j + w k j) (fun k j => v k j + w k j) +
  qs_dot (fun k j => v k j - w k j) (fun k j => v k j - w k j) = 2 * (qs_dot v v + qs_dot w w).
Proof.
  intros v w. unfold qs_dot. rewrite <- sumL_plus, <- sumL_plus, <- sumL_scale_l.
  apply sumL_ext. intros k _. rewrite <- sumL_plus, <- sumL_plus, <- sumL_scale_l.
  apply sumL_ext. intros j _. ring.
Qed.

(** A quantum strategy: a unit state and two observables on each side. *)
Record qs_strategy : Type := {
  qs_psi : I -> J -> R;
  qs_A0 : I -> I -> R; qs_A1 : I -> I -> R;
  qs_B0 : J -> J -> R; qs_B1 : J -> J -> R
}.

Definition qs_valid (s : qs_strategy) : Prop :=
  qs_unit (qs_psi s) /\ qs_obsI (qs_A0 s) /\ qs_obsI (qs_A1 s) /\
  qs_obsJ (qs_B0 s) /\ qs_obsJ (qs_B1 s).

Definition qs_S (s : qs_strategy) : R :=
  qs_corr (qs_psi s) (qs_A0 s) (qs_B0 s) + qs_corr (qs_psi s) (qs_A0 s) (qs_B1 s) +
  qs_corr (qs_psi s) (qs_A1 s) (qs_B0 s) - qs_corr (qs_psi s) (qs_A1 s) (qs_B1 s).

(** Tsirelson's bound for every strategy of this kind. *)
Theorem qs_tsirelson : forall s, qs_valid s -> qs_S s * qs_S s <= 8.
Proof.
  intros s [Hu [HA0 [HA1 [HB0 HB1]]]]. unfold qs_S. rewrite !qs_corr_dot.
  set (psi := qs_psi s) in *.
  set (u0 := qs_uvec (qs_A0 s) psi). set (u1 := qs_uvec (qs_A1 s) psi).
  set (v0 := qs_vvec (qs_B0 s) psi). set (v1 := qs_vvec (qs_B1 s) psi).
  assert (Hu0 : qs_dot u0 u0 = 1) by (apply qs_uvec_unit; assumption).
  assert (Hu1 : qs_dot u1 u1 = 1) by (apply qs_uvec_unit; assumption).
  assert (Hv0 : qs_dot v0 v0 = 1) by (apply qs_vvec_unit; assumption).
  assert (Hv1 : qs_dot v1 v1 = 1) by (apply qs_vvec_unit; assumption).
  set (wp := fun k j => v0 k j + v1 k j). set (wm := fun k j => v0 k j - v1 k j).
  assert (EX : qs_dot u0 v0 + qs_dot u0 v1 = qs_dot u0 wp) by (unfold wp; rewrite qs_dot_plus_r; reflexivity).
  assert (EY : qs_dot u1 v0 - qs_dot u1 v1 = qs_dot u1 wm) by (unfold wm; rewrite qs_dot_minus_r; reflexivity).
  set (X := qs_dot u0 wp). set (Y := qs_dot u1 wm).
  assert (HX : X * X <= qs_dot wp wp).
  { pose proof (qs_dot_cs u0 wp) as H. rewrite Hu0, Rmult_1_l in H. exact H. }
  assert (HY : Y * Y <= qs_dot wm wm).
  { pose proof (qs_dot_cs u1 wm) as H. rewrite Hu1, Rmult_1_l in H. exact H. }
  assert (HPQ : qs_dot wp wp + qs_dot wm wm = 4).
  { unfold wp, wm. rewrite qs_dot_sum_diff, Hv0, Hv1. ring. }
  replace (qs_dot u0 v0 + qs_dot u0 v1 + qs_dot u1 v0 - qs_dot u1 v1) with (X + Y) by (unfold X, Y; lra).
  pose proof (sq_nonneg (X - Y)) as HD.
  assert (E : (X + Y) * (X + Y) = 2 * (X * X) + 2 * (Y * Y) - (X - Y) * (X - Y)) by ring.
  rewrite E. nra.
Qed.

End Strategy.

(** * Two qubits *)

Definition qs_bits : list bool := [false; true].

Lemma qs_bits_nodup : NoDup qs_bits.
Proof. constructor; [intros [H | []]; discriminate | constructor; [intros [] | constructor]]. Qed.

Definition qs_r : R := / sqrt 2.

Lemma qs_r_sq : qs_r * qs_r = / 2.
Proof.
  unfold qs_r. rewrite <- Rinv_mult. rewrite sqrt_sqrt by lra. reflexivity.
Qed.

Definition qs_bell (i j : bool) : R := if Bool.eqb i j then qs_r else 0.
Definition qs_Z (i k : bool) : R := if Bool.eqb i k then (if i then -1 else 1) else 0.
Definition qs_X (i k : bool) : R := if Bool.eqb i k then 0 else 1.
Definition qs_Bp (i k : bool) : R := qs_r * (qs_Z i k + qs_X i k).
Definition qs_Bm (i k : bool) : R := qs_r * (qs_Z i k - qs_X i k).

Definition qs_bell_strategy : qs_strategy bool bool :=
  {| qs_psi := qs_bell; qs_A0 := qs_Z; qs_A1 := qs_X; qs_B0 := qs_Bp; qs_B1 := qs_Bm |}.

Ltac qs_bits_compute :=
  repeat match goal with b : bool |- _ => destruct b end;
  cbn [sumL fold_right qs_bits qs_bell qs_Z qs_X qs_Bp qs_Bm qs_deltaI qs_deltaJ Bool.eqb Bool.bool_dec
       sumbool_rec sumbool_rect];
  try (pose proof qs_r_sq; nra).

Lemma qs_bell_valid : qs_valid bool bool Bool.bool_dec Bool.bool_dec qs_bits qs_bits qs_bell_strategy.
Proof.
  pose proof qs_r_sq as Hr.
  unfold qs_valid, qs_unit, qs_obsI, qs_obsJ. cbn [qs_psi qs_A0 qs_A1 qs_B0 qs_B1 qs_bell_strategy].
  repeat split; intros; unfold qs_deltaI, qs_deltaJ, qs_bits in *; simpl in *;
    repeat match goal with H : _ \/ _ |- _ => destruct H as [<- | H] | H : False |- _ => destruct H end;
    repeat match goal with b : bool |- _ => destruct b end;
    unfold qs_bell, qs_Bp, qs_Bm, qs_Z, qs_X; simpl; nra.
Qed.

Theorem qs_tsirelson_reached :
  qs_valid bool bool Bool.bool_dec Bool.bool_dec qs_bits qs_bits qs_bell_strategy /\
  qs_corr bool bool qs_bits qs_bits qs_bell qs_Z qs_Bp = / sqrt 2 /\
  qs_corr bool bool qs_bits qs_bits qs_bell qs_Z qs_Bm = / sqrt 2 /\
  qs_corr bool bool qs_bits qs_bits qs_bell qs_X qs_Bp = / sqrt 2 /\
  qs_corr bool bool qs_bits qs_bits qs_bell qs_X qs_Bm = - / sqrt 2 /\
  qs_S bool bool qs_bits qs_bits qs_bell_strategy = 2 * sqrt 2.
Proof.
  pose proof qs_r_sq as Hr.
  assert (Hs : sqrt 2 * sqrt 2 = 2) by (apply sqrt_sqrt; lra).
  assert (Hpos : 0 < sqrt 2) by (apply sqrt_lt_R0; lra).
  split; [exact qs_bell_valid |].
  unfold qs_S, qs_corr, qs_bits. cbn [qs_psi qs_A0 qs_A1 qs_B0 qs_B1 qs_bell_strategy].
  unfold qs_bell, qs_Bp, qs_Bm, qs_Z, qs_X. simpl. fold qs_r.
  assert (Hr3 : qs_r * qs_r * qs_r = qs_r * / 2) by (rewrite Hr; ring).
  assert (Hval : / sqrt 2 * 2 = sqrt 2).
  { apply (Rmult_eq_reg_r (sqrt 2)); [| lra]. rewrite Rmult_assoc, (Rmult_comm 2), <- Rmult_assoc.
    rewrite Rinv_l by lra. lra. }
  fold qs_r in Hval.
  repeat split; ring_simplify; try rewrite Hr3; lra.
Qed.

(** * Deterministic plans *)

Definition qs_zero_state (i j : bool) : R := if i then 0 else if j then 0 else 1.
Definition qs_sign (a : R) (i k : bool) : R := if Bool.eqb i k then a else 0.

Definition qs_plan (a0 a1 b0 b1 : R) : qs_strategy bool bool :=
  {| qs_psi := qs_zero_state; qs_A0 := qs_sign a0; qs_A1 := qs_sign a1;
     qs_B0 := qs_sign b0; qs_B1 := qs_sign b1 |}.

Theorem qs_deterministic_plan : forall a0 a1 b0 b1 : R,
  a0 * a0 = 1 -> a1 * a1 = 1 -> b0 * b0 = 1 -> b1 * b1 = 1 ->
  qs_valid bool bool Bool.bool_dec Bool.bool_dec qs_bits qs_bits (qs_plan a0 a1 b0 b1) /\
  qs_corr bool bool qs_bits qs_bits qs_zero_state (qs_sign a0) (qs_sign b0) = a0 * b0 /\
  qs_corr bool bool qs_bits qs_bits qs_zero_state (qs_sign a0) (qs_sign b1) = a0 * b1 /\
  qs_corr bool bool qs_bits qs_bits qs_zero_state (qs_sign a1) (qs_sign b0) = a1 * b0 /\
  qs_corr bool bool qs_bits qs_bits qs_zero_state (qs_sign a1) (qs_sign b1) = a1 * b1.
Proof.
  intros a0 a1 b0 b1 H0 H1 H2 H3.
  split.
  - unfold qs_valid, qs_unit, qs_obsI, qs_obsJ. cbn [qs_psi qs_A0 qs_A1 qs_B0 qs_B1 qs_plan].
    repeat split; intros; unfold qs_deltaI, qs_deltaJ, qs_bits in *; simpl in *;
      repeat match goal with H : _ \/ _ |- _ => destruct H as [<- | H] | H : False |- _ => destruct H end;
      repeat match goal with b : bool |- _ => destruct b end;
      unfold qs_zero_state, qs_sign; simpl; lra.
  - unfold qs_corr, qs_bits, qs_zero_state, qs_sign. simpl. repeat split; ring.
Qed.

(** * The level-1 moment matrix of a strategy is positive semidefinite *)

Section NPA.

Variables (I J : Type).
Variable eqI : forall a b : I, {a = b} + {a <> b}.
Variable eqJ : forall a b : J, {a = b} + {a <> b}.
Variables (LI : list I) (LJ : list J).
Hypothesis LI_nodup : NoDup LI.
Hypothesis LJ_nodup : NoDup LJ.

Let dot := qs_dot I J LI LJ.

Lemma qs_dot_sym : forall u v, dot u v = dot v u.
Proof. intros u v. unfold dot, qs_dot. apply sumL_ext. intros k _. apply sumL_ext. intros j _. ring. Qed.

(** The five vectors whose inner products fill the moment matrix:
    psi, (A0 (x) 1) psi, (A1 (x) 1) psi, (1 (x) B0) psi, (1 (x) B1) psi. *)
Definition qs_vec_n (s : qs_strategy I J) (n : nat) : I -> J -> R :=
  match n with
  | 0%nat => qs_psi I J s
  | 1%nat => qs_uvec I J LI (qs_A0 I J s) (qs_psi I J s)
  | 2%nat => qs_uvec I J LI (qs_A1 I J s) (qs_psi I J s)
  | 3%nat => qs_vvec I J LJ (qs_B0 I J s) (qs_psi I J s)
  | _ => qs_vvec I J LJ (qs_B1 I J s) (qs_psi I J s)
  end.

Definition qs_vec (s : qs_strategy I J) (t : Fin5) : I -> J -> R := qs_vec_n s (fin_to_nat t).

Definition qs_npa (s : qs_strategy I J) : NPAMomentMatrix := {|
  npa_EA0 := dot (qs_vec_n s 0) (qs_vec_n s 1);
  npa_EA1 := dot (qs_vec_n s 0) (qs_vec_n s 2);
  npa_EB0 := dot (qs_vec_n s 0) (qs_vec_n s 3);
  npa_EB1 := dot (qs_vec_n s 0) (qs_vec_n s 4);
  npa_E00 := dot (qs_vec_n s 1) (qs_vec_n s 3);
  npa_E01 := dot (qs_vec_n s 1) (qs_vec_n s 4);
  npa_E10 := dot (qs_vec_n s 2) (qs_vec_n s 3);
  npa_E11 := dot (qs_vec_n s 2) (qs_vec_n s 4);
  npa_rho_AA := dot (qs_vec_n s 1) (qs_vec_n s 2);
  npa_rho_BB := dot (qs_vec_n s 3) (qs_vec_n s 4);
|}.

(** Its correlators are the strategy's correlators. *)
Lemma qs_npa_correlators : forall s,
  npa_E00 (qs_npa s) = qs_corr I J LI LJ (qs_psi I J s) (qs_A0 I J s) (qs_B0 I J s) /\
  npa_E01 (qs_npa s) = qs_corr I J LI LJ (qs_psi I J s) (qs_A0 I J s) (qs_B1 I J s) /\
  npa_E10 (qs_npa s) = qs_corr I J LI LJ (qs_psi I J s) (qs_A1 I J s) (qs_B0 I J s) /\
  npa_E11 (qs_npa s) = qs_corr I J LI LJ (qs_psi I J s) (qs_A1 I J s) (qs_B1 I J s).
Proof. intro s. cbn. rewrite !qs_corr_dot. repeat split. Qed.

Lemma qs_vec_unit : forall s n, qs_valid I J eqI eqJ LI LJ s -> dot (qs_vec_n s n) (qs_vec_n s n) = 1.
Proof.
  intros s n [Hu [HA0 [HA1 [HB0 HB1]]]].
  destruct n as [| [| [| [| n]]]]; simpl; unfold dot.
  - exact Hu.
  - apply (qs_uvec_unit I J eqI LI LJ LI_nodup); assumption.
  - apply (qs_uvec_unit I J eqI LI LJ LI_nodup); assumption.
  - apply (qs_vvec_unit I J eqJ LI LJ LJ_nodup); assumption.
  - apply (qs_vvec_unit I J eqJ LI LJ LJ_nodup); assumption.
Qed.

Lemma qs_npa_entries : forall s, qs_valid I J eqI eqJ LI LJ s ->
  forall i j : Fin5, nat_matrix_to_fin5 (npa_to_matrix (qs_npa s)) i j = dot (qs_vec s i) (qs_vec s j).
Proof.
  intros s Hv i j. unfold nat_matrix_to_fin5, qs_vec, fin_to_nat.
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
  first [ symmetry; apply (qs_vec_unit s 0 Hv) | symmetry; apply (qs_vec_unit s 1 Hv)
        | symmetry; apply (qs_vec_unit s 2 Hv) | symmetry; apply (qs_vec_unit s 3 Hv)
        | symmetry; apply (qs_vec_unit s 4 Hv) | reflexivity | apply qs_dot_sym ].
Qed.

Definition qs_fin5_list : list Fin5 :=
  [Fin.F1; Fin.FS Fin.F1; Fin.FS (Fin.FS Fin.F1); Fin.FS (Fin.FS (Fin.FS Fin.F1));
   Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))].

Lemma qs_sum_fin5 : forall f, sum_fin5 f = sumL qs_fin5_list f.
Proof. intro f. unfold sum_fin5, qs_fin5_list. simpl. ring. Qed.

(** A combination of vectors: its squared length is the double sum of the
    coefficients against the inner products. *)
Lemma qs_dot_combination : forall (T : list Fin5) (c : Fin5 -> R) (w : Fin5 -> I -> J -> R),
  dot (fun k j => sumL T (fun t => c t * w t k j)) (fun k j => sumL T (fun t => c t * w t k j)) =
  sumL T (fun t => sumL T (fun t' => c t * dot (w t) (w t') * c t')).
Proof.
  intros T c w. unfold dot, qs_dot.
  transitivity (sumL LI (fun k => sumL LJ (fun j => sumL T (fun t => sumL T (fun t' =>
    c t * w t k j * (c t' * w t' k j)))))).
  { apply sumL_ext. intros k _. apply sumL_ext. intros j _. apply sumL_mult. }
  etransitivity. { apply sumL_ext. intros k _. apply sumL_swap. }
  etransitivity. { apply sumL_swap. }
  apply sumL_ext. intros t _.
  etransitivity. { apply sumL_ext. intros k _. apply sumL_swap. }
  etransitivity. { apply sumL_swap. }
  apply sumL_ext. intros t' _.
  transitivity ((c t * c t') * sumL LI (fun k => sumL LJ (fun j => w t k j * w t' k j))).
  - rewrite <- sumL_scale_l. apply sumL_ext. intros k _.
    rewrite <- sumL_scale_l. apply sumL_ext. intros j _. ring.
  - ring.
Qed.

Theorem qs_npa_psd : forall s, qs_valid I J eqI eqJ LI LJ s -> npa_psd (qs_npa s).
Proof.
  intros s Hv. unfold npa_psd. split.
  - intros i j. rewrite !(qs_npa_entries s Hv). apply qs_dot_sym.
  - intro v. unfold quad5. rewrite qs_sum_fin5. apply Rle_ge.
    assert (E : sumL qs_fin5_list (fun i => sum_fin5 (fun j =>
                  v i * nat_matrix_to_fin5 (npa_to_matrix (qs_npa s)) i j * v j)) =
                sumL qs_fin5_list (fun i => sumL qs_fin5_list (fun j =>
                  v i * dot (qs_vec s i) (qs_vec s j) * v j))).
    { apply sumL_ext. intros i _. rewrite qs_sum_fin5. apply sumL_ext. intros j _.
      rewrite (qs_npa_entries s Hv). reflexivity. }
    rewrite E, <- qs_dot_combination. apply qs_dot_nonneg.
Qed.

End NPA.

Print Assumptions qs_tsirelson.
Print Assumptions qs_tsirelson_reached.
Print Assumptions qs_deterministic_plan.
Print Assumptions qs_npa_psd.
Print Assumptions qs_npa_correlators.
