(** ArcsineBoundary: the arcsine characterization of the CHSH quantum set.

    For correlators E00, E01, E10, E11 in [-1, 1], write s_xy = asin E_xy.
    The table has a PSD completion (equivalently, by TsirelsonRepresentation.v,
    it is the correlator table of a quantum strategy) if and only if

      |s00 + s01 + s10 - s11| <= pi,   |s00 + s01 - s10 + s11| <= pi,
      |s00 - s01 + s10 + s11| <= pi,   |-s00 + s01 + s10 + s11| <= pi

    ([am_arcsine], [am_quantum_arcsine]). This is the characterization of
    Landau (1988) and Masanes (2003).

    - Necessity: the completion is a Gram matrix of four unit vectors, and
      the angle acos (u . w) obeys the triangle inequality on the sphere
      ([am_sphere_triangle]); each inequality is two triangle steps around
      the cycle a0, b0, a1, b1, with one vector replaced by its antipode for
      the inequalities with pi on the other side.
    - Sufficiency: with theta_xy = acos E_xy, take beta to be the larger of
      |theta00 - theta01| and |theta10 - theta11|. The inequalities put beta
      in the range where two spherical triangles with sides (theta00,
      theta01, beta) and (theta10, theta11, beta) exist
      ([am_triangle_det]); b0 and b1 at angle beta and a0, a1 built on them
      are four unit vectors in R^4 with the given cross inner products
      ([am_sufficient]).
    - The point (3/5, 4/5, 4/5, -3/5) and Tsirelson's point
      (1/sqrt 2, 1/sqrt 2, 1/sqrt 2, -1/sqrt 2) lie on the boundary
      ([am_pythagorean_boundary], [am_tsirelson_boundary]). *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics. No definition or theorem here mentions a certification
   system, a ledger or a machine step; it imports only the finite-sum, PSD
   and quantum-strategy files.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. The standalone boundary is stated here rather than inferred from
   an import. *)

From Coq Require Import List Reals Lra Psatz Lia.
Import ListNotations.
From Kernel Require Import FiniteSums ConstructivePSD NPAMomentMatrix ElliptopeCompletion.
From Kernel Require Import QuantumStrategies TsirelsonRepresentation.
Open Scope R_scope.

(** * Trigonometric facts *)

Lemma am_cos_le : forall x y, 0 <= x -> x <= y -> y <= PI -> cos y <= cos x.
Proof.
  intros x y Hx Hxy Hy. destruct (Req_dec x y) as [<- | Hne]; [lra |].
  left. apply cos_decreasing_1; lra.
Qed.

Lemma am_acos_le : forall x t, 0 <= t <= PI -> -1 <= x <= 1 -> cos t <= x -> acos x <= t.
Proof.
  intros x t Ht Hx Hc. destruct (Rle_dec (acos x) t) as [H | H]; [exact H |].
  exfalso. pose proof (acos_bound x) as Hb.
  assert (cos (acos x) < cos t) by (apply cos_decreasing_1; lra).
  rewrite cos_acos in H0 by exact Hx. lra.
Qed.

Lemma am_cos_PI_minus : forall t, cos (PI - t) = - cos t.
Proof. intro t. rewrite cos_minus, cos_PI, sin_PI. ring. Qed.

Lemma am_acos_opp : forall x, -1 <= x <= 1 -> acos (- x) = PI - acos x.
Proof.
  intros x Hx. pose proof (acos_bound x).
  rewrite <- (cos_acos x Hx) at 1. rewrite <- am_cos_PI_minus. apply acos_cos. lra.
Qed.

Lemma am_cos_abs : forall t, cos (Rabs t) = cos t.
Proof. intro t. unfold Rabs. destruct (Rcase_abs t); [apply cos_neg | reflexivity]. Qed.

Lemma am_sq_sin : forall t, sin t * sin t = 1 - cos t * cos t.
Proof. intro t. pose proof (sin2_cos2 t). unfold Rsqr in H. lra. Qed.

(** Three angles with the third between the difference and the smaller of
    the sum and its complement to 2 pi: the Gram determinant of three unit
    vectors at those angles is nonnegative. *)
Lemma am_triangle_det : forall t1 t2 b,
  0 <= t1 <= PI -> 0 <= t2 <= PI ->
  Rabs (t1 - t2) <= b -> b <= t1 + t2 -> b <= 2 * PI - (t1 + t2) ->
  0 <= (1 - cos t1 * cos t1) * (1 - cos b * cos b) - (cos t2 - cos t1 * cos b) * (cos t2 - cos t1 * cos b).
Proof.
  intros t1 t2 b H1 H2 Hl Hu1 Hu2.
  assert (Hb : 0 <= b <= PI).
  { split; [pose proof (Rabs_pos (t1 - t2)); lra |]. lra. }
  assert (E : (1 - cos t1 * cos t1) * (1 - cos b * cos b) - (cos t2 - cos t1 * cos b) * (cos t2 - cos t1 * cos b) =
              (cos b - cos (t1 + t2)) * (cos (t1 - t2) - cos b)).
  { rewrite cos_plus, cos_minus.
    transitivity ((sin t1 * sin t1) * (sin t2 * sin t2) - (cos b - cos t1 * cos t2) * (cos b - cos t1 * cos t2)).
    - rewrite !am_sq_sin. ring.
    - ring. }
  rewrite E. apply Rmult_le_pos.
  - destruct (Rle_dec (t1 + t2) PI) as [Hs | Hs].
    + pose proof (am_cos_le b (t1 + t2)). lra.
    + assert (C : cos (t1 + t2) = cos (2 * PI - (t1 + t2))).
      { rewrite cos_minus, cos_2PI, sin_2PI. ring. }
      rewrite C. pose proof (am_cos_le b (2 * PI - (t1 + t2))). lra.
  - rewrite <- am_cos_abs. pose proof (am_cos_le (Rabs (t1 - t2)) b (Rabs_pos _) Hl). lra.
Qed.

(** * Unit vectors in R^4 and the angle between them *)

Definition am_dist (u v : nat -> R) : R := acos (tr_inner u v).

Lemma am_inner_sym : forall u v, tr_inner u v = tr_inner v u.
Proof. intros u v. unfold tr_inner. apply sumL_ext. intros. ring. Qed.

Lemma am_comb4 : forall (l : list nat) f1 f2 f3 f4 c1 c2 c3 c4,
  sumL l (fun m => c1 * f1 m + c2 * f2 m + c3 * f3 m + c4 * f4 m) =
  c1 * sumL l f1 + c2 * sumL l f2 + c3 * sumL l f3 + c4 * sumL l f4.
Proof. intros. rewrite !sumL_plus, !sumL_scale_l. reflexivity. Qed.

Lemma am_inner_bound : forall u v, tr_unitv u -> tr_unitv v -> -1 <= tr_inner u v <= 1.
Proof.
  intros u v Hu Hv. pose proof (sumL_cauchy_schwarz nat (tr_idx 4) u v) as H.
  unfold tr_unitv, tr_inner in *. rewrite Hu, Hv in H. nra.
Qed.

(** The angle on the sphere obeys the triangle inequality. *)
Theorem am_sphere_triangle : forall u v w, tr_unitv u -> tr_unitv v -> tr_unitv w ->
  am_dist u w <= am_dist u v + am_dist v w.
Proof.
  intros u v w Hu Hv Hw. unfold am_dist.
  set (p := tr_inner u v). set (q := tr_inner v w). set (r := tr_inner u w).
  pose proof (am_inner_bound u v Hu Hv) as Hp. pose proof (am_inner_bound v w Hv Hw) as Hq.
  pose proof (am_inner_bound u w Hu Hw) as Hr. fold p q r in Hp, Hq, Hr.
  pose proof (acos_bound p) as Ha. pose proof (acos_bound q) as Hb. pose proof (acos_bound r) as Hc.
  destruct (Rle_dec PI (acos p + acos q)) as [Hbig | Hsmall]; [lra |].
  apply am_acos_le; [lra | exact Hr |].
  (* cos (alpha + beta) = p q - sin alpha sin beta, and r - p q >= - sin alpha sin beta *)
  rewrite cos_plus, cos_acos, cos_acos, sin_acos, sin_acos by assumption.
  set (x := fun m => u m - p * v m). set (y := fun m => w m - q * v m).
  assert (Exy : tr_inner x y = r - p * q).
  { unfold tr_inner, x, y.
    transitivity (sumL (tr_idx 4) (fun m => 1 * (u m * w m) + (- q) * (u m * v m) + (- p) * (v m * w m) +
                                             (p * q) * (v m * v m))).
    { apply sumL_ext. intros. ring. }
    rewrite am_comb4. fold (tr_inner u w) (tr_inner u v) (tr_inner v w) (tr_inner v v). fold r p q.
    unfold tr_unitv in Hv. fold (tr_inner v v) in Hv. rewrite Hv. ring. }
  assert (Exx : tr_inner x x = 1 - p * p).
  { unfold tr_inner, x.
    transitivity (sumL (tr_idx 4) (fun m => 1 * (u m * u m) + (- 2 * p) * (u m * v m) + 0 * (v m * w m) +
                                             (p * p) * (v m * v m))).
    { apply sumL_ext. intros. ring. }
    rewrite am_comb4. fold (tr_inner u u) (tr_inner u v) (tr_inner v v). fold p.
    unfold tr_unitv in Hu, Hv. fold (tr_inner u u) in Hu. fold (tr_inner v v) in Hv. rewrite Hu, Hv. ring. }
  assert (Eyy : tr_inner y y = 1 - q * q).
  { unfold tr_inner, y.
    transitivity (sumL (tr_idx 4) (fun m => 1 * (w m * w m) + (- 2 * q) * (v m * w m) + 0 * (u m * v m) +
                                             (q * q) * (v m * v m))).
    { apply sumL_ext. intros. ring. }
    rewrite am_comb4. fold (tr_inner w w) (tr_inner v w) (tr_inner v v). fold q.
    unfold tr_unitv in Hw, Hv. fold (tr_inner w w) in Hw. fold (tr_inner v v) in Hv. rewrite Hw, Hv. ring. }
  pose proof (sumL_cauchy_schwarz nat (tr_idx 4) x y) as CS.
  fold (tr_inner x y) (tr_inner x x) (tr_inner y y) in CS. rewrite Exy, Exx, Eyy in CS.
  assert (H1 : 0 <= 1 - p * p) by nra. assert (H2 : 0 <= 1 - q * q) by nra.
  unfold Rsqr. rewrite <- sqrt_mult by assumption.
  assert (Hs : Rabs (r - p * q) <= sqrt ((1 - p * p) * (1 - q * q))).
  { rewrite <- (sqrt_Rsqr_abs (r - p * q)). apply sqrt_le_1_alt. unfold Rsqr. lra. }
  unfold Rabs in Hs. destruct (Rcase_abs (r - p * q)); lra.
Qed.

Lemma am_path3 : forall p r s q, tr_unitv p -> tr_unitv r -> tr_unitv s -> tr_unitv q ->
  am_dist p q <= am_dist p r + am_dist r s + am_dist s q.
Proof.
  intros p r s q Hp Hr Hs Hq.
  pose proof (am_sphere_triangle p r q Hp Hr Hq). pose proof (am_sphere_triangle r s q Hr Hs Hq). lra.
Qed.

Definition am_neg (u : nat -> R) (m : nat) : R := - u m.

Lemma am_neg_unit : forall u, tr_unitv u -> tr_unitv (am_neg u).
Proof.
  intros u Hu. unfold tr_unitv, am_neg in *. rewrite <- Hu. apply sumL_ext. intros. ring.
Qed.

Lemma am_dist_neg_l : forall u v, tr_unitv u -> tr_unitv v -> am_dist (am_neg u) v = PI - am_dist u v.
Proof.
  intros u v Hu Hv. unfold am_dist.
  assert (E : tr_inner (am_neg u) v = - tr_inner u v).
  { unfold tr_inner, am_neg. transitivity (-1 * sumL (tr_idx 4) (fun m => u m * v m)); [| ring].
    rewrite <- sumL_scale_l. apply sumL_ext. intros. ring. }
  rewrite E. apply am_acos_opp. apply am_inner_bound; assumption.
Qed.

Lemma am_dist_sym : forall u v, am_dist u v = am_dist v u.
Proof. intros. unfold am_dist. rewrite am_inner_sym. reflexivity. Qed.

(** Four unit vectors from a PSD completion. *)
Lemma am_vectors : forall E00 E01 E10 E11, elliptope_realizable E00 E01 E10 E11 ->
  exists a0 a1 b0 b1, tr_unitv a0 /\ tr_unitv a1 /\ tr_unitv b0 /\ tr_unitv b1 /\
    tr_inner a0 b0 = E00 /\ tr_inner a0 b1 = E01 /\ tr_inner a1 b0 = E10 /\ tr_inner a1 b1 = E11.
Proof.
  intros E00 E01 E10 E11 [x [y Hpsd]].
  destruct (tr_gram 4 _ (tr_G_sym E00 E01 E10 E11 x y) (tr_G_psd E00 E01 E10 E11 x y Hpsd)) as [u Hu].
  exists (u 0%nat), (u 1%nat), (u 2%nat), (u 3%nat). unfold tr_unitv, tr_inner.
  rewrite (Hu 0%nat 0%nat), (Hu 1%nat 1%nat), (Hu 2%nat 2%nat), (Hu 3%nat 3%nat),
          (Hu 0%nat 2%nat), (Hu 0%nat 3%nat), (Hu 1%nat 2%nat), (Hu 1%nat 3%nat) by lia.
  repeat split; reflexivity.
Qed.

(** The eight angle inequalities, with theta_xy = acos E_xy. *)
Definition am_cycle (t00 t01 t10 t11 : R) : Prop :=
  t00 <= t01 + t10 + t11 /\ t01 <= t00 + t10 + t11 /\
  t10 <= t00 + t01 + t11 /\ t11 <= t00 + t01 + t10 /\
  t01 + t10 + t11 - t00 <= 2 * PI /\ t00 + t10 + t11 - t01 <= 2 * PI /\
  t00 + t01 + t11 - t10 <= 2 * PI /\ t00 + t01 + t10 - t11 <= 2 * PI.

Theorem am_necessary : forall E00 E01 E10 E11, elliptope_realizable E00 E01 E10 E11 ->
  (-1 <= E00 <= 1) /\ (-1 <= E01 <= 1) /\ (-1 <= E10 <= 1) /\ (-1 <= E11 <= 1) /\
  am_cycle (acos E00) (acos E01) (acos E10) (acos E11).
Proof.
  intros E00 E01 E10 E11 H.
  destruct (am_vectors _ _ _ _ H) as [a0 [a1 [b0 [b1 [Ha0 [Ha1 [Hb0 [Hb1 [e00 [e01 [e10 e11]]]]]]]]]]].
  assert (D00 : am_dist a0 b0 = acos E00) by (unfold am_dist; rewrite e00; reflexivity).
  assert (D01 : am_dist a0 b1 = acos E01) by (unfold am_dist; rewrite e01; reflexivity).
  assert (D10 : am_dist a1 b0 = acos E10) by (unfold am_dist; rewrite e10; reflexivity).
  assert (D11 : am_dist a1 b1 = acos E11) by (unfold am_dist; rewrite e11; reflexivity).
  pose proof (am_dist_neg_l a0 b0 Ha0 Hb0) as N00. pose proof (am_dist_neg_l a0 b1 Ha0 Hb1) as N01.
  pose proof (am_dist_neg_l a1 b0 Ha1 Hb0) as N10. pose proof (am_dist_neg_l a1 b1 Ha1 Hb1) as N11.
  pose proof (am_neg_unit a0 Ha0) as Hn0. pose proof (am_neg_unit a1 Ha1) as Hn1.
  pose proof (am_path3 a0 b1 a1 b0 Ha0 Hb1 Ha1 Hb0) as T00.
  pose proof (am_path3 a0 b0 a1 b1 Ha0 Hb0 Ha1 Hb1) as T01.
  pose proof (am_path3 a1 b1 a0 b0 Ha1 Hb1 Ha0 Hb0) as T10.
  pose proof (am_path3 a1 b0 a0 b1 Ha1 Hb0 Ha0 Hb1) as T11.
  pose proof (am_path3 a0 b1 (am_neg a1) b0 Ha0 Hb1 Hn1 Hb0) as P01.
  pose proof (am_path3 a0 b0 (am_neg a1) b1 Ha0 Hb0 Hn1 Hb1) as P00.
  pose proof (am_path3 a1 b1 (am_neg a0) b0 Ha1 Hb1 Hn0 Hb0) as P11.
  pose proof (am_path3 a1 b0 (am_neg a0) b1 Ha1 Hb0 Hn0 Hb1) as P10.
  rewrite (am_dist_sym b1 a1), (am_dist_sym b0 a1), (am_dist_sym b1 a0), (am_dist_sym b0 a0) in *.
  rewrite (am_dist_sym b1 (am_neg a1)), (am_dist_sym b0 (am_neg a1)),
          (am_dist_sym b1 (am_neg a0)), (am_dist_sym b0 (am_neg a0)) in *.
  rewrite N00, N01, N10, N11, D00, D01, D10, D11 in *.
  rewrite <- e00, <- e01, <- e10, <- e11.
  repeat split; try apply am_inner_bound; try assumption; unfold am_cycle;
    rewrite ?e00, ?e01, ?e10, ?e11; lra.
Qed.

(** * Sufficiency: four unit vectors from the angle inequalities *)

Section Build.

Variable beta : R.
Hypothesis beta_range : 0 <= beta <= PI.

Let C := cos beta.
Let S := sin beta.

Lemma am_S_nonneg : 0 <= S.
Proof. unfold S. apply sin_ge_0; lra. Qed.

Lemma am_SC : S * S = 1 - C * C.
Proof. unfold S, C. apply am_sq_sin. Qed.

Definition am_b0 (m : nat) : R := match m with 0%nat => 1 | _ => 0 end.
Definition am_b1 (m : nat) : R := match m with 0%nat => C | 1%nat => S | _ => 0 end.

(** A unit vector at angle acos e from b0 and acos f from b1. *)
Definition am_P (e f : R) : R := if Req_EM_T S 0 then 0 else (f - e * C) / S.
Definition am_a (e f : R) (m : nat) : R :=
  match m with
  | 0%nat => e
  | 1%nat => am_P e f
  | 2%nat => sqrt (1 - e * e - am_P e f * am_P e f)
  | _ => 0
  end.

Lemma am_inner4 : forall u v, tr_inner u v = u 0%nat * v 0%nat + u 1%nat * v 1%nat + u 2%nat * v 2%nat + u 3%nat * v 3%nat.
Proof. intros u v. unfold tr_inner, tr_idx. simpl. ring. Qed.

Lemma am_b0_unit : tr_unitv am_b0.
Proof. unfold tr_unitv, tr_idx. simpl. ring. Qed.

Lemma am_b1_unit : tr_unitv am_b1.
Proof. unfold tr_unitv, tr_idx. simpl. pose proof am_SC. lra. Qed.

Lemma am_a_ok : forall e f, -1 <= e <= 1 -> -1 <= f <= 1 ->
  0 <= (1 - e * e) * (1 - C * C) - (f - e * C) * (f - e * C) ->
  tr_unitv (am_a e f) /\ tr_inner (am_a e f) am_b0 = e /\ tr_inner (am_a e f) am_b1 = f.
Proof.
  intros e f He Hf Hdet. pose proof am_SC as HSC. pose proof am_S_nonneg as HS.
  assert (Hrad : 0 <= 1 - e * e - am_P e f * am_P e f).
  { unfold am_P. destruct (Req_EM_T S 0) as [Z | NZ]; [nra |].
    assert (HSp : 0 < S) by lra.
    assert (E : 1 - e * e - (f - e * C) / S * ((f - e * C) / S) =
                ((1 - e * e) * (1 - C * C) - (f - e * C) * (f - e * C)) / (S * S)).
    { rewrite <- HSC. field. lra. }
    rewrite E. unfold Rdiv. apply Rmult_le_pos; [exact Hdet |].
    left. apply Rinv_0_lt_compat. nra. }
  split; [| split].
  - unfold tr_unitv. fold (tr_inner (am_a e f) (am_a e f)). rewrite am_inner4. simpl.
    rewrite sqrt_sqrt by exact Hrad. ring.
  - rewrite am_inner4. simpl. ring.
  - rewrite am_inner4. simpl. unfold am_P. destruct (Req_EM_T S 0) as [Z | NZ].
    + rewrite Z in HSC. assert (HC : C * C = 1) by lra. rewrite HC in Hdet.
      assert (Hz : (f - e * C) * (f - e * C) <= 0) by lra.
      assert (f - e * C = 0) by nra. rewrite Z. lra.
    + field. exact NZ.
Qed.

End Build.

Definition am_lift (v : nat -> R) (m : nat) (_ : unit) : R := v m.

Lemma am_dot_lift : forall u v, qs_dot nat unit (tr_idx 4) [tt] (am_lift u) (am_lift v) = tr_inner u v.
Proof.
  intros u v. unfold qs_dot, tr_inner, am_lift. apply sumL_ext. intros. simpl. ring.
Qed.

Lemma am_rabs_le : forall x a, -a <= x <= a -> Rabs x <= a.
Proof. intros x a H. unfold Rabs. destruct (Rcase_abs x); lra. Qed.

Theorem am_sufficient : forall E00 E01 E10 E11,
  -1 <= E00 <= 1 -> -1 <= E01 <= 1 -> -1 <= E10 <= 1 -> -1 <= E11 <= 1 ->
  am_cycle (acos E00) (acos E01) (acos E10) (acos E11) ->
  elliptope_realizable E00 E01 E10 E11.
Proof.
  intros E00 E01 E10 E11 H00 H01 H10 H11 Hc.
  set (t00 := acos E00) in *. set (t01 := acos E01) in *. set (t10 := acos E10) in *. set (t11 := acos E11) in *.
  pose proof (acos_bound E00) as B00. pose proof (acos_bound E01) as B01.
  pose proof (acos_bound E10) as B10. pose proof (acos_bound E11) as B11. fold t00 t01 t10 t11 in B00, B01, B10, B11.
  destruct Hc as [T00 [T01 [T10 [T11 [P00 [P01 [P10 P11]]]]]]].
  set (beta := Rmax (Rabs (t00 - t01)) (Rabs (t10 - t11))).
  assert (L1 : Rabs (t00 - t01) <= beta) by apply Rmax_l.
  assert (L2 : Rabs (t10 - t11) <= beta) by apply Rmax_r.
  assert (Ab1 : Rabs (t00 - t01) <= t00 + t01 /\ Rabs (t00 - t01) <= 2 * PI - (t00 + t01) /\
                Rabs (t00 - t01) <= t10 + t11 /\ Rabs (t00 - t01) <= 2 * PI - (t10 + t11))
    by (repeat split; apply am_rabs_le; lra).
  assert (Ab2 : Rabs (t10 - t11) <= t10 + t11 /\ Rabs (t10 - t11) <= 2 * PI - (t10 + t11) /\
                Rabs (t10 - t11) <= t00 + t01 /\ Rabs (t10 - t11) <= 2 * PI - (t00 + t01))
    by (repeat split; apply am_rabs_le; lra).
  assert (U0 : beta <= t00 + t01) by (apply Rmax_lub; lra).
  assert (U0' : beta <= 2 * PI - (t00 + t01)) by (apply Rmax_lub; lra).
  assert (U1 : beta <= t10 + t11) by (apply Rmax_lub; lra).
  assert (U1' : beta <= 2 * PI - (t10 + t11)) by (apply Rmax_lub; lra).
  assert (Hb : 0 <= beta <= PI).
  { split; [pose proof (Rabs_pos (t00 - t01)); lra |].
    apply Rmax_lub; apply am_rabs_le; lra. }
  pose proof (am_triangle_det t00 t01 beta B00 B01 L1 U0 U0') as D0.
  pose proof (am_triangle_det t10 t11 beta B10 B11 L2 U1 U1') as D1.
  unfold t00, t01, t10, t11 in D0, D1. rewrite !cos_acos in D0, D1 by assumption.
  destruct (am_a_ok beta Hb E00 E01 H00 H01 D0) as [Ua0 [Ia00 Ia01]].
  destruct (am_a_ok beta Hb E10 E11 H10 H11 D1) as [Ua1 [Ia10 Ia11]].
  pose proof (tr_vectors_elliptope nat unit (tr_idx 4) [tt]
    (am_lift (am_a beta E00 E01)) (am_lift (am_a beta E10 E11))
    (am_lift (am_b0)) (am_lift (am_b1 beta))) as H.
  rewrite !am_dot_lift in H. rewrite Ia00, Ia01, Ia10, Ia11 in H.
  apply H; [exact Ua0 | exact Ua1 | apply am_b0_unit | apply am_b1_unit].
Qed.

(** * The arcsine form *)

Definition am_arcsine_region (E00 E01 E10 E11 : R) : Prop :=
  (-1 <= E00 <= 1) /\ (-1 <= E01 <= 1) /\ (-1 <= E10 <= 1) /\ (-1 <= E11 <= 1) /\
  Rabs (asin E00 + asin E01 + asin E10 - asin E11) <= PI /\
  Rabs (asin E00 + asin E01 - asin E10 + asin E11) <= PI /\
  Rabs (asin E00 - asin E01 + asin E10 + asin E11) <= PI /\
  Rabs (- asin E00 + asin E01 + asin E10 + asin E11) <= PI.

Lemma am_cycle_arcsine : forall E00 E01 E10 E11,
  -1 <= E00 <= 1 -> -1 <= E01 <= 1 -> -1 <= E10 <= 1 -> -1 <= E11 <= 1 ->
  (am_cycle (acos E00) (acos E01) (acos E10) (acos E11) <->
   Rabs (asin E00 + asin E01 + asin E10 - asin E11) <= PI /\
   Rabs (asin E00 + asin E01 - asin E10 + asin E11) <= PI /\
   Rabs (asin E00 - asin E01 + asin E10 + asin E11) <= PI /\
   Rabs (- asin E00 + asin E01 + asin E10 + asin E11) <= PI).
Proof.
  intros E00 E01 E10 E11 H00 H01 H10 H11.
  rewrite (acos_asin E00 H00), (acos_asin E01 H01), (acos_asin E10 H10), (acos_asin E11 H11).
  unfold am_cycle. split.
  - intros [T00 [T01 [T10 [T11 [P00 [P01 [P10 P11]]]]]]].
    repeat split; apply am_rabs_le; lra.
  - intros [A [B [C D]]].
    unfold Rabs in A, B, C, D.
    destruct (Rcase_abs (asin E00 + asin E01 + asin E10 - asin E11));
    destruct (Rcase_abs (asin E00 + asin E01 - asin E10 + asin E11));
    destruct (Rcase_abs (asin E00 - asin E01 + asin E10 + asin E11));
    destruct (Rcase_abs (- asin E00 + asin E01 + asin E10 + asin E11));
    repeat split; lra.
Qed.

(** Landau and Masanes: a correlator table has a PSD completion exactly when
    its entries lie in [-1, 1] and the four arcsine inequalities hold. *)
Theorem am_arcsine : forall E00 E01 E10 E11,
  elliptope_realizable E00 E01 E10 E11 <-> am_arcsine_region E00 E01 E10 E11.
Proof.
  intros E00 E01 E10 E11. unfold am_arcsine_region. split.
  - intro H. destruct (am_necessary _ _ _ _ H) as [H00 [H01 [H10 [H11 Hc]]]].
    repeat (split; [assumption |]). apply am_cycle_arcsine; assumption.
  - intros [H00 [H01 [H10 [H11 Ha]]]]. apply am_sufficient; try assumption.
    apply am_cycle_arcsine; assumption.
Qed.

(** With TsirelsonRepresentation.v: the correlator tables of quantum
    strategies in finite dimension are exactly the arcsine region. *)
Theorem am_quantum_arcsine : forall E00 E01 E10 E11,
  am_arcsine_region E00 E01 E10 E11 <->
  exists s : qs_strategy nat nat,
    qs_valid nat nat Nat.eq_dec Nat.eq_dec (tr_idx 8) (tr_idx 8) s /\
    qs_corr nat nat (tr_idx 8) (tr_idx 8) (qs_psi _ _ s) (qs_A0 _ _ s) (qs_B0 _ _ s) = E00 /\
    qs_corr nat nat (tr_idx 8) (tr_idx 8) (qs_psi _ _ s) (qs_A0 _ _ s) (qs_B1 _ _ s) = E01 /\
    qs_corr nat nat (tr_idx 8) (tr_idx 8) (qs_psi _ _ s) (qs_A1 _ _ s) (qs_B0 _ _ s) = E10 /\
    qs_corr nat nat (tr_idx 8) (tr_idx 8) (qs_psi _ _ s) (qs_A1 _ _ s) (qs_B1 _ _ s) = E11.
Proof. intros. rewrite <- am_arcsine. apply tr_representation. Qed.

(** * Two points on the boundary *)

(** asin (3/5) + asin (4/5) = pi / 2, by the 3-4-5 triangle. *)
Lemma am_345 : asin (3 / 5) + asin (4 / 5) = PI / 2.
Proof.
  assert (H35 : -1 <= 3 / 5 <= 1) by lra.
  assert (Hs : sin (acos (3 / 5)) = 4 / 5).
  { rewrite sin_acos by exact H35. replace (1 - (3 / 5)²) with ((4 / 5) * (4 / 5)) by (unfold Rsqr; field).
    apply sqrt_square. lra. }
  assert (Hb : 0 <= acos (3 / 5) <= PI / 2).
  { split; [apply acos_bound |]. rewrite <- acos_0. apply (am_acos_le); try lra.
    - split; [pose proof (acos_bound 0); lra | rewrite acos_0; pose proof PI_RGT_0; lra].
    - rewrite acos_0, cos_PI2. lra. }
  rewrite <- Hs, asin_sin by (pose proof PI_RGT_0; lra).
  rewrite (acos_asin (3 / 5) H35). ring.
Qed.

(** The point (3/5, 4/5, 4/5, -3/5) is in the region and on its boundary. *)
Theorem am_pythagorean_boundary :
  am_arcsine_region (3 / 5) (4 / 5) (4 / 5) (- (3 / 5)) /\
  asin (3 / 5) + asin (4 / 5) + asin (4 / 5) - asin (- (3 / 5)) = PI.
Proof.
  pose proof am_345 as H. rewrite asin_opp. pose proof PI_RGT_0.
  assert (E : asin (3 / 5) + asin (4 / 5) + asin (4 / 5) - - asin (3 / 5) = PI) by lra.
  split; [| exact E].
  unfold am_arcsine_region. rewrite asin_opp.
  pose proof (asin_bound (3 / 5)). pose proof (asin_bound (4 / 5)).
  repeat split; try lra; apply am_rabs_le; split; lra.
Qed.

(** Tsirelson's point (1/sqrt 2, 1/sqrt 2, 1/sqrt 2, -1/sqrt 2) is in the
    region and on its boundary. *)
Theorem am_tsirelson_boundary :
  am_arcsine_region (/ sqrt 2) (/ sqrt 2) (/ sqrt 2) (- / sqrt 2) /\
  asin (/ sqrt 2) + asin (/ sqrt 2) + asin (/ sqrt 2) - asin (- / sqrt 2) = PI.
Proof.
  assert (Hs2 : 1 < sqrt 2).
  { rewrite <- sqrt_1. apply sqrt_lt_1_alt. lra. }
  assert (Hr : 0 < / sqrt 2 < 1).
  { split; [apply Rinv_0_lt_compat; lra |]. rewrite <- Rinv_1. apply Rinv_lt_contravar; lra. }
  rewrite asin_opp, asin_inv_sqrt2. pose proof PI_RGT_0.
  split; [| field].
  unfold am_arcsine_region. rewrite asin_opp, asin_inv_sqrt2.
  pose proof (asin_bound (3 / 5)). pose proof (asin_bound (4 / 5)).
  repeat split; try lra; apply am_rabs_le; split; lra.
Qed.

Print Assumptions am_sphere_triangle.
Print Assumptions am_triangle_det.
Print Assumptions am_necessary.
Print Assumptions am_sufficient.
Print Assumptions am_arcsine.
Print Assumptions am_quantum_arcsine.
Print Assumptions am_pythagorean_boundary.
Print Assumptions am_tsirelson_boundary.
