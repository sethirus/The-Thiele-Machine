(** RelaxationContinuousLimit: in continuous time the relaxation settles,
    and the entropy produced over the whole relaxation is the starting
    relative entropy.

    The setting of RelaxationContinuous.v (rates q >= 0, a positive steady
    spread pi of total mass 1 with detailed balance, a solution p of the
    master equation that is positive after time 0, starting from a
    probability vector), plus the continuous-time form of Doeblin's
    condition: some c > 0 with q x y >= c * pi y for all listed x, y.

    - The production rate is at least c times the relative entropy
      ([rcl_sigma_ge]).
    - So the relative entropy falls at least exponentially:
      D (p b) <= D (p a) * exp (- c (b - a)) for 0 < a <= b
      ([rcl_D_decay]), and it tends to 0 ([rcl_D_limit]).
    - The entropy produced from time a on, the integral of the production
      rate out to infinity, is D (p a) ([rcl_produced_limit]).
    - The relative entropy is continuous at time 0, even where the start
      puts no weight ([rcl_D_at_zero]); so from a known start s the entropy
      produced over the whole relaxation is - ln (pi s)
      ([rcl_known_start_total]). *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics. No definition or theorem here mentions a certification
   system, a ledger or a machine step; it imports only FiniteSums.v and the
   relaxation files.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. The standalone boundary is stated here rather than inferred from
   an import. *)

From Coq Require Import List Reals Lra Psatz Ranalysis1 Ranalysis4.
Import ListNotations.
From Kernel Require Import FiniteSums RelaxationEntropy RelaxationContinuous.
Open Scope R_scope.

Section Limit.

Variable X : Type.
Variable LX : list X.
Variable q : X -> X -> R.
Variable pi : X -> R.
Hypothesis q_nonneg : forall x y, 0 <= q x y.
Hypothesis pi_pos : forall x, 0 < pi x.
Hypothesis pi_mass : sumL LX pi = 1.
Hypothesis detailed_balance : forall x y, pi x * q x y = pi y * q y x.
Variable c : R.
Hypothesis c_pos : 0 < c.
Hypothesis doeblin : forall x y, In x LX -> In y LX -> c * pi y <= q x y.

Let D := rcd_D X LX pi.
Let sigma := rcd_sigma X LX q pi.

Lemma rcl_lin4 : forall (g1 g2 g3 g4 : X -> R) k1 k2 k3 k4,
  sumL LX (fun y => k1 * g1 y - k2 * g2 y - k3 * g3 y + k4 * g4 y) =
  k1 * sumL LX g1 - k2 * sumL LX g2 - k3 * sumL LX g3 + k4 * sumL LX g4.
Proof. intros. rewrite sumL_plus, !sumL_minus, !sumL_scale_l. reflexivity. Qed.

Lemma rcl_sum_le_gen : forall (L : list X) (f g : X -> R), (forall a, In a L -> f a <= g a) -> sumL L f <= sumL L g.
Proof.
  intros L f g H. induction L as [| a L IH]; simpl; [lra |].
  pose proof (H a (or_introl eq_refl)). assert (sumL L f <= sumL L g) by (apply IH; intros; apply H; right; assumption). lra.
Qed.

Lemma rcl_sum_le : forall (f g : X -> R), (forall a, In a LX -> f a <= g a) -> sumL LX f <= sumL LX g.
Proof. intros f g H. apply rcl_sum_le_gen. exact H. Qed.

(** The production rate is at least c times the relative entropy. *)
Theorem rcl_sigma_ge : forall r, (forall x, 0 < r x) -> sumL LX r = 1 -> c * D r <= sigma r.
Proof.
  intros r Hr Hm. unfold sigma, D, rcd_sigma.
  set (a := fun x => r x / pi x).
  assert (Ha : forall x, 0 < a x) by (intro x; unfold a; apply Rdiv_lt_0_compat; [apply Hr | apply pi_pos]).
  assert (HL : forall x, rcd_L X pi r x = ln (a x)) by reflexivity.
  set (A := sumL LX (fun x => pi x * (a x * ln (a x)))).
  set (C := sumL LX (fun x => pi x * ln (a x))).
  assert (HB : sumL LX (fun x => pi x * a x) = 1).
  { rewrite <- Hm. apply sumL_ext. intros x _. unfold a. field. pose proof (pi_pos x). lra. }
  assert (HA : A = rcd_D X LX pi r).
  { unfold A, rcd_D. apply sumL_ext. intros x _. unfold a. field. pose proof (pi_pos x). lra. }
  assert (HC : C <= 0).
  { unfold C.
    apply Rle_trans with (sumL LX (fun x => r x - pi x)).
    - apply rcl_sum_le. intros x _. pose proof (pi_pos x). pose proof (Hr x).
      pose proof (re_term_ge (pi x) (r x) ltac:(lra) ltac:(lra) (fun _ => Hr x)) as T.
      assert (E : ln (a x) = - ln (pi x / r x)).
      { unfold a. rewrite <- ln_Rinv by (apply Rdiv_lt_0_compat; lra). f_equal. field. lra. }
      rewrite E. lra.
    - rewrite sumL_minus, pi_mass, Hm. lra. }
  (* each term of the double sum, through detailed balance and the condition *)
  assert (Hterm : forall x y, In x LX -> In y LX ->
    c * (pi x * pi y * ((a x - a y) * (ln (a x) - ln (a y)))) <=
    (r x * q x y - r y * q y x) * (rcd_L X pi r x - rcd_L X pi r y)).
  { intros x y Hx Hy. rewrite !HL.
    assert (E : r x * q x y - r y * q y x = q x y * pi x * (a x - a y)).
    { assert (Hq : r y * q y x = r y * (pi x * q x y) / pi y).
      { rewrite detailed_balance. field. pose proof (pi_pos y). lra. }
      rewrite Hq. unfold a. field. split; pose proof (pi_pos x); pose proof (pi_pos y); lra. }
    rewrite E. pose proof (rcd_ln_mono (a x) (a y) (Ha x) (Ha y)) as M.
    pose proof (doeblin x y Hx Hy). pose proof (pi_pos x). pose proof (pi_pos y).
    assert (K : c * pi y <= q x y) by assumption.
    set (T := (a x - a y) * (ln (a x) - ln (a y))) in *.
    replace (c * (pi x * pi y * T)) with ((c * pi y) * (pi x * T)) by ring.
    replace (q x y * pi x * (a x - a y) * (ln (a x) - ln (a y))) with (q x y * (pi x * T)) by (unfold T; ring).
    apply Rmult_le_compat_r; [apply Rmult_le_pos; [lra | exact M] | exact K]. }
  (* the double sum of pi x pi y (a x - a y)(ln a x - ln a y) is 2 (A - C) *)
  assert (Hdouble : sumL LX (fun x => sumL LX (fun y => pi x * pi y * ((a x - a y) * (ln (a x) - ln (a y))))) =
                    2 * (A - C)).
  { transitivity (sumL LX (fun x => (pi x * (a x * ln (a x))) * 1 - (pi x * a x) * C
                                     - (pi x * ln (a x)) * 1 + pi x * A)).
    - apply sumL_ext. intros x _.
      transitivity (sumL LX (fun y => (pi x * (a x * ln (a x))) * pi y - (pi x * a x) * (pi y * ln (a y))
                                       - (pi x * ln (a x)) * (pi y * a y) + pi x * (pi y * (a y * ln (a y))))).
      + apply sumL_ext. intros. ring.
      + rewrite rcl_lin4, pi_mass, HB. fold C A. ring.
    - transitivity (sumL LX (fun x => 1 * (pi x * (a x * ln (a x))) - C * (pi x * a x)
                                     - 1 * (pi x * ln (a x)) + A * pi x)).
      + apply sumL_ext. intros. ring.
      + rewrite rcl_lin4. fold A C. rewrite HB, pi_mass. ring. }
  assert (Hsum : c * (2 * (A - C)) <=
                 sumL LX (fun x => sumL LX (fun y => (r x * q x y - r y * q y x) * (rcd_L X pi r x - rcd_L X pi r y)))).
  { rewrite <- Hdouble, <- sumL_scale_l. apply rcl_sum_le. intros x Hx.
    rewrite <- sumL_scale_l. apply rcl_sum_le. intros y Hy. apply Hterm; assumption. }
  rewrite <- HA. nra.
Qed.

(** ** A solution and its decay *)

Lemma rcl_D_nonneg : forall r, (forall x, 0 < r x) -> sumL LX r = 1 -> 0 <= D r.
Proof.
  intros r Hr Hm. unfold D, rcd_D.
  apply Rle_trans with (sumL LX (fun x => r x - pi x)).
  - rewrite sumL_minus, Hm, pi_mass. lra.
  - apply rcl_sum_le. intros x _. pose proof (Hr x). pose proof (pi_pos x).
    pose proof (re_term_ge (r x) (pi x) ltac:(lra) ltac:(lra) (fun _ => pi_pos x)). lra.
Qed.

Variable p : R -> X -> R.
Hypothesis p_pos : forall t x, 0 < t -> 0 < p t x.
Hypothesis master : forall t x, derivable_pt_lim (fun s => p s x) t (rcd_flow X LX q (p t) x).
Hypothesis p_mass0 : sumL LX (p 0) = 1.

Lemma rcl_mass : forall t, sumL LX (p t) = 1.
Proof.
  assert (Hd : forall t, derivable_pt_lim (fun s => sumL LX (fun x => p s x)) t 0).
  { intro t. eapply rcd_lim_ext.
    - apply (rcd_sum_deriv X LX (fun x s => p s x) (fun x => rcd_flow X LX q (p t) x) t).
      intros x _. apply master.
    - apply rcd_flow_total. }
  intro t. rewrite <- p_mass0.
  change (sumL LX (p t)) with ((fun s => sumL LX (fun x => p s x)) t).
  change (sumL LX (p 0)) with ((fun s => sumL LX (fun x => p s x)) 0).
  destruct (Rtotal_order t 0) as [Hlt | [Heq | Hgt]].
  - destruct (MVT_cor2 (fun s => sumL LX (fun x => p s x)) (fun _ => 0) t 0 Hlt (fun c _ => Hd c)) as [k [Hk _]].
    lra.
  - rewrite Heq. reflexivity.
  - destruct (MVT_cor2 (fun s => sumL LX (fun x => p s x)) (fun _ => 0) 0 t Hgt (fun c _ => Hd c)) as [k [Hk _]].
    lra.
Qed.

Lemma rcl_D_deriv : forall t, 0 < t -> derivable_pt_lim (fun s => D (p s)) t (- sigma (p t)).
Proof. intros t Ht. unfold D, sigma. eapply rcd_D_derivative; eauto. Qed.

(** The relative entropy falls at least exponentially. *)
Theorem rcl_D_decay : forall a b, 0 < a -> a <= b -> D (p b) <= D (p a) * exp (- (c * (b - a))).
Proof.
  intros a b Ha Hab.
  set (f := fun t => D (p t) * exp (c * t)).
  set (f' := fun t => (- sigma (p t)) * exp (c * t) + D (p t) * (c * exp (c * t))).
  assert (Hf : forall t, 0 < t -> derivable_pt_lim f t (f' t)).
  { intros t Ht.
    assert (He : derivable_pt_lim (fun s => exp (c * s)) t (c * exp (c * t))).
    { assert (Hl : derivable_pt_lim (fun s => c * s) t c).
      { eapply rcd_lim_ext; [apply (derivable_pt_lim_scal id c t 1 (derivable_pt_lim_id t)) | ring]. }
      eapply rcd_lim_ext; [apply (derivable_pt_lim_comp (fun s => c * s) exp t c (exp (c * t)) Hl (derivable_pt_lim_exp (c * t))) | ring]. }
    apply (derivable_pt_lim_mult (fun s => D (p s)) (fun s => exp (c * s)) t _ _ (rcl_D_deriv t Ht) He). }
  assert (Hneg : forall t, 0 < t -> f' t <= 0).
  { intros t Ht. unfold f'. pose proof (rcl_sigma_ge (p t) (fun x => p_pos t x Ht) (rcl_mass t)) as G.
    pose proof (exp_pos (c * t)). fold D sigma in G. nra. }
  assert (Hfab : f b <= f a).
  { destruct (Req_dec a b) as [-> | Hne]; [lra |].
    destruct (MVT_cor2 f f' a b ltac:(lra) (fun t Ht => Hf t ltac:(lra))) as [k [Hk Hkr]].
    pose proof (Hneg k ltac:(lra)). nra. }
  unfold f in Hfab.
  assert (E : exp (c * a) = exp (c * b) * exp (- (c * (b - a)))).
  { rewrite <- exp_plus. f_equal. ring. }
  rewrite E in Hfab. pose proof (exp_pos (c * b)) as Pb.
  apply (Rmult_le_reg_r (exp (c * b))); [exact Pb |]. nra.
Qed.

Lemma rcl_exp_neg_le : forall y, 0 <= y -> exp (- y) <= / (1 + y).
Proof.
  intros y Hy. rewrite exp_Ropp. apply Rinv_le_contravar; [lra |]. apply re_exp_ge.
Qed.

(** The relative entropy tends to 0. *)
Theorem rcl_D_limit : forall a, 0 < a -> forall eps, 0 < eps ->
  exists T, forall b, T <= b -> 0 <= D (p b) < eps.
Proof.
  intros a Ha eps Heps.
  pose proof (rcl_D_nonneg (p a) (fun x => p_pos a x Ha) (rcl_mass a)) as Da.
  exists (a + D (p a) / (c * eps) + 1). intros b Hb.
  assert (Hab : a <= b).
  { assert (0 <= D (p a) / (c * eps)) by (apply Rmult_le_pos; [exact Da | left; apply Rinv_0_lt_compat; nra]). lra. }
  assert (Hb0 : 0 < b) by lra.
  split; [exact (rcl_D_nonneg (p b) (fun x => p_pos b x Hb0) (rcl_mass b)) |].
  pose proof (rcl_D_decay a b Ha Hab) as Dec.
  pose proof (rcl_exp_neg_le (c * (b - a)) ltac:(nra)) as Ex.
  assert (Hk : D (p a) < eps * (1 + c * (b - a))).
  { assert (Hq : D (p a) / (c * eps) + 1 <= b - a) by lra.
    assert (Hq2 : D (p a) <= c * eps * (b - a - 1)).
    { apply Rmult_le_compat_l with (r := c * eps) in Hq; [| nra].
      replace (c * eps * (D (p a) / (c * eps) + 1)) with (D (p a) + c * eps) in Hq by (field; nra). nra. }
    nra. }
  assert (Hpos : 0 < 1 + c * (b - a)) by nra.
  apply Rle_lt_trans with (D (p a) * / (1 + c * (b - a))).
  - apply Rle_trans with (D (p a) * exp (- (c * (b - a)))); [exact Dec |].
    apply Rmult_le_compat_l; [exact Da | exact Ex].
  - apply (Rmult_lt_reg_r (1 + c * (b - a))); [exact Hpos |].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. exact Hk.
Qed.

(** The entropy produced from time a on, out to infinity, is D (p a). *)
Theorem rcl_produced_limit : forall a (Ha : 0 < a) eps, 0 < eps ->
  exists T, forall b (Hab : a <= b), T <= b ->
    Rabs (NewtonInt (fun t => sigma (p t)) a b (rcd_window X LX q pi pi_pos p p_pos master a b Ha Hab)
          - D (p a)) < eps.
Proof.
  intros a Ha eps Heps. destruct (rcl_D_limit a Ha eps Heps) as [T HT].
  exists T. intros b Hab Hb. destruct (HT b Hb) as [H0 H1].
  unfold sigma. rewrite rcd_produced_window. fold D.
  replace (D (p a) - D (p b) - D (p a)) with (- D (p b)) by ring.
  rewrite Rabs_Ropp, Rabs_right by lra. exact H1.
Qed.

(** ** Continuity at time 0 and the known start *)

Definition rcl_lim0 (g : R -> R) (l : R) : Prop :=
  forall eps, 0 < eps -> exists del, 0 < del /\ forall t, 0 < t < del -> Rabs (g t - l) < eps.

Lemma rcl_lim0_sum : forall (L : list X) (g : X -> R -> R) (l : X -> R),
  (forall x, In x L -> rcl_lim0 (g x) (l x)) -> rcl_lim0 (fun t => sumL L (fun x => g x t)) (sumL L l).
Proof.
  induction L as [| a L IH]; intros g l H eps Heps.
  - exists 1. split; [lra |]. intros t _. simpl. rewrite Rminus_0_r, Rabs_R0. exact Heps.
  - destruct (H a (or_introl eq_refl) (eps / 2) ltac:(lra)) as [d1 [Hd1 H1]].
    destruct (IH g l (fun x Hx => H x (or_intror Hx)) (eps / 2) ltac:(lra)) as [d2 [Hd2 H2]].
    exists (Rmin d1 d2). split; [apply Rmin_glb_lt; assumption |].
    intros t [Ht1 Ht2]. simpl.
    pose proof (H1 t (conj Ht1 (Rlt_le_trans _ _ _ Ht2 (Rmin_l d1 d2)))) as A1.
    pose proof (H2 t (conj Ht1 (Rlt_le_trans _ _ _ Ht2 (Rmin_r d1 d2)))) as A2.
    replace (g a t + sumL L (fun x => g x t) - (l a + sumL L l))
      with ((g a t - l a) + (sumL L (fun x => g x t) - sumL L l)) by ring.
    eapply Rle_lt_trans; [apply Rabs_triang | lra].
Qed.

Lemma rcl_cont_lim0 : forall g, continuity_pt g 0 -> rcl_lim0 g (g 0).
Proof.
  intros g Hc eps Heps. unfold continuity_pt, continue_in, limit1_in, limit_in in Hc.
  destruct (Hc eps Heps) as [alp [Halp H]]. exists alp. split; [lra |].
  intros t [Ht1 Ht2]. apply H. split.
  - unfold D_x, no_cond. split; [exact I | lra].
  - simpl. unfold R_dist. rewrite Rminus_0_r, Rabs_right; lra.
Qed.

Lemma rcl_p_cont : forall x, continuity_pt (fun s => p s x) 0.
Proof. intro x. apply (derivable_continuous_pt _ 0 (exist _ _ (master 0 x))). Qed.

Lemma rcl_vlnv : forall v, 0 < v <= 1 -> Rabs (v * ln v) <= 2 * sqrt v.
Proof.
  intros v [Hv0 Hv1].
  assert (Hln : ln v <= 0).
  { destruct (Req_dec v 1) as [-> | Hne]; [rewrite ln_1; lra |].
    pose proof (ln_increasing v 1 Hv0 ltac:(lra)) as Hi. rewrite ln_1 in Hi. lra. }
  set (w := sqrt v). assert (Hw : 0 < w) by (apply sqrt_lt_R0; exact Hv0).
  assert (Hww : w * w = v) by (apply sqrt_sqrt; lra).
  assert (E : ln v = 2 * ln w) by (rewrite <- Hww, ln_mult by exact Hw; ring).
  pose proof (re_ln_le (/ w) (Rinv_0_lt_compat w Hw)) as L. rewrite ln_Rinv in L by exact Hw.
  rewrite Rabs_left1 by nra. rewrite E, <- Hww.
  assert (Hiw : w * / w = 1) by (field; lra).
  nra.
Qed.

Hypothesis p0_nonneg : forall x, 0 <= p 0 x.

Lemma rcl_term_cont : forall x,
  rcl_lim0 (fun t => p t x * ln (p t x / pi x)) (p 0 x * ln (p 0 x / pi x)).
Proof.
  intro x. pose proof (pi_pos x) as Hpi.
  destruct (Rle_lt_or_eq_dec 0 (p 0 x) (p0_nonneg x)) as [Hu | Hu].
  - (* a positive start: the term is continuous there *)
    set (h := fun u => u * ln (u / pi x)).
    assert (Dh : derivable_pt h (p 0 x)).
    { exists (ln (p 0 x / pi x) + 1).
      assert (Hu' : derivable_pt_lim (mult_fct id (fct_cte (/ pi x))) (p 0 x) (1 * / pi x + p 0 x * 0)).
      { exact (derivable_pt_lim_mult id (fct_cte (/ pi x)) (p 0 x) 1 0
          (derivable_pt_lim_id (p 0 x)) (derivable_pt_lim_const (/ pi x) (p 0 x))). }
      assert (Hpos : 0 < p 0 x / pi x) by (apply Rdiv_lt_0_compat; lra).
      assert (Hl : derivable_pt_lim (comp ln (mult_fct id (fct_cte (/ pi x)))) (p 0 x)
                     (/ (p 0 x / pi x) * (1 * / pi x + p 0 x * 0))).
      { apply derivable_pt_lim_comp; [exact Hu' |]. apply derivable_pt_lim_ln. exact Hpos. }
      pose proof (derivable_pt_lim_mult id (comp ln (mult_fct id (fct_cte (/ pi x)))) (p 0 x) 1 _
        (derivable_pt_lim_id (p 0 x)) Hl) as Hm.
      eapply rcd_lim_ext; [exact Hm |]. unfold comp, mult_fct, fct_cte, id. unfold Rdiv. field. lra. }
    pose proof (continuity_pt_comp (fun s => p s x) h 0 (rcl_p_cont x) (derivable_continuous_pt h (p 0 x) Dh)) as Hc.
    exact (rcl_cont_lim0 (comp h (fun s => p s x)) Hc).
  - (* a start with no weight here: u ln u goes to 0 *)
    rewrite <- Hu. rewrite Rmult_0_l. intros eps Heps.
    set (e := eps / (2 * pi x)). assert (He : 0 < e) by (unfold e; apply Rdiv_lt_0_compat; lra).
    set (eta := pi x * Rmin 1 (e * e)).
    assert (Heta : 0 < eta) by (unfold eta; apply Rmult_lt_0_compat; [lra | apply Rmin_glb_lt; nra]).
    destruct (rcl_cont_lim0 _ (rcl_p_cont x) eta Heta) as [del [Hdel H]].
    exists del. split; [exact Hdel |]. intros t Ht.
    pose proof (H t Ht) as Hp. cbv beta in Hp. rewrite <- Hu, Rminus_0_r in Hp.
    pose proof (p_pos t x (proj1 Ht)) as Ppos.
    rewrite Rabs_right in Hp by lra.
    set (v := p t x / pi x).
    assert (Hv : 0 < v <= 1).
    { unfold v. split; [apply Rdiv_lt_0_compat; lra |].
      apply (Rmult_le_reg_r (pi x)); [lra |]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
      pose proof (Rmin_l 1 (e * e)). unfold eta in Hp. nra. }
    assert (Hve : v < e * e).
    { unfold v. apply (Rmult_lt_reg_r (pi x)); [lra |]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
      pose proof (Rmin_r 1 (e * e)). unfold eta in Hp. nra. }
    assert (Hsv : sqrt v < e).
    { destruct (Rlt_or_le (sqrt v) e) as [L | L]; [exact L |].
      exfalso. pose proof (sqrt_sqrt v ltac:(lra)). nra. }
    assert (Eterm : p t x * ln v = pi x * (v * ln v)) by (unfold v; field; lra).
    cbv beta. rewrite Rminus_0_r, Eterm, Rabs_mult, (Rabs_right (pi x)) by lra.
    pose proof (rcl_vlnv v Hv) as B.
    apply Rle_lt_trans with (pi x * (2 * sqrt v)); [apply Rmult_le_compat_l; lra |].
    unfold e in Hsv. apply (Rmult_lt_compat_l (2 * pi x)) in Hsv; [| lra].
    replace (2 * pi x * (eps / (2 * pi x))) with eps in Hsv by (field; lra). lra.
Qed.

(** The relative entropy is continuous at time 0. *)
Theorem rcl_D_at_zero : rcl_lim0 (fun t => D (p t)) (D (p 0)).
Proof.
  unfold D, rcd_D.
  apply (rcl_lim0_sum LX (fun x t => p t x * ln (p t x / pi x)) (fun x => p 0 x * ln (p 0 x / pi x))).
  intros x _. apply rcl_term_cont.
Qed.

Variable eqX : forall a b : X, {a = b} + {a <> b}.
Hypothesis LX_nodup : NoDup LX.
Variable s0 : X.
Hypothesis s0_in : In s0 LX.
Hypothesis p0_point : forall x, p 0 x = if eqX s0 x then 1 else 0.

Lemma rcl_D_point : D (p 0) = - ln (pi s0).
Proof.
  unfold D, rcd_D.
  transitivity (sumL LX (fun x => (if eqX s0 x then 1 else 0) * ln (1 / pi x))).
  - apply sumL_ext. intros x _. rewrite p0_point. destruct (eqX s0 x); [reflexivity | ring].
  - rewrite (sumL_delta X eqX LX s0 (fun x => ln (1 / pi x)) LX_nodup s0_in).
    unfold Rdiv. rewrite Rmult_1_l, ln_Rinv by apply pi_pos. reflexivity.
Qed.

(** From a known start s0, the entropy produced over the whole relaxation
    is - ln (pi s0): from a time a near 0 out to infinity it comes as close
    as asked. *)
Theorem rcl_known_start_total : forall eps, 0 < eps -> exists del, 0 < del /\
  forall a (Ha : 0 < a), a < del -> exists T, forall b (Hab : a <= b), T <= b ->
    Rabs (NewtonInt (fun t => sigma (p t)) a b (rcd_window X LX q pi pi_pos p p_pos master a b Ha Hab)
          - (- ln (pi s0))) < eps.
Proof.
  intros eps Heps.
  destruct (rcl_D_at_zero (eps / 2) ltac:(lra)) as [del [Hdel H0]].
  exists del. split; [exact Hdel |]. intros a Ha Hadel.
  destruct (rcl_produced_limit a Ha (eps / 2) ltac:(lra)) as [T HT].
  exists T. intros b Hab Hb. pose proof (HT b Hab Hb) as A. pose proof (H0 a (conj Ha Hadel)) as B.
  rewrite rcl_D_point in B.
  replace (NewtonInt (fun t => sigma (p t)) a b (rcd_window X LX q pi pi_pos p p_pos master a b Ha Hab) - - ln (pi s0))
    with ((NewtonInt (fun t => sigma (p t)) a b (rcd_window X LX q pi pi_pos p p_pos master a b Ha Hab) - D (p a))
          + (D (p a) - - ln (pi s0))) by ring.
  eapply Rle_lt_trans; [apply Rabs_triang | lra].
Qed.

End Limit.

Print Assumptions rcl_sigma_ge.
Print Assumptions rcl_D_decay.
Print Assumptions rcl_D_limit.
Print Assumptions rcl_produced_limit.
Print Assumptions rcl_D_at_zero.
Print Assumptions rcl_known_start_total.
