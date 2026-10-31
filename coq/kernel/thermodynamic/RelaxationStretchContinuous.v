(** RelaxationStretchContinuous: in continuous time, the mean length of a
    stretch with the flag up, in seconds, is the steady mass of the
    up-states over the flow into them.

    A finite set of states, rates q x y >= 0 of hopping from x to y, a steady
    spread pi (stationary, not necessarily reversible: the flow into each
    state equals the flow out of it), and a reading that splits the states
    into up (U) and down (N). The flow into U is
    Phi = sum over x in N, y in U of pi x q x y. A stretch is entered at y in
    U with chance e y = (sum over x in N of pi x q x y) / Phi.

    - The mean time to leave U from y, h y, satisfies the equations
      out y * h y - sum over z in U of q y z h z = 1 for y in U, where out y
      is the total rate out of y ([rsc_leave]). Under Doeblin's condition
      in rates (c * pi y <= q x y) they have a solution
      ([rsc_leave_exists]): it is the limit of the uniformized
      iteration, which stays between 0 and 1 / (c pi(N)) and only grows.
    - For any solution, Phi times the mean of h over the entrance spread is
      pi(U) ([rsc_mass_over_flow]). The proof is the stationarity of pi and
      one exchange of the order of summation.
    - In seconds: let s t be any solution of the master equation with the
      chain stopped on leaving U, started from the entrance spread
      ([killed], [s_start]), and S t the chance the stretch is still running
      at time t. S starts at 1 ([rsc_S_start]) and falls at least like
      exp (- c pi(N) t) ([rsc_S_decay]); the time spent up between 0 and T,
      the Newton integral of S, is the mean of h minus what is left
      ([rsc_window_value]); and as T grows it tends to pi(U) / Phi
      ([rsc_mean_stretch_time]): mass over flow, in seconds. *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics. No definition or theorem here mentions a certification
   system, a ledger or a machine step; it imports FiniteSums.v and two
   derivative lemmas from RelaxationContinuous.v.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. The standalone boundary is stated here rather than inferred from
   an import. *)

From Coq Require Import List Reals Lra Psatz Ranalysis1 Ranalysis4 SeqProp.
Import ListNotations.
From Kernel Require Import FiniteSums RelaxationEntropy RelaxationContinuous.
Open Scope R_scope.

Section StretchContinuous.

Variable X : Type.
Variable LX : list X.
Variable q : X -> X -> R.
Variable pi : X -> R.
Variable read : X -> bool.
Hypothesis q_nonneg : forall x y, 0 <= q x y.
Hypothesis pi_nonneg : forall x, 0 <= pi x.

(** The total rate out of a state. *)
Definition rsc_out (x : X) : R := sumL LX (fun y => q x y).

Hypothesis pi_stationary : forall y, In y LX -> sumL LX (fun x => pi x * q x y) = pi y * rsc_out y.
Variable c : R.
Hypothesis c_pos : 0 < c.
Hypothesis doeblin : forall x y, In x LX -> In y LX -> c * pi y <= q x y.

Definition rsc_U (x : X) : R := if read x then 1 else 0.
Definition rsc_N (x : X) : R := if read x then 0 else 1.

Definition rsc_massU : R := sumL LX (fun x => pi x * rsc_U x).
Definition rsc_massN : R := sumL LX (fun x => pi x * rsc_N x).

(** The flow from N into y, and the flow from N into U. *)
Definition rsc_inflow (y : X) : R := sumL LX (fun x => rsc_N x * pi x * q x y).
Definition rsc_Phi : R := sumL LX (fun y => rsc_U y * rsc_inflow y).

Hypothesis Phi_pos : 0 < rsc_Phi.

(** The entrance spread. *)
Definition rsc_entry (y : X) : R := rsc_U y * rsc_inflow y / rsc_Phi.

(** The equations for the mean time to leave U. *)
Definition rsc_leave (h : X -> R) : Prop :=
  forall x, In x LX -> rsc_U x = 1 ->
    rsc_out x * h x - sumL LX (fun y => rsc_U y * q x y * h y) = 1.

(** ** Small facts *)

Lemma rsc_UU : forall x, rsc_U x * rsc_U x = rsc_U x.
Proof. intro x. unfold rsc_U. destruct (read x); ring. Qed.

Lemma rsc_UN : forall x, rsc_U x + rsc_N x = 1.
Proof. intro x. unfold rsc_U, rsc_N. destruct (read x); ring. Qed.

Lemma rsc_U01 : forall x, rsc_U x = 0 \/ rsc_U x = 1.
Proof. intro x. unfold rsc_U. destruct (read x); auto. Qed.

Lemma rsc_U_nonneg : forall x, 0 <= rsc_U x.
Proof. intro x. unfold rsc_U. destruct (read x); lra. Qed.

Lemma rsc_N_nonneg : forall x, 0 <= rsc_N x.
Proof. intro x. unfold rsc_N. destruct (read x); lra. Qed.

Lemma rsc_sum_le : forall (L : list X) (f g : X -> R), (forall a, In a L -> f a <= g a) -> sumL L f <= sumL L g.
Proof.
  intros L f g H. induction L as [| a L IH]; simpl; [lra |].
  pose proof (H a (or_introl eq_refl)). assert (sumL L f <= sumL L g) by (apply IH; intros; apply H; right; assumption). lra.
Qed.

Lemma rsc_le_sum : forall (L : list X) (f : X -> R) a, (forall b, In b L -> 0 <= f b) -> In a L -> f a <= sumL L f.
Proof.
  induction L as [| b L IH]; intros f a Hf Ha; [destruct Ha |].
  rewrite sumL_cons. destruct Ha as [<- | Ha].
  - assert (0 <= sumL L f) by (apply sumL_nonneg; intros; apply Hf; right; assumption). lra.
  - pose proof (Hf b (or_introl eq_refl)).
    pose proof (IH f a (fun b' Hb => Hf b' (or_intror Hb)) Ha). lra.
Qed.

Lemma rsc_out_nonneg : forall x, 0 <= rsc_out x.
Proof. intro x. unfold rsc_out. apply sumL_nonneg. intros. apply q_nonneg. Qed.

(** The rate out of x splits into the rates into U and into N. *)
Lemma rsc_out_split : forall x,
  rsc_out x = sumL LX (fun y => rsc_U y * q x y) + sumL LX (fun y => rsc_N y * q x y).
Proof.
  intro x. unfold rsc_out. rewrite <- sumL_plus. apply sumL_ext. intros y _.
  pose proof (rsc_UN y). nra.
Qed.

(** From every state the rate into N is at least c pi(N). *)
Lemma rsc_into_N : forall x, In x LX -> c * rsc_massN <= sumL LX (fun y => rsc_N y * q x y).
Proof.
  intros x Hx. unfold rsc_massN. rewrite <- sumL_scale_l. apply rsc_sum_le. intros y Hy.
  pose proof (doeblin x y Hx Hy). pose proof (rsc_N_nonneg y). nra.
Qed.

(** A positive flow into U needs weight in N. *)
Lemma rsc_massN_pos : 0 < rsc_massN.
Proof.
  destruct (Rlt_or_le 0 rsc_massN) as [H | H]; [exact H | exfalso].
  assert (Z : forall x, In x LX -> rsc_N x * pi x = 0).
  { intros x Hx.
    assert (A : pi x * rsc_N x <= rsc_massN).
    { unfold rsc_massN. apply (rsc_le_sum LX (fun x => pi x * rsc_N x) x); [| exact Hx].
      intros b _. pose proof (pi_nonneg b). pose proof (rsc_N_nonneg b). nra. }
    pose proof (pi_nonneg x). pose proof (rsc_N_nonneg x). nra. }
  assert (E : rsc_Phi = 0).
  { unfold rsc_Phi. rewrite <- (sumL_zero X LX). apply sumL_ext. intros y _.
    unfold rsc_inflow. rewrite (sumL_ext X LX _ (fun _ => 0)); [rewrite sumL_zero; ring |].
    intros x Hx. rewrite (Z x Hx). ring. }
  lra.
Qed.

(** ** Mass over flow *)

Theorem rsc_mass_over_flow : forall h, rsc_leave h ->
  rsc_Phi * sumL LX (fun y => rsc_entry y * h y) = rsc_massU.
Proof.
  intros h Hh.
  assert (E1 : rsc_Phi * sumL LX (fun y => rsc_entry y * h y) = sumL LX (fun y => rsc_U y * h y * rsc_inflow y)).
  { rewrite <- sumL_scale_l. apply sumL_ext. intros y _. unfold rsc_entry. field. lra. }
  assert (E2 : forall y, In y LX ->
    rsc_inflow y = pi y * rsc_out y - sumL LX (fun x => rsc_U x * pi x * q x y)).
  { intros y Hy. rewrite <- (pi_stationary y Hy). unfold rsc_inflow. rewrite <- sumL_minus.
    apply sumL_ext. intros x _. pose proof (rsc_UN x). nra. }
  rewrite E1.
  transitivity (sumL LX (fun x => rsc_U x * pi x * (rsc_out x * h x - sumL LX (fun y => rsc_U y * q x y * h y)))).
  - transitivity (sumL LX (fun y => rsc_U y * pi y * (rsc_out y * h y))
                  - sumL LX (fun y => sumL LX (fun x => rsc_U y * h y * (rsc_U x * pi x * q x y)))).
    + rewrite <- sumL_minus. apply sumL_ext. intros y Hy. rewrite (E2 y Hy).
      rewrite (sumL_scale_l X LX (rsc_U y * h y) (fun x => rsc_U x * pi x * q x y)). ring.
    + rewrite sumL_swap. rewrite <- sumL_minus. apply sumL_ext. intros x _.
      assert (Hs : sumL LX (fun y => rsc_U y * h y * (rsc_U x * pi x * q x y))
                   = rsc_U x * pi x * sumL LX (fun y => rsc_U y * q x y * h y))
        by (rewrite <- sumL_scale_l; apply sumL_ext; intros; ring).
      rewrite Hs. ring.
  - unfold rsc_massU. apply sumL_ext. intros x Hx.
    destruct (rsc_U01 x) as [H0 | H1]; rewrite ?H0, ?H1; [ring |].
    rewrite (Hh x Hx H1). ring.
Qed.

(** ** The leaving times exist *)

(** A uniform clock rate above every rate out. *)
Definition rsc_Lam : R := 1 + sumL LX rsc_out.

Lemma rsc_Lam_pos : 0 < rsc_Lam.
Proof.
  unfold rsc_Lam. assert (0 <= sumL LX rsc_out) by (apply sumL_nonneg; intros; apply rsc_out_nonneg). lra.
Qed.

Lemma rsc_A_nonneg : forall x, In x LX -> 0 <= 1 - rsc_out x / rsc_Lam.
Proof.
  intros x Hx. pose proof rsc_Lam_pos as HL.
  assert (Ho : rsc_out x <= rsc_Lam).
  { unfold rsc_Lam. pose proof (rsc_le_sum LX rsc_out x (fun b _ => rsc_out_nonneg b) Hx). lra. }
  assert (rsc_out x / rsc_Lam <= 1).
  { apply (Rmult_le_reg_r rsc_Lam); [exact HL |]. unfold Rdiv.
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra. }
  lra.
Qed.

(** The bound the leaving times stay under. *)
Definition rsc_M : R := / (c * rsc_massN).

Lemma rsc_M_pos : 0 < rsc_M.
Proof. unfold rsc_M. apply Rinv_0_lt_compat. pose proof rsc_massN_pos. nra. Qed.

(** One tick of the uniformized clock: a tick takes 1 / Lam seconds on
    average, and the chain stays put or hops along a rate. *)
Definition rsc_step (g : X -> R) (x : X) : R :=
  rsc_U x * (/ rsc_Lam + (1 - rsc_out x / rsc_Lam) * g x
             + / rsc_Lam * sumL LX (fun y => rsc_U y * q x y * g y)).

Fixpoint rsc_it (n : nat) : X -> R :=
  match n with
  | O => fun _ => 0
  | S n => rsc_step (rsc_it n)
  end.

Lemma rsc_step_mono : forall g1 g2, (forall y, In y LX -> g1 y <= g2 y) ->
  forall x, In x LX -> rsc_step g1 x <= rsc_step g2 x.
Proof.
  intros g1 g2 H x Hx. unfold rsc_step. apply Rmult_le_compat_l; [apply rsc_U_nonneg |].
  pose proof (rsc_A_nonneg x Hx). pose proof (H x Hx). pose proof rsc_Lam_pos.
  assert (Hs : sumL LX (fun y => rsc_U y * q x y * g1 y) <= sumL LX (fun y => rsc_U y * q x y * g2 y)).
  { apply rsc_sum_le. intros y Hy. apply Rmult_le_compat_l; [| exact (H y Hy)].
    pose proof (rsc_U_nonneg y). pose proof (q_nonneg x y). nra. }
  assert (0 < / rsc_Lam) by (apply Rinv_0_lt_compat; lra).
  nra.
Qed.

Lemma rsc_step_bound : forall g, (forall y, In y LX -> 0 <= g y <= rsc_M) ->
  forall x, In x LX -> 0 <= rsc_step g x <= rsc_M.
Proof.
  intros g H x Hx. pose proof rsc_M_pos as HM. unfold rsc_step.
  destruct (rsc_U01 x) as [H0 | H1]; rewrite ?H0, ?H1; [lra |].
  pose proof (rsc_A_nonneg x Hx) as HA. pose proof (H x Hx) as Hg. pose proof rsc_Lam_pos as HL.
  assert (HiL : 0 < / rsc_Lam) by (apply Rinv_0_lt_compat; lra).
  set (SU := sumL LX (fun y => rsc_U y * q x y)).
  set (SN := sumL LX (fun y => rsc_N y * q x y)).
  assert (Hs0 : 0 <= sumL LX (fun y => rsc_U y * q x y * g y)).
  { apply sumL_nonneg. intros y Hy. pose proof (rsc_U_nonneg y). pose proof (q_nonneg x y).
    pose proof (H y Hy). apply Rmult_le_pos; [nra | lra]. }
  assert (Hs1 : sumL LX (fun y => rsc_U y * q x y * g y) <= SU * rsc_M).
  { unfold SU. rewrite <- sumL_scale_r. apply rsc_sum_le. intros y Hy.
    apply Rmult_le_compat_l; [| apply (H y Hy)].
    pose proof (rsc_U_nonneg y). pose proof (q_nonneg x y). nra. }
  assert (Ho : rsc_out x = SU + SN) by (apply rsc_out_split).
  assert (HN : c * rsc_massN <= SN) by (apply rsc_into_N; exact Hx).
  assert (HMk : rsc_M * (c * rsc_massN) = 1).
  { unfold rsc_M. rewrite Rinv_l; [reflexivity |]. pose proof rsc_massN_pos. nra. }
  assert (Hdiv : rsc_out x / rsc_Lam = rsc_out x * / rsc_Lam) by reflexivity.
  rewrite Hdiv. split.
  - assert (0 <= (1 - rsc_out x * / rsc_Lam) * g x) by (apply Rmult_le_pos; [rewrite <- Hdiv; exact HA | lra]).
    assert (0 <= / rsc_Lam * sumL LX (fun y => rsc_U y * q x y * g y)) by (apply Rmult_le_pos; lra).
    lra.
  - assert (E1 : (1 - rsc_out x * / rsc_Lam) * g x <= (1 - rsc_out x * / rsc_Lam) * rsc_M)
      by (apply Rmult_le_compat_l; [rewrite <- Hdiv; exact HA | lra]).
    assert (E2 : / rsc_Lam * sumL LX (fun y => rsc_U y * q x y * g y) <= / rsc_Lam * (SU * rsc_M))
      by (apply Rmult_le_compat_l; lra).
    assert (E3 : / rsc_Lam * rsc_M * (c * rsc_massN) <= / rsc_Lam * rsc_M * SN).
    { apply Rmult_le_compat_l; [apply Rmult_le_pos; lra | exact HN]. }
    rewrite Ho in E1. nra.
Qed.

Lemma rsc_it_bound : forall n x, In x LX -> 0 <= rsc_it n x <= rsc_M.
Proof.
  induction n as [| n IH]; intros x Hx.
  - simpl. pose proof rsc_M_pos. lra.
  - cbn [rsc_it]. apply rsc_step_bound; [exact IH | exact Hx].
Qed.

Lemma rsc_it_grow : forall n x, In x LX -> rsc_it n x <= rsc_it (S n) x.
Proof.
  induction n as [| n IH]; intros x Hx.
  - cbn [rsc_it]. exact (proj1 (rsc_it_bound 1 x Hx)).
  - cbn [rsc_it]. apply rsc_step_mono; [exact IH | exact Hx].
Qed.

Definition rsc_seq (x : X) (n : nat) : R := Rmin rsc_M (rsc_it n x).

Lemma rsc_seq_ub : forall x, has_ub (rsc_seq x).
Proof. intro x. exists rsc_M. intros r [n ->]. unfold rsc_seq. apply Rbasic_fun.Rmin_l. Qed.

(** The leaving time from x, the limit of the ticks. *)
Definition rsc_h (x : X) : R :=
  proj1_sig (completeness (EUn (rsc_seq x)) (rsc_seq_ub x) (EUn_noempty (rsc_seq x))).

Lemma rsc_cv_ext : forall (u v : nat -> R) l, (forall n, u n = v n) -> Un_cv u l -> Un_cv v l.
Proof. intros u v l E H eps He. destruct (H eps He) as [N HN]. exists N. intros n Hn. rewrite <- E. apply HN. exact Hn. Qed.

Lemma rsc_cv_const : forall k, Un_cv (fun _ => k) k.
Proof. intros k eps He. exists O. intros n _. unfold R_dist. replace (k - k) with 0 by ring. rewrite Rabs_R0. exact He. Qed.

Lemma rsc_h_lim : forall x, In x LX -> Un_cv (fun n => rsc_it n x) (rsc_h x).
Proof.
  intros x Hx.
  assert (E : forall n, rsc_seq x n = rsc_it n x).
  { intro n. unfold rsc_seq. apply Rmin_right. apply rsc_it_bound. exact Hx. }
  assert (Hg : Un_growing (rsc_seq x)).
  { intro n. rewrite !E. apply rsc_it_grow. exact Hx. }
  apply (rsc_cv_ext (rsc_seq x)); [exact E |].
  unfold rsc_h. destruct (completeness _ _ _) as [l Hl]. simpl.
  apply Un_cv_crit_lub; assumption.
Qed.

Lemma rsc_cv_sum : forall (L : list X) (a : nat -> X -> R) (l k : X -> R),
  (forall y, In y L -> Un_cv (fun n => a n y) (l y)) ->
  Un_cv (fun n => sumL L (fun y => k y * a n y)) (sumL L (fun y => k y * l y)).
Proof.
  induction L as [| b L IH]; intros a l k H.
  - simpl. apply rsc_cv_const.
  - simpl. apply (CV_plus (fun n => k b * a n b) (fun n => sumL L (fun y => k y * a n y))).
    + apply (CV_mult (fun _ => k b) (fun n => a n b)); [apply rsc_cv_const | apply H; left; reflexivity].
    + apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma rsc_h_fix : forall x, In x LX -> rsc_h x = rsc_step rsc_h x.
Proof.
  intros x Hx.
  assert (Hs := rsc_cv_sum LX (fun n y => rsc_it n y) rsc_h (fun y => rsc_U y * q x y) (fun y Hy => rsc_h_lim y Hy)).
  assert (Hc : Un_cv (fun n => rsc_U x * / rsc_Lam + rsc_U x * (1 - rsc_out x / rsc_Lam) * rsc_it n x
                     + rsc_U x * / rsc_Lam * sumL LX (fun y => rsc_U y * q x y * rsc_it n y))
                     (rsc_U x * / rsc_Lam + rsc_U x * (1 - rsc_out x / rsc_Lam) * rsc_h x
                     + rsc_U x * / rsc_Lam * sumL LX (fun y => rsc_U y * q x y * rsc_h y))).
  { apply CV_plus; [apply CV_plus |].
    - apply rsc_cv_const.
    - apply CV_mult; [apply rsc_cv_const | apply rsc_h_lim; exact Hx].
    - apply CV_mult; [apply rsc_cv_const | exact Hs]. }
  assert (Hshift : Un_cv (fun n => rsc_it (S n) x) (rsc_h x)).
  { intros eps He. destruct (rsc_h_lim x Hx eps He) as [N HN]. exists N. intros n Hn. apply HN. lia. }
  apply (UL_sequence (fun n => rsc_it (S n) x)); [exact Hshift |].
  assert (Eq : forall n, rsc_U x * / rsc_Lam + rsc_U x * (1 - rsc_out x / rsc_Lam) * rsc_it n x
                     + rsc_U x * / rsc_Lam * sumL LX (fun y => rsc_U y * q x y * rsc_it n y) = rsc_it (S n) x)
    by (intro n; cbn [rsc_it]; unfold rsc_step; ring).
  apply (rsc_cv_ext _ _ _ Eq) in Hc.
  replace (rsc_step rsc_h x) with (rsc_U x * / rsc_Lam + rsc_U x * (1 - rsc_out x / rsc_Lam) * rsc_h x
                     + rsc_U x * / rsc_Lam * sumL LX (fun y => rsc_U y * q x y * rsc_h y)) by (unfold rsc_step; ring).
  exact Hc.
Qed.

(** The leaving-time equations have a solution. *)
Theorem rsc_leave_exists : rsc_leave rsc_h.
Proof.
  intros x Hx H1. pose proof (rsc_h_fix x Hx) as E. unfold rsc_step in E. rewrite H1 in E.
  pose proof rsc_Lam_pos as HL.
  set (Sg := sumL LX (fun y => rsc_U y * q x y * rsc_h y)) in *.
  assert (K : rsc_out x * rsc_h x - Sg - 1
              = - rsc_Lam * (1 * (/ rsc_Lam + (1 - rsc_out x / rsc_Lam) * rsc_h x + / rsc_Lam * Sg) - rsc_h x))
    by (field; lra).
  rewrite <- E in K. lra.
Qed.

(** Mass over flow, for the leaving times themselves. *)
Corollary rsc_mean_leave : rsc_Phi * sumL LX (fun y => rsc_entry y * rsc_h y) = rsc_massU.
Proof. apply rsc_mass_over_flow. exact rsc_leave_exists. Qed.

(** ** Stretches in seconds *)

Variable s : R -> X -> R.
Hypothesis s_nonneg : forall t x, 0 <= t -> 0 <= s t x.
(** The master equation with the chain stopped on leaving U. *)
Hypothesis killed : forall t y, derivable_pt_lim (fun r => s r y) t
  (rsc_U y * (sumL LX (fun x => rsc_U x * s t x * q x y) - s t y * rsc_out y)).
Hypothesis s_start : forall y, In y LX -> s 0 y = rsc_entry y.

(** A weighted total of the running stretches. *)
Definition rsc_G (g : X -> R) (t : R) : R := sumL LX (fun y => rsc_U y * g y * s t y).

(** The chance the stretch is still running at time t: weight 1. *)
Definition rsc_S (t : R) : R := rsc_G (fun _ => 1) t.

Lemma rsc_G_deriv : forall g t, derivable_pt_lim (rsc_G g) t
  (- sumL LX (fun x => rsc_U x * s t x * (rsc_out x * g x - sumL LX (fun y => rsc_U y * q x y * g y)))).
Proof.
  intros g t. unfold rsc_G.
  eapply rcd_lim_ext.
  - apply (rcd_sum_deriv X LX (fun y r => rsc_U y * g y * s r y)
      (fun y => rsc_U y * g y * (rsc_U y * (sumL LX (fun x => rsc_U x * s t x * q x y) - s t y * rsc_out y))) t).
    intros y _. apply (derivable_pt_lim_scal (fun r => s r y) (rsc_U y * g y) t _ (killed t y)).
  - transitivity (sumL LX (fun y => sumL LX (fun x => rsc_U y * g y * (rsc_U x * s t x * q x y)))
                  - sumL LX (fun y => rsc_U y * s t y * (rsc_out y * g y))).
    + rewrite <- sumL_minus. apply sumL_ext. intros y _.
      rewrite (sumL_scale_l X LX (rsc_U y * g y) (fun x => rsc_U x * s t x * q x y)).
      transitivity (rsc_U y * rsc_U y * g y * (sumL LX (fun x => rsc_U x * s t x * q x y) - s t y * rsc_out y)); [ring |].
      rewrite rsc_UU. ring.
    + rewrite sumL_swap, <- sumL_minus.
      match goal with |- _ = - sumL LX ?F => replace (- sumL LX F) with (-1 * sumL LX F) by ring end.
      rewrite <- (sumL_scale_l X LX (-1)). apply sumL_ext. intros x _.
      assert (Hs : sumL LX (fun y => rsc_U y * g y * (rsc_U x * s t x * q x y))
                   = rsc_U x * s t x * sumL LX (fun y => rsc_U y * q x y * g y))
        by (rewrite <- sumL_scale_l; apply sumL_ext; intros; ring).
      rewrite Hs. ring.
Qed.

(** With the leaving times, the weighted total falls at the rate S. *)
Lemma rsc_F_deriv : forall h, rsc_leave h -> forall t, derivable_pt_lim (rsc_G h) t (- rsc_S t).
Proof.
  intros h Hh t. eapply rcd_lim_ext; [apply rsc_G_deriv |].
  f_equal. unfold rsc_S, rsc_G. apply sumL_ext. intros x Hx.
  destruct (rsc_U01 x) as [H0 | H1]; rewrite ?H0, ?H1; [ring |].
  rewrite (Hh x Hx H1). ring.
Qed.

(** S falls at the rate out into N. *)
Lemma rsc_S_deriv : forall t, derivable_pt_lim rsc_S t
  (- sumL LX (fun x => rsc_U x * s t x * sumL LX (fun y => rsc_N y * q x y))).
Proof.
  intro t. unfold rsc_S. eapply rcd_lim_ext; [apply rsc_G_deriv |].
  f_equal. apply sumL_ext. intros x _. rewrite (rsc_out_split x).
  rewrite (sumL_ext X LX (fun y => rsc_U y * q x y * 1) (fun y => rsc_U y * q x y)) by (intros; ring).
  ring.
Qed.

(** A stretch is surely running at time 0. *)
Theorem rsc_S_start : rsc_S 0 = 1.
Proof.
  unfold rsc_S, rsc_G.
  rewrite (sumL_ext X LX _ (fun y => rsc_U y * rsc_inflow y * / rsc_Phi)).
  - rewrite sumL_scale_r. fold rsc_Phi. field. lra.
  - intros y Hy. rewrite (s_start y Hy). unfold rsc_entry. unfold Rdiv.
    transitivity (rsc_U y * rsc_U y * rsc_inflow y * / rsc_Phi); [ring |]. rewrite rsc_UU. ring.
Qed.

Lemma rsc_S_nonneg : forall t, 0 <= t -> 0 <= rsc_S t.
Proof.
  intros t Ht. unfold rsc_S, rsc_G. apply sumL_nonneg. intros y _.
  pose proof (rsc_U_nonneg y). pose proof (s_nonneg t y Ht). nra.
Qed.

(** The chance the stretch is still running falls at least like
    exp (- c pi(N) t). *)
Theorem rsc_S_decay : forall b, 0 <= b -> rsc_S b <= exp (- (c * rsc_massN * b)).
Proof.
  intros b Hb. set (k := c * rsc_massN).
  assert (Hk : 0 < k) by (unfold k; pose proof rsc_massN_pos; nra).
  set (f := fun t => rsc_S t * exp (k * t)).
  set (f' := fun t => (- sumL LX (fun x => rsc_U x * s t x * sumL LX (fun y => rsc_N y * q x y))) * exp (k * t)
                      + rsc_S t * (k * exp (k * t))).
  assert (Hf : forall t, derivable_pt_lim f t (f' t)).
  { intro t.
    assert (He : derivable_pt_lim (fun r => exp (k * r)) t (k * exp (k * t))).
    { assert (Hl : derivable_pt_lim (fun r => k * r) t k).
      { eapply rcd_lim_ext; [apply (derivable_pt_lim_scal id k t 1 (derivable_pt_lim_id t)) | ring]. }
      eapply rcd_lim_ext; [apply (derivable_pt_lim_comp (fun r => k * r) exp t k (exp (k * t)) Hl (derivable_pt_lim_exp (k * t))) | ring]. }
    apply (derivable_pt_lim_mult rsc_S (fun r => exp (k * r)) t _ _ (rsc_S_deriv t) He). }
  assert (Hneg : forall t, 0 <= t -> f' t <= 0).
  { intros t Ht. unfold f'.
    assert (G : k * rsc_S t <= sumL LX (fun x => rsc_U x * s t x * sumL LX (fun y => rsc_N y * q x y))).
    { unfold rsc_S, rsc_G. rewrite <- sumL_scale_l. apply rsc_sum_le. intros x Hx.
      pose proof (rsc_into_N x Hx). pose proof (rsc_U_nonneg x). pose proof (s_nonneg t x Ht).
      assert (0 <= rsc_U x * s t x) by nra. fold k in H. nra. }
    pose proof (exp_pos (k * t)). nra. }
  assert (Hfb : f b <= f 0).
  { destruct (Req_dec b 0) as [-> | Hne]; [lra |].
    destruct (MVT_cor2 f f' 0 b ltac:(lra) (fun t Ht => Hf t)) as [m [Hm Hmr]].
    pose proof (Hneg m ltac:(lra)). nra. }
  unfold f in Hfb. rewrite rsc_S_start in Hfb. rewrite Rmult_0_r, exp_0, Rmult_1_r in Hfb.
  assert (E : exp (- (k * b)) * exp (k * b) = 1) by (rewrite <- exp_plus; replace (- (k * b) + k * b) with 0 by ring; apply exp_0).
  pose proof (exp_pos (k * b)). pose proof (exp_pos (- (k * b))).
  apply (Rmult_le_reg_r (exp (k * b))); [assumption |]. rewrite E. exact Hfb.
Qed.

(** The time spent up between 0 and T, as a Newton integral of S. *)
Lemma rsc_negG_deriv : forall h, rsc_leave h -> forall t, derivable_pt_lim (opp_fct (rsc_G h)) t (rsc_S t).
Proof.
  intros h Hh t. eapply rcd_lim_ext; [apply derivable_pt_lim_opp; apply rsc_F_deriv; exact Hh | ring].
Qed.

Definition rsc_window (h : X -> R) (Hh : rsc_leave h) (T : R) (HT : 0 <= T) : Newton_integrable rsc_S 0 T.
Proof.
  exists (opp_fct (rsc_G h)). left. split; [| exact HT].
  intros x Hx. exists (exist _ (rsc_S x) (rsc_negG_deriv h Hh x)). reflexivity.
Defined.

(** At time 0 the weighted total is the mean leaving time over the
    entrance spread. *)
Lemma rsc_G_start : forall h, rsc_G h 0 = sumL LX (fun y => rsc_entry y * h y).
Proof.
  intro h. unfold rsc_G. apply sumL_ext. intros y Hy. rewrite (s_start y Hy). unfold rsc_entry, Rdiv.
  transitivity (rsc_U y * rsc_U y * rsc_inflow y * / rsc_Phi * h y); [ring |]. rewrite rsc_UU. ring.
Qed.

Theorem rsc_window_value : forall h (Hh : rsc_leave h) T (HT : 0 <= T),
  NewtonInt rsc_S 0 T (rsc_window h Hh T HT) = rsc_massU / rsc_Phi - rsc_G h T.
Proof.
  intros h Hh T HT. unfold NewtonInt, rsc_window. simpl. unfold opp_fct.
  rewrite rsc_G_start. rewrite <- (rsc_mass_over_flow h Hh). field. lra.
Qed.

(** What is left at time T is at most the largest leaving time times S T. *)
Lemma rsc_G_small : forall h T, 0 <= T ->
  Rabs (rsc_G h T) <= sumL LX (fun y => Rabs (h y)) * rsc_S T.
Proof.
  intros h T HT. set (B := sumL LX (fun y => Rabs (h y))).
  assert (HB : forall y, In y LX -> Rabs (h y) <= B).
  { intros y Hy. apply (rsc_le_sum LX (fun y => Rabs (h y)) y); [intros; apply Rabs_pos | exact Hy]. }
  unfold rsc_S, rsc_G. rewrite <- sumL_scale_l. apply Rabs_le. split.
  - assert (P : 0 <= sumL LX (fun y => rsc_U y * h y * s T y + B * (rsc_U y * 1 * s T y))).
    { apply sumL_nonneg. intros y Hy.
      pose proof (HB y Hy). pose proof (Rle_abs (- h y)) as A. rewrite Rabs_Ropp in A.
      pose proof (rsc_U_nonneg y). pose proof (s_nonneg T y HT).
      assert (0 <= rsc_U y * s T y) by nra. nra. }
    rewrite sumL_plus in P. lra.
  - apply rsc_sum_le. intros y Hy.
    pose proof (HB y Hy). pose proof (Rle_abs (h y)). pose proof (rsc_U_nonneg y). pose proof (s_nonneg T y HT).
    assert (0 <= rsc_U y * s T y) by nra. nra.
Qed.

(** The mean length of a stretch with the flag up, in seconds, is pi(U) / Phi. *)
Theorem rsc_mean_stretch_time : forall h (Hh : rsc_leave h) eps, 0 < eps ->
  exists T0, forall T (HT : 0 <= T), T0 <= T ->
    Rabs (NewtonInt rsc_S 0 T (rsc_window h Hh T HT) - rsc_massU / rsc_Phi) < eps.
Proof.
  intros h Hh eps He. set (B := sumL LX (fun y => Rabs (h y))). set (k := c * rsc_massN).
  assert (Hk : 0 < k) by (unfold k; pose proof rsc_massN_pos; nra).
  assert (HB : 0 <= B) by (apply sumL_nonneg; intros; apply Rabs_pos).
  exists (B / (k * eps) + 1). intros T HT HT0.
  rewrite rsc_window_value. replace (rsc_massU / rsc_Phi - rsc_G h T - rsc_massU / rsc_Phi) with (- rsc_G h T) by ring.
  rewrite Rabs_Ropp.
  pose proof (rsc_G_small h T HT) as G. fold B in G.
  pose proof (rsc_S_decay T HT) as D. fold k in D.
  assert (Ex : exp (- (k * T)) <= / (1 + k * T)).
  { rewrite exp_Ropp. apply Rinv_le_contravar; [nra |]. apply re_exp_ge. }
  assert (Hq : B <= k * eps * T).
  { assert (B / (k * eps) <= T) by lra.
    apply (Rmult_le_compat_l (k * eps)) in H; [| nra].
    replace (k * eps * (B / (k * eps))) with B in H by (field; nra). lra. }
  assert (HS : rsc_S T <= / (1 + k * T)) by lra.
  apply Rle_lt_trans with (B * / (1 + k * T)).
  - apply Rle_trans with (B * rsc_S T); [exact G | apply Rmult_le_compat_l; [exact HB | exact HS]].
  - apply (Rmult_lt_reg_r (1 + k * T)); [nra |].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by nra. nra.
Qed.

(** Together: the leaving times exist, and the time spent up tends to
    pi(U) / Phi. *)
Corollary rsc_stretch_identity : forall eps, 0 < eps ->
  exists T0, forall T (HT : 0 <= T), T0 <= T ->
    Rabs (NewtonInt rsc_S 0 T (rsc_window rsc_h rsc_leave_exists T HT) - rsc_massU / rsc_Phi) < eps.
Proof. intros eps He. exact (rsc_mean_stretch_time rsc_h rsc_leave_exists eps He). Qed.

End StretchContinuous.

Print Assumptions rsc_mass_over_flow.
Print Assumptions rsc_leave_exists.
Print Assumptions rsc_S_decay.
Print Assumptions rsc_window_value.
Print Assumptions rsc_mean_stretch_time.
Print Assumptions rsc_stretch_identity.
