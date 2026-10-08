(** RelaxationContinuous: the relaxation bound in continuous time.

    A finite set of states, rates q x y >= 0 of hopping from x to y, a
    positive steady spread pi with detailed balance, pi x q x y = pi y q y x.
    Let p t be any spread over time that solves the master equation

      d/dt p t x = sum_y (p t y q y x - p t x q x y)

    and stays positive. Write D for the relative entropy to pi and sigma for
    the entropy production rate,

      sigma = 1/2 sum_x sum_y (p x q x y - p y q y x)
                 (ln (p x / pi x) - ln (p y / pi y)),

    which under detailed balance is the familiar
    1/2 sum (p x q x y - p y q y x) ln (p x q x y / (p y q y x)) on every
    hop with a positive rate.

    - The entropy production rate is never negative ([rcd_sigma_nonneg]).
    - The relative entropy falls at exactly that rate:
      d/dt D (p t) = - sigma (p t) ([rcd_D_derivative]), the continuous
      form of re_sigma_is_drop.
    - So D never rises along the run ([rcd_D_monotone]).
    - The entropy produced between times a and b, the Newton integral of
      sigma, is D (p a) - D (p b) ([rcd_produced_window]), never negative and
      never more than D (p a) ([rcd_produced_bounds]). *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics. No definition or theorem here mentions a certification
   system, a ledger or a machine step; it imports only FiniteSums.v.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. The standalone boundary is stated here rather than inferred from
   an import. *)

From Coq Require Import List Reals Lra Psatz Ranalysis1 Ranalysis4.
Import ListNotations.
From Kernel Require Import FiniteSums.
Open Scope R_scope.

Section Continuous.

Variable X : Type.
Variable LX : list X.
Variable q : X -> X -> R.
Variable pi : X -> R.
Hypothesis q_nonneg : forall x y, 0 <= q x y.
Hypothesis pi_pos : forall x, 0 < pi x.
Hypothesis detailed_balance : forall x y, pi x * q x y = pi y * q y x.

Definition rcd_flow (r : X -> R) (x : X) : R := sumL LX (fun y => r y * q y x - r x * q x y).

Definition rcd_D (r : X -> R) : R := sumL LX (fun x => r x * ln (r x / pi x)).

Definition rcd_L (r : X -> R) (x : X) : R := ln (r x / pi x).

Definition rcd_sigma (r : X -> R) : R :=
  / 2 * sumL LX (fun x => sumL LX (fun y => (r x * q x y - r y * q y x) * (rcd_L r x - rcd_L r y))).

(** ** The production rate is nonnegative *)

Lemma rcd_ln_mono : forall a b, 0 < a -> 0 < b -> 0 <= (a - b) * (ln a - ln b).
Proof.
  intros a b Ha Hb. destruct (Rle_lt_dec a b) as [H | H].
  - destruct (Req_dec a b) as [-> | Hne]; [lra |].
    assert (ln a < ln b) by (apply ln_increasing; lra). nra.
  - assert (ln b < ln a) by (apply ln_increasing; lra). nra.
Qed.

Theorem rcd_sigma_nonneg : forall r, (forall x, 0 < r x) -> 0 <= rcd_sigma r.
Proof.
  intros r Hr. unfold rcd_sigma. apply Rmult_le_pos; [lra |].
  apply sumL_nonneg. intros x _. apply sumL_nonneg. intros y _.
  assert (E : r x * q x y - r y * q y x = q x y * pi x * (r x / pi x - r y / pi y)).
  { assert (Hq : r y * q y x = r y * (pi x * q x y) / pi y).
    { rewrite detailed_balance. field. pose proof (pi_pos y). lra. }
    rewrite Hq. field. split; pose proof (pi_pos x); pose proof (pi_pos y); lra. }
  rewrite E. unfold rcd_L.
  assert (Ha : 0 < r x / pi x) by (apply Rdiv_lt_0_compat; [apply Hr | apply pi_pos]).
  assert (Hb : 0 < r y / pi y) by (apply Rdiv_lt_0_compat; [apply Hr | apply pi_pos]).
  pose proof (rcd_ln_mono _ _ Ha Hb) as H. pose proof (q_nonneg x y). pose proof (pi_pos x).
  rewrite Rmult_assoc. apply Rmult_le_pos; [apply Rmult_le_pos; lra | exact H].
Qed.

(** ** The derivative of the relative entropy *)

Lemma rcd_lim_ext : forall f t l l', derivable_pt_lim f t l -> l = l' -> derivable_pt_lim f t l'.
Proof. intros f t l l' H <-. exact H. Qed.

Lemma rcd_sum_deriv : forall (L : list X) (fs : X -> R -> R) (ds : X -> R) t,
  (forall x, In x L -> derivable_pt_lim (fs x) t (ds x)) ->
  derivable_pt_lim (fun s => sumL L (fun x => fs x s)) t (sumL L ds).
Proof.
  intros L fs ds t. induction L as [| a L IH]; intro H.
  - simpl. apply (derivable_pt_lim_const 0 t).
  - simpl. apply (derivable_pt_lim_plus (fs a) (fun s => sumL L (fun x => fs x s))).
    + apply H. left. reflexivity.
    + apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Variable p : R -> X -> R.
Hypothesis p_pos : forall t x, 0 < p t x.
Hypothesis master : forall t x, derivable_pt_lim (fun s => p s x) t (rcd_flow (p t) x).

Lemma rcd_term_deriv : forall t x,
  derivable_pt_lim (fun s => p s x * ln (p s x / pi x)) t (rcd_flow (p t) x * (rcd_L (p t) x + 1)).
Proof.
  intros t x. set (d := rcd_flow (p t) x).
  assert (Hu : derivable_pt_lim (mult_fct (fun s => p s x) (fct_cte (/ pi x))) t (d * / pi x + p t x * 0)).
  { apply (derivable_pt_lim_mult (fun s => p s x) (fct_cte (/ pi x))); [apply master | apply derivable_pt_lim_const]. }
  assert (Hpos : 0 < p t x / pi x) by (apply Rdiv_lt_0_compat; [apply p_pos | apply pi_pos]).
  assert (Hl : derivable_pt_lim (comp ln (mult_fct (fun s => p s x) (fct_cte (/ pi x)))) t
                 (/ (p t x / pi x) * (d * / pi x + p t x * 0))).
  { apply derivable_pt_lim_comp; [exact Hu |]. apply derivable_pt_lim_ln. exact Hpos. }
  pose proof (derivable_pt_lim_mult (fun s => p s x) (comp ln (mult_fct (fun s => p s x) (fct_cte (/ pi x))))
    t d _ (master t x) Hl) as Hm.
  eapply rcd_lim_ext; [exact Hm |].
  unfold comp, mult_fct, fct_cte, rcd_L. unfold Rdiv.
  pose proof (p_pos t x). pose proof (pi_pos x). field. split; lra.
Qed.

Lemma rcd_flow_total : forall r, sumL LX (rcd_flow r) = 0.
Proof.
  intro r. unfold rcd_flow.
  set (S := sumL LX (fun x => sumL LX (fun y => r y * q y x - r x * q x y))).
  assert (Hsw : S = sumL LX (fun y => sumL LX (fun x => r y * q y x - r x * q x y))) by apply sumL_swap.
  assert (Hneg : sumL LX (fun y => sumL LX (fun x => r y * q y x - r x * q x y)) = -1 * S).
  { unfold S. rewrite <- sumL_scale_l. apply sumL_ext. intros y _.
    rewrite <- sumL_scale_l. apply sumL_ext. intros x _. ring. }
  lra.
Qed.

Lemma rcd_flow_L : forall r, sumL LX (fun x => rcd_flow r x * rcd_L r x) = - rcd_sigma r.
Proof.
  intro r. unfold rcd_sigma, rcd_flow.
  set (A := sumL LX (fun x => sumL LX (fun y => (r x * q x y - r y * q y x) * rcd_L r x))).
  set (B := sumL LX (fun x => sumL LX (fun y => (r x * q x y - r y * q y x) * rcd_L r y))).
  assert (E1 : sumL LX (fun x => sumL LX (fun y => r y * q y x - r x * q x y) * rcd_L r x) = -1 * A).
  { unfold A. rewrite <- sumL_scale_l. apply sumL_ext. intros x _.
    rewrite <- sumL_scale_r, <- sumL_scale_l. apply sumL_ext. intros y _. ring. }
  assert (E2 : B = -1 * A).
  { unfold A, B. rewrite sumL_swap. rewrite <- sumL_scale_l. apply sumL_ext. intros x _.
    rewrite <- sumL_scale_l. apply sumL_ext. intros y _. ring. }
  assert (E3 : sumL LX (fun x => sumL LX (fun y => (r x * q x y - r y * q y x) * (rcd_L r x - rcd_L r y))) = A - B).
  { unfold A, B. rewrite <- sumL_minus. apply sumL_ext. intros x _. rewrite <- sumL_minus.
    apply sumL_ext. intros y _. ring. }
  rewrite E1, E3, E2. field.
Qed.

(** The relative entropy falls at exactly the production rate. *)
Theorem rcd_D_derivative : forall t, derivable_pt_lim (fun s => rcd_D (p s)) t (- rcd_sigma (p t)).
Proof.
  intro t. unfold rcd_D.
  eapply rcd_lim_ext.
  - apply (rcd_sum_deriv LX (fun x s => p s x * ln (p s x / pi x)) (fun x => rcd_flow (p t) x * (rcd_L (p t) x + 1)) t).
    intros x _. apply rcd_term_deriv.
  - transitivity (sumL LX (fun x => rcd_flow (p t) x * rcd_L (p t) x) + sumL LX (rcd_flow (p t))).
    + rewrite <- sumL_plus. apply sumL_ext. intros. ring.
    + rewrite rcd_flow_total, rcd_flow_L. ring.
Qed.

(** So the relative entropy never rises along the run. *)
Theorem rcd_D_monotone : forall t1 t2, t1 <= t2 -> rcd_D (p t2) <= rcd_D (p t1).
Proof.
  intros t1 t2 H. destruct (Req_dec t1 t2) as [-> | Hne]; [lra |].
  destruct (MVT_cor2 (fun s => rcd_D (p s)) (fun s => - rcd_sigma (p s)) t1 t2 ltac:(lra)
    (fun c _ => rcd_D_derivative c)) as [c [Hc _]].
  pose proof (rcd_sigma_nonneg (p c) (p_pos c)). nra.
Qed.

(** ** The entropy produced over a window of time *)

Lemma rcd_neg_D_deriv : forall t,
  derivable_pt_lim (opp_fct (fun s => rcd_D (p s))) t (rcd_sigma (p t)).
Proof.
  intro t. eapply rcd_lim_ext; [apply derivable_pt_lim_opp; apply rcd_D_derivative | ring].
Qed.

Definition rcd_window (a b : R) (Hab : a <= b) : Newton_integrable (fun t => rcd_sigma (p t)) a b.
Proof.
  exists (opp_fct (fun s => rcd_D (p s))). left. split; [| exact Hab].
  intros x _. exists (exist _ (rcd_sigma (p x)) (rcd_neg_D_deriv x)). reflexivity.
Defined.

(** The entropy produced between times a and b, the integral of the
    production rate, is the drop in relative entropy, and so it is never
    negative and never more than the relative entropy at time a. *)
Theorem rcd_produced_window : forall a b (Hab : a <= b),
  NewtonInt (fun t => rcd_sigma (p t)) a b (rcd_window a b Hab) = rcd_D (p a) - rcd_D (p b).
Proof. intros a b Hab. unfold NewtonInt, rcd_window. simpl. unfold opp_fct. ring. Qed.

Theorem rcd_produced_bounds : forall a b (Hab : a <= b), 0 <= rcd_D (p b) ->
  0 <= NewtonInt (fun t => rcd_sigma (p t)) a b (rcd_window a b Hab) <= rcd_D (p a).
Proof.
  intros a b Hab H0. rewrite rcd_produced_window. pose proof (rcd_D_monotone a b Hab). lra.
Qed.

End Continuous.

Print Assumptions rcd_sigma_nonneg.
Print Assumptions rcd_D_derivative.
Print Assumptions rcd_D_monotone.
Print Assumptions rcd_produced_window.
