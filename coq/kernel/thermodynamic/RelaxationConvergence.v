(** RelaxationConvergence: the relaxation of RelaxationEntropy.v reaches its
    steady spread, and the bound from a known start is attained in the
    limit.

    Take the finite chain of RelaxationEntropy.v, with steady spread pi and
    detailed balance, and add Doeblin's condition: some delta > 0 with
    P x y >= delta * pi y for all listed x, y (every row puts at least a
    delta share of the steady spread everywhere; a chain whose entries are
    all positive has it).

    - Each step shrinks the distance sum_x |p x - pi x| by the factor
      1 - delta ([rc_contract]), so after t steps it is at most
      2 (1 - delta)^t for a probability vector ([rc_l1_pow]).
    - The relative entropy is at most the chi-square distance
      sum_x (p x - pi x)^2 / pi x ([rc_D_le_chi2]), which is at most the
      squared distance over the smallest steady weight.
    - So the spread converges to pi at every state ([rc_converges]), and the
      entropy produced from a known start s tends to - ln (pi s), with the
      explicit gap - ln (pi s) - produced <= (4 / m) (1 - delta)^(2 T)
      ([rc_known_start_gap], [rc_known_start_limit]). *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics. No definition or theorem here mentions a certification
   system, a ledger or a machine step; it imports only FiniteSums.v and
   RelaxationEntropy.v.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. The standalone boundary is stated here rather than inferred from
   an import. *)

From Coq Require Import List Reals Lra Psatz.
Import ListNotations.
From Kernel Require Import FiniteSums RelaxationEntropy.
Open Scope R_scope.

Section Convergence.

Variable X : Type.
Variable LX : list X.
Variable P : X -> X -> R.
Variable pi : X -> R.
Hypothesis P_nonneg : forall x y, 0 <= P x y.
Hypothesis P_rows : forall x, In x LX -> sumL LX (fun y => P x y) = 1.
Hypothesis pi_pos : forall x, 0 < pi x.
Hypothesis pi_mass : sumL LX pi = 1.
Hypothesis detailed_balance : forall x y, pi x * P x y = pi y * P y x.
Variable eqX : forall a b : X, {a = b} + {a <> b}.
Hypothesis LX_nodup : NoDup LX.
Variable delta : R.
Hypothesis delta_pos : 0 < delta.
Hypothesis doeblin : forall x y, In x LX -> In y LX -> delta * pi y <= P x y.

Let step := re_step X LX P.
Let run := re_run X LX P.

Definition rc_l1 (p : X -> R) : R := sumL LX (fun x => Rabs (p x - pi x)).

Lemma rc_sum_abs : forall (A : Type) (L : list A) (f : A -> R), Rabs (sumL L f) <= sumL L (fun a => Rabs (f a)).
Proof.
  intros A L f. induction L as [| a L IH]; simpl.
  - rewrite Rabs_R0. lra.
  - eapply Rle_trans; [apply Rabs_triang | lra].
Qed.

Lemma rc_sum_le : forall (A : Type) (L : list A) (f g : A -> R),
  (forall a, In a L -> f a <= g a) -> sumL L f <= sumL L g.
Proof.
  intros A L f g H. induction L as [| a L IH]; simpl; [lra |].
  pose proof (H a (or_introl eq_refl)). assert (sumL L f <= sumL L g) by (apply IH; intros; apply H; right; assumption).
  lra.
Qed.


(** One step shrinks the distance by 1 - delta. *)
Theorem rc_contract : forall p, sumL LX p = 1 -> rc_l1 (step p) <= (1 - delta) * rc_l1 p.
Proof.
  intros p Hp. unfold rc_l1.
  set (e := fun x => p x - pi x).
  assert (He0 : sumL LX e = 0) by (unfold e; rewrite sumL_minus, Hp, pi_mass; ring).
  (* at each y: step p y - pi y = sum_x e x (P x y - delta pi y) *)
  assert (Hy : forall y, In y LX ->
    step p y - pi y = sumL LX (fun x => e x * (P x y - delta * pi y))).
  { intros y Hyin.
    assert (Hs : pi y = sumL LX (fun x => pi x * P x y)).
    { symmetry. assert (H : re_step X LX P pi y = pi y) by (eapply re_pi_stationary; eauto).
      unfold re_step in H. exact H. }
    transitivity (sumL LX (fun x => e x * P x y) - delta * pi y * sumL LX e).
    - rewrite He0, Rmult_0_r, Rminus_0_r. unfold step, re_step. rewrite Hs at 1.
      rewrite <- sumL_minus. apply sumL_ext. intros. unfold e. ring.
    - rewrite <- sumL_scale_l, <- sumL_minus. apply sumL_ext. intros. ring. }
  apply Rle_trans with (sumL LX (fun y => sumL LX (fun x => Rabs (e x) * (P x y - delta * pi y)))).
  - apply rc_sum_le. intros y Hyin. rewrite (Hy y Hyin).
    eapply Rle_trans; [apply rc_sum_abs |].
    apply rc_sum_le. intros x Hx. rewrite Rabs_mult.
    rewrite (Rabs_right (P x y - delta * pi y)) by (pose proof (doeblin x y Hx Hyin); lra). lra.
  - rewrite sumL_swap.
    apply Rle_trans with (sumL LX (fun x => (1 - delta) * Rabs (e x))).
    + apply Req_le. apply sumL_ext. intros x Hx.
      transitivity (Rabs (e x) * sumL LX (fun y => P x y - delta * pi y)).
      * rewrite <- sumL_scale_l. reflexivity.
      * rewrite (sumL_minus X LX (fun y => P x y) (fun y => delta * pi y)), (P_rows x Hx).
        rewrite (sumL_scale_l X LX delta pi), pi_mass. ring.
    + rewrite sumL_scale_l. apply Req_le. unfold e. reflexivity.
Qed.

Lemma rc_delta_le_1 : delta <= 1.
Proof.
  assert (Hne : exists x0, In x0 LX).
  { pose proof pi_mass as Hm. destruct LX as [| x0 L]; [simpl in Hm; lra | exists x0; left; reflexivity]. }
  destruct Hne as [x0 Hx].
  assert (H : sumL LX (fun y => delta * pi y) <= sumL LX (fun y => P x0 y)).
  { apply rc_sum_le. intros y Hy. apply doeblin; assumption. }
  rewrite (P_rows x0 Hx), (sumL_scale_l X LX delta pi), pi_mass in H. lra.
Qed.

Lemma rc_prob_run : forall t p, re_prob X LX p -> re_prob X LX (run t p).
Proof.
  intros t p [Hn Hm]. split.
  - intro x. unfold run. eapply re_run_nonneg; eauto.
  - unfold run. erewrite re_run_mass; eauto.
Qed.

Lemma rc_l1_le_2 : forall p, re_prob X LX p -> rc_l1 p <= 2.
Proof.
  intros p [Hn Hm]. unfold rc_l1.
  apply Rle_trans with (sumL LX (fun x => p x + pi x)).
  - apply rc_sum_le. intros x _. pose proof (Hn x). pose proof (pi_pos x).
    unfold Rabs. destruct (Rcase_abs (p x - pi x)); lra.
  - rewrite sumL_plus, Hm, pi_mass. lra.
Qed.

Theorem rc_l1_pow : forall t p, re_prob X LX p -> rc_l1 (run t p) <= (1 - delta) ^ t * rc_l1 p.
Proof.
  pose proof rc_delta_le_1 as Hd.
  induction t as [| t IH]; intros p Hp; [simpl; lra |].
  change (run (S t) p) with (step (run t p)).
  pose proof (rc_contract (run t p) (proj2 (rc_prob_run t p Hp))) as H.
  pose proof (IH p Hp) as H2. simpl.
  apply Rle_trans with ((1 - delta) * rc_l1 (run t p)); [exact H |].
  rewrite Rmult_assoc. apply Rmult_le_compat_l; [lra | exact H2].
Qed.

(** The relative entropy is at most the chi-square distance. *)
Theorem rc_D_le_chi2 : forall p, re_prob X LX p ->
  re_D X LX p pi <= sumL LX (fun x => (p x - pi x) * (p x - pi x) / pi x).
Proof.
  intros p [Hn Hm]. unfold re_D.
  apply Rle_trans with (sumL LX (fun x => (p x - pi x) * (p x - pi x) / pi x + (p x - pi x))).
  - apply rc_sum_le. intros x _. pose proof (pi_pos x) as Hpx. pose proof (Hn x) as Hp.
    destruct (Req_dec (p x) 0) as [Z | NZ].
    + rewrite Z. rewrite Rmult_0_l. assert (E : (0 - pi x) * (0 - pi x) / pi x + (0 - pi x) = 0) by (field; lra).
      lra.
    + assert (Hq : 0 < p x / pi x) by (apply Rdiv_lt_0_compat; lra).
      pose proof (re_ln_le (p x / pi x) Hq) as Hl.
      assert (E : (p x - pi x) * (p x - pi x) / pi x + (p x - pi x) = p x * (p x / pi x - 1)) by (field; lra).
      rewrite E. apply Rmult_le_compat_l; lra.
  - rewrite sumL_plus, sumL_minus, Hm, pi_mass. lra.
Qed.

Lemma rc_pi_min : exists m, 0 < m /\ forall x, In x LX -> m <= pi x.
Proof.
  clear - pi_pos. induction LX as [| a L IH].
  - exists 1. split; [lra | intros x []].
  - destruct IH as [m [Hm H]]. exists (Rmin (pi a) m). split.
    + apply Rmin_glb_lt; [apply pi_pos | exact Hm].
    + intros x [<- | Hx]; [apply Rmin_l |]. eapply Rle_trans; [apply Rmin_r | apply H; exact Hx].
Qed.

Lemma rc_sq_sum : forall (A : Type) (L : list A) (f : A -> R), (forall a, 0 <= f a) ->
  sumL L (fun a => f a * f a) <= sumL L f * sumL L f.
Proof.
  intros A L f Hf. induction L as [| a L IH]; simpl; [lra |].
  assert (Hs : 0 <= sumL L f) by (apply sumL_nonneg; intros; apply Hf).
  pose proof (Hf a). nra.
Qed.

Lemma rc_chi2_le : forall p m, 0 < m -> (forall x, In x LX -> m <= pi x) ->
  sumL LX (fun x => (p x - pi x) * (p x - pi x) / pi x) <= / m * (rc_l1 p * rc_l1 p).
Proof.
  intros p m Hm Hmin. unfold rc_l1.
  apply Rle_trans with (sumL LX (fun x => / m * (Rabs (p x - pi x) * Rabs (p x - pi x)))).
  - apply rc_sum_le. intros x Hx. pose proof (pi_pos x). pose proof (Hmin x Hx).
    rewrite <- Rabs_mult, Rabs_right by (apply Rle_ge; apply sq_nonneg).
    unfold Rdiv. rewrite Rmult_comm. apply Rmult_le_compat_r; [apply sq_nonneg |].
    apply Rinv_le_contravar; assumption.
  - rewrite (sumL_scale_l X LX (/ m) (fun x => Rabs (p x - pi x) * Rabs (p x - pi x))).
    apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat; exact Hm |].
    apply (rc_sq_sum X LX (fun x => Rabs (p x - pi x))). intros. apply Rabs_pos.
Qed.

(** The spread converges to pi at every listed state. *)
Theorem rc_converges : forall p, re_prob X LX p -> forall x, In x LX ->
  Un_cv (fun t => run t p x) (pi x).
Proof.
  intros p Hp x Hx eps Heps. pose proof rc_delta_le_1 as Hd.
  destruct (pow_lt_1_zero (1 - delta) ltac:(rewrite Rabs_right by lra; lra) (eps / 2)
    ltac:(lra)) as [N HN].
  exists N. intros n Hn. unfold R_dist.
  apply Rle_lt_trans with (rc_l1 (run n p)).
  - unfold rc_l1. apply (re_term_le_sum X LX (fun y => Rabs (run n p y - pi y)) x); [intros; apply Rabs_pos | exact Hx].
  - apply Rle_lt_trans with ((1 - delta) ^ n * 2).
    + apply Rle_trans with ((1 - delta) ^ n * rc_l1 p); [apply rc_l1_pow; exact Hp |].
      apply Rmult_le_compat_l; [apply pow_le; lra | apply rc_l1_le_2; exact Hp].
    + specialize (HN n Hn). rewrite Rabs_right in HN by (apply Rle_ge; apply pow_le; lra). lra.
Qed.

(** From a known start s, the entropy produced in T steps falls short of
    - ln (pi s) by at most (4 / m) (1 - delta)^(2 T). *)
Theorem rc_known_start_gap : forall s m T, In s LX -> 0 < m -> (forall x, In x LX -> m <= pi x) ->
  - ln (pi s) - re_produced X LX P T (re_point X eqX s) <= 4 / m * ((1 - delta) ^ T * (1 - delta) ^ T).
Proof.
  intros s m T Hs Hm Hmin. pose proof rc_delta_le_1 as Hd.
  rewrite (re_known_start_total X LX P pi P_nonneg P_rows pi_pos detailed_balance eqX LX_nodup s T Hs).
  assert (Hp : re_prob X LX (re_point X eqX s)) by (apply re_point_prob; assumption).
  set (q := re_run X LX P T (re_point X eqX s)).
  assert (Hq : re_prob X LX q) by (apply rc_prob_run; exact Hp).
  pose proof (rc_D_le_chi2 q Hq) as H1. pose proof (rc_chi2_le q m Hm Hmin) as H2.
  pose proof (rc_l1_pow T _ Hp) as H3. fold q in H3. change (run T (re_point X eqX s)) with q in H3.
  pose proof (rc_l1_le_2 _ Hp) as H4.
  assert (H0 : 0 <= rc_l1 q) by (apply sumL_nonneg; intros; apply Rabs_pos).
  assert (Hpw : 0 <= (1 - delta) ^ T) by (apply pow_le; lra).
  assert (H5 : rc_l1 q <= 2 * (1 - delta) ^ T).
  { apply Rle_trans with ((1 - delta) ^ T * rc_l1 (re_point X eqX s)); [exact H3 | nra]. }
  assert (H6 : rc_l1 q * rc_l1 q <= 4 * ((1 - delta) ^ T * (1 - delta) ^ T)) by nra.
  assert (Hmi : 0 < / m) by (apply Rinv_0_lt_compat; exact Hm).
  unfold Rdiv. nra.
Qed.

(** And so it converges to - ln (pi s): the bound of RelaxationEntropy.v is
    reached in the limit. *)
Theorem rc_known_start_limit : forall s, In s LX ->
  Un_cv (fun T => re_produced X LX P T (re_point X eqX s)) (- ln (pi s)).
Proof.
  intros s Hs eps Heps. pose proof rc_delta_le_1 as Hd.
  destruct rc_pi_min as [m [Hm Hmin]].
  destruct (pow_lt_1_zero ((1 - delta) * (1 - delta)) ltac:(rewrite Rabs_right by nra; nra) (eps * m / 4)
    ltac:(apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; lra | lra])) as [N HN].
  exists N. intros n Hn. unfold R_dist.
  pose proof (rc_known_start_gap s m n Hs Hm Hmin) as G.
  pose proof (re_known_start_bound X LX P pi P_nonneg P_rows pi_pos pi_mass detailed_balance eqX LX_nodup s n Hs) as [B1 B2].
  specialize (HN n Hn). rewrite <- Rpow_mult_distr in G.
  rewrite Rabs_right in HN by (apply Rle_ge; apply pow_le; nra).
  rewrite Rabs_left1 by lra.
  assert (E : 4 / m * ((1 - delta) * (1 - delta)) ^ n < eps).
  { apply Rmult_lt_reg_l with (m / 4); [lra |].
    replace (m / 4 * (4 / m * ((1 - delta) * (1 - delta)) ^ n)) with (((1 - delta) * (1 - delta)) ^ n) by (field; lra).
    replace (m / 4 * eps) with (eps * m / 4) by (field; lra). exact HN. }
  lra.
Qed.

End Convergence.

Print Assumptions rc_contract.
Print Assumptions rc_converges.
Print Assumptions rc_known_start_gap.
Print Assumptions rc_known_start_limit.
