(** RelaxationEntropy: the discrete-time core of the relaxation bound.

    A finite Markov chain with transition weights P and a distribution pi
    that is strictly positive, sums to one, and satisfies detailed balance,
    pi x P x y = pi y P y x. Write D(p || q) = sum_x p x ln (p x / q x) for
    the relative entropy, and sigma(p) for the entropy produced in one step
    from p, the relative entropy of the forward flow p x P x y against the
    backward flow (pP) y P y x.

    - Gibbs' inequality: D(p || q) >= 0 for probability vectors where q is
      positive wherever p is ([re_gibbs]).
    - pi is stationary ([re_pi_stationary]); a step keeps a probability vector
      a probability vector ([re_step_mass], [re_step_nonneg]).
    - Under detailed balance, the entropy produced in a step is exactly the
      drop in relative entropy to pi, and it is never negative
      ([re_sigma_is_drop], [re_sigma_nonneg]); so relative entropy to pi never
      rises ([re_relative_entropy_monotone]).
    - From a known start s, the entropy produced in the first T steps is
      -ln pi(s) - D(p_T || pi): never more than -ln pi(s), and equal to it in
      the limit exactly when D(p_T || pi) goes to zero
      ([re_known_start_total], [re_known_start_bound]).
    - If s lies in a set N of states, -ln pi(s) >= -ln pi(N)
      ([re_known_start_vs_set]).
    - Under stationarity the flow from N to its complement U equals the flow
      back ([re_flux_balance]); with mean stretch lengths defined as mass over
      flow, -ln pi(N) = ln (1 + T_up / T_down) ([re_stretch_ratio]).

    The book's argument is in continuous time and uses convergence to pi;
    this file is the discrete-time analogue and states convergence as the
    condition it is. *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics. No definition or theorem here mentions a certification
   system, a ledger or a machine step; it imports only FiniteSums.v.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. The standalone boundary is stated here rather than inferred from
   an import. *)

From Coq Require Import List Reals Lra Psatz.
Import ListNotations.
From Kernel Require Import FiniteSums.
Open Scope R_scope.

(** * Logarithm facts *)

Lemma re_exp_ge : forall x, 1 + x <= exp x.
Proof.
  intro x. destruct (Req_dec x 0) as [-> | H].
  - rewrite exp_0. lra.
  - left. apply exp_ineq1. exact H.
Qed.

Lemma re_ln_le : forall y, 0 < y -> ln y <= y - 1.
Proof.
  intros y Hy. pose proof (re_exp_ge (ln y)) as H. rewrite exp_ln in H by exact Hy. lra.
Qed.

(** One term of a relative entropy is at least p - q. *)
Lemma re_term_ge : forall p q, 0 <= p -> 0 <= q -> (0 < p -> 0 < q) ->
  p * ln (p / q) >= p - q.
Proof.
  intros p q Hp Hq Hsupp. destruct (Req_dec p 0) as [-> | Hp0].
  - rewrite Rmult_0_l. lra.
  - assert (Hp' : 0 < p) by lra. assert (Hq' : 0 < q) by (apply Hsupp; exact Hp').
    assert (E : ln (p / q) = - ln (q / p)).
    { rewrite <- ln_Rinv by (apply Rdiv_lt_0_compat; assumption).
      f_equal. field. split; lra. }
    rewrite E. pose proof (re_ln_le (q / p) (Rdiv_lt_0_compat q p Hq' Hp')) as H.
    assert (H2 : p * (q / p - 1) = q - p) by (field; lra).
    apply Rle_ge. apply (Rmult_le_compat_l p) in H; [| lra]. lra.
Qed.

Section Chain.

Variable X : Type.
Variable LX : list X.
Variable P : X -> X -> R.
Variable pi : X -> R.
Hypothesis P_nonneg : forall x y, 0 <= P x y.
Hypothesis P_rows : forall x, In x LX -> sumL LX (fun y => P x y) = 1.
Hypothesis pi_pos : forall x, 0 < pi x.
Hypothesis pi_mass : sumL LX pi = 1.
Hypothesis detailed_balance : forall x y, pi x * P x y = pi y * P y x.

Definition re_step (p : X -> R) (y : X) : R := sumL LX (fun x => p x * P x y).
Definition re_D (p q : X -> R) : R := sumL LX (fun x => p x * ln (p x / q x)).

Definition re_prob (p : X -> R) : Prop := (forall x, 0 <= p x) /\ sumL LX p = 1.

(** Gibbs' inequality over any finite list. *)
Lemma re_gibbs_list : forall (A : Type) (L : list A) (p q : A -> R),
  (forall a, In a L -> 0 <= p a) -> (forall a, In a L -> 0 <= q a) ->
  (forall a, In a L -> 0 < p a -> 0 < q a) ->
  sumL L p = 1 -> sumL L q = 1 ->
  sumL L (fun a => p a * ln (p a / q a)) >= 0.
Proof.
  intros A L p q Hp Hq Hs Hpm Hqm.
  assert (H : sumL L (fun a => p a - q a) <= sumL L (fun a => p a * ln (p a / q a))).
  { clear Hpm Hqm. induction L as [| a L IH]; simpl; [lra |].
    pose proof (re_term_ge (p a) (q a) (Hp a (or_introl eq_refl)) (Hq a (or_introl eq_refl))
                  (Hs a (or_introl eq_refl))).
    assert (sumL L (fun a => p a - q a) <= sumL L (fun a => p a * ln (p a / q a))).
    { apply IH; intros b Hb; [apply Hp | apply Hq | apply Hs]; right; exact Hb. }
    lra. }
  rewrite sumL_minus, Hpm, Hqm in H. lra.
Qed.

Theorem re_gibbs : forall p q, re_prob p -> re_prob q -> (forall x, 0 < p x -> 0 < q x) ->
  re_D p q >= 0.
Proof.
  intros p q [Hp Hpm] [Hq Hqm] Hs. unfold re_D. apply re_gibbs_list; auto.
Qed.

Theorem re_pi_stationary : forall y, In y LX -> re_step pi y = pi y.
Proof.
  intros y Hy. unfold re_step.
  transitivity (sumL LX (fun x => pi y * P y x)).
  - apply sumL_ext. intros x _. apply detailed_balance.
  - transitivity (pi y * sumL LX (fun x => P y x)); [apply sumL_scale_l |].
    rewrite (P_rows y Hy). ring.
Qed.

Lemma re_step_nonneg : forall p, (forall x, 0 <= p x) -> forall y, 0 <= re_step p y.
Proof.
  intros p Hp y. unfold re_step. apply sumL_nonneg. intros x _.
  apply Rmult_le_pos; [apply Hp | apply P_nonneg].
Qed.

Lemma re_step_mass : forall p, sumL LX (re_step p) = sumL LX p.
Proof.
  intro p. unfold re_step. rewrite sumL_swap. apply sumL_ext. intros x Hx.
  transitivity (p x * sumL LX (fun y => P x y)); [apply sumL_scale_l |].
  rewrite (P_rows x Hx). ring.
Qed.

(** One term of a sum of nonnegative terms is at most the sum. *)
Lemma re_term_le_sum : forall (A : Type) (L : list A) (f : A -> R) a,
  (forall b, In b L -> 0 <= f b) -> In a L -> f a <= sumL L f.
Proof.
  intros A L f a Hf Ha. induction L as [| b L IH]; [destruct Ha |]. simpl.
  assert (0 <= sumL L f) by (apply sumL_nonneg; intros c Hc; apply Hf; right; exact Hc).
  destruct Ha as [<- | Ha].
  - lra.
  - assert (f a <= sumL L f) by (apply IH; [intros c Hc; apply Hf; right; exact Hc | exact Ha]).
    pose proof (Hf b (or_introl eq_refl)). lra.
Qed.

Lemma re_ln_div : forall a b, 0 < a -> 0 < b -> ln (a / b) = ln a - ln b.
Proof. intros a b Ha Hb. unfold Rdiv. rewrite ln_mult, ln_Rinv by (try apply Rinv_0_lt_compat; lra). ring. Qed.

(** The entropy produced in one step from p. *)
Definition re_sigma (p : X -> R) : R :=
  sumL LX (fun x => sumL LX (fun y =>
    p x * P x y * ln ((p x * P x y) / (re_step p y * P y x)))).

Lemma re_sigma_term : forall p x y, (forall z, 0 <= p z) -> In x LX ->
  p x * P x y * ln ((p x * P x y) / (re_step p y * P y x)) =
  p x * P x y * ln (p x / pi x) - p x * P x y * ln (re_step p y / pi y).
Proof.
  intros p x y Hp Hx.
  destruct (Req_dec (p x * P x y) 0) as [H0 | H0]; [rewrite H0; ring |].
  assert (Hpx : 0 < p x) by (destruct (Hp x) as [h | h]; [exact h | rewrite <- h in H0; lra]).
  assert (HPxy : 0 < P x y) by (destruct (P_nonneg x y) as [h | h]; [exact h | rewrite <- h in H0; lra]).
  assert (HPyx : 0 < P y x).
  { assert (E : P y x = pi x * P x y / pi y) by (rewrite detailed_balance; field; pose proof (pi_pos y); lra).
    rewrite E. apply Rdiv_lt_0_compat; [apply Rmult_lt_0_compat; [apply pi_pos | exact HPxy] | apply pi_pos]. }
  assert (Hstep : 0 < re_step p y).
  { unfold re_step. apply Rlt_le_trans with (p x * P x y); [apply Rmult_lt_0_compat; assumption |].
    apply (re_term_le_sum X LX (fun z => p z * P z y) x); [| exact Hx].
    intros z _. apply Rmult_le_pos; [apply Hp | apply P_nonneg]. }
  pose proof (pi_pos x) as Hpix. pose proof (pi_pos y) as Hpiy.
  assert (Hratio : (p x * P x y) / (re_step p y * P y x) = (p x / pi x) / (re_step p y / pi y)).
  { assert (E : P x y = pi y * P y x / pi x) by (rewrite <- detailed_balance; field; lra).
    rewrite E. field. repeat split; lra. }
  rewrite Hratio, re_ln_div by (apply Rdiv_lt_0_compat; assumption). ring.
Qed.

Theorem re_sigma_is_drop : forall p, (forall z, 0 <= p z) ->
  re_sigma p = re_D p pi - re_D (re_step p) pi.
Proof.
  intros p Hp. unfold re_sigma, re_D.
  transitivity (sumL LX (fun x => sumL LX (fun y => p x * P x y * ln (p x / pi x))) -
                sumL LX (fun x => sumL LX (fun y => p x * P x y * ln (re_step p y / pi y)))).
  - rewrite <- sumL_minus. apply sumL_ext. intros x Hx. rewrite <- sumL_minus.
    apply sumL_ext. intros y _. apply re_sigma_term; assumption.
  - f_equal.
    + apply sumL_ext. intros x Hx.
      transitivity (p x * ln (p x / pi x) * sumL LX (fun y => P x y)).
      * rewrite <- sumL_scale_l. apply sumL_ext. intros y _. ring.
      * rewrite (P_rows x Hx). ring.
    + rewrite sumL_swap. apply sumL_ext. intros y _. unfold re_step.
      rewrite <- sumL_scale_r. apply sumL_ext. intros x _. ring.
Qed.

Theorem re_sigma_nonneg : forall p, re_prob p -> re_sigma p >= 0.
Proof.
  intros p [Hp Hpm]. unfold re_sigma.
  rewrite <- (sumL_prod X X LX LX (fun x y => p x * P x y * ln ((p x * P x y) / (re_step p y * P y x)))).
  apply (re_gibbs_list (X * X) (list_prod LX LX)
           (fun a => p (fst a) * P (fst a) (snd a))
           (fun a => re_step p (snd a) * P (snd a) (fst a))).
  - intros [x y] _. apply Rmult_le_pos; [apply Hp | apply P_nonneg].
  - intros [x y] _. apply Rmult_le_pos; [apply re_step_nonneg; exact Hp | apply P_nonneg].
  - intros [x y] Hin H. simpl in *. apply in_prod_iff in Hin. destruct Hin as [Hx _].
    assert (Hpx : 0 < p x).
    { destruct (Hp x) as [h | h]; [exact h | rewrite <- h, Rmult_0_l in H; lra]. }
    assert (HPxy : 0 < P x y).
    { destruct (P_nonneg x y) as [h | h]; [exact h | rewrite <- h, Rmult_0_r in H; lra]. }
    assert (HPyx : 0 < P y x).
    { assert (E : P y x = pi x * P x y / pi y) by (rewrite detailed_balance; field; pose proof (pi_pos y); lra).
      rewrite E. apply Rdiv_lt_0_compat; [apply Rmult_lt_0_compat; [apply pi_pos | exact HPxy] | apply pi_pos]. }
    assert (Hstep : 0 < re_step p y).
    { unfold re_step. apply Rlt_le_trans with (p x * P x y); [exact H |].
      apply (re_term_le_sum X LX (fun z => p z * P z y) x); [| exact Hx].
      intros z _. apply Rmult_le_pos; [apply Hp | apply P_nonneg]. }
    apply Rmult_lt_0_compat; assumption.
  - rewrite (sumL_prod X X LX LX (fun x y => p x * P x y)).
    transitivity (sumL LX p); [| exact Hpm]. apply sumL_ext. intros x Hx.
    transitivity (p x * sumL LX (fun y => P x y)); [apply sumL_scale_l | rewrite (P_rows x Hx); ring].
  - rewrite (sumL_prod X X LX LX (fun x y => re_step p y * P y x)).
    rewrite sumL_swap. transitivity (sumL LX (re_step p)); [| rewrite re_step_mass; exact Hpm].
    apply sumL_ext. intros y Hy.
    transitivity (re_step p y * sumL LX (fun x => P y x)); [apply sumL_scale_l | rewrite (P_rows y Hy); ring].
Qed.

Theorem re_relative_entropy_monotone : forall p, re_prob p -> re_D (re_step p) pi <= re_D p pi.
Proof.
  intros p Hpr. pose proof (re_sigma_nonneg p Hpr) as H.
  rewrite (re_sigma_is_drop p (proj1 Hpr)) in H. lra.
Qed.

(** * From a known start *)

Variable eqX : forall a b : X, {a = b} + {a <> b}.
Hypothesis LX_nodup : NoDup LX.

Definition re_point (s : X) (x : X) : R := if eqX s x then 1 else 0.

Fixpoint re_run (t : nat) (p : X -> R) : X -> R :=
  match t with 0%nat => p | S t' => re_step (re_run t' p) end.

Fixpoint re_produced (T : nat) (p : X -> R) : R :=
  match T with 0%nat => 0 | S T' => re_produced T' p + re_sigma (re_run T' p) end.

Lemma re_run_nonneg : forall t p, (forall x, 0 <= p x) -> forall x, 0 <= re_run t p x.
Proof.
  intros t. induction t as [| t IH]; intros p Hp x; simpl; [apply Hp |].
  apply re_step_nonneg. intro z. apply IH. exact Hp.
Qed.

Lemma re_run_mass : forall t p, sumL LX (re_run t p) = sumL LX p.
Proof. intros t. induction t as [| t IH]; intro p; simpl; [reflexivity | rewrite re_step_mass; apply IH]. Qed.

Lemma re_point_prob : forall s, In s LX -> re_prob (re_point s).
Proof.
  intros s Hs. split.
  - intro x. unfold re_point. destruct (eqX s x); lra.
  - unfold re_point.
    transitivity (sumL LX (fun x => (if eqX s x then 1 else 0) * 1)).
    + apply sumL_ext. intros x _. ring.
    + apply (sumL_delta X eqX LX s (fun _ => 1) LX_nodup Hs).
Qed.

Lemma re_point_entropy : forall s, In s LX -> re_D (re_point s) pi = - ln (pi s).
Proof.
  intros s Hs. unfold re_D, re_point.
  transitivity (sumL LX (fun x => (if eqX s x then 1 else 0) * ln (1 / pi x))).
  - apply sumL_ext. intros x _. destruct (eqX s x); [reflexivity | ring].
  - rewrite (sumL_delta X eqX LX s (fun x => ln (1 / pi x)) LX_nodup Hs).
    unfold Rdiv. rewrite Rmult_1_l, ln_Rinv by apply pi_pos. reflexivity.
Qed.

Theorem re_known_start_total : forall s T, In s LX ->
  re_produced T (re_point s) = - ln (pi s) - re_D (re_run T (re_point s)) pi.
Proof.
  intros s T Hs. induction T as [| T IH]; simpl.
  - rewrite re_point_entropy by exact Hs. ring.
  - rewrite IH, re_sigma_is_drop.
    + ring.
    + apply re_run_nonneg. apply (proj1 (re_point_prob s Hs)).
Qed.

Theorem re_known_start_bound : forall s T, In s LX ->
  0 <= re_produced T (re_point s) <= - ln (pi s).
Proof.
  intros s T Hs. split.
  - induction T as [| T IH]; simpl; [lra |].
    pose proof (re_sigma_nonneg (re_run T (re_point s))) as H.
    assert (Hpr : re_prob (re_run T (re_point s))).
    { split; [apply re_run_nonneg; apply (proj1 (re_point_prob s Hs)) |].
      rewrite re_run_mass. apply (proj2 (re_point_prob s Hs)). }
    specialize (H Hpr). lra.
  - rewrite re_known_start_total by exact Hs.
    assert (Hpr : re_prob (re_run T (re_point s))).
    { split; [apply re_run_nonneg; apply (proj1 (re_point_prob s Hs)) |].
      rewrite re_run_mass. apply (proj2 (re_point_prob s Hs)). }
    assert (Hpi : re_prob pi) by (split; [intro x; left; apply pi_pos | exact pi_mass]).
    pose proof (re_gibbs _ _ Hpr Hpi (fun x _ => pi_pos x)). lra.
Qed.

(** * A start in a set of states *)

Theorem re_known_start_vs_set : forall (LN : list X) s,
  In s LN -> - ln (pi s) >= - ln (sumL LN pi).
Proof.
  intros LN s Hs.
  assert (Hle : pi s <= sumL LN pi).
  { apply (re_term_le_sum X LN pi s); [intros b _; left; apply pi_pos | exact Hs]. }
  destruct (Req_dec (pi s) (sumL LN pi)) as [E | Hne]; [rewrite E; lra |].
  assert (ln (pi s) < ln (sumL LN pi)) by (apply ln_increasing; [apply pi_pos | lra]). lra.
Qed.

(** * Flow balance and the stretch ratio *)

Variable read : X -> bool.
Definition re_inN (x : X) : R := if read x then 0 else 1.
Definition re_inU (x : X) : R := if read x then 1 else 0.

Definition re_flow_NU : R :=
  sumL LX (fun x => sumL LX (fun y => re_inN x * re_inU y * (pi x * P x y))).
Definition re_flow_UN : R :=
  sumL LX (fun x => sumL LX (fun y => re_inU x * re_inN y * (pi x * P x y))).

Theorem re_flux_balance : re_flow_NU = re_flow_UN.
Proof.
  unfold re_flow_NU, re_flow_UN. rewrite sumL_swap. apply sumL_ext. intros y _.
  apply sumL_ext. intros x _. rewrite detailed_balance. ring.
Qed.

Definition re_massN : R := sumL LX (fun x => re_inN x * pi x).
Definition re_massU : R := sumL LX (fun x => re_inU x * pi x).

Lemma re_mass_split : re_massN + re_massU = 1.
Proof.
  unfold re_massN, re_massU. rewrite <- sumL_plus, <- pi_mass. apply sumL_ext. intros x _.
  unfold re_inN, re_inU. destruct (read x); ring.
Qed.

(** Mean stretch lengths as mass over flow. *)
Theorem re_stretch_ratio : forall J, 0 < J -> 0 < re_massN ->
  - ln re_massN = ln (1 + (re_massU / J) / (re_massN / J)).
Proof.
  intros J HJ HN. pose proof re_mass_split as Hs.
  assert (E : 1 + (re_massU / J) / (re_massN / J) = / re_massN).
  { field_simplify; [| lra | lra]. replace re_massU with (1 - re_massN) by lra. field. lra. }
  rewrite E, ln_Rinv by exact HN. reflexivity.
Qed.

End Chain.

Print Assumptions re_gibbs.
Print Assumptions re_pi_stationary.
Print Assumptions re_sigma_is_drop.
Print Assumptions re_sigma_nonneg.
Print Assumptions re_relative_entropy_monotone.
Print Assumptions re_known_start_total.
Print Assumptions re_known_start_bound.
Print Assumptions re_known_start_vs_set.
Print Assumptions re_flux_balance.
Print Assumptions re_stretch_ratio.

