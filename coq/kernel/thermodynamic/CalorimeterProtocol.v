(** Exact energy bookkeeping and its dimensional boundary for the
    two-state calorimeter protocol.

    - The canonical reset (population one half to zero in one step, with
      up rate 0 and down rate 1) is bookkeeping. Its rates satisfy detailed
      balance at no gap ([canonical_rates_break_detailed_balance]); with
      rates that do, a relaxation at a fixed gap settles at the equilibrium
      population 1 / (1 + exp (Delta / kT)), which is 1/5 at the gap
      2 kT ln 2, and never reaches 0
      ([detailed_balance_settles_at_gibbs], [landauer_gap_settles_at_one_fifth],
      [detailed_balance_never_empties]). The heat Delta / 2 it books at gap
      kT ln 2 is below kT ln 2 ([canonical_reset_heat_below_landauer_at_small_gap]):
      the toy has no second law.
    - The driven reset. Raise the gap in steps, letting the register settle
      at each one. The work is never below the free-energy change
      ([driven_work_second_law]), comes within the step size of it
      ([driven_work_near_free_energy]), and for N equal raises to gap D lies
      between kT ln 2 - kT exp (- D / kT) and kT ln 2 + D / (2 N), with the
      final excited population at most exp (- D / kT)
      ([driven_reset_work_window]). Work minus heat is the change in the
      register's mean energy ([driven_first_law]). So kT ln 2 comes out of
      the work of a driven reset, with nothing chosen to make it so. *)

(* SCOPE NOTE: standalone proof scope. The two-state calorimeter protocol
   is a physical model with its own parameters; no machine ledger fixes its
   units. *)

From Coq Require Import Reals Lra Lia Psatz Ranalysis1 Ranalysis4 MVT.
From Kernel Require Import CalorimeterProtocolTarget.

Local Open Scope R_scope.

Theorem canonical_reset_satisfies_master_equation :
  master_next canonical_reset_dt canonical_reset_k01 canonical_reset_k10
    canonical_reset_before = canonical_reset_after.
Proof.
  unfold master_next, canonical_reset_dt, canonical_reset_k01,
    canonical_reset_k10, canonical_reset_before, canonical_reset_after.
  field.
Qed.

Theorem canonical_reset_heat_exact : forall Delta,
  bath_heat_fixed_hamiltonian Delta canonical_reset_before
    canonical_reset_after = Delta / 2.
Proof.
  intro Delta.
  unfold bath_heat_fixed_hamiltonian, mean_register_energy,
    canonical_reset_before, canonical_reset_after.
  field.
Qed.

Theorem selected_gap_gives_landauer_heat : forall k_B T,
  bath_heat_fixed_hamiltonian (2 * k_B * T * ln 2)
    canonical_reset_before canonical_reset_after = k_B * T * ln 2.
Proof.
  intros k_B T. rewrite canonical_reset_heat_exact. field.
Qed.

Lemma ln_two_positive : 0 < ln 2.
Proof.
  rewrite <- ln_1. apply ln_increasing; lra.
Qed.

(** The toy has no second law: at gap kT ln 2 it books less heat than
    kT ln 2 for taking the register from one half to zero. *)
Theorem canonical_reset_heat_below_landauer_at_small_gap : forall k_B T,
  0 < k_B -> 0 < T ->
  bath_heat_fixed_hamiltonian (k_B * T * ln 2)
    canonical_reset_before canonical_reset_after < k_B * T * ln 2.
Proof.
  intros k_B T Hk HT.
  rewrite canonical_reset_heat_exact.
  assert (Hscale : 0 < k_B * T * ln 2).
  { apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat; assumption.
    - exact ln_two_positive. }
  lra.
Qed.

(** The population dynamics are identical for both gaps, while the exact
    energy transfer differs. *)
Theorem master_equation_does_not_fix_heat_scale :
  exists Delta1 Delta2,
    Delta1 <> Delta2 /\
    master_next canonical_reset_dt canonical_reset_k01 canonical_reset_k10
      canonical_reset_before = canonical_reset_after /\
    master_next canonical_reset_dt canonical_reset_k01 canonical_reset_k10
      canonical_reset_before = canonical_reset_after /\
    bath_heat_fixed_hamiltonian Delta1 canonical_reset_before
      canonical_reset_after <>
    bath_heat_fixed_hamiltonian Delta2 canonical_reset_before
      canonical_reset_after.
Proof.
  exists 1, 2. repeat split.
  - lra.
  - exact canonical_reset_satisfies_master_equation.
  - exact canonical_reset_satisfies_master_equation.
  - rewrite !canonical_reset_heat_exact. lra.
Qed.

Lemma canonical_reset_is_one_mu : canonical_reset_mu = 1%nat.
Proof. reflexivity. Qed.

(** * The canonical rates break detailed balance *)

(** No gap and no temperature make the canonical rates (up 0, down 1) stand
    in the Boltzmann ratio: the factor exp (- Delta / kT) is never 0. *)
Theorem canonical_rates_break_detailed_balance : forall kT Delta,
  ~ detailed_balance kT Delta canonical_reset_k01 canonical_reset_k10.
Proof.
  intros kT Delta H. unfold detailed_balance, canonical_reset_k01, canonical_reset_k10 in H.
  pose proof (exp_pos (- (Delta / kT))). lra.
Qed.

(** With rates in detailed balance, one step of the master equation moves
    the population toward the equilibrium value by the factor
    1 - dt (k01 + k10). *)
Theorem detailed_balance_settles_at_gibbs : forall kT Delta dt k01 k10 p,
  detailed_balance kT Delta k01 k10 ->
  master_next dt k01 k10 p - gibbs_excited kT Delta
    = (1 - dt * (k01 + k10)) * (p - gibbs_excited kT Delta).
Proof.
  intros kT Delta dt k01 k10 p H. unfold detailed_balance in H. subst k01.
  unfold master_next, gibbs_excited. rewrite exp_Ropp.
  pose proof (exp_pos (Delta / kT)) as He. set (e := exp (Delta / kT)) in *.
  field. split; lra.
Qed.

(** A step with dt (k01 + k10) = 1 lands on the equilibrium population from
    any start: a thermalizing step that obeys detailed balance. *)
Theorem detailed_balance_thermalizing_step : forall kT Delta dt k01 k10 p,
  detailed_balance kT Delta k01 k10 -> dt * (k01 + k10) = 1 ->
  master_next dt k01 k10 p = gibbs_excited kT Delta.
Proof.
  intros kT Delta dt k01 k10 p H Hdt.
  pose proof (detailed_balance_settles_at_gibbs kT Delta dt k01 k10 p H) as E.
  rewrite Hdt in E. lra.
Qed.

Lemma gibbs_pos : forall kT x, 0 < gibbs_excited kT x.
Proof. intros. unfold gibbs_excited. apply Rinv_0_lt_compat. pose proof (exp_pos (x / kT)). lra. Qed.

(** A relaxation at a fixed gap, with rates in detailed balance and a step
    short enough not to overshoot, never brings the excited population
    below its equilibrium value, which is positive: it never empties. *)
Theorem detailed_balance_never_empties : forall kT Delta dt k01 k10 p,
  detailed_balance kT Delta k01 k10 -> 0 <= 1 - dt * (k01 + k10) ->
  gibbs_excited kT Delta <= p ->
  0 < gibbs_excited kT Delta <= master_next dt k01 k10 p.
Proof.
  intros kT Delta dt k01 k10 p H Hl Hp. split; [apply gibbs_pos |].
  pose proof (detailed_balance_settles_at_gibbs kT Delta dt k01 k10 p H) as E.
  assert (0 <= (1 - dt * (k01 + k10)) * (p - gibbs_excited kT Delta)) by (apply Rmult_le_pos; lra).
  lra.
Qed.

(** At the gap 2 kT ln 2, the equilibrium excited population is 1/5. *)
Theorem landauer_gap_settles_at_one_fifth : forall k_B T, k_B * T <> 0 ->
  gibbs_excited (k_B * T) (2 * k_B * T * ln 2) = / 5.
Proof.
  intros k_B T H. unfold gibbs_excited.
  assert (Hk : k_B <> 0) by (intro E; apply H; rewrite E; ring).
  assert (HT : T <> 0) by (intro E; apply H; rewrite E; ring).
  replace (2 * k_B * T * ln 2 / (k_B * T)) with (ln 2 + ln 2) by (field; split; assumption).
  rewrite exp_plus, exp_ln by lra. f_equal; ring.
Qed.

(** * The driven reset *)

Lemma dpl_ext : forall f g x l, (forall y, f y = g y) -> derivable_pt_lim f x l -> derivable_pt_lim g x l.
Proof.
  intros f g x l E H eps He. destruct (H eps He) as [d Hd]. exists d.
  intros h H0 H1. rewrite <- !E. apply Hd; assumption.
Qed.

Lemma dpl_val : forall f x l l', derivable_pt_lim f x l -> l = l' -> derivable_pt_lim f x l'.
Proof. intros f x l l' H <-. exact H. Qed.

(** The free energy's slope in the gap is the equilibrium excited
    population. *)
Lemma free_energy_derivative : forall kT x, 0 < kT ->
  derivable_pt_lim (two_state_free_energy kT) x (gibbs_excited kT x).
Proof.
  intros kT x Hk.
  assert (Hin : derivable_pt_lim (mult_real_fct (- / kT) id) x (- / kT * 1)).
  { apply derivable_pt_lim_scal, derivable_pt_lim_id. }
  assert (Hpos : 0 < 1 + exp (mult_real_fct (- / kT) id x)).
  { pose proof (exp_pos (mult_real_fct (- / kT) id x)). lra. }
  assert (Hmid : derivable_pt_lim (fun z => 1 + exp z) (mult_real_fct (- / kT) id x) (exp (mult_real_fct (- / kT) id x))).
  { apply (dpl_val _ _ (0 + exp (mult_real_fct (- / kT) id x))); [| ring].
    apply (derivable_pt_lim_plus (fct_cte 1) exp). apply derivable_pt_lim_const. apply derivable_pt_lim_exp. }
  pose proof (derivable_pt_lim_comp _ _ _ _ _ Hin Hmid) as H1.
  pose proof (derivable_pt_lim_comp _ _ _ _ _ H1 (derivable_pt_lim_ln _ Hpos)) as H2.
  pose proof (derivable_pt_lim_scal _ (- kT) _ _ H2) as H3.
  eapply dpl_val; [eapply dpl_ext; [| exact H3] |].
  - intro y. unfold mult_real_fct, comp, id, two_state_free_energy.
    replace (- / kT * y) with (- (y / kT)) by (field; lra). reflexivity.
  - unfold mult_real_fct, id, gibbs_excited.
    replace (- / kT * x) with (- (x / kT)) by (field; lra).
    rewrite exp_Ropp. pose proof (exp_pos (x / kT)) as He. set (e := exp (x / kT)) in *.
    assert (He1 : 1 + / e <> 0) by (pose proof (Rinv_0_lt_compat e He); lra).
    assert (He2 : 1 + e <> 0) by lra.
    replace (1 + / e) with ((1 + e) / e) by (field; lra).
    field. lra.
Qed.

Lemma gibbs_le_half_at_nonneg : forall kT x, 0 < kT -> 0 <= x -> gibbs_excited kT x <= / 2.
Proof.
  intros kT x Hk Hx. unfold gibbs_excited. apply Rinv_le_contravar; [lra |].
  assert (1 <= exp (x / kT)).
  { rewrite <- exp_0. destruct (Req_dec x 0) as [-> | Hne].
    - unfold Rdiv. rewrite Rmult_0_l. lra.
    - left. apply exp_increasing. apply Rdiv_lt_0_compat; lra. }
  lra.
Qed.

Lemma gibbs_antitone : forall kT a b, 0 < kT -> a <= b -> gibbs_excited kT b <= gibbs_excited kT a.
Proof.
  intros kT a b Hk Hab. unfold gibbs_excited.
  apply Rinv_le_contravar; [pose proof (exp_pos (a / kT)); lra |].
  destruct (Req_dec a b) as [-> | Hne]; [lra |].
  assert (H : a / kT < b / kT) by (unfold Rdiv; apply Rmult_lt_compat_r; [apply Rinv_0_lt_compat; lra | lra]).
  pose proof (exp_increasing _ _ H). lra.
Qed.

(** Raising the gap from a to b changes the free energy by at least the
    work at the population for b and at most the work at the population
    for a. *)
Lemma free_energy_step_bounds : forall kT a b, 0 < kT -> a <= b ->
  gibbs_excited kT b * (b - a) <= two_state_free_energy kT b - two_state_free_energy kT a <=
  gibbs_excited kT a * (b - a).
Proof.
  intros kT a b Hk Hab. destruct (Req_dec a b) as [-> | Hne].
  - rewrite Rminus_diag. rewrite !Rmult_0_r. lra.
  - assert (Hlt : a < b) by lra.
    destruct (MVT_cor2 (two_state_free_energy kT) (gibbs_excited kT) a b Hlt
               (fun c _ => free_energy_derivative kT c Hk)) as [c [Ec [Hac Hcb]]].
    rewrite Ec.
    pose proof (gibbs_antitone kT c b Hk (Rlt_le _ _ Hcb)).
    pose proof (gibbs_antitone kT a c Hk (Rlt_le _ _ Hac)).
    split; apply Rmult_le_compat_r; lra.
Qed.

(** Work minus heat is the change in the register's mean energy. *)
Theorem driven_first_law : forall kT g n,
  driven_work kT g n = driven_heat kT g n
    + mean_register_energy (g n) (gibbs_excited kT (g n))
    - mean_register_energy (g O) (gibbs_excited kT (g O)).
Proof.
  intros kT g n. unfold mean_register_energy.
  induction n as [| n IH]; simpl; [ring |]. rewrite IH. ring.
Qed.

(** The work of a driven reset is never below the free-energy change, for
    any rising schedule. *)
Theorem driven_work_second_law : forall kT g n, 0 < kT ->
  (forall m, g m <= g (S m)) ->
  two_state_free_energy kT (g n) - two_state_free_energy kT (g O) <= driven_work kT g n.
Proof.
  intros kT g n Hk Hmono. induction n as [| n IH]; simpl; [lra |].
  pose proof (free_energy_step_bounds kT (g n) (g (S n)) Hk (Hmono n)). lra.
Qed.

(** And it exceeds the free-energy change by at most the largest step h
    times the fall in the population. *)
Theorem driven_work_near_free_energy : forall kT g n h, 0 < kT ->
  (forall m, g m <= g (S m) <= g m + h) ->
  driven_work kT g n <= two_state_free_energy kT (g n) - two_state_free_energy kT (g O)
    + h * (gibbs_excited kT (g O) - gibbs_excited kT (g n)).
Proof.
  intros kT g n h Hk Hs. induction n as [| n IH]; simpl; [lra |].
  destruct (Hs n) as [H1 H2].
  pose proof (free_energy_step_bounds kT (g n) (g (S n)) Hk H1) as [B1 B2].
  pose proof (gibbs_antitone kT (g n) (g (S n)) Hk H1) as Ha.
  assert ((gibbs_excited kT (g n) - gibbs_excited kT (g (S n))) * (g (S n) - g n)
          <= (gibbs_excited kT (g n) - gibbs_excited kT (g (S n))) * h)
    by (apply Rmult_le_compat_l; lra).
  nra.
Qed.

Lemma free_energy_at_zero : forall kT, 0 < kT -> two_state_free_energy kT 0 = - kT * ln 2.
Proof.
  intros kT Hk. unfold two_state_free_energy. unfold Rdiv. rewrite Rmult_0_l, Ropp_0, exp_0.
  replace (1 + 1) with 2 by ring. reflexivity.
Qed.

Lemma ln_le_loc : forall x y, 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros x y Hx [Hlt | ->]; [left; apply ln_increasing; assumption | right; reflexivity].
Qed.

Lemma ln_one_plus_le : forall y, 0 <= y -> ln (1 + y) <= y.
Proof.
  intros y Hy. assert (H : 0 < 1 + y) by lra.
  pose proof (exp_ineq1_le y) as He.
  apply Rle_trans with (ln (exp y)); [apply ln_le_loc; lra | rewrite ln_exp; lra].
Qed.

(** N equal raises from a degenerate register (gap 0, population one half)
    to gap D: the work lies between kT ln 2 - kT exp (- D / kT) and
    kT ln 2 + D / (2 N), and the excited population left at the end is at
    most exp (- D / kT). Large D and many more steps than D bring both the
    work to kT ln 2 and the population to 0. *)
Theorem driven_reset_work_window : forall k_B T D N, 0 < k_B * T -> 0 <= D -> (0 < N)%nat ->
  k_B * T * ln 2 - k_B * T * exp (- (D / (k_B * T)))
    <= driven_work (k_B * T) (uniform_schedule D N) N
    <= k_B * T * ln 2 + D / (2 * INR N) /\
  gibbs_excited (k_B * T) (uniform_schedule D N N) <= exp (- (D / (k_B * T))).
Proof.
  intros k_B T D N Hk HD HN. set (kT := k_B * T) in *.
  assert (HNr : 0 < INR N) by (apply lt_0_INR; exact HN).
  assert (Hg0 : uniform_schedule D N 0 = 0) by (unfold uniform_schedule; simpl; field; lra).
  assert (HgN : uniform_schedule D N N = D) by (unfold uniform_schedule; field; lra).
  assert (Hstep : forall m, uniform_schedule D N m <= uniform_schedule D N (S m) <= uniform_schedule D N m + D / INR N).
  { intro m. unfold uniform_schedule. rewrite S_INR.
    split; [| right; field; lra].
    unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra |]. nra. }
  assert (Hmono : forall m, uniform_schedule D N m <= uniform_schedule D N (S m)) by (intro m; apply Hstep).
  pose proof (driven_work_second_law kT (uniform_schedule D N) N Hk Hmono) as L.
  pose proof (driven_work_near_free_energy kT (uniform_schedule D N) N (D / INR N) Hk Hstep) as U.
  rewrite HgN, Hg0 in L, U. rewrite free_energy_at_zero in L, U by exact Hk.
  unfold two_state_free_energy in L, U.
  pose proof (exp_pos (- (D / kT))) as He.
  pose proof (ln_one_plus_le _ (Rlt_le _ _ He)) as Hln.
  assert (Hln0 : 0 <= ln (1 + exp (- (D / kT)))).
  { rewrite <- ln_1. apply ln_le_loc; lra. }
  pose proof (gibbs_pos kT D) as Gp.
  pose proof (gibbs_le_half_at_nonneg kT D Hk HD) as Gh.
  assert (Hg0v : gibbs_excited kT 0 = / 2).
  { unfold gibbs_excited. unfold Rdiv. rewrite Rmult_0_l, exp_0. reflexivity. }
  rewrite Hg0v in U.
  assert (HDN : 0 <= D / INR N) by (unfold Rdiv; apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]).
  assert (Hh : D / INR N * (/ 2 - gibbs_excited kT D) <= D / (2 * INR N)).
  { replace (D / (2 * INR N)) with (D / INR N * / 2) by (field; lra).
    apply Rmult_le_compat_l; lra. }
  split; [split |].
  - assert (kT * ln (1 + exp (- (D / kT))) <= kT * exp (- (D / kT))) by (apply Rmult_le_compat_l; lra).
    lra.
  - assert (0 <= kT * ln (1 + exp (- (D / kT)))) by (apply Rmult_le_pos; lra). lra.
  - rewrite HgN. unfold gibbs_excited. rewrite exp_Ropp.
    pose proof (exp_pos (D / kT)). apply Rinv_le_contravar; lra.
Qed.

Print Assumptions canonical_reset_satisfies_master_equation.
Print Assumptions canonical_reset_heat_exact.
Print Assumptions selected_gap_gives_landauer_heat.
Print Assumptions canonical_reset_heat_below_landauer_at_small_gap.
Print Assumptions master_equation_does_not_fix_heat_scale.
Print Assumptions canonical_rates_break_detailed_balance.
Print Assumptions detailed_balance_settles_at_gibbs.
Print Assumptions detailed_balance_thermalizing_step.
Print Assumptions detailed_balance_never_empties.
Print Assumptions landauer_gap_settles_at_one_fifth.
Print Assumptions driven_first_law.
Print Assumptions driven_work_second_law.
Print Assumptions driven_work_near_free_energy.
Print Assumptions driven_reset_work_window.
