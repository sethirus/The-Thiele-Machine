(** CHSHStatisticalBridge: count the CHSH evidence, then ask what it rules out

    This file does one job. It starts from aggregate CHSH witness counts and
    pushes them through two deterministic facts that already live in the repo:
    the Bell-side contradiction and the W2 counting lower bound from
    QuantitativeNoFI.v.

   N valid CHSH_TRIAL instructions
   [chsh_trial_count_lower_bound in QuantitativeNoFI.v]
     ↓
   N counted CHSH trials in vm_witness
     ↓
   observed CHSH statistic S from WitnessCounts
   [chsh_stat_from_wc, defined here]
     ↓
   if S > 2, no local deterministic strategy fits those counts
   [proved here through local_bound_for_wc]

        1. how to read S off the witness counters
    2. the algebraic ceiling |S| <= 4
    3. a concrete witness-count pattern with S = 4, checked by vm_compute
    4. the local deterministic Bell bound |S| <= 2 for locally consistent counts
    5. S > 2 means the counts are not locally consistent
    6. hitting a trial-count threshold still costs that many CHSH_TRIAL steps

    There is no Hoeffding theorem here, and no confidence theorem.
    Finite-sample certification needs a real probability library and
    explicit sampling assumptions; this file does not provide either.
    The deterministic chain stands on its own. *)

From Coq Require Import List Arith.PeanoNat Lia QArith QArith.Qabs ZArith Lra PArith.BinPos PArith.Pnat.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof
                           AbstractNoFI UniversalCertificationCost
                           QuantitativeNoFI CHSH.

Open Scope Q_scope.

(** CHSH statistic from witness counts.

    WitnessCounts stores eight buckets: same and diff for each setting pair.
    From that I build the usual correlators

      E(X,Y) = (same_XY - diff_XY) / (same_XY + diff_XY)

    and then the CHSH statistic

      S = E(0,0) + E(0,1) + E(1,0) - E(1,1).

    I absorb the minus sign on E(1,1) by swapping same and diff in the last
    term, so the code can sum four expressions with the same shape.

    If you want the falsification condition for that sign convention, it is
    local_bound_for_wc below. For every deterministic local strategy with all
    four settings sampled, this witness-count formula lands at |S| = 2.
*)

(** Per-setting correlator: (pos - neg) / (pos + neg).
    Returns 0 when no trials for this setting (convention: undefined → 0). *)
Definition chsh_correlator_q (pos neg : nat) : Q :=
  let total := (pos + neg)%nat in
  if Nat.eqb total 0 then 0
  else (Z.of_nat pos - Z.of_nat neg # Pos.of_nat total).

(** CHSH statistic from aggregate WitnessCounts.
    The final term uses reversed arguments: E*(1,1) = (diff_11 - same_11)/N_11. *)
Definition chsh_stat_from_wc (wc : WitnessCounts) : Q :=
  chsh_correlator_q (wc_same_00 wc) (wc_diff_00 wc) +
  chsh_correlator_q (wc_same_01 wc) (wc_diff_01 wc) +
  chsh_correlator_q (wc_same_10 wc) (wc_diff_10 wc) +
  chsh_correlator_q (wc_diff_11 wc) (wc_same_11 wc).

(** Algebraic bound |S| <= 4.

  This is the loose ceiling that comes from the triangle inequality alone.
  It does not use locality. It does not prove Tsirelson. The stronger local
  deterministic bound |S| <= 2 shows up later and needs more structure.
*)

(** Z.of_nat n = Zpos (Pos.of_nat n) for n > 0.
    Proof: Z.of_nat (S k) = Zpos (Pos.of_succ_nat k) = Zpos (Pos.of_nat (S k))
    by the Coq standard library definitions of Z.of_nat and Pos.of_nat. *)
Lemma Z_of_nat_pos :
  forall n : nat, (0 < n)%nat -> Z.of_nat n = Zpos (Pos.of_nat n).
Proof.
  intros n Hn. destruct n. lia.
  (* Z.of_nat (S n) = Zpos (Pos.of_succ_nat n) by definition.
     Pos.of_nat_succ : Pos.of_succ_nat n = Pos.of_nat (S n). *)
  rewrite <- Pos.of_nat_succ. reflexivity.
Qed.

(** Each correlator is bounded by 1 in absolute value.
    Key arithmetic: |pos - neg| ≤ pos + neg when pos, neg ≥ 0. *)
Lemma correlator_abs_le_1 :
  forall p n : nat,
    Qabs (chsh_correlator_q p n) <= 1.
Proof.
  intros p n.
  unfold chsh_correlator_q.
  destruct (Nat.eqb (p + n) 0) eqn:Htot.
  - (* p + n = 0: return 0, |0| = 0 ≤ 1 *)
    unfold Qabs, Qle. simpl. lia.
  - (* p + n > 0: |(p-n)/(p+n)| ≤ 1 *)
    apply Nat.eqb_neq in Htot.
    assert (Hpn : (0 < p + n)%nat) by lia.
    unfold Qabs, Qle. simpl.
    rewrite Z.mul_1_r.
    (* Goal: Z.abs (Z.of_nat p - Z.of_nat n) <= Zpos (Pos.of_nat (p + n)) *)
    rewrite <- Z_of_nat_pos by exact Hpn.
    rewrite Nat2Z.inj_add.
    (* Goal: Z.abs (Z.of_nat p - Z.of_nat n) <= Z.of_nat p + Z.of_nat n *)
    apply Z.abs_le. split; lia.
Qed.

(** CHSH statistic is bounded by the algebraic ceiling of 4.
    Proof: |a+b+c+d| ≤ |a|+|b|+|c|+|d| ≤ 1+1+1+1 = 4. *)
Theorem chsh_stat_algebraic_bound :
  forall wc : WitnessCounts,
    Qabs (chsh_stat_from_wc wc) <= 4.
Proof.
  intros wc.
  unfold chsh_stat_from_wc.
  set (E00  := chsh_correlator_q (wc_same_00 wc) (wc_diff_00 wc)).
  set (E01  := chsh_correlator_q (wc_same_01 wc) (wc_diff_01 wc)).
  set (E10  := chsh_correlator_q (wc_same_10 wc) (wc_diff_10 wc)).
  set (E11r := chsh_correlator_q (wc_diff_11 wc) (wc_same_11 wc)).
  assert (H00  : Qabs E00  <= 1) by (unfold E00;  apply correlator_abs_le_1).
  assert (H01  : Qabs E01  <= 1) by (unfold E01;  apply correlator_abs_le_1).
  assert (H10  : Qabs E10  <= 1) by (unfold E10;  apply correlator_abs_le_1).
  assert (H11r : Qabs E11r <= 1) by (unfold E11r; apply correlator_abs_le_1).
  (* Triangle inequality: |a+b+c+d| ≤ |a|+|b|+|c|+|d| ≤ 4 *)
  apply Qle_trans with (Qabs E00 + Qabs E01 + Qabs E10 + Qabs E11r).
  - fold E00 E01 E10 E11r.
    eapply Qle_trans. { apply Qabs_triangle. }
    apply Qplus_le_compat. 2: apply Qle_refl.
    eapply Qle_trans. { apply Qabs_triangle. }
    apply Qplus_le_compat. 2: apply Qle_refl.
    apply Qabs_triangle.
  - apply Qle_trans with (1 + 1 + 1 + 1).
    + apply Qplus_le_compat. apply Qplus_le_compat. apply Qplus_le_compat.
      exact H00. exact H01. exact H10. exact H11r.
    + unfold Qle. simpl. lia.
Qed.

(** Concrete violation witness.

    I pin down one explicit WitnessCounts value with S = 4 > 2.

    It uses one trial per setting. The first three settings are all-same.
    The (1,1) setting is all-diff. That makes all four correlator terms equal 1,
    so the total lands at 4.

    This is only a witness-count pattern. It is not a trace-construction theorem.
    The W2 connection later says what any real trace has to pay to reach counts
    like this.
*)

Definition violation_wc : WitnessCounts :=
  {| wc_same_00 := 1; wc_diff_00 := 0;
     wc_same_01 := 1; wc_diff_01 := 0;
     wc_same_10 := 1; wc_diff_10 := 0;
     wc_same_11 := 0; wc_diff_11 := 1 |}.

(** The violation witness achieves S = 4 (vm_compute verified). *)
Lemma violation_wc_stat_eq_4 :
  chsh_stat_from_wc violation_wc == 4.
Proof.
  unfold chsh_stat_from_wc, violation_wc, chsh_correlator_q.
  simpl. vm_compute. reflexivity.
Qed.

(** The violation witness exceeds the classical Bell bound of 2. *)
Lemma violation_wc_exceeds_bell :
  chsh_stat_from_wc violation_wc > 2.
Proof.
  rewrite violation_wc_stat_eq_4.
  unfold Qlt. simpl. lia.
Qed.

(** The violation witness does not exceed the algebraic bound of 4. *)
Lemma violation_wc_within_algebraic :
  Qabs (chsh_stat_from_wc violation_wc) <= 4.
Proof.
  apply chsh_stat_algebraic_bound.
Qed.

(** Local consistency and Bell incompatibility.

    Here is the idea. Fix a deterministic local strategy (a0, a1, b0, b1).
    If a witness count is locally consistent with that strategy, then every
    bucket is forced: each setting is either all-same or all-diff.

    Once that happens, every correlator is either 1 or -1. The CHSH expression
    collapses to the usual local deterministic form

      S_WC = A0*B0 + A0*B1 + A1*B0 - A1*B1.

    From there the 16 possible bit assignments are enough. In every case,
    |S_WC| lands at 2. That is the Bell-side contradiction this file needs.
*)

(** Predicate: WitnessCounts consistent with local strategy (a0,a1,b0,b1). *)
Record WCLocallyConsistent (a0 a1 b0 b1 : nat) (wc : WitnessCounts) : Prop :=
  mk_wclc {
    (** Setting (0,0): all same if a0=b0, all diff if a0≠b0. *)
    wclc_00     : if Nat.eqb a0 b0
                  then (wc_diff_00 wc = 0)%nat
                  else (wc_same_00 wc = 0)%nat;
    (** Setting (0,1): all same if a0=b1, all diff otherwise. *)
    wclc_01     : if Nat.eqb a0 b1
                  then (wc_diff_01 wc = 0)%nat
                  else (wc_same_01 wc = 0)%nat;
    (** Setting (1,0): all same if a1=b0, all diff otherwise. *)
    wclc_10     : if Nat.eqb a1 b0
                  then (wc_diff_10 wc = 0)%nat
                  else (wc_same_10 wc = 0)%nat;
    (** Setting (1,1): all same if a1=b1, all diff otherwise. *)
    wclc_11     : if Nat.eqb a1 b1
                  then (wc_diff_11 wc = 0)%nat
                  else (wc_same_11 wc = 0)%nat;
    (** All four settings have at least one trial (necessary for full CHSH). *)
    wclc_all_sampled :
      (wc_same_00 wc + wc_diff_00 wc > 0)%nat /\
      (wc_same_01 wc + wc_diff_01 wc > 0)%nat /\
      (wc_same_10 wc + wc_diff_10 wc > 0)%nat /\
      (wc_same_11 wc + wc_diff_11 wc > 0)%nat
  }.

(** Bell's inequality for WitnessCounts.

  I prove this the blunt way: split on the four strategy bits, simplify the
  forced correlators, and check all 16 cases. Same skeleton as the local CHSH
  bound in CHSH.v.
*)

(** Helper: correlator when neg = 0 and pos > 0 yields 1. *)
Lemma correlator_pos_only : forall p : nat,
    (p > 0)%nat -> chsh_correlator_q p 0 == 1.
Proof.
  intros p Hp. unfold chsh_correlator_q.
  rewrite Nat.add_0_r.
  destruct (Nat.eqb p 0) eqn:He.
  - apply Nat.eqb_eq in He. lia.
  - unfold Qeq. simpl. rewrite Z.mul_1_r. rewrite Z.sub_0_r.
    rewrite Z_of_nat_pos by lia. reflexivity.
Qed.

(** Helper: correlator when pos = 0 and neg > 0 yields -1. *)
Lemma correlator_neg_only : forall n : nat,
    (n > 0)%nat -> chsh_correlator_q 0 n == -(1).
Proof.
  intros n Hn. unfold chsh_correlator_q.
  destruct (Nat.eqb (0 + n) 0) eqn:He.
  - apply Nat.eqb_eq in He. lia.
  - unfold Qeq. simpl. rewrite Z.mul_1_r.
    rewrite Z_of_nat_pos by lia.
    simpl. reflexivity.
Qed.

(** Helper: bit values are exactly 0 or 1. *)
Lemma bit_cases : forall n, is_bit n = true -> n = 0%nat \/ n = 1%nat.
Proof.
  intros n H. unfold is_bit in H.
  destruct n as [|[|n]]; auto; simpl in H; discriminate.
Qed.

(** Bell's inequality for WitnessCounts, proved by 16-case exhaustive check. *)
Lemma local_bound_for_wc :
  forall (a0 a1 b0 b1 : nat) (wc : WitnessCounts),
    is_bit a0 = true ->
    is_bit a1 = true ->
    is_bit b0 = true ->
    is_bit b1 = true ->
    WCLocallyConsistent a0 a1 b0 b1 wc ->
    Qabs (chsh_stat_from_wc wc) <= 2.
Proof.
  intros a0 a1 b0 b1 wc Ha0 Ha1 Hb0 Hb1 Hlc.
  destruct Hlc as [H00 H01 H10 H11 [Hs00 [Hs01 [Hs10 Hs11]]]].
  destruct (bit_cases a0 Ha0) as [-> | ->];
  destruct (bit_cases a1 Ha1) as [-> | ->];
  destruct (bit_cases b0 Hb0) as [-> | ->];
  destruct (bit_cases b1 Hb1) as [-> | ->];
  simpl in H00, H01, H10, H11;
  (* In each of the 16 cases, the consistency conditions
     set wc_diff or wc_same to 0 for each setting *)
  unfold chsh_stat_from_wc;
  (* Each case: correlator with one side zero, then simplify. *)
  rewrite ?H00, ?H01, ?H10, ?H11;
  (* After rewriting zeros, each correlator_q has form (n,0) or (0,n) *)
  (* Use the helper lemmas to simplify *)
  repeat match goal with
  | |- context [chsh_correlator_q ?p 0] =>
      let Heq := fresh "Heq" in
      assert (Heq : chsh_correlator_q p 0 == 1)
        by (apply correlator_pos_only; lia);
      setoid_rewrite Heq; clear Heq
  | |- context [chsh_correlator_q 0 ?n] =>
      let Heq := fresh "Heq" in
      assert (Heq : chsh_correlator_q 0 n == -(1))
        by (apply correlator_neg_only; lia);
      setoid_rewrite Heq; clear Heq
  end;
  (* Now goal is Qabs (concrete_Q) <= 2; use Qabs_Qle_condition to split *)
  apply (proj2 (Qabs_Qle_condition _ _)); split; unfold Qle; simpl; lia.
Qed.

Section BellInequality.

(** If S > 2, no local deterministic strategy (with valid bits) can explain wc.
    Proof: if wc were locally consistent, local_bound_for_wc would give |S| ≤ 2;
    but |S| ≥ S > 2 → contradiction. *)
Theorem chsh_stat_violation_not_local :
  forall (wc : WitnessCounts),
    chsh_stat_from_wc wc > 2 ->
    forall (a0 a1 b0 b1 : nat),
      is_bit a0 = true ->
      is_bit a1 = true ->
      is_bit b0 = true ->
      is_bit b1 = true ->
      ~WCLocallyConsistent a0 a1 b0 b1 wc.
Proof.
  intros wc Hviolation a0 a1 b0 b1 Ha0 Ha1 Hb0 Hb1 Hlocal.
  (* local_bound_for_wc gives |S| ≤ 2 *)
  pose proof (local_bound_for_wc a0 a1 b0 b1 wc Ha0 Ha1 Hb0 Hb1 Hlocal) as Hbound.
  (* S ≤ |S| ≤ 2 contradicts S > 2 *)
  pose proof (Qle_Qabs (chsh_stat_from_wc wc)) as Hle_abs.
  exact (Qlt_irrefl 2
    (Qlt_le_trans 2 _ 2 Hviolation (Qle_trans _ _ _ Hle_abs Hbound))).
Qed.

(** Concrete: violation_wc is not locally consistent with any valid strategy. *)
Corollary violation_wc_not_local :
  forall (a0 a1 b0 b1 : nat),
    is_bit a0 = true ->
    is_bit a1 = true ->
    is_bit b0 = true ->
    is_bit b1 = true ->
    ~WCLocallyConsistent a0 a1 b0 b1 violation_wc.
Proof.
  intros a0 a1 b0 b1 Ha0 Ha1 Hb0 Hb1.
  apply chsh_stat_violation_not_local.
  - apply violation_wc_exceeds_bell.
  - exact Ha0.
  - exact Ha1.
  - exact Hb0.
  - exact Hb1.
Qed.

(** Hoeffding boundary. Not proved here.

    The deterministic result in this file is simple: if the observed witness
    counts give S > 2, those counts are not locally deterministic.

    The statistical problem is different. With finitely many trials, the sample
    statistic can drift away from the expectation. Hoeffding is the standard way
    to control that drift, but this file does not import a probability library,
    so I am not pretending to have proved that part.

    If someone wants the exact boundary later, the usual route is a Hoeffding
    bound on the four setting-wise estimators plus a union bound. Until that is
    formalized in Coq, it stays outside the closeout claim.
*)

(** Deterministic closeout.

  This is the part I am actually claiming here: if the witness counts push
  the observed statistic above 2, then no valid-bit deterministic local
  strategy explains those counts.
*)

(** The statistical certification predicate:
    A VMState certifies a CHSH violation if observed S > 2. *)
Definition chsh_violation_certified (s : VMState) : Prop :=
  chsh_stat_from_wc s.(vm_witness) > 2.

(** If a VMState's witness counts have S > 2, no valid deterministic local
    strategy can explain those witness counts. *)
Theorem chsh_certification_not_local :
  forall (s : VMState),
    chsh_violation_certified s ->
    forall (a0 a1 b0 b1 : nat),
      is_bit a0 = true ->
      is_bit a1 = true ->
      is_bit b0 = true ->
      is_bit b1 = true ->
      ~WCLocallyConsistent a0 a1 b0 b1 s.(vm_witness).
Proof.
  intros s Hcert a0 a1 b0 b1 Ha0 Ha1 Hb0 Hb1.
  unfold chsh_violation_certified in Hcert.
  exact (chsh_stat_violation_not_local s.(vm_witness) Hcert
           a0 a1 b0 b1 Ha0 Ha1 Hb0 Hb1).
Qed.

End BellInequality.

(** W2 connection: counted trials still cost counted instructions.

    This is where the Bell side meets the cost side. If you want N counted
    CHSH trials in the witness ledger, W2 says you pay with N valid
    CHSH_TRIAL instructions. There is no shortcut hidden in the counters.
*)

(** Close Q_scope for the nat-based W7 section. *)
Local Close Scope Q_scope.

(** The violation_wc has total witness count 4 (1 trial per setting). *)
Lemma violation_wc_total :
  witness_total violation_wc = 4%nat.
Proof. unfold witness_total, violation_wc. simpl. reflexivity. Qed.

(** Reserved: chsh_violation_witness_count would state:
    Starting from zero witness counts and executing 4 CHSH_TRIAL instructions
    covering all setting pairs costs at least 4 μ-units.
    The real content is in chsh_trial_count_lower_bound for n = 4.
    Reserved for future connection to the actual W2 lower-bound proof. *)

(** Direct application of W2 (chsh_trial_count_lower_bound with n = 4):
    Any trace from zero trials to witness_total ≥ 4 requires ≥ 4
    valid CHSH_TRIAL instructions. *)
Theorem four_trials_require_four_instructions :
  forall (trace : list vm_instruction) (s0 : VMState),
    witness_total s0.(vm_witness) = 0%nat ->
    chsh_cert_n 4%nat (cs_run (chsh_cert_system_n 4%nat) trace s0) = true ->
    cs_total_cost (chsh_cert_system_n 4%nat) trace >= 4%nat.
Proof.
  intros trace s0 Hinit Hcert.
  exact (chsh_trial_count_lower_bound 4%nat trace s0 Hinit Hcert).
Qed.

(** General: N certified trials require N counted instructions. *)
Corollary n_trials_require_n_instructions :
  forall (n : nat) (trace : list vm_instruction) (s0 : VMState),
    witness_total s0.(vm_witness) = 0%nat ->
    chsh_cert_n n (cs_run (chsh_cert_system_n n) trace s0) = true ->
    cs_total_cost (chsh_cert_system_n n) trace >= n.
Proof.
  intros n trace s0 Hinit Hcert.
  exact (chsh_trial_count_lower_bound n trace s0 Hinit Hcert).
Qed.

(** Summary.

  Here is the full deterministic chain proved in this file:

  CHSH_TRIAL instructions -> witness counter -> observed CHSH statistic ->
  if S > 2, no deterministic local strategy fits the counts.

  The probability side is outside this file's scope and is not
  attempted: lifting the deterministic CHSH chain to a finite-sample
  confidence statement requires a real probability formalisation that
  the kernel does not currently provide. *)
