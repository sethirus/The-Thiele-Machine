(** This file connects aggregate [WitnessCounts] to two deterministic results.
    It computes the CHSH statistic, proves the algebraic ceiling, exhibits one count pattern with value 4, proves that locally consistent deterministic counts stay within 2, and connects counted trial instructions to the W2 cost lower bound.
    It does not prove a Hoeffding bound, a confidence level, or a physical Bell-test conclusion. *)

From Coq Require Import List Arith.PeanoNat Lia QArith QArith.Qabs ZArith Lra PArith.BinPos PArith.Pnat.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof
                           AbstractNoFI UniversalCertificationCost
                           QuantitativeNoFI CHSH.

Open Scope Q_scope.

(** [chsh_stat_from_wc] computes the four-setting CHSH expression from the eight same/different witness buckets.
    The last term swaps its buckets to implement the chosen minus sign. *)

(** [chsh_correlator_q] returns (pos - neg) / (pos + neg), with rational zero when the denominator is zero by convention. *)
Definition chsh_correlator_q (pos neg : nat) : Q :=
  let total := (pos + neg)%nat in
  if Nat.eqb total 0 then 0
  else (Z.of_nat pos - Z.of_nat neg # Pos.of_nat total).

Definition chsh_stat_from_wc (wc : WitnessCounts) : Q :=
  chsh_correlator_q (wc_same_00 wc) (wc_diff_00 wc) +
  chsh_correlator_q (wc_same_01 wc) (wc_diff_01 wc) +
  chsh_correlator_q (wc_same_10 wc) (wc_diff_10 wc) +
  chsh_correlator_q (wc_diff_11 wc) (wc_same_11 wc).

(** The next theorem proves the algebraic ceiling using only the four correlator bounds and the triangle inequality. *)

(** Positive naturals are represented by the corresponding positive integers in this arithmetic development. *)
Lemma Z_of_nat_pos :
  forall n : nat, (0 < n)%nat -> Z.of_nat n = Zpos (Pos.of_nat n).
Proof.
  intros n Hn. destruct n. lia.
  (* The successor representation is definitionally the positive-integer representation. *)
  rewrite <- Pos.of_nat_succ. reflexivity.
Qed.

(** Each correlator has absolute value at most one because the absolute difference is at most the sum. *)
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
    (* Rewrite the positive denominator as the corresponding integer. *)
    rewrite <- Z_of_nat_pos by exact Hpn.
    rewrite Nat2Z.inj_add.
    (* Reduce the remaining goal to the integer absolute-value inequality. *)
    apply Z.abs_le. split; lia.
Qed.

(** The four correlator terms give an algebraic absolute-value bound of four. *)
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

(** [violation_wc] is one explicit count pattern with one trial per setting and CHSH value four.
    It is a data witness, not a theorem that a VM trace constructs this pattern. *)

Definition violation_wc : WitnessCounts :=
  {| wc_same_00 := 1; wc_diff_00 := 0;
     wc_same_01 := 1; wc_diff_01 := 0;
     wc_same_10 := 1; wc_diff_10 := 0;
     wc_same_11 := 0; wc_diff_11 := 1 |}.

(** The closed count witness evaluates to CHSH value four. *)
Lemma violation_wc_stat_eq_4 :
  chsh_stat_from_wc violation_wc == 4.
Proof.
  unfold chsh_stat_from_wc, violation_wc, chsh_correlator_q.
  simpl. vm_compute. reflexivity.
Qed.

(** The closed count witness is greater than two. *)
Lemma violation_wc_exceeds_bell :
  chsh_stat_from_wc violation_wc > 2.
Proof.
  rewrite violation_wc_stat_eq_4.
  unfold Qlt. simpl. lia.
Qed.

(** The closed count witness satisfies the algebraic ceiling. *)
Lemma violation_wc_within_algebraic :
  Qabs (chsh_stat_from_wc violation_wc) <= 4.
Proof.
  apply chsh_stat_algebraic_bound.
Qed.

(** [WCLocallyConsistent] records the zero bucket forced by a deterministic response table for each setting pair and requires every pair to have been sampled. *)

(** Predicate: WitnessCounts consistent with local strategy (a0,a1,b0,b1). *)
Record WCLocallyConsistent (a0 a1 b0 b1 : nat) (wc : WitnessCounts) : Prop :=
  mk_wclc {
    (** The (0,0) bucket follows the equality of [a0] and [b0]. *)
    wclc_00     : if Nat.eqb a0 b0
                  then (wc_diff_00 wc = 0)%nat
                  else (wc_same_00 wc = 0)%nat;
    (** The (0,1) bucket follows the equality of [a0] and [b1]. *)
    wclc_01     : if Nat.eqb a0 b1
                  then (wc_diff_01 wc = 0)%nat
                  else (wc_same_01 wc = 0)%nat;
    (** The (1,0) bucket follows the equality of [a1] and [b0]. *)
    wclc_10     : if Nat.eqb a1 b0
                  then (wc_diff_10 wc = 0)%nat
                  else (wc_same_10 wc = 0)%nat;
    (** The (1,1) bucket follows the equality of [a1] and [b1]. *)
    wclc_11     : if Nat.eqb a1 b1
                  then (wc_diff_11 wc = 0)%nat
                  else (wc_same_11 wc = 0)%nat;
    (** Every setting pair has at least one counted trial. *)
    wclc_all_sampled :
      (wc_same_00 wc + wc_diff_00 wc > 0)%nat /\
      (wc_same_01 wc + wc_diff_01 wc > 0)%nat /\
      (wc_same_10 wc + wc_diff_10 wc > 0)%nat /\
      (wc_same_11 wc + wc_diff_11 wc > 0)%nat
  }.

(** The local-count theorem below reduces the four response bits to the 16 finite cases, as in [CHSH.v]. *)

(** A nonempty all-positive bucket has correlator one. *)
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

(** A nonempty all-negative bucket has correlator minus one. *)
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

(** A successful [is_bit] check leaves the two natural-number cases. *)
Lemma bit_cases : forall n, is_bit n = true -> n = 0%nat \/ n = 1%nat.
Proof.
  intros n H. unfold is_bit in H.
  destruct n as [|[|n]]; auto; simpl in H; discriminate.
Qed.

(** Locally consistent sampled counts satisfy the deterministic CHSH bound. *)
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
  (* In each finite case, consistency sets one bucket to zero for every setting. *)
  unfold chsh_stat_from_wc;
  (* Each correlator now has one zero bucket. *)
  rewrite ?H00, ?H01, ?H10, ?H11;
  (* Rewrite the remaining correlators with the helper lemmas. *)
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
  (* The final integer inequality follows from the absolute-value characterization. *)
  apply (proj2 (Qabs_Qle_condition _ _)); split; unfold Qle; simpl; lia.
Qed.

Section BellInequality.

(** A count pattern with value greater than two cannot satisfy [WCLocallyConsistent] for any valid response table. *)
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

(** The explicit value-four witness is not locally consistent with any valid response table. *)
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

(** The file stops at the deterministic count result.
    A finite-sample confidence statement would need a probability model, sampling assumptions, and a separate formal development. *)

(** This predicate records the aggregate-count condition [S > 2] for a VM state. *)
Definition chsh_violation_certified (s : VMState) : Prop :=
  chsh_stat_from_wc s.(vm_witness) > 2.

(** A VM state satisfying the aggregate-count condition has no locally consistent valid response table. *)
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

(** The W2 results connect counted trial instructions to the witness-count threshold.
    They do not infer a probability statement from the aggregate counts. *)

(** The remaining lemmas use natural-number cost statements rather than rational expressions. *)
Local Close Scope Q_scope.

(** The explicit witness contains four counted trials. *)
Lemma violation_wc_total :
  witness_total violation_wc = 4%nat.
Proof. unfold witness_total, violation_wc. simpl. reflexivity. Qed.

(** The execution-to-count bridge is [chsh_trial_count_lower_bound]; this aggregate model does not add a separate probability or sampling theorem. *)

(** Four counted trials require at least four valid trial instructions under the W2 premises. *)
Theorem four_trials_require_four_instructions :
  forall (trace : list vm_instruction) (s0 : VMState),
    witness_total s0.(vm_witness) = 0%nat ->
    chsh_cert_n 4%nat (cs_run (chsh_cert_system_n 4%nat) trace s0) = true ->
    cs_total_cost (chsh_cert_system_n 4%nat) trace >= 4%nat.
Proof.
  intros trace s0 Hinit Hcert.
  exact (chsh_trial_count_lower_bound 4%nat trace s0 Hinit Hcert).
Qed.

(** In general, the W2 theorem gives one counted instruction per certified trial threshold. *)
Corollary n_trials_require_n_instructions :
  forall (n : nat) (trace : list vm_instruction) (s0 : VMState),
    witness_total s0.(vm_witness) = 0%nat ->
    chsh_cert_n n (cs_run (chsh_cert_system_n n) trace s0) = true ->
    cs_total_cost (chsh_cert_system_n n) trace >= n.
Proof.
  intros n trace s0 Hinit Hcert.
  exact (chsh_trial_count_lower_bound n trace s0 Hinit Hcert).
Qed.

(** The proved chain is: trial instructions update witness counts, the counts determine the chosen statistic, and a value above two excludes the stated deterministic local response tables.
    Finite-sample confidence remains outside this aggregate-count model. *)
