(** NecEChshInt.v: the integer side of the CHSH check, at its limits.

    Everything here is integer or rational arithmetic and is closed under
    the global context.

    1. None of the seven integer facts of the check follows from the other
       six: for each fact a tally passes the other six and fails that one
       [nec_e_check_facts_irredundant].
    2. Every tally whose pairs 00 and 10 were sampled and came out all
       "same" or all "different" fails the check. In particular every
       deterministic plan, replayed any number of times, is refused
       [nec_e_check_refuses_deterministic].
    3. The counter-record bound (the book's "A tally above 2 is not one
       replayed strategy"): |S| <= 2 is attained by a locally consistent
       record [nec_e_local_bound_attained]; it fails without the sampling
       clause (score 3) [nec_e_local_bound_needs_sampling] and fails for
       response labels that are not bits (score -4)
       [nec_e_local_bound_needs_bits]; but the one-sided form "S > 2 rules
       out every table" holds for any labels at all
       [nec_e_violation_any_labels].
    4. The deterministic sum a0 b0 + a0 b1 + a1 b0 - a1 b1 reaches both 2
       and -2 [nec_e_deterministic_tight].

    Dependencies: SmallChshCheck.v, CHSHColumnCheck.v,
    CHSHStatisticalBridge.v. No axioms used by these results.            *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is integer arithmetic about the CHSH check (it imports the machine-free
   quantum files only). Its link to the abstract record (the machine of
   SmallChshMachine.v as a CertificationSystem, with the floor of 3 for a
   certified run) lives in SmallChshLinks.v. *)

From Coq Require Import List Arith Lia Bool ZArith QArith Qabs.
Import ListNotations.
From Kernel Require Import CHSHColumnCheck CHSHStatisticalBridge SmallChshCheck.
Local Open Scope nat_scope.

(* ================================================================= *)
(* 1. The seven facts, one at a time.                                  *)
(* ================================================================= *)

Definition nec_e_fact (k : nat) (t : small_chsh_tally) : bool :=
  let d00 := small_chsh_d t.(small_chsh_same00) t.(small_chsh_diff00) in
  let n00 := small_chsh_n t.(small_chsh_same00) t.(small_chsh_diff00) in
  let d01 := small_chsh_d t.(small_chsh_same01) t.(small_chsh_diff01) in
  let n01 := small_chsh_n t.(small_chsh_same01) t.(small_chsh_diff01) in
  let d10 := small_chsh_d t.(small_chsh_same10) t.(small_chsh_diff10) in
  let n10 := small_chsh_n t.(small_chsh_same10) t.(small_chsh_diff10) in
  let d11 := small_chsh_d t.(small_chsh_same11) t.(small_chsh_diff11) in
  let n11 := small_chsh_n t.(small_chsh_same11) t.(small_chsh_diff11) in
  let A := (n00 * n00 * (n10 * n10) - d00 * d00 * (n10 * n10) - d10 * d10 * (n00 * n00))%Z in
  let B := (n01 * n01 * (n11 * n11) - d01 * d01 * (n11 * n11) - d11 * d11 * (n01 * n01))%Z in
  let C := (d00 * d01 * n10 * n11 + d10 * d11 * n00 * n01)%Z in
  match k with
  | 0 => Z.ltb 0 n00
  | 1 => Z.ltb 0 n01
  | 2 => Z.ltb 0 n10
  | 3 => Z.ltb 0 n11
  | 4 => Z.leb 0 A
  | 5 => Z.leb 0 B
  | _ => Z.leb (C * C) (A * B)
  end.

Lemma nec_e_check_split : forall t,
  small_chsh_check t =
  nec_e_fact 0 t && (nec_e_fact 1 t && (nec_e_fact 2 t && (nec_e_fact 3 t &&
  (nec_e_fact 4 t && (nec_e_fact 5 t && nec_e_fact 6 t))))).
Proof. intro t. reflexivity. Qed.

Theorem nec_e_check_iff_facts : forall t,
  small_chsh_check t = true <-> (forall k, k < 7 -> nec_e_fact k t = true).
Proof.
  intro t. rewrite nec_e_check_split. split.
  - intros H k Hk. repeat rewrite andb_true_iff in H.
    destruct H as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
    destruct k as [| [| [| [| [| [| [| k]]]]]]]; auto; lia.
  - intro H. repeat rewrite andb_true_iff.
    repeat split; apply H; lia.
Qed.

(* The witnesses, one per fact. Counts are (same, diff) for 00, 01, 10, 11. *)
Definition nec_e_t0 := small_chsh_mk 0 0 1 1 1 1 1 1.
Definition nec_e_t1 := small_chsh_mk 1 1 0 0 1 1 1 1.
Definition nec_e_t2 := small_chsh_mk 1 1 1 1 0 0 1 1.
Definition nec_e_t3 := small_chsh_mk 1 1 1 1 1 1 0 0.
(* E00 = 1, E01 = 3/5, E10 = -3/4, E11 = 4/5: the first column is too long. *)
Definition nec_e_t4 := small_chsh_mk 1 0 4 1 1 7 9 1.
(* E00 = 3/5, E01 = 1, E10 = 4/5, E11 = -3/4: the second column is too long. *)
Definition nec_e_t5 := small_chsh_mk 4 1 1 0 9 1 1 7.
(* All four correlators 3/5: each column fits, the columns overlap too much. *)
Definition nec_e_t6 := small_chsh_mk 4 1 4 1 4 1 4 1.

Definition nec_e_wit (k : nat) : small_chsh_tally :=
  match k with
  | 0 => nec_e_t0 | 1 => nec_e_t1 | 2 => nec_e_t2 | 3 => nec_e_t3
  | 4 => nec_e_t4 | 5 => nec_e_t5 | _ => nec_e_t6
  end.

(* No fact of the seven follows from the other six. *)
Theorem nec_e_check_facts_irredundant : forall k, k < 7 ->
  nec_e_fact k (nec_e_wit k) = false /\
  (forall j, j < 7 -> j <> k -> nec_e_fact j (nec_e_wit k) = true) /\
  small_chsh_check (nec_e_wit k) = false.
Proof.
  intros k Hk.
  destruct k as [| [| [| [| [| [| [| k]]]]]]]; [| | | | | | | lia];
  (split; [vm_compute; reflexivity |]);
  (split; [intros j Hj Hne;
           destruct j as [| [| [| [| [| [| [| j]]]]]]]; try lia; vm_compute; reflexivity
          | vm_compute; reflexivity]).
Qed.

(* ================================================================= *)
(* 2. Deterministic pairs are refused.                                 *)
(* ================================================================= *)

Lemma nec_e_d_sq : forall s df, (s = 0 \/ df = 0)%nat ->
  (small_chsh_d s df * small_chsh_d s df = small_chsh_n s df * small_chsh_n s df)%Z.
Proof.
  intros s df [-> | ->]; unfold small_chsh_d, small_chsh_n; simpl; lia.
Qed.

(* If pairs 00 and 10 were sampled and each came out all "same" or all
   "different", the first column fact fails, so the check refuses. Every
   deterministic plan has this shape. *)
Theorem nec_e_check_refuses_deterministic : forall t,
  (t.(small_chsh_same00) = 0 \/ t.(small_chsh_diff00) = 0)%nat ->
  (t.(small_chsh_same10) = 0 \/ t.(small_chsh_diff10) = 0)%nat ->
  (0 < t.(small_chsh_same00) + t.(small_chsh_diff00))%nat ->
  (0 < t.(small_chsh_same10) + t.(small_chsh_diff10))%nat ->
  nec_e_fact 4 t = false /\ small_chsh_check t = false.
Proof.
  intros t H00 H10 P00 P10.
  assert (H4 : nec_e_fact 4 t = false).
  { unfold nec_e_fact. cbv zeta.
    pose proof (nec_e_d_sq _ _ H00) as E0. pose proof (nec_e_d_sq _ _ H10) as E1.
    set (n0 := small_chsh_n (small_chsh_same00 t) (small_chsh_diff00 t)) in *.
    set (n1 := small_chsh_n (small_chsh_same10 t) (small_chsh_diff10 t)) in *.
    set (d0 := small_chsh_d (small_chsh_same00 t) (small_chsh_diff00 t)) in *.
    set (d1 := small_chsh_d (small_chsh_same10 t) (small_chsh_diff10 t)) in *.
    assert (Hn0 : (0 < n0)%Z) by (unfold n0, small_chsh_n; lia).
    assert (Hn1 : (0 < n1)%Z) by (unfold n1, small_chsh_n; lia).
    apply Z.leb_gt. rewrite E0, E1.
    assert (0 < n0 * n0 * (n1 * n1))%Z by (apply Z.mul_pos_pos; nia). nia. }
  split; [exact H4 |].
  rewrite nec_e_check_split, H4. simpl. rewrite !andb_false_r. reflexivity.
Qed.

(* The sixteen deterministic plans, written as tallies of one round per
   pair: the answer bits a0 a1 b0 b1, "same" when a_x = b_y. *)
Definition nec_e_plan (a0 a1 b0 b1 : bool) : small_chsh_tally :=
  let cell (a b : bool) := if Bool.eqb a b then (1, 0)%nat else (0, 1)%nat in
  small_chsh_mk (fst (cell a0 b0)) (snd (cell a0 b0)) (fst (cell a0 b1)) (snd (cell a0 b1))
                (fst (cell a1 b0)) (snd (cell a1 b0)) (fst (cell a1 b1)) (snd (cell a1 b1)).

Theorem nec_e_check_refuses_all_plans : forall a0 a1 b0 b1,
  small_chsh_check (nec_e_plan a0 a1 b0 b1) = false.
Proof. intros [] [] [] []; vm_compute; reflexivity. Qed.

(* ================================================================= *)
(* 3. The counter-record classical bound.                              *)
(* ================================================================= *)

Definition nec_e_wc (s00 d00 s01 d01 s10 d10 s11 d11 : nat) : WitnessCounts :=
  {| wc_same_00 := s00; wc_diff_00 := d00; wc_same_01 := s01; wc_diff_01 := d01;
     wc_same_10 := s10; wc_diff_10 := d10; wc_same_11 := s11; wc_diff_11 := d11 |}.

(* |S| = 2 is attained by a record consistent with the all-zero table. *)
Theorem nec_e_local_bound_attained :
  WCLocallyConsistent 0 0 0 0 (nec_e_wc 1 0 1 0 1 0 1 0) /\
  (chsh_stat_from_wc (nec_e_wc 1 0 1 0 1 0 1 0) == 2)%Q.
Proof.
  split; [| vm_compute; reflexivity].
  constructor; simpl; try reflexivity. repeat split; lia.
Qed.

(* Without the sampling clause the bound fails: the bucket conditions of
   the all-zero table hold, pair 11 was never sampled, and the score is
   3. *)
Theorem nec_e_local_bound_needs_sampling :
  let wc := nec_e_wc 1 0 1 0 1 0 0 0 in
  (if Nat.eqb 0 0 then wc_diff_00 wc = 0%nat else wc_same_00 wc = 0%nat) /\
  (if Nat.eqb 0 0 then wc_diff_01 wc = 0%nat else wc_same_01 wc = 0%nat) /\
  (if Nat.eqb 0 0 then wc_diff_10 wc = 0%nat else wc_same_10 wc = 0%nat) /\
  (if Nat.eqb 0 0 then wc_diff_11 wc = 0%nat else wc_same_11 wc = 0%nat) /\
  (wc_same_11 wc + wc_diff_11 wc = 0)%nat /\
  (chsh_stat_from_wc wc == 3)%Q /\
  ~ (Qabs (chsh_stat_from_wc wc) <= 2)%Q.
Proof.
  intro wc. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [reflexivity |]. split; [reflexivity |]. split; [vm_compute; reflexivity |].
  vm_compute. intro H. apply H. reflexivity.
Qed.

(* Without "the answers are bits" the bound fails: labels a0 = 0, b0 = 1,
   a1 = b1 = 2 make three pairs differ and one agree, every pair is
   sampled, and the score is -4. *)
Theorem nec_e_local_bound_needs_bits :
  let wc := nec_e_wc 0 1 0 1 0 1 1 0 in
  WCLocallyConsistent 0 2 1 2 wc /\
  is_bit 2 = false /\
  (chsh_stat_from_wc wc == -4)%Q /\
  ~ (Qabs (chsh_stat_from_wc wc) <= 2)%Q.
Proof.
  intro wc. split; [constructor; simpl; try reflexivity; repeat split; lia |].
  split; [reflexivity |]. split; [vm_compute; reflexivity |].
  vm_compute. intro H. apply H. reflexivity.
Qed.

(* The one-sided form needs no bits: a score above 2 rules out every
   response table with any labels. *)
Theorem nec_e_violation_any_labels : forall wc,
  (2 < chsh_stat_from_wc wc)%Q ->
  forall a0 a1 b0 b1 : nat, ~ WCLocallyConsistent a0 a1 b0 b1 wc.
Proof.
  intros wc Hv a0 a1 b0 b1 Hlc.
  destruct Hlc as [H00 H01 H10 H11 [Hs00 [Hs01 [Hs10 Hs11]]]].
  destruct (Nat.eqb a0 b0) eqn:E00; destruct (Nat.eqb a0 b1) eqn:E01;
  destruct (Nat.eqb a1 b0) eqn:E10; destruct (Nat.eqb a1 b1) eqn:E11;
  (* the one impossible pattern: three equalities force the fourth *)
  try (apply Nat.eqb_eq in E00; apply Nat.eqb_eq in E01; apply Nat.eqb_eq in E10;
       apply Nat.eqb_neq in E11; lia);
  unfold chsh_stat_from_wc in Hv;
  rewrite ?H00, ?H01, ?H10, ?H11 in Hv;
  repeat match type of Hv with
  | context [chsh_correlator_q ?p 0] =>
      let Heq := fresh "Heq" in
      assert (Heq : (chsh_correlator_q p 0 == 1)%Q) by (apply correlator_pos_only; lia);
      setoid_rewrite Heq in Hv; clear Heq
  | context [chsh_correlator_q 0 ?n] =>
      let Heq := fresh "Heq" in
      assert (Heq : (chsh_correlator_q 0 n == -(1))%Q) by (apply correlator_neg_only; lia);
      setoid_rewrite Heq in Hv; clear Heq
  end;
  unfold Qlt in Hv; simpl in Hv; lia.
Qed.

(* ================================================================= *)
(* 4. The deterministic sum reaches both ends.                         *)
(* ================================================================= *)

Theorem nec_e_deterministic_tight :
  (forall a0 a1 b0 b1 : Z, (a0 = 1 \/ a0 = -1) -> (a1 = 1 \/ a1 = -1) ->
     (b0 = 1 \/ b0 = -1) -> (b1 = 1 \/ b1 = -1) ->
     -2 <= a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1 <= 2)%Z /\
  (1 * 1 + 1 * 1 + 1 * 1 - 1 * 1 = 2)%Z /\
  ((-1) * 1 + (-1) * 1 + (-1) * 1 - (-1) * 1 = -2)%Z.
Proof.
  split; [| split; reflexivity].
  intros a0 a1 b0 b1 [-> | ->] [-> | ->] [-> | ->] [-> | ->]; simpl; lia.
Qed.

Print Assumptions nec_e_check_iff_facts.
Print Assumptions nec_e_check_facts_irredundant.
Print Assumptions nec_e_check_refuses_deterministic.
Print Assumptions nec_e_check_refuses_all_plans.
Print Assumptions nec_e_local_bound_attained.
Print Assumptions nec_e_local_bound_needs_sampling.
Print Assumptions nec_e_local_bound_needs_bits.
Print Assumptions nec_e_violation_any_labels.
Print Assumptions nec_e_deterministic_tight.
