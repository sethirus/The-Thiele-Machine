(** AxNecessity: each clause of Thiele-complete on the axis does work.

    A clock fails.  A machine that charges 1 for every move has the toll for
    free, and a universal base, whatever its record is and whatever order the
    record lives in; it is not Thiele-complete on the axis, because a
    Thiele-complete machine has a move that costs nothing
    ([ax_clock_weakly_complete], [ax_clock_not_tc]).  Even a record that is
    the whole shadow, the counter configuration itself, is a clock record.

    For each clause there is a neighbour of any Thiele-complete machine that
    meets the other three and fails that one.  The neighbours of the book's
    necessity results are used through the two-point reading
    ([lift_base_iff], [lift_toll_iff], [lift_nonvac_iff], [lift_earned_iff]
    of AxTwoPoint):

      ax_nec_earned_chain    a move ZAP that costs 1 and raises the record
                             from every state: base, toll and non-vacuity
                             hold, the earned clause fails.
      ax_nec_toll_cost       charging twice for every move: base, earned
                             clause and non-vacuity hold, the toll fails.
      ax_nec_toll_ledger     a ledger that reads 0: the toll fails, the rest
                             holds.
      ax_nec_sound_check     a CHECK that always passes: the earned clause
                             fails at its soundness conjunct.
      ax_nec_respect_same    "unchanged" holding of every pair of states: the
                             earned clause fails at its respect conjunct.
      ax_nec_base            a machine whose only free move does nothing meets
                             the other three clauses (the book's loose
                             notion) and no axis interface makes it
                             Thiele-complete ([ax_nb_not_tc]).

    The clauses that exist only on the axis have their own witnesses in
    AxNecessity2: the record after a move is exactly the join of the old
    record and the point of the claim, and the record never goes down. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Kernel Require Import AxCore AxLatch AxComplete AxComplete2 AxTwoPoint.
Require Minimal.ThieleComplete.
Require Minimal.NecTEarned.
Require Minimal.NecTToll.
Require Minimal.NecTLoop.
Require Minimal.NecTLoose.
Module T := Minimal.ThieleComplete.

(** * A clock fails *)

(** Every move costs 1, the record is any function of the configuration. *)
Definition ax_clock {A : Type} {P : BPre A} (rd : T.cm_conf -> A) : amachine A P :=
  mk_am A P T.cm_conf T.cm_instr (fun x i => T.cm_exec i x) (fun _ => 1) rd.

Definition ax_clock_ub {A : Type} {P : BPre A} (rd : T.cm_conf -> A)
  : T.universal_base (am_bare (ax_clock (P := P) rd)) :=
  T.mk_ub (am_bare (ax_clock (P := P) rd)) (fun x => x) (fun _ => True) (fun i => i)
    (fun a b => (1, (a, b))) (fun a b => eq_refl) (fun a b => I)
    (fun s i _ => conj eq_refl I).

(** The toll holds for a clock, whatever the record, and the base is universal:
    the weak notion. *)
Theorem ax_clock_weakly_complete : forall {A : Type} {P : BPre A} (rd : T.cm_conf -> A),
  ax_a2 (X := am_axsys (ax_clock (P := P) rd)) /\
  inhabited (T.universal_base (am_bare (ax_clock (P := P) rd))).
Proof.
  intros A P rd. split.
  - intros s i _. simpl. lia.
  - exact (inhabits (ax_clock_ub rd)).
Qed.

(** A Thiele-complete axis machine has a move that costs nothing. *)
Theorem ax_tc_has_free_move : forall {A : Type} {P : BPre A} (AM : amachine A P),
  ax_thiele_complete AM -> exists m, am_cost AM m = 0.
Proof.
  intros A P AM [I [[Hk _] [_ [[Hcost _] _]]]].
  exists (T.ub_compile (axi_base I) (T.CINC T.RA)). rewrite Hcost.
  unfold ax_record_move. rewrite Hk. reflexivity.
Qed.

Theorem ax_clock_not_tc : forall {A : Type} {P : BPre A} (AM : amachine A P),
  (forall m, am_cost AM m >= 1) -> ~ ax_thiele_complete AM.
Proof.
  intros A P AM Hc H. destruct (ax_tc_has_free_move AM H) as [m Hm].
  specialize (Hc m). lia.
Qed.

Corollary ax_clock_not_complete : forall {A : Type} {P : BPre A} (rd : T.cm_conf -> A),
  ~ ax_thiele_complete (ax_clock (P := P) rd).
Proof. intros A P rd. apply ax_clock_not_tc. intro m. simpl. lia. Qed.

(** * Each clause, through the two-point reading *)

Section Neighbours.

Variable M : T.machine.
Variable I : T.thiele_interface M.
Hypothesis HC : T.thiele_complete_with I.

(** The earned clause: a move that raises the record from every state. *)
Theorem ax_nec_earned_chain :
  let J := Minimal.NecTEarned.zap_interface I in
  axc_base (lift_ai J) /\ axc_toll (lift_ai J) /\ axc_nonvac (lift_ai J) /\
  ~ axc_earned (lift_ai J).
Proof.
  destruct (Minimal.NecTEarned.nec_t_zap_meets_all_but_chain M I HC)
    as [Hb [_ [Ht [Hn Hnot]]]].
  simpl. split; [apply lift_base_iff; exact Hb |]. split; [apply lift_toll_iff; exact Ht |].
  split; [apply lift_nonvac_iff; exact Hn |].
  intro He. apply Hnot. apply (proj2 (lift_earned_iff _ _ Hb)). exact He.
Qed.

(** The exact toll, cost half: charge twice as much for every move. *)
Theorem ax_nec_toll_cost :
  let f := fun m => 2 * T.m_cost M m in
  let J := Minimal.NecTToll.cm_interface f I in
  axc_base (lift_ai J) /\ axc_earned (lift_ai J) /\ axc_nonvac (lift_ai J) /\
  ~ axc_toll (lift_ai J).
Proof.
  destruct (Minimal.NecTToll.nec_t_doubled_cost_meets_all_but_toll M I HC)
    as [Hb [He [Hn [Ht _]]]].
  simpl. split; [apply lift_base_iff; exact Hb |].
  split; [apply (proj1 (lift_earned_iff _ _ Hb)); exact He |].
  split; [apply lift_nonvac_iff; exact Hn |].
  intro H. apply Ht. apply lift_toll_iff. exact H.
Qed.

(** The exact toll, ledger half: a ledger that reads 0. *)
Theorem ax_nec_toll_ledger :
  let J := Minimal.NecTToll.with_ledger I (fun _ => 0) in
  axc_base (lift_ai J) /\ axc_earned (lift_ai J) /\ axc_nonvac (lift_ai J) /\
  ~ axc_toll (lift_ai J).
Proof.
  destruct (Minimal.NecTToll.nec_t_ledgerless_meets_all_but_ledger M I HC)
    as [Hb [He [Hn [_ [Ht _]]]]].
  simpl. split; [apply lift_base_iff; exact Hb |].
  split; [apply (proj1 (lift_earned_iff _ _ Hb)); exact He |].
  split; [apply lift_nonvac_iff; exact Hn |].
  intro H. apply Ht. apply lift_toll_iff. exact H.
Qed.

(** The earned clause, soundness conjunct: a CHECK that always passes. *)
Theorem ax_nec_sound_check :
  let J := Minimal.NecTToll.with_check I (fun _ _ => true) in
  axc_base (lift_ai J) /\ axc_toll (lift_ai J) /\ axc_nonvac (lift_ai J) /\
  ~ (forall s c, axi_check (lift_ai J) s c = true -> axi_meaning (lift_ai J) c s) /\
  ~ axc_earned (lift_ai J).
Proof.
  destruct (Minimal.NecTToll.nec_t_unsound_check_meets_all_but_soundness M I HC)
    as [Hb [Ht [Hn [_ [_ [_ [Hns _]]]]]]].
  simpl. split; [apply lift_base_iff; exact Hb |]. split; [apply lift_toll_iff; exact Ht |].
  split; [apply lift_nonvac_iff; exact Hn |]. split; [exact Hns |].
  intros [_ [_ [Hs _]]]. apply Hns. exact Hs.
Qed.

(** The earned clause, respect conjunct: every pair is "unchanged". *)
Theorem ax_nec_respect_same :
  let J := Minimal.NecTToll.with_same I (fun _ _ _ => True) in
  axc_base (lift_ai J) /\ axc_toll (lift_ai J) /\ axc_nonvac (lift_ai J) /\
  ~ (forall c s s', axi_same (lift_ai J) c s s' -> axi_meaning (lift_ai J) c s ->
                    axi_meaning (lift_ai J) c s') /\
  ~ axc_earned (lift_ai J).
Proof.
  destruct (Minimal.NecTToll.nec_t_same_true_meets_all_but_respect M I HC)
    as [Hb [Ht [Hn [_ [_ [_ Hnr]]]]]].
  simpl. split; [apply lift_base_iff; exact Hb |]. split; [apply lift_toll_iff; exact Ht |].
  split; [apply lift_nonvac_iff; exact Hn |]. split; [exact Hnr |].
  intros [_ [_ [_ Hr]]]. apply Hnr. exact Hr.
Qed.

End Neighbours.

(** * The base clause *)

(** The three-state machine of the book's necessity result, read as an axis
    machine over the two-point order, meets the loose notion (the other three
    clauses without a base, [Minimal.NecTLoose.nec_t_nb_loose_complete]) and no
    axis interface makes it Thiele-complete: its one free move cannot be the
    compiled form of both counter increments. *)
Theorem ax_nb_not_tc : ~ ax_thiele_complete (lift_am Minimal.NecTLoose.nb_machine).
Proof.
  intros [J [[Hk [_ [_ _]]] [_ [[Hcost _] _]]]].
  assert (Hfree : forall i, T.ub_compile (axi_base J) i = Minimal.NecTLoose.NNOP).
  { intro i. specialize (Hk i). pose proof (Hcost (T.ub_compile (axi_base J) i)) as Hc.
    unfold ax_record_move in Hc. rewrite Hk in Hc.
    destruct (T.ub_compile (axi_base J) i); simpl in Hc; try discriminate Hc; reflexivity. }
  set (s0 := T.ub_load (axi_base J) 0 0).
  destruct (T.ub_sim (axi_base J) s0 (T.CINC T.RA) (T.ub_load_live (axi_base J) 0 0)) as [HA _].
  destruct (T.ub_sim (axi_base J) s0 (T.CINC T.RB) (T.ub_load_live (axi_base J) 0 0)) as [HB _].
  rewrite (Hfree (T.CINC T.RA)) in HA. rewrite (Hfree (T.CINC T.RB)) in HB.
  rewrite HA in HB. unfold s0 in HB. rewrite T.ub_load_window in HB. simpl in HB.
  discriminate HB.
Qed.

Theorem ax_nec_base :
  Minimal.NecTLoose.loose_complete_with Minimal.NecTLoose.nb_machine Minimal.NecTLoose.nb_loose /\
  ~ ax_thiele_complete (lift_am Minimal.NecTLoose.nb_machine).
Proof. split; [exact Minimal.NecTLoose.nec_t_nb_loose_complete | exact ax_nb_not_tc]. Qed.

Print Assumptions ax_clock_weakly_complete.
Print Assumptions ax_tc_has_free_move.
Print Assumptions ax_clock_not_tc.
Print Assumptions ax_clock_not_complete.
Print Assumptions ax_nec_earned_chain.
Print Assumptions ax_nec_toll_cost.
Print Assumptions ax_nec_toll_ledger.
Print Assumptions ax_nec_sound_check.
Print Assumptions ax_nec_respect_same.
Print Assumptions ax_nb_not_tc.
Print Assumptions ax_nec_base.
