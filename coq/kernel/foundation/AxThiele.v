(** AxThiele: the member predicate, the flat reading, the smallest machine
    and the history lift.

    This is the definition the README states: a Thiele machine is a priced
    record system whose reading never falls and that some run, from a
    designated start, raises.

    AxCore states the ambient class: a state, moves, a step, a price on each move,
    a reading into a preorder, and the toll on every move that carries the
    reading out of its down-set.  The toll alone is met by a reading that
    never moves, so it alone does not say which systems the name belongs
    to.  This file says it.

    A Thiele machine is a system of the ambient class whose reading some
    run raises and no move lowers: the toll [ax_a2], permanence
    [ax_grows], and a designated start from which some run carries the
    reading out of its down-set [ax_distinction].  The three together are
    [ax_thiele].

    A reading no move ever carries out of its down-set is flat.  Flat is a
    property of the reading, not of the machine: when the states have a
    Boolean equality test and some run ends on a state other than its start,
    the same moves, carried along with a bit fitted beside the state and read
    through that bit, are a member.  The history lift below fits the bit.

    Results (every one closed under the global context):

      flat_obeys_toll             a flat reading obeys the toll; the toll
                                  asks nothing of it.
      flat_has_no_distinction     no run of a flat reading leaves the
                                  down-set of its start.
      flat_is_not_thiele          a flat reading is outside the class, for
                                  every choice of starts.
      thiele_has_a_priced_move    every member has a move that costs at
                                  least 1.
      thiele_floor                every member has the floor.
      two_point_member_raising_move
                                  over the two-point order every member
                                  has a move that raises the reading from
                                  some no-state and keeps every yes-state
                                  at yes.
      latch_is_thiele             the two-state latch with one move priced
                                  1 is a member.
      latch_merges                its one move is not injective: both
                                  states land on one.
      no_one_state_member         a member has two states with different
                                  readings; a constant reading is outside
                                  the class.
      two_state_member_has_latch_move
                                  on two states read as themselves, every
                                  member has the latch's move: both states
                                  land on yes.
      toggle_is_not_thiele        the two-state toggle is not a member: it
                                  fails permanence.
      history_lift_shadow         forgetting the bit of the history lift
                                  gives back the run of the machine
                                  lifted.
      history_lift_is_thiele      every machine with a Boolean equality
                                  test on its states and a run that ends on
                                  a state other than its start is the
                                  shadow of a member.
      moving_machine_is_a_shadow  the same, with the lift taken at the
                                  state the run ends on.
      shadow_hides_history        above every shadow sit two lifted states
                                  with different readings, and no function
                                  of the shadow recovers the reading. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import AxCore.
From Kernel Require Import AxMerge.

(** * The member *)

Section Member.

Variable A : Type.
Variable P : BPre A.
Variable X : AxSys A P.
Variable starts : ax_state A P X -> Prop.

(** A reading no move carries out of its down-set. *)
Definition ax_flat : Prop :=
  forall s i, bp_le P (ax_rec A P X (ax_step A P X s i)) (ax_rec A P X s).

(** From some designated start, some run carries the reading out of its
    down-set. *)
Definition ax_distinction : Prop :=
  exists s tr, starts s /\
    ~ bp_le P (ax_rec A P X (ax_run tr s)) (ax_rec A P X s).

(** The toll, permanence, and a distinction some run makes. *)
Definition ax_thiele : Prop :=
  ax_a2 (X := X) /\ ax_grows (X := X) /\ ax_distinction.

(** The toll asks nothing of a flat reading. *)
Theorem flat_obeys_toll : ax_flat -> ax_a2 (X := X).
Proof. intros Hf s i Hex. exfalso. exact (Hex (Hf s i)). Qed.

Lemma ax_flat_run : ax_flat ->
  forall tr s, bp_le P (ax_rec A P X (ax_run tr s)) (ax_rec A P X s).
Proof.
  intros Hf tr. induction tr as [| i rest IH]; intro s; simpl.
  - apply bp_le_refl.
  - eapply bp_le_trans; [apply IH | apply Hf].
Qed.

(** No run of a flat reading leaves the down-set of its start. *)
Theorem flat_has_no_distinction : ax_flat -> ~ ax_distinction.
Proof. intros Hf [s [tr [_ Hnot]]]. exact (Hnot (ax_flat_run Hf tr s)). Qed.

(** Flat readings are outside the class, whatever the starts. *)
Theorem flat_is_not_thiele : ax_flat -> ~ ax_thiele.
Proof. intros Hf [_ [_ Hd]]. exact (flat_has_no_distinction Hf Hd). Qed.

Lemma ax_total_pos_has_priced : forall tr,
  ax_total (X := X) tr >= 1 -> exists i, In i tr /\ ax_cost A P X i >= 1.
Proof.
  induction tr as [| i rest IH]; simpl; intro H; [lia |].
  destruct (Nat.eq_dec (ax_cost A P X i) 0) as [Hz | Hnz].
  - rewrite Hz in H. simpl in H.
    destruct (IH H) as [j [Hj Hc]]. exists j. split; [right; exact Hj | exact Hc].
  - exists i. split; [left; reflexivity | lia].
Qed.

(** Every member has a move that costs. *)
Theorem thiele_has_a_priced_move : ax_thiele -> exists i, ax_cost A P X i >= 1.
Proof.
  intros [Ha [_ [s [tr [_ Hnot]]]]].
  destruct (ax_total_pos_has_priced tr (proj2 (ax_floor_iff_a2 X) Ha tr s Hnot))
    as [i [_ Hi]].
  exists i. exact Hi.
Qed.

(** Every member has the floor: a run that leaves the down-set of its
    start costs at least 1. *)
Theorem thiele_floor : ax_thiele -> ax_floor (X := X).
Proof. intros [Ha _]. exact (proj2 (ax_floor_iff_a2 X) Ha). Qed.

End Member.

Arguments ax_flat {A P} X.
Arguments ax_distinction {A P} X starts.
Arguments ax_thiele {A P} X starts.

(** * Members over the two-point order *)

Section TwoPoint.

Variable X : AxSys bool two_pre.
Variable starts : ax_state bool two_pre X -> Prop.

Lemma two_not_le : forall a b, ~ bp_le two_pre a b -> a = true /\ b = false.
Proof.
  intros [] [] H; try (split; reflexivity); exfalso; apply H; unfold bp_le; reflexivity.
Qed.

Lemma two_point_run_crosses : forall tr s,
  ax_rec bool two_pre X s = false ->
  ax_rec bool two_pre X (ax_run tr s) = true ->
  exists i t, In i tr /\ ax_rec bool two_pre X t = false /\
    ax_rec bool two_pre X (ax_step bool two_pre X t i) = true.
Proof.
  induction tr as [| i rest IH]; intros s H0 H1; simpl in H1.
  - rewrite H0 in H1. discriminate.
  - destruct (ax_rec bool two_pre X (ax_step bool two_pre X s i)) eqn:E.
    + exists i, s. split; [left; reflexivity | split; [exact H0 | exact E]].
    + destruct (IH _ E H1) as [j [t [Hj Ht]]].
      exists j, t. split; [right; exact Hj | exact Ht].
Qed.

(** Over the two-point order a member has a move that raises the reading
    from some no-state, and that move, like every move, keeps every
    yes-state at yes. *)
Theorem two_point_member_raising_move : ax_thiele X starts ->
  exists i,
    (exists s, ax_rec bool two_pre X s = false /\
               ax_rec bool two_pre X (ax_step bool two_pre X s i) = true) /\
    (forall s, ax_rec bool two_pre X s = true ->
               ax_rec bool two_pre X (ax_step bool two_pre X s i) = true).
Proof.
  intros [_ [Hg [s [tr [_ Hnot]]]]].
  destruct (two_not_le _ _ Hnot) as [H1 H0].
  destruct (two_point_run_crosses tr s H0 H1) as [i [t [_ Hit]]].
  exists i. split; [exists t; exact Hit |].
  intros u Hu. exact (proj1 (two_le _ _) (Hg u i) Hu).
Qed.

End TwoPoint.

(** * The smallest machine *)

(** Two states, no and yes; one move that sends both to yes at price 1;
    the reading is the state.  This is [stamp_sys] of AxMerge with its
    move priced. *)
Definition latch_sys : AxSys bool two_pre :=
  mk_axsys bool two_pre bool unit (fun _ _ => true) (fun _ => 1) (fun b => b).

(** The latch is a member, started at no. *)
Theorem latch_is_thiele : ax_thiele latch_sys (fun b => b = false).
Proof.
  unfold ax_thiele. repeat split.
  - intros s i _. simpl. lia.
  - intros s i. destruct s; unfold bp_le; simpl; reflexivity.
  - exists false, [tt]. split; [reflexivity |]. unfold bp_le. simpl. discriminate.
Qed.

(** The latch's one move sends both states to one: it is not injective. *)
Theorem latch_merges : ~ ax_step_injective latch_sys tt.
Proof. intro H. specialize (H false true eq_refl). discriminate. Qed.

(** A member has two states with different readings, so a one-state
    machine, and any machine with a constant reading, is outside the
    class. *)
Theorem no_one_state_member : forall (A : Type) (P : BPre A) (X : AxSys A P) starts,
  ax_thiele X starts ->
  exists s t : ax_state A P X, s <> t /\ ax_rec A P X s <> ax_rec A P X t.
Proof.
  intros A P X starts [_ [_ [s [tr [_ Hnot]]]]].
  exists (ax_run tr s), s. split; intro E; apply Hnot; rewrite E; apply bp_le_refl.
Qed.

(** On two states read as themselves, every member has the latch's move:
    a move that sends no to yes and yes to yes. *)
Theorem two_state_member_has_latch_move :
  forall (I : Type) (step : bool -> I -> bool) (cost : I -> nat) (starts : bool -> Prop),
  ax_thiele (mk_axsys bool two_pre bool I step cost (fun b => b)) starts ->
  exists i, step false i = true /\ step true i = true.
Proof.
  intros I step cost starts H.
  destruct (two_point_member_raising_move _ _ H) as [i [[s [Hs Hsi]] Hup]].
  simpl in Hs, Hsi, Hup. subst s.
  exists i. split; [exact Hsi | apply Hup; reflexivity].
Qed.

(** The toggle is not a member: its move turns yes back to no. *)
Theorem toggle_is_not_thiele : forall starts, ~ ax_thiele toggle_sys starts.
Proof.
  intros starts [_ [Hg _]].
  specialize (Hg true tt). unfold bp_le in Hg. simpl in Hg. discriminate.
Qed.

(** * The history lift *)

Section HistoryLift.

Variable A : Type.
Variable P : BPre A.
Variable M : AxSys A P.
Variable eqb : ax_state A P M -> ax_state A P M -> bool.
Hypothesis eqb_eq : forall a b, eqb a b = true <-> a = b.
Variable x : ax_state A P M.

(** The machine M with a bit beside it that goes up when a move lands on
    x and never comes down; every move priced 1, the clock price; the
    reading is the bit. *)
Definition history_lift : AxSys bool two_pre :=
  mk_axsys bool two_pre (ax_state A P M * bool) (ax_instr A P M)
    (fun p i => (ax_step A P M (fst p) i,
                 snd p || eqb (ax_step A P M (fst p) i) x))
    (fun _ => 1)
    (fun p => snd p).

(** Forgetting the bit gives back the run of M. *)
Theorem history_lift_shadow : forall tr s b,
  fst (ax_run (X := history_lift) tr (s, b)) = ax_run (X := M) tr s.
Proof.
  induction tr as [| i rest IH]; intros s b; simpl; [reflexivity | apply IH].
Qed.

(** The bit, once up, stays up along every run. *)
Lemma history_lift_bit_stays : forall tr s,
  snd (ax_run (X := history_lift) tr (s, true)) = true.
Proof. induction tr as [| i rest IH]; intros s; simpl; [reflexivity | apply IH]. Qed.

(** A run of M that ends at x, from a start other than x, puts the bit up. *)
Lemma history_lift_bit_up : forall tr s0,
  ax_run (X := M) tr s0 = x -> s0 <> x ->
  snd (ax_run (X := history_lift) tr (s0, false)) = true.
Proof.
  induction tr as [| i rest IH]; intros s0 Hrun Hne; simpl in Hrun; simpl.
  - exfalso. exact (Hne Hrun).
  - destruct (eqb (ax_step A P M s0 i) x) eqn:E.
    + apply history_lift_bit_stays.
    + apply IH; [exact Hrun |].
      intro Hx. rewrite (proj2 (eqb_eq _ _) Hx) in E. discriminate.
Qed.

(** Every machine with a run that ends on a state other than its start is
    the shadow of a member: lift it at the state the run ends on and start
    it with the bit down. *)
Theorem history_lift_is_thiele : forall s0 tr,
  ax_run (X := M) tr s0 = x -> s0 <> x ->
  ax_thiele history_lift (fun p => p = (s0, false)).
Proof.
  intros s0 tr Hrun Hne.
  unfold ax_thiele. repeat split.
  - intros p j _. simpl. lia.
  - intros [s b] j. apply (proj2 (two_le _ _)). simpl. intro Hb. rewrite Hb. reflexivity.
  - exists (s0, false), tr. split; [reflexivity |].
    intro H. pose proof (proj1 (two_le _ _) H) as H'. simpl in H'.
    discriminate (H' (history_lift_bit_up tr s0 Hrun Hne)).
Qed.

(** Above every shadow sit two lifted states with different readings, and
    no function of the shadow recovers the reading. *)
Theorem shadow_hides_history :
  (forall p : ax_state bool two_pre history_lift,
     exists q : ax_state bool two_pre history_lift,
       fst q = fst p /\
       ax_rec bool two_pre history_lift q <> ax_rec bool two_pre history_lift p) /\
  ~ (exists f : ax_state A P M -> bool,
       forall p : ax_state bool two_pre history_lift,
         f (fst p) = ax_rec bool two_pre history_lift p).
Proof.
  split.
  - intros [s b]. exists (s, negb b). split; [reflexivity | simpl; destruct b; discriminate].
  - intros [f Hf].
    pose proof (Hf (x, true)) as H1. pose proof (Hf (x, false)) as H2.
    simpl in H1, H2. rewrite H1 in H2. discriminate.
Qed.

End HistoryLift.

(** The lift taken at the state a run ends on: a machine with a run that
    does not return to its start is the shadow of a member. *)
Theorem moving_machine_is_a_shadow :
  forall (A : Type) (P : BPre A) (M : AxSys A P)
         (eqb : ax_state A P M -> ax_state A P M -> bool),
  (forall a b, eqb a b = true <-> a = b) ->
  forall s0 tr, ax_run (X := M) tr s0 <> s0 ->
  ax_thiele (history_lift A P M eqb (ax_run tr s0)) (fun p => p = (s0, false)).
Proof.
  intros A P M eqb Heqb s0 tr H.
  apply (history_lift_is_thiele A P M eqb Heqb (ax_run tr s0) s0 tr); [reflexivity |].
  intro E. apply H. symmetry. exact E.
Qed.

Print Assumptions flat_obeys_toll.
Print Assumptions flat_has_no_distinction.
Print Assumptions flat_is_not_thiele.
Print Assumptions thiele_has_a_priced_move.
Print Assumptions thiele_floor.
Print Assumptions two_point_member_raising_move.
Print Assumptions latch_is_thiele.
Print Assumptions latch_merges.
Print Assumptions no_one_state_member.
Print Assumptions two_state_member_has_latch_move.
Print Assumptions toggle_is_not_thiele.
Print Assumptions history_lift_shadow.
Print Assumptions history_lift_is_thiele.
Print Assumptions moving_machine_is_a_shadow.
Print Assumptions shadow_hides_history.
