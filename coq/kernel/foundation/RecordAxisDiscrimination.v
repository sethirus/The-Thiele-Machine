(** RecordAxisDiscrimination: which machines carry the record axis.

    - Every base carries it. For any base and any event the base reaches
      from a starting state, the latch of that event, priced one unit per
      write, is an honest extension ([latch_core_honest]). A RAM, a Turing
      machine, and L are all bases, so each carries the axis as itself
      plus a latch.
    - A reversible base with unbounded memory carries it and stays
      reversible: keep every old record value in a history, and the whole
      step forgets nothing ([history_latch_injective],
      [history_latch_honest]).
    - A reversible machine with finite memory cannot: on a finite state
      space a step that writes a permanent record is not injective
      ([finite_reversible_cannot_write], from
      [permanent_flip_is_not_injective]).

    A record run by a hidden clock ([clock_record_not_driven]) and a record
    that can switch back off ([toggle_not_latch]) are ruled out in
    [StructuralRecordAxis]. A machine that bills for time only changes its
    ledger, which the latch form does not constrain. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import StructuralCore StructuralCoreCover StructuralCoreAnyBase.
From Kernel Require Import PermanentCertification.

(** * Every base carries the axis *)

Section Latch.

Variable B : BaseMachine.
Variable h : b_state B -> bool.

Definition flip_cost (b : b_state B) (r : bool) : nat :=
  if r then 0 else if h b then 1 else 0.

Definition LatchCore : RCM := {|
  rc_state := b_state B * bool * nat;
  rc_next := fun x => let '(b, r, m) := x in
    (b_next B b, orb r (h b), m + flip_cost b r);
  rc_init := fun x => let '(b, r, m) := x in b_init B b /\ r = false /\ m = 0;
  rc_cert := fun x => let '(_, r, _) := x in r;
  rc_mu := fun x => let '(_, _, m) := x in m;
  rc_halted := fun x => let '(b, _, _) := x in b_halted B b
|}.

Definition latch_cover : BaseCover LatchCore B.
Proof.
  refine (Build_BaseCover LatchCore B (fun x => let '(b, _, _) := x in b) _ _ _ _).
  - intros [[b r] m] [Hb _]. exact Hb.
  - intros b Hb. exists (b, false, 0). split; [split; [exact Hb | split; reflexivity] | reflexivity].
  - intros [[b r] m]. reflexivity.
  - intros [[b r] m]. simpl. tauto.
Defined.

Theorem latch_core_honest :
  (exists b0 n, b_init B b0 /\
     let '(b, r, _) := rc_run LatchCore n (b0, false, 0) in r = false /\ h b = true) ->
  HonestBaseExtension LatchCore B latch_cover.
Proof.
  intros [b0 [n [Hb0 Hwrite]]].
  split; [exists (fun b r => orb r (h b)); intros [[b r] m]; reflexivity |].
  split; [intros [[b r] m]; simpl; lia |].
  split.
  - intros [[b r] m] H0 H1. unfold step_cost. simpl in H0, H1 |- *.
    subst r. simpl in H1. unfold flip_cost. rewrite H1. lia.
  - split.
    + intros [[b r] m] H. simpl in *. rewrite H. reflexivity.
    + exists (b0, false, 0), n. split; [split; [exact Hb0 | split; reflexivity] |].
      destruct (rc_run LatchCore n (b0, false, 0)) as [[b r] m] eqn:Hrun.
      destruct Hwrite as [Hr Hh]. subst r.
      split; [reflexivity |]. simpl. rewrite Hh. reflexivity.
Qed.

End Latch.

(** * A reversible base with unbounded memory *)

Section History.

Variable B : BaseMachine.
Variable h : b_state B -> bool.

(** The latch, keeping every earlier record value. *)
Definition HistoryLatch : RCM := {|
  rc_state := b_state B * bool * list bool * nat;
  rc_next := fun x => let '(b, r, hist, m) := x in
    (b_next B b, orb r (h b), r :: hist, m + flip_cost B h b r);
  rc_init := fun x => let '(b, r, hist, m) := x in
    b_init B b /\ r = false /\ hist = [] /\ m = 0;
  rc_cert := fun x => let '(_, r, _, _) := x in r;
  rc_mu := fun x => let '(_, _, _, m) := x in m;
  rc_halted := fun x => let '(b, _, _, _) := x in b_halted B b
|}.

Theorem history_latch_injective :
  (forall a b, b_next B a = b_next B b -> a = b) ->
  forall x y, rc_next HistoryLatch x = rc_next HistoryLatch y -> x = y.
Proof.
  intros next_injective [[[b r] hist] m] [[[b' r'] hist'] m'] H. simpl in H.
  injection H as Hb Hr Hh Hm.
  apply next_injective in Hb. subst b' r' hist'.
  f_equal. lia.
Qed.

Definition history_cover : BaseCover HistoryLatch B.
Proof.
  refine (Build_BaseCover HistoryLatch B
            (fun x => let '(b, _, _, _) := x in b) _ _ _ _).
  - intros [[[b r] hist] m] [Hb _]. exact Hb.
  - intros b Hb. exists (b, false, [], 0).
    split; [split; [exact Hb | split; [reflexivity | split; reflexivity]] | reflexivity].
  - intros [[[b r] hist] m]. reflexivity.
  - intros [[[b r] hist] m]. simpl. tauto.
Defined.

Theorem history_latch_honest :
  (exists b0 n, b_init B b0 /\
     let '(b, r, _, _) := rc_run HistoryLatch n (b0, false, [], 0) in
     r = false /\ h b = true) ->
  HonestBaseExtension HistoryLatch B history_cover.
Proof.
  intros [b0 [n [Hb0 Hwrite]]].
  split; [exists (fun b r => orb r (h b)); intros [[[b r] hist] m]; reflexivity |].
  split; [intros [[[b r] hist] m]; simpl; lia |].
  split.
  - intros [[[b r] hist] m] H0 H1. unfold step_cost. simpl in H0, H1 |- *.
    subst r. simpl in H1. unfold flip_cost. rewrite H1. lia.
  - split.
    + intros [[[b r] hist] m] H. simpl in *. rewrite H. reflexivity.
    + exists (b0, false, [], 0), n.
      split; [split; [exact Hb0 | split; [reflexivity | split; reflexivity]] |].
      destruct (rc_run HistoryLatch n (b0, false, [], 0)) as [[[b r] hist] m] eqn:Hrun.
      destruct Hwrite as [Hr Hh]. subst r.
      split; [reflexivity |]. simpl. rewrite Hh. reflexivity.
Qed.

End History.


(** * A reversible machine with finite memory cannot write the record *)

Theorem finite_reversible_cannot_write :
  forall (S : Type) (step : S -> unit -> S) (cert : S -> bool) (all : list S) s,
    finite_states all ->
    permanent step cert ->
    step_injective step tt ->
    ~ (cert s = false /\ cert (step s tt) = true).
Proof.
  intros S step cert all s Hfin Hperm Hinj [H0 H1].
  exact (permanent_flip_is_not_injective S unit step cert all s tt Hfin Hperm H0 H1 Hinj).
Qed.

Print Assumptions latch_core_honest.
Print Assumptions history_latch_injective.
Print Assumptions history_latch_honest.
Print Assumptions finite_reversible_cannot_write.
