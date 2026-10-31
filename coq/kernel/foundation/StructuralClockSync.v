(** StructuralClockSync: what the latch theorem uses, and what separates a
    clock from a latch.

    StructuralRecordAxis.v proves that a base-driven record (R1 to R5 of
    the book) factors as a latch [record_axis_is_latch_holds]. Its proof uses
    only R1 (driven by the computation) and R4 (permanence). This file
    states that form, and then asks what "driven" has to mean for the
    clock of StructuralRecordAxis.v to be told apart from a latch.

      record_axis_is_latch_r1_r4   R1 and R4 alone give the latch; the ledger,
                                   the toll and the reachable write are not
                                   hypotheses.
      reachably_driven             R1 asked only of states some run reaches
                                   from a starting state.
      record_axis_is_latch_reachable
                                   reachable R1 and R4 give the latch on every
                                   state a run reaches.
      clock_not_reachably_driven   the clock of StructuralRecordAxis.v, where
                                   every state is a starting state, fails R1
                                   even on reachable states: two starting
                                   states over the same base state with the
                                   same record disagree about the next one.
      SyncClockCore                the same clock started in sync, at
                                   (b, b, off).
      sync_clock_not_driven        R1 as stated, over every state, still
                                   rejects it, through states no run reaches;
      sync_clock_reachably_driven, sync_clock_reachable_latch
                                   on the states its runs reach it is driven,
                                   and it is exactly the latch of [b = 5].

    So what separates the clock from a latch is that the base state does
    not fix when it fires along the runs that happen; R1 over every state
    is a stronger demand that also rejects the synchronised clock. *)

From Coq Require Import Bool Arith.PeanoNat Lia.
From Kernel Require Import StructuralCore StructuralCoreCover.
From Kernel Require Import StructuralCoreAnyBase StructuralRecordAxis.

(** * The latch from R1 and R4 alone *)

Theorem record_axis_is_latch_r1_r4 : forall M B C,
  computation_driven M B C -> record_permanent M ->
  exists h, latch_factorization M B C h.
Proof.
  intros M B C [f Hf] Hperm. exists (fun b => f b false).
  intro m. unfold latch_next. simpl. f_equal.
  - apply base_step.
  - destruct (rc_cert M m) eqn:Hc.
    + rewrite (Hperm m Hc). reflexivity.
    + rewrite (Hf m), Hc. reflexivity.
Qed.

(** * Driven on the states runs reach *)

Definition reachably_driven (M : RCM) (B : BaseMachine) (C : BaseCover M B) : Prop :=
  exists f : b_state B -> bool -> bool,
    forall m0 n, rc_init M m0 ->
      rc_cert M (rc_next M (rc_run M n m0)) =
      f (base_state M B C (rc_run M n m0)) (rc_cert M (rc_run M n m0)).

Definition latch_on_reachable (M : RCM) (B : BaseMachine) (C : BaseCover M B)
    (h : b_state B -> bool) : Prop :=
  forall m0 n, rc_init M m0 ->
    (base_state M B C (rc_next M (rc_run M n m0)), rc_cert M (rc_next M (rc_run M n m0))) =
    latch_next B h (base_state M B C (rc_run M n m0), rc_cert M (rc_run M n m0)).

Lemma driven_reachably_driven : forall M B C,
  computation_driven M B C -> reachably_driven M B C.
Proof. intros M B C [f Hf]. exists f. intros m0 n _. apply Hf. Qed.

Theorem record_axis_is_latch_reachable : forall M B C,
  reachably_driven M B C -> record_permanent M ->
  exists h, latch_on_reachable M B C h.
Proof.
  intros M B C [f Hf] Hperm. exists (fun b => f b false).
  intros m0 n H0. unfold latch_next. simpl. f_equal.
  - apply base_step.
  - destruct (rc_cert M (rc_run M n m0)) eqn:Hc.
    + rewrite (Hperm _ Hc). reflexivity.
    + rewrite (Hf m0 n H0), Hc. reflexivity.
Qed.

(** * The clock, on reachable states *)

Theorem clock_not_reachably_driven :
  ~ reachably_driven ClockCore counter_base clock_cover.
Proof.
  intros [f Hf].
  pose proof (Hf (0, 5, false) 0 I) as Ha.
  pose proof (Hf (0, 0, false) 0 I) as Hb.
  simpl in Ha, Hb. rewrite <- Ha in Hb. discriminate.
Qed.

(** * The clock started in sync *)

Definition SyncClockCore : RCM := {|
  rc_state := nat * nat * bool;
  rc_next := fun x => let '(b, k, r) := x in (S b, S k, orb r (Nat.eqb k 5));
  rc_init := fun x => let '(b, k, r) := x in k = b /\ r = false;
  rc_cert := fun x => let '(_, _, r) := x in r;
  rc_mu := fun x => let '(b, _, _) := x in b;
  rc_halted := fun _ => False
|}.

Definition sync_clock_cover : BaseCover SyncClockCore counter_base.
Proof.
  refine (Build_BaseCover SyncClockCore counter_base
            (fun x => let '(b, _, _) := x in b) _ _ _ _).
  - intros; exact I.
  - intros b _. exists (b, b, false). split; [split; reflexivity | reflexivity].
  - intros [[b k] r]. reflexivity.
  - intros [[b k] r]. simpl. tauto.
Defined.

Lemma sync_clock_in_step : forall n b r,
  exists b' r', rc_run SyncClockCore n (b, b, r) = (b', b', r').
Proof.
  induction n as [| n IH]; intros b r.
  - exists b, r. reflexivity.
  - destruct (IH b r) as [b' [r' E]].
    change (rc_run SyncClockCore (S n) (b, b, r))
      with (rc_next SyncClockCore (rc_run SyncClockCore n (b, b, r))).
    rewrite E.
    exists (S b'), (r' || Nat.eqb b' 5). reflexivity.
Qed.

Theorem sync_clock_not_driven :
  ~ computation_driven SyncClockCore counter_base sync_clock_cover.
Proof.
  intros [f Hf].
  pose proof (Hf (0, 5, false)) as Ha.
  pose proof (Hf (0, 0, false)) as Hb.
  simpl in Ha, Hb. rewrite <- Ha in Hb. discriminate.
Qed.

Theorem sync_clock_reachably_driven :
  reachably_driven SyncClockCore counter_base sync_clock_cover.
Proof.
  exists (fun b r => orb r (Nat.eqb b 5)).
  intros [[b k] r] n [Hk Hr]. subst k r.
  destruct (sync_clock_in_step n b false) as [b' [r' E]].
  rewrite E. reflexivity.
Qed.

Theorem sync_clock_reachable_latch :
  latch_on_reachable SyncClockCore counter_base sync_clock_cover
    (fun b => Nat.eqb b 5).
Proof.
  intros [[b k] r] n [Hk Hr]. subst k r.
  destruct (sync_clock_in_step n b false) as [b' [r' E]].
  rewrite E. reflexivity.
Qed.

Theorem sync_clock_record_permanent : record_permanent SyncClockCore.
Proof. intros [[b k] r] H. simpl in *. rewrite H. reflexivity. Qed.

Print Assumptions record_axis_is_latch_r1_r4.
Print Assumptions record_axis_is_latch_reachable.
Print Assumptions clock_not_reachably_driven.
Print Assumptions sync_clock_not_driven.
Print Assumptions sync_clock_reachably_driven.
Print Assumptions sync_clock_reachable_latch.
Print Assumptions sync_clock_record_permanent.
