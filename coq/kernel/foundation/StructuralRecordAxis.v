(** StructuralRecordAxis: the record axis over any base is a latch.

    Every honest extension of a base factors as a latch of one base event
    ([record_axis_is_latch_holds]): the base state and the record evolve exactly
    as "switch on at the first base state where h holds, never switch off."
    Two permanent records factor as two latches, each of whose events may
    read the other record ([record_pair_is_two_latches_holds]).

    Both conditions of the entry do work.

    - Permanence. A record driven by the computation that can switch back
      off is not a latch of any event ([toggle_not_latch]).
    - Being driven by the computation. A record switched on by a hidden
      clock is permanent, and it is not driven by the computation
      ([clock_record_not_driven]). *)

From Coq Require Import Bool Arith.PeanoNat Lia.
From Kernel Require Import StructuralCore StructuralCoreCover.
From Kernel Require Import StructuralCoreAnyBase.

(** * One record *)

Theorem record_axis_is_latch_holds : record_axis_is_latch.
Proof.
  intros M B C [[f Hf] [_ [_ [Hperm _]]]].
  exists (fun b => f b false).
  intro m. unfold latch_next. simpl.
  rewrite (base_step M B C m).
  destruct (rc_cert M m) eqn:Hc.
  - rewrite (Hperm m Hc). reflexivity.
  - rewrite Hf, Hc. reflexivity.
Qed.

(** * Two records *)

Theorem record_pair_is_two_latches_holds : record_pair_is_two_latches.
Proof.
  intros M B C c1 c2 [[f Hf] [_ [_ [Hp1 Hp2]]]].
  exists (fun b r2 => fst (f b false r2)), (fun b r1 => snd (f b r1 false)).
  intro m. pose proof (Hf m) as Hm.
  split.
  - destruct (c1 m) eqn:H1.
    + rewrite (Hp1 m H1). reflexivity.
    + simpl. rewrite <- Hm. reflexivity.
  - destruct (c2 m) eqn:H2.
    + rewrite (Hp2 m H2). reflexivity.
    + simpl. rewrite <- Hm. reflexivity.
Qed.

(** * Permanence does work *)

(** A counter as the base. *)
Definition counter_base : BaseMachine := {|
  b_state := nat;
  b_next := S;
  b_init := fun _ => True;
  b_halted := fun _ => False
|}.

(** A record that flips at every step. *)
Definition ToggleCore : RCM := {|
  rc_state := nat * bool;
  rc_next := fun x => (S (fst x), negb (snd x));
  rc_init := fun _ => True;
  rc_cert := snd;
  rc_mu := fst;
  rc_halted := fun _ => False
|}.

Definition toggle_cover : BaseCover ToggleCore counter_base.
Proof.
  refine (Build_BaseCover ToggleCore counter_base fst _ _ _ _).
  - intros; exact I.
  - intros b _. exists (b, false). split; [exact I | reflexivity].
  - intros m. reflexivity.
  - intros m. simpl. tauto.
Defined.

Theorem toggle_computation_driven :
  computation_driven ToggleCore counter_base toggle_cover.
Proof. exists (fun _ r => negb r). intro m. reflexivity. Qed.

Theorem toggle_not_permanent : ~ record_permanent ToggleCore.
Proof. intro H. specialize (H (0, true) eq_refl). discriminate. Qed.

Theorem toggle_not_latch :
  ~ exists h, latch_factorization ToggleCore counter_base toggle_cover h.
Proof.
  intros [h Hh]. specialize (Hh (0, true)).
  unfold latch_next in Hh. simpl in Hh. inversion Hh.
Qed.

(** * Being driven by the computation does work *)

(** A record switched on by a hidden clock at its fifth tick, whatever the
    base computes. The clock is state the base does not see. *)
Definition ClockCore : RCM := {|
  rc_state := nat * nat * bool;
  rc_next := fun x => let '(b, k, r) := x in (S b, S k, orb r (Nat.eqb k 5));
  rc_init := fun _ => True;
  rc_cert := fun x => let '(_, _, r) := x in r;
  rc_mu := fun x => let '(b, _, _) := x in b;
  rc_halted := fun _ => False
|}.

Definition clock_cover : BaseCover ClockCore counter_base.
Proof.
  refine (Build_BaseCover ClockCore counter_base
            (fun x => let '(b, _, _) := x in b) _ _ _ _).
  - intros; exact I.
  - intros b _. exists (b, 0, false). split; [exact I | reflexivity].
  - intros [[b k] r]. reflexivity.
  - intros [[b k] r]. simpl. tauto.
Defined.

Theorem clock_record_permanent : record_permanent ClockCore.
Proof. intros [[b k] r] H. simpl in *. rewrite H. reflexivity. Qed.

Theorem clock_record_not_driven :
  ~ computation_driven ClockCore counter_base clock_cover.
Proof.
  intros [f Hf].
  pose proof (Hf (0, 5, false)) as Ha.
  pose proof (Hf (0, 0, false)) as Hb.
  simpl in Ha, Hb. rewrite <- Ha in Hb. discriminate.
Qed.

Print Assumptions record_axis_is_latch_holds.
Print Assumptions record_pair_is_two_latches_holds.
Print Assumptions toggle_not_latch.
Print Assumptions clock_record_not_driven.
