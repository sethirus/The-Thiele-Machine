(** Proved outcomes for the finite-weight probabilistic targets. *)

(* SCOPE NOTE: standalone proof scope. These finite-weight counterexamples
   are independent of any machine's execution semantics. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import ProbabilisticRecordCore.

Definition fair_branch_kernel : weighted_kernel := fun b =>
  if b then [(1, true)] else [(1, false); (1, true)].

Definition biased_branch_kernel : weighted_kernel := fun b =>
  if b then [(1, true)] else [(1, false); (2, true)].

Definition branch_write_charge : branch_charge := fun before after =>
  if andb (negb before) after then 1 else 0.

Lemma fair_branch_honest :
  honest_probabilistic_record fair_branch_kernel branch_write_charge.
Proof.
  repeat split.
  - intros [] w b' Hin; simpl in Hin;
      repeat (destruct Hin as [Hin | Hin]; [inversion Hin; subst; simpl; lia |]);
      contradiction.
  - intros []; discriminate.
  - intros w b' Hin. simpl in Hin. destruct Hin as [Hin | []].
    inversion Hin. reflexivity.
  - intros w Hin. unfold branch_write_charge. simpl. lia.
Qed.

Lemma biased_branch_honest :
  honest_probabilistic_record biased_branch_kernel branch_write_charge.
Proof.
  repeat split.
  - intros [] w b' Hin; simpl in Hin;
      repeat (destruct Hin as [Hin | Hin]; [inversion Hin; subst; simpl; lia |]);
      contradiction.
  - intros []; discriminate.
  - intros w b' Hin. simpl in Hin. destruct Hin as [Hin | []].
    inversion Hin. reflexivity.
  - intros w Hin. unfold branch_write_charge. simpl. lia.
Qed.

Theorem deterministic_latch_handles_branching_refuted :
  ~ deterministic_latch_handles_branching.
Proof.
  intro Hall.
  destruct (Hall fair_branch_kernel branch_write_charge fair_branch_honest)
    as [h Hh].
  pose proof (Hh false 1 false (or_introl eq_refl)) as Hfalse.
  pose proof (Hh false 1 true (or_intror (or_introl eq_refl))) as Htrue.
  simpl in Hfalse, Htrue. congruence.
Qed.

Lemma branch_kernels_same_support : forall b b',
  kernel_support fair_branch_kernel b b' <->
  kernel_support biased_branch_kernel b b'.
Proof.
  intros [] []; unfold kernel_support, fair_branch_kernel, biased_branch_kernel;
    simpl; split; intros [w Hin].
  - exists 1. left. reflexivity.
  - exists 1. left. reflexivity.
  - destruct Hin as [Hin | []]. discriminate.
  - destruct Hin as [Hin | []]. discriminate.
  - exists 2. right. left. reflexivity.
  - exists 1. right. left. reflexivity.
  - exists 1. left. reflexivity.
  - exists 1. left. reflexivity.
Qed.

Theorem schedule_determines_probabilities_refuted :
  ~ schedule_determines_probabilities.
Proof.
  intro Hall.
  specialize (Hall fair_branch_kernel biased_branch_kernel
    branch_write_charge branch_write_charge fair_branch_honest
    biased_branch_honest).
  assert (Hschedule : same_probabilistic_schedule fair_branch_kernel
    biased_branch_kernel branch_write_charge branch_write_charge).
  { split; [exact branch_kernels_same_support | reflexivity]. }
  destruct (Hall Hschedule) as [Hkernel _].
  specialize (Hkernel false). discriminate.
Qed.

Theorem probability_preserving_equivalence_reflexive_holds :
  probability_preserving_equivalence_reflexive.
Proof. intros k c. split; reflexivity. Qed.

Print Assumptions deterministic_latch_handles_branching_refuted.
Print Assumptions schedule_determines_probabilities_refuted.
Print Assumptions probability_preserving_equivalence_reflexive_holds.
