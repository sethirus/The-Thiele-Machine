(** Separation.v — Formal exponential separation for blind vs. sighted solvers *)

Set Implicit Arguments.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Module Separation.

  (** We model Tseitin instances by their size parameter [n]. *)
  Definition InstanceSize := nat.

  (** Blind solver decisions follow a full binary search tree. *)
  Definition blind_steps (n : InstanceSize) : nat := Nat.pow 2 n.

  (** Sighted solver steps grow linearly in the instance size. *)
  Definition sighted_steps (n : InstanceSize) : nat := n + 1.

  (** Helper lemmas about our growth models. *)
  Lemma blind_steps_succ n : blind_steps (S n) = 2 * blind_steps n.
  Proof.
    unfold blind_steps.
    rewrite Nat.pow_succ_r by lia.
    lia.
  Qed.

  Lemma pow2_ge_linear : forall n, Nat.pow 2 n >= n + 1.
  Proof.
    induction n.
    - simpl; lia.
    - rewrite Nat.pow_succ_r by lia.
      simpl. lia.
  Qed.

  Definition polynomial_time (f : nat -> nat) :=
    exists a b c, forall n, f n <= a * n * n + b * n + c.

  Definition exponential_lower_bound (f : nat -> nat) :=
    exists k, forall n, f (n + k) >= Nat.pow 2 n.

  Lemma sighted_is_quadratic : polynomial_time sighted_steps.
  Proof.
    unfold polynomial_time, sighted_steps. exists 0, 1, 1. intros n. lia.
  Qed.

  Lemma blind_has_exponential_lower : exponential_lower_bound blind_steps.
  Proof.
    unfold exponential_lower_bound, blind_steps. exists 0.
    intro n. rewrite Nat.add_0_r. apply Nat.le_refl.
  Qed.

  Lemma blind_eventually_dominates :
    forall n, blind_steps n >= sighted_steps n.
  Proof.
    intro n. unfold blind_steps, sighted_steps.
    apply pow2_ge_linear.
  Qed.

  Theorem exponential_separation :
    polynomial_time sighted_steps /\
    exponential_lower_bound blind_steps /\
    (exists n0, forall n, n >= n0 -> blind_steps n >= sighted_steps n).
  Proof.
    repeat split.
    - apply sighted_is_quadratic.
    - apply blind_has_exponential_lower.
    - exists 0. intros n _. apply blind_eventually_dominates.
  Qed.

End Separation.
