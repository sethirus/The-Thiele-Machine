From Coq Require Import List Lia Arith.PeanoNat.

From Kernel Require Import VMStep.

Import ListNotations.

(** * Sensitivity audit: alternative composition laws for weights

    The goal is to test whether the no-go result (non-uniqueness of a
    would-be probability weight) is fragile to small definition changes.

    Here we show that even if we replace additive composition with
    multiplicative composition, we still get an infinite family of weights.
*)

Definition WeightMul := list vm_instruction -> nat.

Definition weight_multiplicative (w : WeightMul) : Prop :=
  w [] = 1 /\
  forall t1 t2, w (t1 ++ t2) = w t1 * w t2.

Definition w_pow (k : nat) : WeightMul :=
  fun t => Nat.pow k (length t).

(** HELPER: Base case property *)
(** HELPER: Base case property *)
Lemma w_pow_empty : forall k, w_pow k [] = 1.
Proof.
  intro k. unfold w_pow. simpl. reflexivity.
Qed.

Lemma w_pow_sequential : forall k t1 t2,
  w_pow k (t1 ++ t2) = w_pow k t1 * w_pow k t2.
Proof.
  intros k t1 t2.
  unfold w_pow.
  rewrite app_length.
  (* Nat.pow_add_r: a^(n+m) = a^n * a^m *)
  rewrite Nat.pow_add_r.
  lia.
Qed.

Lemma w_pow_multiplicative : forall k, weight_multiplicative (w_pow k).
Proof.
  intro k. split.
  - apply w_pow_empty.
  - intros t1 t2. apply w_pow_sequential.
Qed.

(** DEFINITIONAL WITNESS: [w_pow] is the witness, but the proof verifies
    [weight_multiplicative] for all k (via [w_pow_empty], [w_pow_sequential]),
    then constructs a separating trace [instr_halt 0] and derives k1 <> k2
    from exponentiation distinctness via [lia]. *)
(* DEFINITIONAL *)
Theorem MultiplicativeWeightFamily_Infinite :
  exists w : nat -> WeightMul,
    (forall k, weight_multiplicative (w k)) /\
    (forall k1 k2, k1 <> k2 -> exists t, w k1 t <> w k2 t).
Proof.
  exists w_pow.
  split.
  - intro k. apply w_pow_multiplicative.
  - intros k1 k2 Hneq.
    exists [instr_halt 0].
    unfold w_pow. simpl.
    (* k1^1 <> k2^1 *)
    intro Heq. apply Hneq.
    lia.
Qed.
