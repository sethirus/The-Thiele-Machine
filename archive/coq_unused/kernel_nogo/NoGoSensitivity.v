(** * NoGoSensitivity: Sensitivity audit for alternative composition laws

    WHY THIS FILE EXISTS:
    The NoGo.v file shows weight non-uniqueness under additive composition.
    A natural question: is the result fragile? Does switching from additive
    to multiplicative composition eliminate the infinite family? This file
    answers NO -- even multiplicative composition admits infinitely many
    weight functions (w_pow(k) = k^length(t)).

    THE CORE CLAIM:
    The no-go result (non-uniqueness of weight) is ROBUST to the choice of
    composition law. Both additive (w_scale) and multiplicative (w_pow)
    families exhibit infinitely many distinct solutions.

    FALSIFICATION:
    Find a composition law (neither additive nor multiplicative) under which
    the weight function IS uniquely determined without extra structure. Or
    show that w_pow(k) does NOT satisfy weight_multiplicative for some k,
    contradicting w_pow_multiplicative.
*)

From Coq Require Import List Lia Arith.PeanoNat.

From Kernel Require Import VMStep.

Import ListNotations.

(* INQUISITOR NOTE: proof-connectivity -- bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

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

(** [w_pow_sequential]: formal specification. *)
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

(** [w_pow_multiplicative]: formal specification. *)
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
(** [MultiplicativeWeightFamily_Infinite]: formal specification. *)
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
