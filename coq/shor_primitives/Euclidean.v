(** * Euclidean algorithm utilities for Project Sovereign

    The Thiele-machine version of Shor's algorithm relies on a trustworthy
    implementation of the Euclidean algorithm.  This module provides a
    structurally recursive definition over natural numbers together with a
    standard correctness proof that relates it to Coq's reference [Nat.gcd].
 *)

From Coq Require Import Arith.
From Coq Require Import NPeano.
From Coq Require Import PeanoNat.
From Coq Require Import Wf_nat.
From Coq Require Import Lia.

(** We reuse the modular lemmas for later developments. *)
Require Import ShorPrimitives.Modular.

Fixpoint gcd_euclid (a b : nat) : nat :=
  match a with
  | 0 => b
  | S a' => gcd_euclid (b mod S a') (S a')
  end.

Theorem gcd_euclid_correct :
  forall a b, gcd_euclid a b = Nat.gcd a b.
Proof.
  apply (well_founded_induction_type Wf_nat.lt_wf (fun a => forall b, gcd_euclid a b = Nat.gcd a b)).
  intros a IH b.
  destruct a as [|a'].
  - reflexivity.
  - simpl.
    assert (Hlt : b mod S a' < S a') by (apply Nat.mod_upper_bound; lia).
    specialize (IH _ Hlt (S a')).
    exact IH.
Qed.

Corollary gcd_euclid_divides_left :
  forall a b, Nat.divide (gcd_euclid a b) a.
Proof.
  intros a b; rewrite gcd_euclid_correct; apply Nat.gcd_divide_l.
Qed.

Corollary gcd_euclid_divides_right :
  forall a b, Nat.divide (gcd_euclid a b) b.
Proof.
  intros a b; rewrite gcd_euclid_correct; apply Nat.gcd_divide_r.
Qed.

