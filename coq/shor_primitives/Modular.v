(** * Modular arithmetic primitives for Project Sovereign

    This file provides a minimal collection of modular arithmetic utilities
    formalised over natural numbers.  They serve as the reusable bedrock for
    the later Euclidean and period-finding developments.  The lemmas are kept
    intentionally small but explicit so that future proofs can cite them without
    depending on opaque automation.
 *)

From Coq Require Import Arith.

(** We re-export the most common facts from the [Nat] namespace so clients can
    depend on a single module. *)
Export Nat.

Section ModularArithmetic.
  Variable n : nat.

  Definition mod_add (a b : nat) : nat := (a + b) mod n.
  Definition mod_mul (a b : nat) : nat := (a * b) mod n.
  Definition mod_pow (a k : nat) : nat := Nat.pow a k mod n.

  Lemma mod_add_comm : forall a b, mod_add a b = mod_add b a.
  Proof.
    intros a b; unfold mod_add; now rewrite Nat.add_comm.
  Qed.

  Lemma mod_add_lift : forall a b, (a + (b mod n)) mod n = (a + b) mod n.
  Proof.
    intros a b; unfold mod_add; apply Nat.Div0.add_mod_idemp_r.
  Qed.

  Lemma mod_add_assoc : forall a b c,
      mod_add a (mod_add b c) = mod_add (mod_add a b) c.
  Proof.
    intros a b c; unfold mod_add.
    rewrite mod_add_lift.
    rewrite Nat.add_assoc.
    rewrite <- (Nat.Div0.add_mod_idemp_l (a + b) c n).
    reflexivity.
  Qed.

  Lemma mod_mul_comm : forall a b, mod_mul a b = mod_mul b a.
  Proof.
    intros a b; unfold mod_mul; now rewrite Nat.mul_comm.
  Qed.

  Lemma mod_mul_lift : forall a b, (a * (b mod n)) mod n = (a * b) mod n.
  Proof.
    intros a b; unfold mod_mul; apply Nat.Div0.mul_mod_idemp_r.
  Qed.

  Lemma mod_mul_assoc : forall a b c,
      mod_mul a (mod_mul b c) = mod_mul (mod_mul a b) c.
  Proof.
    intros a b c; unfold mod_mul.
    rewrite mod_mul_lift.
    rewrite Nat.mul_assoc.
    rewrite <- (Nat.Div0.mul_mod_idemp_l (a * b) c n).
    reflexivity.
  Qed.

  Lemma mod_pow_succ : forall a k,
      mod_pow a (S k) = mod_mul (mod_pow a k) a.
  Proof.
    intros a k; unfold mod_pow, mod_mul.
    simpl Nat.pow.
    rewrite Nat.mul_comm.
    rewrite <- (Nat.Div0.mul_mod_idemp_l (Nat.pow a k) a n).
    reflexivity.
  Qed.

  Lemma mod_pow_add : forall a k l,
      mod_pow a (k + l) = mod_mul (mod_pow a k) (mod_pow a l).
  Proof.
    intros a k l; unfold mod_pow, mod_mul.
    rewrite Nat.pow_add_r.
    rewrite (Nat.Div0.mul_mod (Nat.pow a k) (Nat.pow a l) n).
    reflexivity.
  Qed.
End ModularArithmetic.

