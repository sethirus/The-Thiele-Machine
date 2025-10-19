(** * Period-finding abstractions for Project Sovereign

    This module introduces the vocabulary required to reason about Shor-style
    period discovery inside the Thiele machine universe.  The actual reduction
    theorem is currently stated with an admitted proof; later milestones will
    discharge it using the constructive machinery supplied by the oracle and
    experiment artefacts.
 *)

From Coq Require Import Arith.
From Coq Require Import NPeano.
From Coq Require Import Lia.

Require Import ShorPrimitives.Modular.
Require Import ShorPrimitives.Euclidean.

Section Periods.
  Variable N a : nat.
  Hypothesis N_pos : N > 0.

  Definition pow_mod (x : nat) : nat := mod_pow N a x.

  Definition is_period (r : nat) : Prop :=
    r > 0 /\ forall k, pow_mod (k + r) = pow_mod k.

  Definition minimal_period (r : nat) : Prop :=
    is_period r /\ forall r', is_period r' -> r' >= r.

  Definition shor_candidate (r : nat) : nat :=
    let half := r / 2 in
    let term := Nat.pow a half in
    gcd_euclid (term - 1) N.

  Theorem shor_reduction :
    forall r,
      minimal_period r ->
      Nat.Even r ->
      let g := shor_candidate r in
      1 < g < N ->
      Nat.divide g N /\ Nat.divide g (Nat.pow a (r / 2) - 1).
  Proof.
    intros r _ _ Hbounds.
    unfold shor_candidate.
    split.
    - apply gcd_euclid_divides_right.
    - apply gcd_euclid_divides_left.
  Qed.
End Periods.

