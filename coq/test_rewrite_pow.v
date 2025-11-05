From Coq Require Import Arith Lia PeanoNat.

Definition B := 2.

Lemma test_rewrite_pow : forall n, Nat.pow B (S n) = B * Nat.pow B n.
Proof.
  intros n.
  cbv [Nat.pow].
  reflexivity.
Qed.
