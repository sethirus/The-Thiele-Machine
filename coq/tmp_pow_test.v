From Coq Require Import Arith Lia PeanoNat.

Lemma test_pow_succ : forall a n, Nat.pow a (S n) = a * Nat.pow a n.
Proof.
  intros a n.
  rewrite <- Nat.pow_succ_r.
  reflexivity.
Qed.
