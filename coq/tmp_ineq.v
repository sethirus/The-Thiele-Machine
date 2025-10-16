From Coq Require Import Arith Lia.

Lemma test_ineq : forall a b x base, 1 <= base -> a <= b - 1 -> x < base -> a*base + x <= base*b - 1.
Proof.
  intros a b x base Hbase Ha Hx.
  lia.
Qed.
