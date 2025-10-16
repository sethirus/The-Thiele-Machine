From Coq Require Import Arith.
Goal forall a b, 0 < 2 -> a <= b -> a * 2 <= b * 2.
Proof.
  intros a b H2 Hab.
  apply (Nat.mul_le_mono_pos_r a b 2) in Hab; [ | apply H2].
  exact Hab.
Qed.
