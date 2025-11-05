From Coq Require Import Lia.
Lemma test_lia : forall n:nat, n <= n * 2.
Proof.
  intros n.
  lia.
Qed.
