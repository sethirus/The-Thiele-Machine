From Coq Require Import List PeanoNat.
Import ListNotations.

From Kernel Require Import ReceiptCore.

Module Causal_to_Kernel.

Definition CAUSAL_QUERY_OP : nat := 1301.

Definition CausalChannel (r : ReceiptCore.Receipt) : bool :=
  Nat.eqb (ReceiptCore.r_op r) CAUSAL_QUERY_OP.

Lemma decodes_to_self :
  forall tr,
    ReceiptCore.decodes_to CausalChannel tr (ReceiptCore.decode CausalChannel tr).
Proof.
  intros; apply ReceiptCore.decodes_to_refl.
Qed.

End Causal_to_Kernel.
