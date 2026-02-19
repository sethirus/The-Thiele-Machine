From Coq Require Import List PeanoNat.
Import ListNotations.

From Kernel Require Import ReceiptCore.

Module Entropy_to_Kernel.

Definition COARSE_GRAIN_OP : nat := 1201.

Definition EntropyChannel (r : ReceiptCore.Receipt) : bool :=
  Nat.eqb (ReceiptCore.r_op r) COARSE_GRAIN_OP.

(* INQUISITOR NOTE: Arithmetic helper proving basic property of defined constant. *)
(** [decodes_to_self]: formal specification. *)
Lemma decodes_to_self :
  forall tr,
    ReceiptCore.decodes_to EntropyChannel tr (ReceiptCore.decode EntropyChannel tr).
Proof.
  intros; apply ReceiptCore.decodes_to_refl.
Qed.

End Entropy_to_Kernel.
