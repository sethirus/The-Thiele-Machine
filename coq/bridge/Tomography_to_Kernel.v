From Coq Require Import List PeanoNat.
Import ListNotations.

From Kernel Require Import ReceiptCore.

Module Tomography_to_Kernel.

Definition MEAS_TRIAL_OP : nat := 1101.

Definition TomoChannel (r : ReceiptCore.Receipt) : bool :=
  Nat.eqb (ReceiptCore.r_op r) MEAS_TRIAL_OP.

(** [decodes_to_self]: formal specification. *)
Lemma decodes_to_self :
  forall tr,
    ReceiptCore.decodes_to TomoChannel tr (ReceiptCore.decode TomoChannel tr).
Proof.
  intros; apply ReceiptCore.decodes_to_refl.
Qed.

End Tomography_to_Kernel.
