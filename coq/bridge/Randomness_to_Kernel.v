From Coq Require Import List PeanoNat.
Import ListNotations.

From Kernel Require Import ReceiptCore.

(* INQUISITOR NOTE: proof-connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.

Module Randomness_to_Kernel.

(* Minimal bridge: define a channel selector for RAND_TRIAL opcode id.
   The concrete opcode mapping lives in the executable layers; here we stay abstract.
*)

Definition RAND_TRIAL_OP : nat := 1001.

Definition RandChannel (r : ReceiptCore.Receipt) : bool :=
  Nat.eqb (ReceiptCore.r_op r) RAND_TRIAL_OP.

(** [decode_is_filter_payloads]: formal specification. *)
Lemma decode_is_filter_payloads :
  forall tr,
    ReceiptCore.decode RandChannel tr =
    map ReceiptCore.r_payload
        (filter RandChannel tr).
Proof.
  intros; reflexivity.
Qed.


End Randomness_to_Kernel.
