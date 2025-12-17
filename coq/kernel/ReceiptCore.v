From Coq Require Import List.
Import ListNotations.

Module ReceiptCore.

(* A minimal, generic receipt “channel” layer.

   This is intentionally abstract: the kernel model decides how receipts are emitted.
   Verifiers/proofs only talk about what can be decoded from a finite trace.
*)

Record Receipt := {
  r_op : nat;
  r_payload : list nat;
}.

Definition Trace := list Receipt.

(* A receipt channel is a boolean predicate that selects receipts.

  Using bool avoids any dependency on classical axioms for decoding.
*)
Definition ReceiptChannel := Receipt -> bool.

(* Generic decoder: extracts the payload stream for receipts that match the channel. *)
Definition decode (ch : ReceiptChannel) (tr : Trace) : list (list nat) :=
  map r_payload (filter ch tr).

(* Decoder predicate: the decoded stream equals some intended stream. *)
Definition decodes_to (ch : ReceiptChannel) (tr : Trace) (xs : list (list nat)) : Prop :=
  decode ch tr = xs.

Lemma decodes_to_refl :
  forall ch tr, decodes_to ch tr (decode ch tr).
Proof.
  intros; unfold decodes_to; reflexivity.
Qed.

End ReceiptCore.
