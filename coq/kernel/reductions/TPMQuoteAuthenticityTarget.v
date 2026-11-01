(** SCOPE NOTE: standalone proof scope. This signature-interface countermodel
    is independent of the kernel and proves no TPM-to-machine correspondence.

    Authenticity boundary for the TPM quote abstraction. *)

From Coq Require Import Bool Arith.PeanoNat.

Record SignatureScheme := {
  PublicKey : Type;
  SecretKey : Type;
  Signature : Type;
  sign : SecretKey -> nat -> Signature;
  verify : PublicKey -> nat -> Signature -> bool
}.

Definition quote_authenticity (S : SignatureScheme) : Prop :=
  forall (pk : PublicKey S) message (sig : Signature S),
    verify S pk message sig = true ->
    exists sk : SecretKey S, sig = sign S sk message.

Definition unconditional_quote_authenticity : Prop :=
  forall S : SignatureScheme, quote_authenticity S.

(** Exact counter-target: the interface alone admits a verifier that accepts
    a signature not produced by the only signing key. *)
Definition interface_authenticity_refuted : Prop :=
  ~ unconditional_quote_authenticity.
