(** SCOPE NOTE: standalone proof scope. The countermodel concerns only the
    signature interface and imports no machine semantics.

    A closed countermodel showing why TPM quote authenticity needs a
    cryptographic trust premise, not merely a sign/verify interface. *)

From Coq Require Import Bool Arith.PeanoNat.
From Kernel Require Import TPMQuoteAuthenticityTarget.

Definition degenerate_signature_scheme : SignatureScheme :=
  {| PublicKey := unit;
     SecretKey := unit;
     Signature := bool;
     sign := fun _ _ => false;
     verify := fun _ _ _ => true |}.

Lemma degenerate_accepts_forgery :
  verify degenerate_signature_scheme tt 0 true = true /\
  ~ exists sk : SecretKey degenerate_signature_scheme,
      true = sign degenerate_signature_scheme sk 0.
Proof.
  split; [reflexivity |].
  intros [sk H]. destruct sk. discriminate.
Qed.

Theorem tpm_interface_authenticity_refuted : interface_authenticity_refuted.
Proof.
  unfold interface_authenticity_refuted, unconditional_quote_authenticity.
  intro Hall. specialize (Hall degenerate_signature_scheme).
  unfold quote_authenticity in Hall.
  specialize (Hall tt 0 true eq_refl).
  destruct degenerate_accepts_forgery as [_ Hforge]. exact (Hforge Hall).
Qed.

Print Assumptions degenerate_accepts_forgery.
Print Assumptions tpm_interface_authenticity_refuted.
