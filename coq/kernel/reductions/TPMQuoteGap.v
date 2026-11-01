(** TPMQuoteGap: a scoped quote-view example for the window theorem.

    [decoding_requires_fiber_constancy] (ObservationPolicy.v) says a decider
    that sees only a view cannot decide a claim that differs between two
    states with the same view. This file uses a deliberately scoped abstraction of TPM quote fields,
    guided by the TPM 2.0 Library specification, Version 185: Part 3
    (Commands), sections 18.4 (TPM2_Quote) and 22.2 (TPM2_PCR_Extend),
    and Part 2 (Structures), sections 10.11.4 and 10.11.12:
    https://trustedcomputinggroup.org/wp-content/uploads/Trusted-Platform-Module-2.0-Library-Part-3-Commands_Version-185_pub.pdf
    https://trustedcomputinggroup.org/wp-content/uploads/Trusted-Platform-Module-2.0-Library-Part-2-Structures_Version-185_pub.pdf

    Specification facts and explicit model choices.

    - TPM2_PCR_Extend updates selected PCR values by hashing the old value
      concatenated with an input digest. The model chooses one PCR/bank, a
      natural-number hash [H], and seed 0 for one abstract epoch. Seed 0 is a
      model choice, not a claim that every TPM PCR has that initial value.
      Reset, restart, locality, banks, and the update counter are omitted.
    - TPM2_Quote accepts caller-supplied [qualifyingData], returns quoted
      [TPMS_ATTEST] data whose [extraData] reflects that input, and includes
      a PCR selection and digest in the quote attestation. This model chooses
      to interpret [qualifyingData] as a verifier nonce and retains only the
      selected-PCR digest and that nonce. The selection and other attestation
      context are fixed or omitted. The command's signature output and its
      verification are not represented; authenticity is an external premise.
    - [runtime_is_measured_software] is an external semantic label introduced
      for this example. It is not a TPM quote field or a fact computed by the
      TPM specification.

    Interpretation choices, recorded. One modeled PCR stands for the selected
    PCR input. PCR selection, signer identity, clock information, firmware
    version, and the attestation header are fixed alike or outside the record.
    When the record is described as authentic, valid-key and signature checks
    are assumed outside the formalization. The external runtime label is one
    Boolean. The nonce is fixed by the verifier in this interpretation.
    [digest] abstracts the PCR-composite digest; no injectivity of either hash
    is assumed.

    What the abstraction proves. A function that reads only this two-field
    quote cannot decide the external runtime label
    ([quote_cannot_attest_unmeasured_state]): two platforms with the same
    modeled log and different labels produce the same modeled quote. It can
    decide any Boolean claim supplied as a function of the retained digest
    ([quote_decides_measured_claims]).

    A TPM quote reports selected PCR state; it does not report arbitrary
    runtime state that was never incorporated into those PCRs. The window
    theorem recovers that projection fact from this abstraction. It is not a theorem
    about every TPM deployment or runtime measurement design. *)

(* SCOPE NOTE: standalone proof scope. A scoped abstraction of TPM quote
   fields read through the window theorem; no machine is fixed. *)

From Coq Require Import List Arith.PeanoNat Bool.
Import ListNotations.
From Kernel Require Import ObservationPolicy.

Section TPM.

(** The hash is abstract; nothing about it is assumed. *)
Variable H : nat -> nat -> nat.
Variable digest : nat -> nat.

Definition pcr_extend (pcr digest : nat) : nat := H pcr digest.

(** The modeled PCR after folding the log from the chosen seed zero. *)
Definition pcr_of_log (log : list nat) : nat := fold_left pcr_extend log 0.

Record Platform : Type := {
  measured_log : list nat;
  runtime_is_measured_software : bool
}.

Record Quote : Type := {
  quote_pcr_digest : nat;
  quote_nonce : nat
}.

Definition quote (nonce : nat) (p : Platform) : Quote :=
  {| quote_pcr_digest := digest (pcr_of_log (measured_log p)); quote_nonce := nonce |}.

(** Two model platforms with the same log and different external runtime
    labels produce the same two-field quote for every nonce. *)
Lemma quote_collision :
  forall nonce log,
    quote nonce {| measured_log := log; runtime_is_measured_software := true |} =
    quote nonce {| measured_log := log; runtime_is_measured_software := false |}.
Proof. reflexivity. Qed.

(** No function of only the modeled quote decides the external runtime label.
    This is [decoding_requires_fiber_constancy] applied to the projection; it
    does not model signature validation or claim that a TPM promised this
    runtime property. *)
Theorem quote_cannot_attest_unmeasured_state :
  forall nonce,
    ~ exists decide : Quote -> bool,
        forall p, decide (quote nonce p) = runtime_is_measured_software p.
Proof.
  intros nonce Hdec.
  pose proof (decoding_requires_fiber_constancy (quote nonce)
                runtime_is_measured_software Hdec) as Hfib.
  specialize (Hfib {| measured_log := []; runtime_is_measured_software := true |}
                   {| measured_log := []; runtime_is_measured_software := false |}
                   (quote_collision nonce [])).
  discriminate.
Qed.

(** A Boolean query on the retained PCR digest factors through the quote. The query
    function is supplied; this theorem does not decide arbitrary predicates
    on natural numbers or reconstruct the measurement log. *)
Theorem quote_decides_measured_claims :
  forall nonce (claim : nat -> bool),
    exists decide : Quote -> bool,
      forall p, decide (quote nonce p) = claim (digest (pcr_of_log (measured_log p))).
Proof.
  intros nonce claim. exists (fun q => claim (quote_pcr_digest q)). reflexivity.
Qed.

End TPM.
