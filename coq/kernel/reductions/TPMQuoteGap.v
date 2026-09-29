(** TPMQuoteGap: a scoped quote-view example for the verifier corollary.

    The kernel's verifier corollary says a verifier that sees only a view
    cannot decide a claim that differs between two states with the same
    view. This file uses a deliberately scoped abstraction of TPM quote fields,
    guided by the TPM 2.0 Library specification, Version 185, published
    12 March 2026: Part 3
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
    runtime state that was never incorporated into those PCRs. The corollary
    recovers that projection fact from this abstraction. It is not a theorem
    about every TPM deployment or runtime measurement design. *)

From Coq Require Import List Arith.PeanoNat Bool.
Import ListNotations.
From Kernel Require Import ObservationPolicy.
From Kernel Require Import VMState.
Require Import NecessityOfMuLedger VerifierModel VerifierExhaustiveness.

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

(** Encode every field of the modeled quote in a classical transcript.
    This is a lossless representation adapter, not a TPM execution trace. *)
Definition quote_projection (nonce : nat) (p : Platform) : BareTranscript :=
  let q := quote nonce p in
  [mk_strict_classical [quote_pcr_digest q; quote_nonce q] [] 0].

Lemma quote_projection_faithful : forall nonce p q,
  quote_projection nonce p = quote_projection nonce q <->
  quote nonce p = quote nonce q.
Proof.
  intros nonce p q. split.
  - unfold quote_projection, quote. intro Heq.
    injection Heq as Hhash. rewrite Hhash. reflexivity.
  - intro Heq. unfold quote_projection. rewrite Heq. reflexivity.
Qed.

(** The two VM witnesses label the two truth values of the runtime claim.
    No equality between TPM energy, execution cost, and vm_mu is asserted. *)
Definition runtime_explains (s : VMState) (p : Platform) : Prop :=
  (runtime_is_measured_software p = true /\ s = po1_state_A) \/
  (runtime_is_measured_software p = false /\ s = po1_state_B).

(** A verifier deciding the external runtime label on full model states cannot
    depend only on the modeled quote. The named verifier corollary is applied
    through the lossless quote adapter and the two truth labels. Authenticity,
    when desired, remains an external premise because no signature is modeled. *)
Theorem quote_runtime_verifier_separation :
  forall nonce (V : Platform -> bool),
    (forall p, V p = runtime_is_measured_software p) ->
    ~ factors_classical (quote_projection nonce) V.
Proof.
  intros nonce V Hcorrect.
  apply (V_does_not_factor_through_classical
    Platform (quote_projection nonce) runtime_explains
    {| measured_log := []; runtime_is_measured_software := true |}
    {| measured_log := []; runtime_is_measured_software := false |} V).
  - reflexivity.
  - left. split; reflexivity.
  - right. split; reflexivity.
  - intros p Haccept s [[Hflag ->] | [Hflag ->]].
    + exact po1_cond4_trace_A_mu_paid.
    + rewrite Hcorrect, Hflag in Haccept. discriminate.
  - intros s p Hmu [[Hflag ->] | [Hflag ->]].
    + rewrite Hcorrect. exact Hflag.
    + rewrite po1_cond5_trace_B_mu_zero in Hmu. discriminate.
Qed.

End TPM.
