(** TEEAttestation: remote attestation against the verifier-factorisation kernel.

    A trusted execution environment proves to a remote party that a specific
    measured binary produced a result. The attestation report is a
    transcript; the measurement register is state the bare classical
    transcript does not carry. This file instantiates the kernel's verifier
    results in that vocabulary.

    Core instantiation: [V_does_not_factor_through_classical] — a sound and
    complete verifier of a mu-dependent claim cannot factor through the bare
    classical transcript. Attestation of a measurement-dependent claim must
    expose non-classical structure (the measurement register), and the
    ineliminable trust is exactly the named Section-Variable surface.
    [substrate_escape_succeeds] is the positive side: enrich the transcript
    with the register and a sound, complete, unit-cost verifier exists.

    Replay attacks are the kernel's two-preimage witnesses in engineering
    clothes: two runs with identical bare transcripts and different
    measurement state.

    FALSIFIER: a sound and complete attestation scheme for a mu-dependent
    claim that reads only the bare transcript. Constructing it in Coq
    contradicts [V_does_not_factor_through_classical] directly.

    This file does not model side channels, key management, or the CPU
    vendor's signing PKI; the trust surface it names is structural. *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

Require Import VerifierModel.
Require Import VerifierExhaustiveness.
Require Import VerifierEscape_Substrate.

(* The po1 collision witnesses and the mu=1 verification problem live in
   [NecessityOfMuLedger] and [VerifierImpossibility]. The imports above
   load both transitively but do not open them; we open them here, plus
   the kernel VM state for [vm_mu]. *)
From Kernel Require Import VMState.
Require Import NecessityOfMuLedger.
Require Import VerifierImpossibility.

(* -------------------------------------------------------------------- *)
(** ** Attestation reports.

    A TEE attestation report, reduced to its load-bearing skeleton: the
    bare transcript the enclave's run presents to a classical observer,
    plus one measurement register. The register is the PCR/MRENCLAVE-style
    slot — a value the trusted hardware accumulates as the run commits,
    which no replay of the bare transcript recomputes. In the kernel's
    coordinates the register carries [vm_mu]: the structural ledger the
    strict classical shadow forgets. *)

Record TEEReport := mk_tee_report {
  rep_bare        : BareTranscript; (** what a classical observer sees *)
  rep_measurement : nat             (** the trusted measurement register *)
}.

(** Forgetting the register: the classical projection of a report. An
    attestation verifier that "just checks the logs" is exactly a verifier
    that factors through this map. *)
Definition report_projection (r : TEEReport) : BareTranscript :=
  rep_bare r.

(** When a report honestly attests prover state [s]:

      - its bare field is explained by [s] under the kernel's mu=1
        verification problem — [bare_explains mu_eq_one_problem], the
        relation the bare-setting impossibility is stated over; and
      - its measurement register equals the state's mu ledger.

    The second conjunct is the hardware's promise: the register is a
    faithful readout of structural state, not a free-form integer. The
    whole file is about what happens when a verifier is, or is not,
    allowed to read it. *)
Definition report_explains (s : VMState) (r : TEEReport) : Prop :=
  bare_explains mu_eq_one_problem s (rep_bare r)
  /\ rep_measurement r = s.(vm_mu).

(** Soundness in attestation vocabulary: an accepted report vouches for
    every state that explains it — the verifier cannot accept a report
    consistent with an unpaid run. *)
Definition attestation_sound (V : TEEReport -> bool) : Prop :=
  forall r, V r = true ->
    forall s, report_explains s r -> s.(vm_mu) = 1.

(** Completeness in attestation vocabulary: every honest report for a
    paid run is accepted. *)
Definition attestation_complete (V : TEEReport -> bool) : Prop :=
  forall s r, s.(vm_mu) = 1 -> report_explains s r -> V r = true.

(* -------------------------------------------------------------------- *)
(** ** The two reports the kernel's collision pair produces.

    Trace A pays for certification (CERTIFY: mu goes 0 to 1); Trace B runs
    a partition instruction at mu-cost 0. Their strict classical shadows
    are equal ([po1_cond2_shadow_traces_equal]): the bare transcript
    cannot tell the runs apart. The measurement registers differ — 1 for
    the run that paid, 0 for the run that did not. [report_B] is the
    replayed report: same observable log, no payment behind it. *)

Definition report_A : TEEReport :=
  {| rep_bare := po1_strict_trace_A; rep_measurement := 1 |}.

Definition report_B : TEEReport :=
  {| rep_bare := po1_strict_trace_B; rep_measurement := 0 |}.

(** The two reports are classically indistinguishable: their projections
    are the kernel's shadow-trace equality, verbatim. *)
(* INQUISITOR NOTE: alias for po1_cond2_shadow_traces_equal — deliberate vocabulary lift of the kernel collision onto TEEReport projections for MAIN 1. *)
Lemma reports_project_equal :
  report_projection report_A = report_projection report_B.
Proof.
  exact po1_cond2_shadow_traces_equal.
Qed.

(** [report_A] honestly attests the paying state: the bare field is the
    kernel's shared trace ([witness_A_explains_shared]) and the register
    reads the mu that CERTIFY charged ([po1_cond4_trace_A_mu_paid]). *)
Lemma report_A_explains_A : report_explains po1_state_A report_A.
Proof.
  split.
  - exact witness_A_explains_shared.
  - symmetry. exact po1_cond4_trace_A_mu_paid.
Qed.

(** [report_B] honestly attests the non-paying state: its bare field is
    Trace B's shadow, equal to the shared trace, and the register reads
    the mu that PNEW did not charge ([po1_cond5_trace_B_mu_zero]). *)
Lemma report_B_explains_B : report_explains po1_state_B report_B.
Proof.
  split.
  - split.
    + symmetry. exact po1_cond2_shadow_traces_equal.
    + right. reflexivity.
  - symmetry. exact po1_cond5_trace_B_mu_zero.
Qed.

(* -------------------------------------------------------------------- *)
(** ** MAIN 1: attestation cannot factor through the bare transcript.

    Any attestation verifier that is sound and complete for the
    mu-dependent claim depends on more than the bare transcript: it
    cannot be a function of [report_projection]. Concretely, "verify the
    enclave by auditing its classical execution log" is not a sound and
    complete attestation scheme for measurement-dependent claims, no
    matter how clever the auditor.

    This is an honest instantiation: it is
    [V_does_not_factor_through_classical] at [T := TEEReport], with the
    projection collision supplied by [report_A] / [report_B] and the
    explanation pair by the kernel's po1 witnesses. The attestation
    content is in the instance, not the argument.

    FALSIFIER: a sound and complete [V : TEEReport -> bool] together with
    a proof of [factors_classical report_projection V]. *)
Theorem attestation_cannot_factor_through_bare_transcript :
  forall V : TEEReport -> bool,
    attestation_sound V ->
    attestation_complete V ->
    ~ factors_classical report_projection V.
Proof.
  intros V Hsound Hcomplete.
  apply (V_does_not_factor_through_classical
           TEEReport report_projection report_explains
           report_A report_B V).
  - exact reports_project_equal.
  - exact report_A_explains_A.
  - exact report_B_explains_B.
  - exact Hsound.
  - exact Hcomplete.
Qed.

(* -------------------------------------------------------------------- *)
(** ** MAIN 2: the replay attack, as a theorem.

    Two attestation reports with the same classical projection and
    different measurement registers, each honestly explained by a real
    prover state: the paid run and the unpaid run. This is the replay
    attack in its structural form — the adversary re-presents the
    observable log of a paid run, and the bare transcript carries
    nothing that could expose the substitution. The only field that
    separates the two reports is the register.

    Nothing here is hypothetical: both reports are explained by concrete
    kernel states ([po1_state_A], [po1_state_B]), so the two-preimage
    collision is exhibited, not assumed.

    FALSIFIER: a proof that any two reports with equal projections,
    explained by the po1 pair, must agree on the register — that would
    contradict this witness directly. *)
Theorem replay_is_a_two_preimage_witness :
  exists r_A r_B : TEEReport,
    report_projection r_A = report_projection r_B
    /\ rep_measurement r_A <> rep_measurement r_B
    /\ report_explains po1_state_A r_A
    /\ report_explains po1_state_B r_B.
Proof.
  exists report_A, report_B.
  split; [| split; [| split]].
  - exact reports_project_equal.
  - simpl. discriminate.
  - exact report_A_explains_A.
  - exact report_B_explains_B.
Qed.

(* -------------------------------------------------------------------- *)
(** ** MAIN 3: exposing the register restores verification.

    The positive side. An attestation verifier that may read the
    measurement register is sound, complete, and unit-cost for the
    mu-dependent claim. The mechanism is the kernel's substrate-trust
    escape: the register is a trusted readout of structural state, so
    the verifier dereferences it instead of re-running the enclave.

    Construction: from a report's register we rebuild the substrate
    snapshot it vouches for ([measured_snapshot]) and hand that to the
    kernel's substrate verifier. The attestation verifier is literally
    [substrate_decide_mu_eq_one] behind a register-decoding shim, and
    the three conjuncts of the headline are discharged by
    [substrate_verifier_sound], [substrate_verifier_complete], and
    [substrate_verifier_cheap] — the components of
    [substrate_escape_succeeds]. *)

(** The state a report's register vouches for, within the po1 collision
    scenario: register 1 names the paid state, anything else the unpaid
    one. *)
Definition snapshot_state (r : TEEReport) : VMState :=
  if Nat.eqb (rep_measurement r) 1 then po1_state_A else po1_state_B.

(** The one-snapshot substrate transcript a report decodes to. *)
Definition measured_snapshot (r : TEEReport) : SubstrateTranscript :=
  [snapshot_state r].

(** The attestation verifier: decode the register, ask the substrate
    verifier. Cost is the substrate verifier's cost — one dereference. *)
Definition attest_decide (r : TEEReport) : bool :=
  substrate_decide_mu_eq_one (measured_snapshot r).

Definition attest_cost (r : TEEReport) : nat :=
  substrate_cost_one (measured_snapshot r).

(** The decoded snapshot is explained, in the substrate sense, by the
    state the register names. *)
Lemma measured_snapshot_explains :
  forall r : TEEReport,
    substrate_explains (snapshot_state r) (measured_snapshot r).
Proof.
  intro r.
  unfold measured_snapshot, substrate_explains, substrate_last_total.
  simpl. reflexivity.
Qed.

(** Register fidelity transfers to the decoded snapshot: for an honestly
    explained report, the snapshot's mu agrees with the prover state's
    mu. This is where the hardware's promise (second conjunct of
    [report_explains]) does its work. *)
Lemma snapshot_state_mu :
  forall (s : VMState) (r : TEEReport),
    report_explains s r ->
    (snapshot_state r).(vm_mu) = s.(vm_mu).
Proof.
  intros s r [Hbare Hmeas].
  destruct Hbare as [_ [HsA | HsB]].
  - subst s. unfold snapshot_state.
    rewrite Hmeas, po1_cond4_trace_A_mu_paid.
    simpl. exact po1_cond4_trace_A_mu_paid.
  - subst s. unfold snapshot_state.
    rewrite Hmeas, po1_cond5_trace_B_mu_zero.
    simpl. exact po1_cond5_trace_B_mu_zero.
Qed.

(** Soundness of the register-reading verifier, discharged by the
    kernel's substrate soundness. *)
Lemma attest_decide_sound : attestation_sound attest_decide.
Proof.
  intros r Hdec s Hexp.
  rewrite <- (snapshot_state_mu s r Hexp).
  eapply substrate_verifier_sound.
  - exact Hdec.
  - apply measured_snapshot_explains.
Qed.

(** Completeness of the register-reading verifier, discharged by the
    kernel's substrate completeness. *)
Lemma attest_decide_complete : attestation_complete attest_decide.
Proof.
  intros s r Hmu Hexp.
  unfold attest_decide.
  apply (substrate_verifier_complete (snapshot_state r)).
  - rewrite (snapshot_state_mu s r Hexp). exact Hmu.
  - apply measured_snapshot_explains.
Qed.

(** The headline: with the measurement register exposed, a sound,
    complete, unit-cost attestation verifier exists for the claim that
    defeated every bare verifier. This is the substrate-trust escape
    ([substrate_escape_succeeds]) in attestation vocabulary; the trust
    being purchased is exactly "the register reports mu faithfully",
    which [report_explains] makes explicit.

    FALSIFIER: a proof that every sound and complete verifier on
    [TEEReport] must pay more than unit cost — the witness below costs 1
    on every report. *)
Theorem measurement_enriched_attestation_succeeds :
  exists (decide : TEEReport -> bool) (cost : TEEReport -> nat),
    attestation_sound decide
    /\ attestation_complete decide
    /\ (forall r, cost r = 1).
Proof.
  exists attest_decide, attest_cost.
  split; [| split].
  - exact attest_decide_sound.
  - exact attest_decide_complete.
  - intro r. apply substrate_verifier_cheap.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Closing corollary: the working verifier really reads the register.

    MAIN 1 applied to MAIN 3's witness: the verifier that works is not a
    function of the bare transcript. The escape and the impossibility
    are two faces of the same fact — the verifier succeeds *because* it
    depends on the field the classical projection forgets. *)
Corollary working_attestation_verifier_reads_the_register :
  ~ factors_classical report_projection attest_decide.
Proof.
  apply attestation_cannot_factor_through_bare_transcript.
  - exact attest_decide_sound.
  - exact attest_decide_complete.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Assumption audit. *)

Print Assumptions attestation_cannot_factor_through_bare_transcript.
Print Assumptions replay_is_a_two_preimage_witness.
Print Assumptions measurement_enriched_attestation_succeeds.
Print Assumptions working_attestation_verifier_reads_the_register.
