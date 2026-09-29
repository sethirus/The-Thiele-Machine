(** TransparencyLog: certificate transparency against the commitment kernel.

    Certificate Transparency (RFC 6962, obsoleted by RFC 9162) works by
    making the claim "this certificate is logged" checkable against a public
    append-only structure whose forgery is computationally hard. This file
    casts that design as the kernel's commitment escape, at the resolution
    of one bit. It keeps the Boolean verdict a CT checker would supply and
    drops everything that produces it: signed tree heads, Merkle inclusion
    proofs, consistency proofs.

    Core instantiation: [commitment_contract_verifier]. Under an exact
    disclosure contract, a transcript carrying the checker's verdict admits
    a sound and complete decision procedure at unit cost. The log's verdict
    IS the commitment bit. By [bare_setting_no_sound_complete_verifier], the
    log-free equivalent with the same soundness target cannot exist: there
    is no sound and complete bare-transcript verifier for the mu-dependent
    claim [vm_mu = 1].

    Split-view attacks motivate the witness pair. The pair is two VM states
    with one bare view that differ on a mu-dependent claim; an RFC split
    view is two inconsistent log histories. The shapes rhyme. No equivalence
    between the two threat models is proved.

    The boundary is the named bare projection and soundness target. A sound and
    complete log-free verifier for that same target would contradict
    [bare_setting_no_sound_complete_verifier].

    This file does not model gossip protocols, log operator governance, or
    Merkle tree internals. The disclosure contract is named, not proven; it
    is not derived from signature security or collision resistance. *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

Require Import VerifierModel.
Require Import VerifierImpossibility.
Require Import VerifierEscape_Hardness.

(* -------------------------------------------------------------------- *)
(** ** Witness-level imports.

    The collision theorem exhibits concrete VM states, so the kernel's
    state type and the mu-collision witnesses are named here in addition
    to the verifier-layer imports above. *)

From Kernel Require Import VMState.
Require Import NecessityOfMuLedger.

(* -------------------------------------------------------------------- *)
(** ** The dictionary.

    Three glosses fix the reading of the kernel's records in RFC 6962
    vocabulary; everything after this comment is the kernel under that
    renaming, and the renaming is the content.

    THE LOG is the hard-to-forge public structure: an append-only Merkle
    tree whose signed head is cross-checked widely enough that fabricating
    an entry after the fact is computationally hard. In the kernel the log
    appears only as a checked inclusion verdict, governed by
    [CommitmentBitContract]: the named, deliberately unproven premise that
    the bit agrees with the claim for every state the transcript can stand
    for. No Merkle or signature security follows from it. The contract is
    what that security would have to deliver.

    AN INCLUSION PROOF is the audit path from a log entry to the signed
    head. In the kernel it is reduced to its checking verdict, the
    commitment bit of a [CommitmentTranscript]: the single bit of
    non-classical structure the bare view lacks. The path, tree head and
    signature are outside this abstraction.

    A SPLIT VIEW shows two populations views that should agree and do not.
    The VM collision makes the same move at the kernel's resolution: two
    states with bare-indistinguishable views that differ on the
    mu-dependent claim. RFC 6962's split view is about inconsistent log
    histories, and the collision is about a mu claim. One shape, two
    objects; no equivalence between them is proved. *)

(* -------------------------------------------------------------------- *)
(** ** Log-backed transcripts.

    What a CT-auditing client holds, cut down to two fields: the bare
    classical view of the served certificate (what any classical observer
    of the handshake records) together with the inclusion-proof verdict
    ("the log vouches for this entry"). A real client also holds the path,
    the tree head, and signatures; they are omitted. A genuine record, not
    a type synonym: the projection [lbt_to_commitment] and the lift lemmas
    below are the checked half of the dictionary. *)

Record LogBackedTranscript : Type := mk_lbt {
  lbt_observed  : BareTranscript;  (* the served view, classically projected *)
  lbt_inclusion : bool             (* the inclusion proof, abstracted to its verdict *)
}.

Definition lbt_to_commitment (t : LogBackedTranscript) : CommitmentTranscript :=
  (lbt_observed t, lbt_inclusion t).

Definition commitment_to_lbt (t : CommitmentTranscript) : LogBackedTranscript :=
  mk_lbt (fst t) (snd t).

(** The lift, entry one: the inclusion-proof bit IS the kernel's
    commitment bit under the projection. *)
Lemma inclusion_is_commitment :
  forall t : LogBackedTranscript,
    ct_commitment (lbt_to_commitment t) = lbt_inclusion t.
Proof. reflexivity. Qed.

(** The lift, entries two and three: the wrapper is lossless in both
    directions. Log-backed and commitment transcripts carry
    exactly the same information; the record exists to fix the reading,
    not to add or hide state. *)
Lemma lbt_roundtrip :
  forall t : LogBackedTranscript,
    commitment_to_lbt (lbt_to_commitment t) = t.
Proof. intros [obs inc]. reflexivity. Qed.

Lemma commitment_roundtrip :
  forall t : CommitmentTranscript,
    lbt_to_commitment (commitment_to_lbt t) = t.
Proof. intros [tr c]. reflexivity. Qed.

(* -------------------------------------------------------------------- *)
(** ** The log auditor.

    Accept iff the inclusion proof checks; charge one unit.  In a real
    deployment the audit-path check is logarithmic in the log and
    constant in the prover's work; the kernel's cost model rounds
    "cheap" to a single unit, matching [commitment_cost]. *)

Definition log_audit_decide (t : LogBackedTranscript) : bool :=
  lbt_inclusion t.

Definition log_audit_cost (t : LogBackedTranscript) : nat := 1.

(** The auditor is the kernel's commitment verifier read through the
    wrapper: definitional, recorded as a lemma so the identification is
    on the books rather than in the elaborator. *)
Lemma log_audit_is_commitment_decide :
  forall t : LogBackedTranscript,
    log_audit_decide t = commitment_decide (lbt_to_commitment t).
Proof. reflexivity. Qed.

(** Soundness and completeness of the auditor, conditional on the exact
    disclosure contract. [lexplains] says which log-backed transcripts each
    state can stand behind, forged ones included. The hypothesis is the
    kernel's [CommitmentBitContract] read through the wrapper: a set
    inclusion bit comes only from a state that satisfies the claim, and an
    honest state always gets one. The soundness here is the strong,
    universal notion, the same one the log-free setting refutes below. *)
Section LogAudit.

Variable lexplains : VMState -> LogBackedTranscript -> Prop.

Definition log_commitment_contract : Prop :=
  CommitmentBitContract (fun s h => lexplains s (commitment_to_lbt h)).

Lemma log_audit_sound :
  log_commitment_contract ->
  forall t, log_audit_decide t = true ->
  forall s, lexplains s t -> s.(vm_mu) = 1.
Proof.
  intros H t Hacc s Hex.
  apply (hh_binding _ H s (lbt_to_commitment t)).
  - rewrite lbt_roundtrip. exact Hex.
  - exact Hacc.
Qed.

Lemma log_audit_complete :
  log_commitment_contract ->
  forall s t, s.(vm_mu) = 1 -> lexplains s t -> log_audit_decide t = true.
Proof.
  intros H s t Hmu Hex.
  rewrite (log_audit_is_commitment_decide t).
  apply (hh_honest _ H s (lbt_to_commitment t)).
  - rewrite lbt_roundtrip. exact Hex.
  - exact Hmu.
Qed.

(* -------------------------------------------------------------------- *)
(** ** MAIN 1: the escape, in log vocabulary. *)

(** [abstract_log_bit_verifier]: under the disclosure contract, log-backed
    transcripts admit a decision procedure at unit cost that is sound and
    complete.

    The witnesses are the concrete auditor above; acceptance routes
    through [inclusion_is_commitment] into the contract's binding field.
    Honestly an instantiation: this is the argument of
    [commitment_contract_verifier] read through [lbt_to_commitment]. What
    this file adds is the checked dictionary: the RFC 6962 design (client
    verifies the inclusion proof, trusts the log) lands on the kernel's
    commitment escape once the log's security is packed into the contract.
    The log is not an optimisation of verification; it is the purchase of
    one non-classical bit. This is not a security proof for RFC 6962. The
    contract is where that proof would have to go. *)
Theorem abstract_log_bit_verifier :
  log_commitment_contract ->
  exists (decide : LogBackedTranscript -> bool)
         (cost   : LogBackedTranscript -> nat),
    (forall t, decide t = true -> forall s, lexplains s t -> s.(vm_mu) = 1) /\
    (forall s t, s.(vm_mu) = 1 -> lexplains s t -> decide t = true) /\
    (forall t, cost t = 1).
Proof.
  intro H. exists log_audit_decide, log_audit_cost.
  split; [exact (log_audit_sound H) |].
  split; [exact (log_audit_complete H) | intro t; reflexivity].
Qed.

End LogAudit.

(* -------------------------------------------------------------------- *)
(** ** MAIN 2: delete the log and the job becomes impossible. *)

(** A log-free verifier reads only the bare classical view: no inclusion
    bit, no log to consult. This is exactly the kernel's
    [BareVerifier]; the definition gives "log-free" a formal referent so
    the impossibility below is about a named class, not an informal
    absence. *)
Definition abstract_log_free_verifier : Type := BareVerifier.

(** [abstract_bare_verifier_impossible]: no log-free verifier is both
    sound and complete for the mu-dependent claim [vm_mu s = 1]. The file's
    CT reading of that claim is "this entry was actually paid into the
    log"; the reading is a label, not a theorem.

    Restatement by exact application of
    [bare_setting_no_sound_complete_verifier]: [abstract_log_free_verifier] is
    definitionally [BareVerifier], so the kernel theorem IS this
    theorem. The point of restating it is the pairing with MAIN 1: same
    claim, same unit-cost regime. The difference between possible and
    impossible is exactly whether the transcript carries the log's bit. *)
(* SCOPE NOTE: alias for bare_setting_no_sound_complete_verifier; deliberate re-export so the log-free impossibility is on the record in CT vocabulary, paired against MAIN 1's escape. *)
Theorem abstract_bare_verifier_impossible :
  ~ exists V : abstract_log_free_verifier,
      bare_sound mu_eq_one_problem V /\
      bare_complete mu_eq_one_problem V.
Proof.
  exact bare_setting_no_sound_complete_verifier.
Qed.

(* -------------------------------------------------------------------- *)
(** ** MAIN 3: the split view's shape, exhibited. *)

(** [abstract_mu_collision_witness]: the concrete pair behind the
    impossibility. Two VM states with literally equal classical projections
    (one bare view serves both) explain the same transcript, with the
    mu-dependent claim true at one and false at the other.

    In CT terms, as a picture: population A is served by an honest run that
    paid mu into the log; population B is served by a run that did not;
    both populations' recorded views are the same list of classical states.
    That is a split view's shape at the kernel's resolution. It is not an
    RFC split view, which is two inconsistent log histories. The witnesses
    are [po1_state_A] / [po1_state_B] from the mu-ledger collision, the same
    pair [bare_setting_no_sound_complete_verifier] plays against
    completeness and soundness in turn, surfaced as a standalone theorem so
    the attack object is a first-class export rather than a step inside the
    impossibility proof. *)
Theorem abstract_mu_collision_witness :
  exists (sA sB : VMState) (view : BareTranscript),
    strict_shadow sA = strict_shadow sB /\
    mu_collision_explains sA view /\
    mu_collision_explains sB view /\
    mu_eq_one_claim sA /\
    ~ mu_eq_one_claim sB.
Proof.
  exists po1_state_A, po1_state_B, po1_strict_trace_A.
  split; [exact po1_cond2_final_shadow_equal|].
  split; [exact witness_A_explains_shared|].
  split; [exact witness_B_explains_shared|].
  split; [exact witness_A_satisfies_claim|].
  exact witness_B_violates_claim.
Qed.

(** Operational corollary: every log-free verifier returns the same
    verdict to both populations.  The two full strict traces are equal
    as lists ([po1_cond2_shadow_traces_equal]), so any decision function
    on bare transcripts is constant across the split.  Blindness here is
    not a defect of a particular verifier; it is a property of the
    interface. *)
Corollary abstract_mu_collision_same_verdict :
  forall V : abstract_log_free_verifier,
    bv_decide V po1_strict_trace_A = bv_decide V po1_strict_trace_B.
Proof.
  intro V.
  apply bare_decide_eq_trans.
  exact po1_cond2_shadow_traces_equal.
Qed.

Print Assumptions abstract_log_bit_verifier.
Print Assumptions abstract_bare_verifier_impossible.
Print Assumptions abstract_mu_collision_witness.
Print Assumptions abstract_mu_collision_same_verdict.
