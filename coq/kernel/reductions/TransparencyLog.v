(** TransparencyLog: certificate transparency against the hardness-escape kernel.

    Certificate Transparency (RFC 6962) works by making the claim "this
    certificate is logged" checkable against a public append-only structure
    whose forgery is computationally hard. This file casts that design as
    the kernel's hardness escape.

    Core instantiation: [hardness_escape_succeeds] — under a hardness
    hypothesis, a transcript carrying a hard-to-forge witness admits a
    decision procedure at unit cost. The log IS the hardness witness.
    By [bare_setting_no_sound_complete_verifier], the log-free equivalent
    with the same soundness target cannot exist: there is no sound and
    complete bare-transcript verifier for the mu-dependent claim.

    Split-view attacks are the impossibility theorem's witness pair run
    against a live system: two populations shown bare-indistinguishable
    views that differ in the non-classical part.

    FALSIFIER: a sound and complete log-free verifier with the same
    soundness target — its Coq construction contradicts
    [bare_setting_no_sound_complete_verifier].

    This file does not model gossip protocols, log operator governance, or
    Merkle tree internals; the hardness hypothesis is named, not proven. *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

Require Import VerifierModel.
Require Import VerifierImpossibility.
Require Import VerifierEscape_Hardness.

(* -------------------------------------------------------------------- *)
(** ** Witness-level imports.

    The split-view theorem exhibits concrete VM states, so the kernel's
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
    tree whose signed head is cross-checked widely enough that
    fabricating an entry after the fact is computationally hard.  In the
    kernel the log appears as the [HardnessHypothesis] record — the
    named, deliberately unproven assumption that the commitment bit
    cannot be set except by an honest, mu-paying run.

    AN INCLUSION PROOF is the hardness witness: the audit path from a
    log entry to the signed head.  In the kernel it is the commitment
    bit of a [HardnessTranscript] — the single bit of non-classical
    structure the bare view lacks.

    A SPLIT VIEW is the impossibility theorem's witness pair deployed
    against a live system: two populations shown bare-indistinguishable
    views that differ on the logged, mu-dependent claim.  RFC 6962's
    threat model and [bare_setting_no_sound_complete_verifier] describe
    the same object at two resolutions. *)

(* -------------------------------------------------------------------- *)
(** ** Log-backed transcripts.

    What a CT-auditing client actually holds: the bare classical view of
    the served certificate (what any classical observer of the handshake
    records) together with the inclusion-proof bit ("the log vouches for
    this entry").  A genuine record, not a type synonym: the projection
    [lbt_to_hardness] and the lift lemmas below are the checked half of
    the dictionary. *)

Record LogBackedTranscript : Type := mk_lbt {
  lbt_observed  : BareTranscript;  (* the served view, classically projected *)
  lbt_inclusion : bool             (* the inclusion proof, abstracted to its verdict *)
}.

Definition lbt_to_hardness (t : LogBackedTranscript) : HardnessTranscript :=
  (lbt_observed t, lbt_inclusion t).

Definition hardness_to_lbt (t : HardnessTranscript) : LogBackedTranscript :=
  mk_lbt (fst t) (snd t).

(** The lift, entry one: the inclusion-proof bit IS the kernel's
    commitment bit under the projection. *)
Lemma inclusion_is_commitment :
  forall t : LogBackedTranscript,
    ht_commitment (lbt_to_hardness t) = lbt_inclusion t.
Proof. reflexivity. Qed.

(** The lift, entries two and three: the wrapper is lossless in both
    directions.  Log-backed transcripts and hardness transcripts carry
    exactly the same information; the record exists to fix the reading,
    not to add or hide state. *)
Lemma lbt_roundtrip :
  forall t : LogBackedTranscript,
    hardness_to_lbt (lbt_to_hardness t) = t.
Proof. intros [obs inc]. reflexivity. Qed.

Lemma hardness_roundtrip :
  forall t : HardnessTranscript,
    lbt_to_hardness (hardness_to_lbt t) = t.
Proof. intros [tr c]. reflexivity. Qed.

(* -------------------------------------------------------------------- *)
(** ** The log auditor.

    Accept iff the inclusion proof checks; charge one unit.  In a real
    deployment the audit-path check is logarithmic in the log and
    constant in the prover's work; the kernel's cost model rounds
    "cheap" to a single unit, matching [hardness_cost]. *)

Definition log_audit_decide (t : LogBackedTranscript) : bool :=
  lbt_inclusion t.

Definition log_audit_cost (t : LogBackedTranscript) : nat := 1.

(** The auditor is the kernel's hardness verifier read through the
    wrapper — definitional, recorded as a lemma so the identification is
    on the books rather than in the elaborator. *)
Lemma log_audit_is_hardness_decide :
  forall t : LogBackedTranscript,
    log_audit_decide t = hardness_decide (lbt_to_hardness t).
Proof. reflexivity. Qed.

(** Weak soundness of the auditor, conditional on the hardness of the
    log: every accepted log-backed transcript is mu-grounded — some VM
    state with [vm_mu s = 1] stands behind it.  Weak (existential)
    soundness is the cryptographic notion, exactly as in
    [hardness_verifier_weak_sound]; the strong (universal) notion is the
    one the log-free setting refutes below. *)
Lemma log_audit_weak_sound :
  forall (H : HardnessHypothesis) (t : LogBackedTranscript),
    log_audit_decide t = true ->
    exists s : VMState, s.(vm_mu) = 1.
Proof.
  intros H t Hacc.
  apply (hardness_verifier_weak_sound H (lbt_to_hardness t)).
  rewrite <- (log_audit_is_hardness_decide t).
  exact Hacc.
Qed.

(* -------------------------------------------------------------------- *)
(** ** MAIN 1: the escape, in log vocabulary. *)

(** [transparency_log_escape]: under any hardness hypothesis, log-backed
    transcripts admit a decision procedure at unit cost whose every
    acceptance is mu-grounded.

    The witnesses are the concrete auditor above; acceptance routes
    through [inclusion_is_commitment] into the hypothesis's
    unforgeability field.  Honestly an instantiation: this is
    [hardness_escape_succeeds] precomposed with [lbt_to_hardness].  What
    this file adds is the checked dictionary — the RFC 6962 design
    (client verifies the inclusion proof, trusts the log's hardness)
    lands on the kernel's hardness escape with no residue.  The log is
    not an optimisation of verification; it is the purchase of one
    non-classical bit. *)
Theorem transparency_log_escape :
  forall H : HardnessHypothesis,
  exists (decide : LogBackedTranscript -> bool)
         (cost   : LogBackedTranscript -> nat),
    (forall t, decide t = true -> exists s : VMState, s.(vm_mu) = 1) /\
    (forall t, cost t = 1).
Proof.
  intro H.
  exists log_audit_decide, log_audit_cost.
  split.
  - intros t Hacc. exact (log_audit_weak_sound H t Hacc).
  - intro t. reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(** ** MAIN 2: delete the log and the job becomes impossible. *)

(** A log-free verifier reads only the bare classical view — no
    inclusion bit, no log to consult.  This is exactly the kernel's
    [BareVerifier]; the definition gives "log-free" a formal referent so
    the impossibility below is about a named class, not an informal
    absence. *)
Definition log_free_verifier : Type := BareVerifier.

(** [log_free_verifier_impossible]: no log-free verifier is both sound
    and complete for the mu-dependent claim ([vm_mu s = 1] — the claim
    whose CT reading is "this entry was actually paid into the log").

    Restatement by exact application of
    [bare_setting_no_sound_complete_verifier]: [log_free_verifier] is
    definitionally [BareVerifier], so the kernel theorem IS this
    theorem.  The point of restating it is the pairing with MAIN 1:
    same claim, same unit-cost regime — the difference between possible
    and impossible is exactly whether the transcript carries the log's
    bit. *)
(* INQUISITOR NOTE: alias for bare_setting_no_sound_complete_verifier — deliberate re-export so the log-free impossibility is on the record in CT vocabulary, paired against MAIN 1's escape. *)
Theorem log_free_verifier_impossible :
  ~ exists V : log_free_verifier,
      bare_sound mu_eq_one_problem V /\
      bare_complete mu_eq_one_problem V.
Proof.
  exact bare_setting_no_sound_complete_verifier.
Qed.

(* -------------------------------------------------------------------- *)
(** ** MAIN 3: the split view, exhibited. *)

(** [split_view_witness]: the concrete pair behind the impossibility.
    Two VM states with literally equal classical projections — one bare
    view serves both — explaining the same transcript, with the
    mu-dependent claim true at one and false at the other.

    In CT terms: population A is served by an honest run that paid mu
    into the log; population B is served by a run that did not; both
    populations' recorded views are the same list of classical states.
    That is the split-view attack at the kernel's resolution.  The
    witnesses are [po1_state_A] / [po1_state_B] from the mu-ledger
    collision — the same pair [bare_setting_no_sound_complete_verifier]
    plays against completeness and soundness in turn — surfaced as a
    standalone theorem so the attack object is a first-class export
    rather than a step inside the impossibility proof. *)
Theorem split_view_witness :
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
Corollary split_view_same_verdict :
  forall V : log_free_verifier,
    bv_decide V po1_strict_trace_A = bv_decide V po1_strict_trace_B.
Proof.
  intro V.
  apply bare_decide_eq_trans.
  exact po1_cond2_shadow_traces_equal.
Qed.

Print Assumptions transparency_log_escape.
Print Assumptions log_free_verifier_impossible.
Print Assumptions split_view_witness.
Print Assumptions split_view_same_verdict.
