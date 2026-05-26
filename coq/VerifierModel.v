(** * VerifierModel.v — generic prover/verifier model for the μ-axis.

    This file defines the verifier setting used by the verifier-corollary
    chain in the monograph (Section "What the projection cannot verify"):

      - [BareTranscript]: what a verifier observes in the bare setting
        (a list of strict-classical-state observations — the kernel's
        Turing-classical projection of a VM execution).
      - [BareVerificationProblem]: a claim [φ] over [VMState] together
        with an explanation relation, a budget, and a recompute-cost.
      - [BareVerifier]: a [decide]/[cost] pair on transcripts.
      - [bare_sound] / [bare_complete] / [bare_cheap]: the three
        properties a verifier may satisfy.

    The bare-setting impossibility ([VerifierImpossibility.v]) instantiates
    [BareVerificationProblem] with a concrete μ-sensitive claim and lifts
    [ReceiptTheorem] into the verifier setting. The three escape files
    ([VerifierEscape_Substrate.v], [VerifierEscape_Hardness.v],
    [VerifierEscape_Interaction.v]) extend [BareTranscript] with extra
    structure and exhibit cheap sound verifiers. [VerifierExhaustiveness.v]
    closes the trichotomy at the bottom.

    No axioms or hypotheses: every export is a [Record] / [Definition] /
    [Theorem] closed under the global context.
*)

From Coq Require Import List.
Import ListNotations.

From Kernel Require Import VMState.
Require Import NecessityOfMuLedger.

(* -------------------------------------------------------------------- *)
(** ** The bare-setting transcript.

    The verifier in the bare setting sees a list of strict classical
    states — exactly what a Turing-classical observer would see along
    the prover's execution. No μ, no certification flag, no graph state.
*)

Definition BareTranscript : Type := list StrictClassicalState.

(* -------------------------------------------------------------------- *)
(** ** Verification problem.

    [bare_honest_claim] is the property of [VMState] the prover is
    asking the verifier to certify. [bare_explains s t] is the
    relation "transcript [t] is consistent with an honest execution
    reaching state [s]"; in the bare setting this will be instantiated
    as "[t] is the strict-shadow trace of an execution producing [s]."

    [bare_cheap_budget] is the cost budget below which the verifier is
    "cheap"; [bare_recompute_cost] is the cost the verifier would pay
    to re-execute the prover's run from scratch. The non-trivial
    setting is [bare_cheap_budget < bare_recompute_cost] (otherwise
    "cheap" is vacuous).
*)

Record BareVerificationProblem := mk_bvp {
  bare_honest_claim    : VMState -> Prop;
  bare_explains        : VMState -> BareTranscript -> Prop;
  bare_cheap_budget    : nat;
  bare_recompute_cost  : nat
}.

(* -------------------------------------------------------------------- *)
(** ** Verifier.

    A bare verifier is a pair: a Boolean decision function on
    transcripts, and a cost function recording the μ-equivalent
    resources the verifier expends.
*)

Record BareVerifier := mk_bv {
  bv_decide : BareTranscript -> bool;
  bv_cost   : BareTranscript -> nat
}.

(* -------------------------------------------------------------------- *)
(** ** Three properties a verifier may satisfy.

    [bare_cheap]: every accepted-or-rejected transcript fits within
    the problem's cost budget.

    [bare_sound]: every accepted transcript witnesses the claim. We
    use *strong soundness* — the claim must hold for every honest
    state that could explain the transcript, not merely for some.
    This captures the verifier's inability to distinguish which prover
    state produced the transcript when the transcript only carries
    classical-projection information.

    [bare_complete]: every honest transcript-for-a-state-satisfying-
    the-claim is accepted.
*)

Definition bare_cheap (P : BareVerificationProblem) (V : BareVerifier) : Prop :=
  forall t, bv_cost V t <= bare_cheap_budget P.

Definition bare_sound (P : BareVerificationProblem) (V : BareVerifier) : Prop :=
  forall t, bv_decide V t = true ->
    forall s, bare_explains P s t -> bare_honest_claim P s.

Definition bare_complete (P : BareVerificationProblem) (V : BareVerifier) : Prop :=
  forall s t,
    bare_honest_claim P s ->
    bare_explains P s t ->
    bv_decide V t = true.

(* -------------------------------------------------------------------- *)
(** ** Sanity lemmas.

    A handful of bookkeeping facts used in downstream proofs. Each is
    short enough that the kernel-conversion vacuity gate may flag it —
    that is *expected* and *desired*; sanity lemmas should be flagged,
    we just want the gate to keep these from masquerading as headline
    results. The downstream Phase-1.b theorem is the headline; these
    are scaffolding.
*)

(** If two transcripts are equal, the verifier agrees on them. *)
Lemma bare_decide_eq_trans :
  forall (V : BareVerifier) (t1 t2 : BareTranscript),
    t1 = t2 -> bv_decide V t1 = bv_decide V t2.
Proof. intros V t1 t2 H. rewrite H. reflexivity. Qed.

(** Strong soundness implies a contrapositive form: if the claim fails
    for some explanation of [t], the verifier rejects [t]. *)
Lemma bare_sound_contrapositive :
  forall (P : BareVerificationProblem) (V : BareVerifier),
    bare_sound P V ->
    forall t s,
      bare_explains P s t ->
      ~ bare_honest_claim P s ->
      bv_decide V t = false.
Proof.
  intros P V Hsound t s Hexp Hnclaim.
  destruct (bv_decide V t) eqn:Hdec.
  - exfalso. apply Hnclaim. eapply Hsound; eauto.
  - reflexivity.
Qed.

Print Assumptions bare_sound_contrapositive.
