(** * VerifierImpossibility.v — bare-setting verifier impossibility.

    Theorem [bare_setting_no_sound_complete_verifier]:
    There exists a [BareVerificationProblem] whose claim is sensitive
    to [vm_mu] (specifically, the claim "vm_mu s = 1") such that no
    [BareVerifier] is simultaneously [bare_sound] and [bare_complete]
    on it.

    Proof technique: lift the classical-shadow collision from
    [NecessityOfMuLedger]. The two witness states [po1_state_A] (μ=1)
    and [po1_state_B] (μ=0) project onto identical strict-classical
    traces. Both states therefore "explain" the same transcript. A
    sound verifier must commit to [vm_mu s = 1] for every explanation
    of any accepted transcript — but the explanation by [po1_state_B]
    contradicts the claim. A complete verifier must accept the
    transcript at the honest [po1_state_A]. Contradiction.

    This is the receipt theorem lifted: the same projection collision
    that makes [vm_mu] non-recoverable from the classical shadow also
    makes [vm_mu]-sensitive claims unverifiable in the bare setting.

    The escape files [VerifierEscape_Substrate.v],
    [VerifierEscape_Hardness.v], and [VerifierEscape_Interaction.v]
    exhibit cheap sound verifiers under three structurally distinct
    transcript augmentations; [VerifierExhaustiveness.v] closes the
    trichotomy with the factorisation impossibility.
*)

From Coq Require Import List.
Import ListNotations.

From Kernel Require Import VMState.
Require Import NecessityOfMuLedger.
Require Import VerifierModel.

(* -------------------------------------------------------------------- *)
(** ** The μ-sensitive verification problem.

    Claim: "vm_mu s = 1".
    Explanation: the transcript equals [po1_strict_trace_A] AND the
    state is one of the two μ-collision witnesses [po1_state_A] /
    [po1_state_B] from NecessityOfMuLedger.

    The budget and recompute fields are filled in with placeholder
    values; this theorem does not depend on the cost numbers (it
    refutes sound+complete unconditionally), but the record demands
    a [nat] in each slot.
*)

Definition mu_eq_one_claim (s : VMState) : Prop := s.(vm_mu) = 1.

Definition mu_collision_explains (s : VMState) (t : BareTranscript) : Prop :=
  t = po1_strict_trace_A /\ (s = po1_state_A \/ s = po1_state_B).

Definition mu_eq_one_problem : BareVerificationProblem :=
  mk_bvp
    mu_eq_one_claim
    mu_collision_explains
    0   (* bare_cheap_budget — unused in this theorem *)
    1.  (* bare_recompute_cost — unused in this theorem *)

(* -------------------------------------------------------------------- *)
(** ** Supporting facts about the witness states.

    These are *re-exports* of NecessityOfMuLedger lemmas in the
    verifier framing; their content is `vm_mu po1_state_A = 1` and
    `vm_mu po1_state_B = 0` from the kernel.
*)

Lemma witness_A_satisfies_claim :
  mu_eq_one_claim po1_state_A.
Proof.
  unfold mu_eq_one_claim.
  apply po1_cond4_trace_A_mu_paid.
Qed.

Lemma witness_B_violates_claim :
  ~ mu_eq_one_claim po1_state_B.
Proof.
  unfold mu_eq_one_claim.
  intros Heq.
  rewrite po1_cond5_trace_B_mu_zero in Heq.
  discriminate Heq.
Qed.

Lemma witness_A_explains_shared :
  mu_collision_explains po1_state_A po1_strict_trace_A.
Proof.
  split.
  - reflexivity.
  - left. reflexivity.
Qed.

Lemma witness_B_explains_shared :
  mu_collision_explains po1_state_B po1_strict_trace_A.
Proof.
  split.
  - reflexivity.
  - right. reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(** ** The headline impossibility. *)

(** No [BareVerifier] is simultaneously [bare_sound] and
    [bare_complete] on [mu_eq_one_problem].

    The transcript [po1_strict_trace_A] is explained by both
    [po1_state_A] (which satisfies the claim) and [po1_state_B]
    (which doesn't). Completeness forces the verifier to accept
    the transcript on the honest [po1_state_A]; soundness then
    requires the claim to hold for every explanation, including
    [po1_state_B]; but the claim is false at [po1_state_B].
*)
Theorem bare_setting_no_sound_complete_verifier :
  ~ exists V : BareVerifier,
      bare_sound mu_eq_one_problem V /\
      bare_complete mu_eq_one_problem V.
Proof.
  intros [V [Hsound Hcomplete]].
  (* Completeness applied to (po1_state_A, po1_strict_trace_A):
     since A satisfies the claim and explains the trace, V accepts. *)
  assert (Haccepts : bv_decide V po1_strict_trace_A = true).
  { apply (Hcomplete po1_state_A po1_strict_trace_A).
    - apply witness_A_satisfies_claim.
    - apply witness_A_explains_shared. }
  (* Soundness applied to the accepted trace at po1_state_B:
     the claim must hold for B's explanation. *)
  pose proof (Hsound po1_strict_trace_A Haccepts po1_state_B
                     witness_B_explains_shared) as Hclaim_B.
  (* But the claim is false at B. *)
  apply witness_B_violates_claim. exact Hclaim_B.
Qed.

Print Assumptions bare_setting_no_sound_complete_verifier.

(* -------------------------------------------------------------------- *)
(** ** Stronger corollary: existence of an obstruction.

    The above theorem refutes simultaneous sound+complete; a slightly
    different framing useful downstream is: there is a specific
    transcript [t] and a specific honest state [s] such that any
    sound verifier must reject [t], blocking completeness on the
    honest run that produced [t].
*)

Corollary bare_sound_blocks_honest_acceptance :
  forall V : BareVerifier,
    bare_sound mu_eq_one_problem V ->
    bv_decide V po1_strict_trace_A = false.
Proof.
  intros V Hsound.
  destruct (bv_decide V po1_strict_trace_A) eqn:Hdec.
  - (* V accepted — soundness gives a contradiction at po1_state_B. *)
    exfalso.
    apply witness_B_violates_claim.
    apply (Hsound po1_strict_trace_A Hdec po1_state_B
                  witness_B_explains_shared).
  - reflexivity.
Qed.

Print Assumptions bare_sound_blocks_honest_acceptance.
