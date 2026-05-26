(** * VerifierExhaustiveness.v — factorisation impossibility for sound verification.

    The three escape files exhibit sound complete verifiers for the
    μ-sensitive claim under three structurally distinct transcript
    augmentations (substrate, hardness, interaction). The natural next
    question is whether some richer transcript could allow a sound
    complete verifier that still factors through the classical
    projection of the transcript. The answer is no.

    What we prove here:

      **Any verifier on any transcript type that is sound and complete
        for the μ-sensitive claim cannot factor through the classical
        projection of the transcript.**

    That is, soundness + completeness forces the verifier to depend on
    non-classical structural information in the transcript. The three
    escapes are three concrete ways of carrying that structural
    information; this theorem says they are not just three options
    among many — they are three instances of the only option, which is
    "the transcript carries non-classical structure and the verifier
    reads it."

    Full meta-theoretic exhaustiveness — whether the substrate,
    hardness, and interaction routes partition the space of
    non-classical structures — sits outside Coq's object-level type
    theory. This file reduces that meta-question to the structural-
    enrichment question, which is what the kernel can speak to.
*)

From Coq Require Import List Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState.
Require Import NecessityOfMuLedger.
Require Import VerifierModel.
Require Import VerifierImpossibility.

(* -------------------------------------------------------------------- *)
(** ** Generalized verifier and projection.

    [T] is an arbitrary transcript type. [proj_classical] is the
    forgetful map to the bare classical transcript — every escape
    transcript admits such a projection (it discards the extra
    structure).
*)

(** A verifier [V : T -> bool] *factors through* the classical
    projection iff its value depends only on [proj t]. Equivalently,
    if [proj t1 = proj t2] then [V t1 = V t2]. *)
Definition factors_classical {T : Type} (proj : T -> BareTranscript)
                             (V : T -> bool) : Prop :=
  forall t1 t2 : T, proj t1 = proj t2 -> V t1 = V t2.

(* -------------------------------------------------------------------- *)
(** ** The factorization-impossibility theorem.

    If V on a generic transcript type T factors through the classical
    projection AND there exist two T-transcripts that map to the same
    classical transcript but explain states with different μ — one
    satisfying μ=1, one not — then V cannot be both sound and complete
    on the μ=1 problem.

    The hypotheses encode that T has at least the structural richness
    of the bare-impossibility scenario: two distinct elements expressing
    the two witness states (A and B) and still projecting to the same
    bare transcript. The collision is what makes the factorisation a
    contradiction.
*)

(** **The factorization-impossibility theorem.**
    V cannot factor through the classical projection: if it did,
    V t_A = V t_B (since they project the same), but completeness
    forces V t_A = true and soundness forces V t_B = false.

    All structural premises (collision, explanation pair, soundness,
    completeness) are explicit forall hypotheses on the theorem
    statement — no Section-local Variables or Hypotheses are used,
    so the theorem carries its own assumption surface and the kernel
    audit reports zero project-local axioms. *)
Theorem V_does_not_factor_through_classical :
  forall (T : Type) (proj : T -> BareTranscript)
         (explains_T : VMState -> T -> Prop)
         (t_A t_B : T) (V : T -> bool),
    proj t_A = proj t_B ->
    explains_T po1_state_A t_A ->
    explains_T po1_state_B t_B ->
    (forall t : T, V t = true ->
       forall s : VMState, explains_T s t -> s.(vm_mu) = 1) ->
    (forall (s : VMState) (t : T),
       s.(vm_mu) = 1 -> explains_T s t -> V t = true) ->
    ~ factors_classical proj V.
Proof.
  intros T proj explains_T t_A t_B V
         proj_collision explains_T_A explains_T_B V_sound V_complete Hfac.
  (* Completeness forces V t_A = true *)
  assert (HA : V t_A = true).
  { apply (V_complete po1_state_A t_A).
    - apply po1_cond4_trace_A_mu_paid.
    - exact explains_T_A. }
  (* Factorization carries acceptance to t_B *)
  assert (HB : V t_B = true).
  { rewrite <- (Hfac t_A t_B proj_collision). exact HA. }
  (* Soundness applied to t_B with state B yields μ B = 1 *)
  pose proof (V_sound t_B HB po1_state_B explains_T_B) as HmuB.
  (* But μ B = 0 *)
  rewrite po1_cond5_trace_B_mu_zero in HmuB. discriminate.
Qed.

Print Assumptions V_does_not_factor_through_classical.

(* -------------------------------------------------------------------- *)
(** ** Corollary: structural-access principle.

    Combining the factorisation impossibility with the existence of the
    three escapes ([VerifierEscape_Substrate], [VerifierEscape_Hardness],
    [VerifierEscape_Interaction]), we get a clean statement:

    *Sound + complete verification of μ-sensitive claims requires
    structural access to the transcript beyond its classical
    projection.*

    Concretely: three structural mechanisms suffice — substrate,
    hardness, interaction — and every sound complete verifier on the
    μ-sensitive problem uses such a mechanism (the contrapositive of
    the factorisation theorem).

    The strongest formal claim Coq carries here, without meta-theoretic
    quantification over transcript types: any verifier sound and
    complete on the μ-sensitive claim cannot be a function of the
    classical projection. Whether the three named mechanisms exhaust
    the space of sufficient mechanisms is the meta-question.
*)

Theorem verifier_corollary_summary :
  (* Bare-setting impossibility: *)
  (~ exists V : BareVerifier,
      bare_sound mu_eq_one_problem V /\
      bare_complete mu_eq_one_problem V)
  /\
  (* Sound+complete verification requires structural access
     beyond the classical projection: *)
  (forall (T : Type) (proj : T -> BareTranscript)
          (explains_T : VMState -> T -> Prop)
          (t_A t_B : T) (V : T -> bool),
     proj t_A = proj t_B ->
     explains_T po1_state_A t_A ->
     explains_T po1_state_B t_B ->
     (forall t, V t = true ->
        forall s, explains_T s t -> s.(vm_mu) = 1) ->
     (forall s t, s.(vm_mu) = 1 -> explains_T s t -> V t = true) ->
     ~ factors_classical proj V).
Proof.
  split.
  - exact bare_setting_no_sound_complete_verifier.
  - intros T proj explains_T t_A t_B V Hproj HA HB Hsound Hcomplete.
    eapply V_does_not_factor_through_classical with
      (proj := proj) (explains_T := explains_T) (t_A := t_A) (t_B := t_B); eauto.
Qed.

Print Assumptions verifier_corollary_summary.
