(** * VerifierEscape_Interaction.v — interaction escape.

    The bare-setting impossibility ruled out cheap sound verifiers
    seeing only the classical projection. Here is the **interaction
    escape**: let the verifier issue a fresh challenge after seeing
    the transcript and inspect the prover's response. The cheap
    deterministic verifier is then sound when the response set is
    rich enough to distinguish μ values.

    Modeling note: we use the *simplest possible* interaction model —
    one round, the prover sends a single value, the verifier checks
    it equals the claimed μ. This is not a serious interactive proof
    system (no error bounds, no public coins, no soundness amplification);
    it is the minimal structural addition needed to refute the bare
    impossibility. The factorisation impossibility in
    [VerifierExhaustiveness.v] cares about the *existence* of an
    escape, not its sophistication.
*)

From Coq Require Import List Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState.
Require Import NecessityOfMuLedger.
Require Import VerifierModel.
Require Import VerifierImpossibility.

(* -------------------------------------------------------------------- *)
(** ** Interactive transcripts.

    An interactive transcript is the bare transcript paired with the
    prover's response to the verifier's challenge. In this simple
    model the verifier's challenge is fixed ("tell me your μ") so the
    response is a single nat.
*)

Definition InteractiveTranscript : Type := BareTranscript * nat.

Definition it_response (t : InteractiveTranscript) : nat := snd t.

(* -------------------------------------------------------------------- *)
(** ** Honest prover's response function.

    An honest prover responds with its actual μ. We model honesty as
    a property of the (state, response) pair rather than as a
    behavioural restriction.
*)

Definition honest_response (s : VMState) (r : nat) : Prop := s.(vm_mu) = r.

(** Explanation relation: the transcript is interactive-honest iff
    its response equals the explaining state's μ. *)
Definition interactive_explains (s : VMState) (t : InteractiveTranscript) : Prop :=
  honest_response s (it_response t).

(* -------------------------------------------------------------------- *)
(** ** Verifier for "μ = 1": accept iff the response is 1. *)

Definition interactive_decide (t : InteractiveTranscript) : bool :=
  Nat.eqb (it_response t) 1.

Definition interactive_cost (t : InteractiveTranscript) : nat := 1.

(* -------------------------------------------------------------------- *)
(** ** Soundness, completeness, cheapness. *)

(** Strong soundness: every honest-interactive explanation of an
    accepted transcript satisfies μ = 1. *)
Theorem interactive_verifier_sound :
  forall t : InteractiveTranscript,
    interactive_decide t = true ->
    forall s : VMState,
      interactive_explains s t -> s.(vm_mu) = 1.
Proof.
  intros t Hdec s Hexp.
  unfold interactive_explains, honest_response in Hexp.
  unfold interactive_decide in Hdec.
  apply Nat.eqb_eq in Hdec.
  rewrite Hexp. exact Hdec.
Qed.

(** Completeness: any honest state with μ = 1 is accepted on its
    matching interactive transcript. *)
Theorem interactive_verifier_complete :
  forall (s : VMState) (t : InteractiveTranscript),
    s.(vm_mu) = 1 ->
    interactive_explains s t ->
    interactive_decide t = true.
Proof.
  intros s t Hmu Hexp.
  unfold interactive_explains, honest_response in Hexp.
  unfold interactive_decide.
  rewrite <- Hexp. rewrite Hmu. reflexivity.
Qed.

Theorem interactive_verifier_cheap :
  forall t : InteractiveTranscript, interactive_cost t = 1.
Proof. intros. reflexivity. Qed.

Theorem interactive_escape_succeeds :
  exists (decide : InteractiveTranscript -> bool)
         (cost   : InteractiveTranscript -> nat),
    (forall t, decide t = true ->
       forall s, interactive_explains s t -> s.(vm_mu) = 1) /\
    (forall s t,
       s.(vm_mu) = 1 ->
       interactive_explains s t ->
       decide t = true) /\
    (forall t, cost t = 1).
Proof.
  exists interactive_decide, interactive_cost.
  split; [|split].
  - exact interactive_verifier_sound.
  - exact interactive_verifier_complete.
  - exact interactive_verifier_cheap.
Qed.

Print Assumptions interactive_escape_succeeds.
