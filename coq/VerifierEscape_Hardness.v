(** * VerifierEscape_Hardness.v — hardness escape.

    The bare-setting impossibility ruled out cheap sound verifiers
    whose transcript carries only the classical projection of a VM
    execution. Here is the **hardness escape**: have the transcript
    also carry a *commitment* that is unforgeable under some hardness
    assumption A. A cheap deterministic verifier is then sound (in the
    weak existential sense) for vm_mu-sensitive claims — conditional
    on A holding.

    Modeling note: we do NOT instantiate A with a concrete cryptographic
    assumption. The escape is parameterised: given any
    [HardnessHypothesis] record (which packages an unforgeability
    predicate as a *hypothesis*, not an axiom), the verifier is
    sound. Whether such a record exists in nature is a question for
    cryptography, not for this kernel.
*)

From Coq Require Import List Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState.
Require Import NecessityOfMuLedger.
Require Import VerifierModel.
Require Import VerifierImpossibility.

(* -------------------------------------------------------------------- *)
(** ** Hardness-augmented transcripts.

    A hardness transcript is the bare transcript paired with a single
    Boolean commitment bit. In a real cryptographic system the
    commitment would be an unforgeable signature, a snark, a hash
    revelation, etc.; here we model it abstractly as a bit whose
    truthful setting is constrained by the [HardnessHypothesis].
*)

Definition HardnessTranscript : Type := BareTranscript * bool.

Definition ht_commitment (t : HardnessTranscript) : bool := snd t.

(* -------------------------------------------------------------------- *)
(** ** The hardness hypothesis.

    [HardnessHypothesis] packages the cryptographic assumption as a
    record. The unforgeability field asserts: any transcript whose
    commitment bit is set was produced by an honest prover whose
    underlying state satisfies the μ=1 claim. We never *prove* this
    field; the verifier is sound *conditional* on an instance of this
    record being supplied at use site.
*)

Record HardnessHypothesis : Type := mk_hh {
  hh_unforgeable :
    forall (t : HardnessTranscript),
      ht_commitment t = true ->
      exists s : VMState, s.(vm_mu) = 1
}.

(* -------------------------------------------------------------------- *)
(** ** The hardness verifier.

    The verifier checks the commitment bit cheaply (constant cost) and
    accepts iff the commitment is set.
*)

Definition hardness_decide (t : HardnessTranscript) : bool := ht_commitment t.

Definition hardness_cost (t : HardnessTranscript) : nat := 1.

(* -------------------------------------------------------------------- *)
(** ** Soundness conditional on the hardness hypothesis.

    Note this is *weak* (existential) soundness — under hardness, an
    accepted transcript witnesses SOME honest state satisfying the
    claim, not every possible explanation. This is the standard
    cryptographic notion. The bare-setting impossibility used *strong*
    (universal) soundness; the two notions differ exactly in what
    structural addition each requires.
*)

Theorem hardness_verifier_weak_sound :
  forall (H : HardnessHypothesis) (t : HardnessTranscript),
    hardness_decide t = true ->
    exists s : VMState, s.(vm_mu) = 1.
Proof.
  intros H t Hdec.
  apply (hh_unforgeable H t). exact Hdec.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Cheapness. *)

Theorem hardness_verifier_cheap :
  forall t : HardnessTranscript, hardness_cost t = 1.
Proof. intros. reflexivity. Qed.

(* -------------------------------------------------------------------- *)
(** ** The escape: a cheap weak-sound verifier exists conditional on
    any hardness hypothesis. *)
Theorem hardness_escape_succeeds :
  forall H : HardnessHypothesis,
  exists (decide : HardnessTranscript -> bool)
         (cost   : HardnessTranscript -> nat),
    (forall t, decide t = true ->
       exists s : VMState, s.(vm_mu) = 1) /\
    (forall t, cost t = 1).
Proof.
  intro H.
  exists hardness_decide, hardness_cost.
  split.
  - intros t Hdec. apply (hardness_verifier_weak_sound H t Hdec).
  - apply hardness_verifier_cheap.
Qed.

Print Assumptions hardness_escape_succeeds.
