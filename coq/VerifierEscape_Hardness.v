(** * VerifierEscape_Hardness.v: the hardness route, as a commitment contract.

    The formal model contains no computational hardness assumption; what a
    deployed system would get from hardness is stated as an exact contract.
    The bare-setting
    impossibility rules out an abstract unit-cost verifier that is both
    sound and complete for a mu-sensitive claim when its transcript carries
    only the classical projection of a run. The hardness escape adds one
    thing to the transcript: a commitment bit. In a real cryptographic
    system the commitment would be an unforgeable signature, a SNARK, a hash
    revelation; here it is a bit. The contract requires that this bit states
    whether the claim holds for every explaining state.

    That contract is [CommitmentBitContract]. It is stated against a relation
    [explains] that says which transcripts each state can stand behind,
    adversarial ones included. It has two fields.

    - Binding: a state that stands behind a transcript with the bit set
      satisfies the claim. Forging the bit is impossible.
    - Honesty: a state that satisfies the claim only stands behind
      transcripts with the bit set. The honest prover always commits.

    Under that contract the verifier that reads the bit is sound and
    complete in the same universal sense the bare setting refutes
    ([commitment_contract_verifier]). The contract is not automatic: it holds
    for the definition that sets the bit from the claim
    ([honest_commitments_satisfy_contract]) and fails when an unchecked bit can
    be set independently ([unchecked_bit_violates_contract]).
    This is a verifier construction from an exact disclosure contract.
    It supplies neither a computational hardness reduction nor a security
    parameter or adversary model. The constant cost is an abstract price
    for reading the bit, not the cost of checking a cryptographic proof.
    Whether a real commitment scheme meets the contract is a question for
    cryptography, not for this kernel. *)

From Coq Require Import List Arith.PeanoNat Bool.
Import ListNotations.

From Kernel Require Import VMState.
Require Import NecessityOfMuLedger.
Require Import VerifierModel.
Require Import VerifierImpossibility.

(** ** Commitment-augmented transcripts *)

(** The bare transcript paired with a commitment bit. In a deployed system
    the bit stands for a signature, a proof, or an inclusion path; here it
    is the verdict of checking one. *)
Definition CommitmentTranscript : Type := BareTranscript * bool.

Definition ct_bare (t : CommitmentTranscript) : BareTranscript := fst t.
Definition ct_commitment (t : CommitmentTranscript) : bool := snd t.

(** ** The verifier *)

(** Accept exactly when the commitment is set. Unit cost. *)
Definition commitment_decide (t : CommitmentTranscript) : bool := ct_commitment t.

Definition commitment_cost (t : CommitmentTranscript) : nat := 1.

Theorem commitment_verifier_abstract_unit_cost :
  forall t : CommitmentTranscript, commitment_cost t = 1.
Proof. reflexivity. Qed.

Section CommitmentContract.

(** Which transcripts each state can stand behind, forged ones included. *)
Variable explains : VMState -> CommitmentTranscript -> Prop.

Record CommitmentBitContract : Prop := mk_hh {
  hh_binding :
    forall s t, explains s t -> ct_commitment t = true -> s.(vm_mu) = 1;
  hh_honest :
    forall s t, explains s t -> s.(vm_mu) = 1 -> ct_commitment t = true
}.

(** The escape: under the hypothesis, a unit-cost verifier is sound and
    complete. *)
Theorem commitment_contract_verifier :
  CommitmentBitContract ->
  exists (decide : CommitmentTranscript -> bool)
         (cost   : CommitmentTranscript -> nat),
    (forall t, decide t = true -> forall s, explains s t -> s.(vm_mu) = 1) /\
    (forall s t, s.(vm_mu) = 1 -> explains s t -> decide t = true) /\
    (forall t, cost t = 1).
Proof.
  intro H. exists commitment_decide, commitment_cost.
  split.
  - intros t Hbit s Hex. exact (hh_binding H s t Hex Hbit).
  - split.
    + intros s t Hmu Hex. exact (hh_honest H s t Hex Hmu).
    + exact commitment_verifier_abstract_unit_cost.
Qed.

End CommitmentContract.

(** ** The hypothesis can hold *)

(** Honest commitments: the bare view is one the state explains, and the
    bit says whether the claim holds. *)
Definition honest_commitment_explains
    (s : VMState) (t : CommitmentTranscript) : Prop :=
  mu_collision_explains s (ct_bare t) /\ ct_commitment t = Nat.eqb s.(vm_mu) 1.

Theorem honest_commitments_satisfy_contract :
  CommitmentBitContract honest_commitment_explains.
Proof.
  split.
  - intros s t [_ Hbit] Hc. rewrite Hc in Hbit.
    apply Nat.eqb_eq. symmetry. exact Hbit.
  - intros s t [_ Hbit] Hmu. rewrite Hbit. rewrite Hmu. reflexivity.
Qed.

(** ** The hypothesis carries weight *)

(** If the bit can be set by anyone, the state with the claim false stands
    behind a committed transcript, and binding fails. *)
Definition unchecked_bit_explains
    (s : VMState) (t : CommitmentTranscript) : Prop :=
  mu_collision_explains s (ct_bare t).

Theorem unchecked_bit_violates_contract :
  ~ CommitmentBitContract unchecked_bit_explains.
Proof.
  intros [Hbind _].
  apply witness_B_violates_claim.
  apply (Hbind po1_state_B (po1_strict_trace_A, true)); [| reflexivity].
  unfold unchecked_bit_explains, mu_collision_explains, ct_bare. simpl.
  split; [reflexivity | right; reflexivity].
Qed.

(** Under honest commitments the bare collision pair lifts to two
    transcripts with the same bare view and different bits. The verifier
    escapes the bare-setting impossibility by reading that bit. *)
Theorem honest_lift_separates_collision :
  honest_commitment_explains po1_state_A (po1_strict_trace_A, true) /\
  honest_commitment_explains po1_state_B (po1_strict_trace_A, false).
Proof.
  unfold honest_commitment_explains, mu_collision_explains, ct_bare, ct_commitment.
  simpl.
  split; split.
  - split; [reflexivity | left; reflexivity].
  - reflexivity.
  - split; [reflexivity | right; reflexivity].
  - reflexivity.
Qed.

Print Assumptions commitment_contract_verifier.
