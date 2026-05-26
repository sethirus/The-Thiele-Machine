(** * VerifierEscape_Substrate.v — substrate-trust escape.

    The bare-setting impossibility ([VerifierImpossibility.v]) ruled out
    sound+complete verifiers whose transcript carries only the strict
    classical projection of a VM execution. Here is the
    **substrate-trust escape**: hand the verifier the full [VMState]
    of the prover — [vm_mu], [vm_certified], the ledger — and a cheap
    deterministic verifier becomes both sound and complete for
    [vm_mu]-sensitive claims.

    The "trust" in substrate-trust is the assumption that the prover
    runs on an A2-respecting substrate that genuinely reports its μ
    rather than fabricating it. Under that trust, the verifier merely
    reads the ledger. This escape is the option the structural axis
    makes available; the [VerifierExhaustiveness.v] factorisation
    impossibility shows it is one of the only options.
*)

From Coq Require Import List Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState.
Require Import NecessityOfMuLedger.
Require Import VerifierModel.
Require Import VerifierImpossibility.

(* -------------------------------------------------------------------- *)
(** ** The substrate-certified transcript.

    A substrate transcript is a list of full [VMState] snapshots — the
    classical projection is augmented with the hidden coordinates
    (vm_mu, vm_certified, ledger structure, graph). The verifier reads
    the last snapshot and trusts the substrate to have reported its
    state truthfully.
*)

Definition SubstrateTranscript : Type := list VMState.

(** The last (most recent) state in a transcript, or [None] if empty. *)
Definition substrate_last (t : SubstrateTranscript) : option VMState :=
  match t with
  | [] => None
  | _ => Some (last t (hd (hd po1_init nil) t))
  end.

(* A simpler, total accessor: explicit nth_error of the last element. *)
Definition substrate_last_total (t : SubstrateTranscript) (default : VMState)
  : VMState :=
  last t default.

(* -------------------------------------------------------------------- *)
(** ** Substrate verifier for "vm_mu s = 1".

    The verifier reads the last state's [vm_mu] field and accepts iff
    it equals 1. Cost: a single dereference (modelled as [1]).
*)

Definition substrate_decide_mu_eq_one (t : SubstrateTranscript) : bool :=
  match t with
  | [] => false
  | _ => Nat.eqb (substrate_last_total t po1_init).(vm_mu) 1
  end.

Definition substrate_cost_one (t : SubstrateTranscript) : nat := 1.

(** The substrate explanation relation: the prover state [s] is the last
    element of the transcript. This is a functional relation — each
    non-empty transcript has a unique explanation. *)
Definition substrate_explains (s : VMState) (t : SubstrateTranscript) : Prop :=
  match t with
  | [] => False
  | _ => s = substrate_last_total t po1_init
  end.

(* -------------------------------------------------------------------- *)
(** ** Sanity facts about the substrate explanation. *)

(** Non-empty transcripts have a unique explanation: every two
    explanations of the same transcript are equal. *)
Lemma substrate_explains_functional :
  forall (s1 s2 : VMState) (t : SubstrateTranscript),
    substrate_explains s1 t ->
    substrate_explains s2 t ->
    s1 = s2.
Proof.
  intros s1 s2 t Hexp1 Hexp2.
  destruct t as [|h tl] eqn:Ht.
  - contradiction.
  - unfold substrate_explains in Hexp1, Hexp2. rewrite Hexp1, Hexp2. reflexivity.
Qed.

(** If the last state's μ equals 1, the substrate verifier accepts. *)
Lemma substrate_decide_accepts :
  forall (s : VMState) (t : SubstrateTranscript),
    substrate_explains s t ->
    s.(vm_mu) = 1 ->
    substrate_decide_mu_eq_one t = true.
Proof.
  intros s t Hexp Hmu.
  destruct t as [|h tl] eqn:Ht.
  - contradiction.
  - unfold substrate_decide_mu_eq_one. unfold substrate_explains in Hexp.
    rewrite <- Hexp. rewrite Hmu. reflexivity.
Qed.

(** If the substrate verifier accepts, the last state's μ equals 1. *)
Lemma substrate_decide_implies_mu_eq_one :
  forall (s : VMState) (t : SubstrateTranscript),
    substrate_explains s t ->
    substrate_decide_mu_eq_one t = true ->
    s.(vm_mu) = 1.
Proof.
  intros s t Hexp Hdec.
  destruct t as [|h tl] eqn:Ht.
  - contradiction.
  - unfold substrate_decide_mu_eq_one in Hdec.
    unfold substrate_explains in Hexp.
    rewrite Hexp.
    apply Nat.eqb_eq. exact Hdec.
Qed.

(* -------------------------------------------------------------------- *)
(** ** The escape: sound, complete, and cheap.

    These three theorems pin down what the substrate-certified
    transcript buys: cheap sound verification of [vm_mu = 1], no
    cryptography, no rounds.
*)

(** Soundness: every explanation of an accepted transcript satisfies the claim. *)
Theorem substrate_verifier_sound :
  forall t : SubstrateTranscript,
    substrate_decide_mu_eq_one t = true ->
    forall s : VMState,
      substrate_explains s t -> s.(vm_mu) = 1.
Proof.
  intros t Hdec s Hexp.
  apply (substrate_decide_implies_mu_eq_one s t Hexp Hdec).
Qed.

(** Completeness: any honest state satisfying the claim, together with
    a transcript explaining it, leads to acceptance. *)
Theorem substrate_verifier_complete :
  forall (s : VMState) (t : SubstrateTranscript),
    s.(vm_mu) = 1 ->
    substrate_explains s t ->
    substrate_decide_mu_eq_one t = true.
Proof.
  intros s t Hmu Hexp.
  apply (substrate_decide_accepts s t Hexp Hmu).
Qed.

(** Cheapness: the verifier's cost is constantly [1], much less than
    the recompute cost of re-executing the prover's program. *)
Theorem substrate_verifier_cheap :
  forall t : SubstrateTranscript,
    substrate_cost_one t = 1.
Proof. intro. reflexivity. Qed.

(** Combined headline: there exists a sound+complete+cheap substrate
    verifier for the μ-sensitive claim that defeated every bare verifier. *)
Theorem substrate_escape_succeeds :
  exists (decide : SubstrateTranscript -> bool)
         (cost   : SubstrateTranscript -> nat),
    (forall t, decide t = true ->
       forall s, substrate_explains s t -> s.(vm_mu) = 1) /\
    (forall s t,
       s.(vm_mu) = 1 ->
       substrate_explains s t ->
       decide t = true) /\
    (forall t, cost t = 1).
Proof.
  exists substrate_decide_mu_eq_one, substrate_cost_one.
  split; [|split].
  - exact substrate_verifier_sound.
  - exact substrate_verifier_complete.
  - exact substrate_verifier_cheap.
Qed.

Print Assumptions substrate_escape_succeeds.
