From Coq Require Import QArith Lia Arith.PeanoNat.
Import QArith.
Open Scope Q_scope.

From ThieleMachine Require Import InfoTheory.

(** Deliverable: 1-bit entropy reduction is a 1-bit μ lower bound.

    Specializes the general theorem [mu_bounds_shannon_entropy] to the concrete
    case before=2, after=1.

    This is the smallest nontrivial, falsifiable instance:
      - shrinking a hypothesis set from 2 to 1 eliminates exactly 1 bit
      - therefore any μ-cost must be ≥ 1 (and is tight when query_bytes=0)
*)

Module DeliverableMuEntropyOneBit.

(** [state_reduction_entropy_two_to_one]: formal specification. *)
Lemma state_reduction_entropy_two_to_one :
  state_reduction_entropy 2%positive 1%positive = (1%Q).
Proof.
  (* Closed computation: log2_up(2)=1 and log2(1)=0. *)
  vm_compute.
  reflexivity.
Qed.

(** [information_cost_two_to_one]: formal specification. *)
Lemma information_cost_two_to_one :
  information_cost 2%positive 1%positive = (1%Q).
Proof.
  unfold information_cost.
  exact state_reduction_entropy_two_to_one.
Qed.

(** [mu_cost_ge_one_bit]: formal specification. *)
Theorem mu_cost_ge_one_bit :
  forall (query_bytes : nat),
    (1%Q <= mu_cost query_bytes 2%positive 1%positive)%Q.
Proof.
  intro query_bytes.
  assert (Hlt : (1%positive < 2%positive)%positive) by reflexivity.
  pose proof (mu_bounds_shannon_entropy query_bytes 2%positive 1%positive Hlt) as Hbound.
  (* Rewrite the RHS to the concrete 1-bit value. *)
  rewrite information_cost_two_to_one in Hbound.
  exact Hbound.
Qed.

(** [mu_cost_tight_when_query_empty]: formal specification. *)
Corollary mu_cost_tight_when_query_empty :
  mu_cost 0 2%positive 1%positive = (1%Q).
Proof.
  unfold mu_cost.
  rewrite information_cost_two_to_one.
  unfold question_cost.
  vm_compute.
  reflexivity.
Qed.

End DeliverableMuEntropyOneBit.
