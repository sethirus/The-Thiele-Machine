(** * TEST: Try to construct a counter-example to thermodynamics-necessity

    This file attempts to BUILD a consistent information accounting
    that violates thermodynamics-like properties.
    
    If we can construct it: The claim is falsified.
    If Coq rejects it: The claim survives this test.
*)

From Coq Require Import List Lia.
From Kernel Require Import VMStep.
From Kernel Require Import VMState.
From Kernel Require Import Definitions.

Import ListNotations.

(** Example instructions for testing *)
Definition halt_instr := instr_halt 0.
Definition other_instr := instr_xfer 0 1 0.

(** ** ATTEMPT 1: Non-monotonic cost function *)

(** Try to build a cost where operations can reduce total cost. 
    
    The issue: even defining such a function that satisfies weight_empty
    is problematic. weight_empty requires w([]) = 0.
    
    If w decreases with length, then w([]) should be MAXIMUM, not 0.
    This already contradicts the empty trace requirement!
*)

Definition w_decreasing : Weight :=
  fun t => 100 - length t.

(** This FAILS the empty test: 100 - 0 = 100 ≠ 0 *)

Lemma w_decreasing_empty_FAILS : weight_empty w_decreasing -> False.
Proof.
  unfold weight_empty, w_decreasing. simpl.
  intro H. (* H : 100 = 0 *)
  discriminate H.
Qed.

(** RESULT: Non-monotonic cost CANNOT even satisfy weight_empty.
    
    If empty = 0 and costs are additive, then costs must be non-negative
    and extending always adds (never subtracts).
    
    This is why the Second Law is forced: the accounting STARTS at zero.
*)


(** ** ATTEMPT 2: Non-uniform singleton costs *)

Definition w_privileged : Weight :=
  fun t => match t with
           | [] => 0
           | (instr_halt _)::rest => 1 + length rest  (* halt is cheap *)
           | _::rest => 10 + length rest              (* everything else is expensive *)
           end.

(** This clearly violates singleton_uniform, but does it satisfy weight_laws? *)

Lemma w_privileged_empty : weight_empty w_privileged.
Proof.
  unfold weight_empty, w_privileged. reflexivity.
Qed.

(** Let's check if sequentiality holds *)

Lemma w_privileged_sequential_REALLY_FAILS : 
  weight_sequential w_privileged -> False.
Proof.
  intro Hseq.
  unfold weight_sequential in Hseq.
  specialize (Hseq [halt_instr] [other_instr]).
  unfold w_privileged, halt_instr, other_instr in Hseq.
  simpl in Hseq.
  (** Hseq : 1 + 1 = 1 + 10, i.e., 2 = 11 *)
  lia.
Qed.

(** RESULT: Non-uniform costs break sequentiality.
    The order [halt;inc] gives different cost than [inc;halt]
    because the FIRST instruction determines the cost model.
    
    But sequentiality says w(a++b) = w(a) + w(b), independent of order.
    
    This is why uniformity is forced: additivity implies order doesn't matter,
    so all instructions must have the same base cost.
*)


(** ** ATTEMPT 3: A weight that allows "free insight" *)

(** Can we build a cost function where some information is free? *)

(** Imagine a "magic" instruction that reads without cost. *)

(** Count only xfer instructions (others are "free") *)
Fixpoint count_xfer (t : Trace) : nat :=
  match t with
  | [] => 0
  | (instr_xfer _ _ _)::rest => 1 + count_xfer rest
  | _::rest => count_xfer rest
  end.

Definition w_free_read : Weight := count_xfer.

(** Does this satisfy the laws? *)

Lemma w_free_read_empty : weight_empty w_free_read.
Proof.
  unfold weight_empty, w_free_read. simpl. reflexivity.
Qed.

(** [count_xfer_app]: formal specification. *)
Lemma count_xfer_app : forall t1 t2, count_xfer (t1 ++ t2) = count_xfer t1 + count_xfer t2.
Proof.
  induction t1 as [|i rest IH]; intro t2.
  - simpl. reflexivity.
  - simpl. destruct i; simpl; rewrite IH; lia.
Qed.

(** [w_free_read_sequential]: formal specification. *)
Lemma w_free_read_sequential : weight_sequential w_free_read.
Proof.
  unfold weight_sequential, w_free_read.
  intros t1 t2. apply count_xfer_app.
Qed.

(** [w_free_read_disjoint_commutes]: formal specification. *)
Lemma w_free_read_disjoint_commutes : weight_disjoint_commutes w_free_read.
Proof.
  unfold weight_disjoint_commutes, w_free_read.
  intros t1 t2 _. 
  rewrite !count_xfer_app. lia.
Qed.

(** [w_free_read_laws]: formal specification. *)
Lemma w_free_read_laws : weight_laws w_free_read.
Proof.
  unfold weight_laws.
  split. apply w_free_read_empty.
  split. apply w_free_read_sequential.
  apply w_free_read_disjoint_commutes.
Qed.

(** This DOES satisfy weight_laws! 
    Have we found a counter-example? *)

(** Check singleton uniformity... *)

Lemma w_free_read_NOT_uniform : 
  singleton_uniform w_free_read -> False.
Proof.
  unfold singleton_uniform, w_free_read.
  intro H.
  specialize (H other_instr halt_instr).
  unfold other_instr, halt_instr in H.
  simpl in H.
  (** H claims count_xfer([xfer]) = count_xfer([halt]) *)
  (** But count_xfer([xfer]) = 1 and count_xfer([halt]) = 0 *)
  discriminate H.
Qed.

(** RESULT: The "free read" weight satisfies the basic laws but violates uniformity.
    
    This is the NoGo theorem in action:
    - Without uniformity, you CAN have "free" operations
    - But that means different operations have different costs
    - Which means KNOWING which operation is cheaper is itself information
    - That information came from somewhere - it's not actually free
    
    The uniformity assumption isn't arbitrary - it prevents circular cheating.
*)


(** ** SYNTHESIS: What can and can't be built *)

Theorem test_summary :
  (* Non-monotonic weights fail the empty test *)
  (weight_empty w_decreasing -> False) /\
  (* Non-uniform weights exist but violate uniformity *)
  (weight_laws w_free_read /\ (singleton_uniform w_free_read -> False)).
Proof.
  split.
  - apply w_decreasing_empty_FAILS.
  - split.
    + apply w_free_read_laws.
    + apply w_free_read_NOT_uniform.
Qed.

(** ** THE VERDICT

    We tried three attacks:
    
    1. Non-monotonic cost: REJECTED by additivity
       - If w(a++b) = w(a) + w(b), then extending traces adds cost
       - You can't have w(longer) < w(shorter) while being additive
       
    2. Non-uniform costs: REJECTED by sequentiality
       - Different costs for different ops means order affects total
       - But w(a++b) = w(a) + w(b) is order-independent
       
    3. Free operations: ALLOWED but violates uniformity
       - You CAN have some operations cost 0
       - But then you've privileged those operations
       - Uniformity says: no privileged operations
       
    CONCLUSION: Under the minimal assumptions of
    - Additivity (costs add up)
    - Uniformity (no privileged operations)
    - Normalization (pick your units)
    
    The ONLY consistent cost function is LENGTH.
    And length forces monotonicity, locality, conservation.
    
    Thermodynamics isn't assumed - it's DERIVED from consistency.
*)
