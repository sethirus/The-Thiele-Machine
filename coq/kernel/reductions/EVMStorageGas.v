(** EVMStorageGas: what Ethereum prices when a storage slot is written.

    Source: the Ethereum execution specification, Prague fork,
    [src/ethereum/forks/prague/vm/instructions/storage.py] ([sstore]) and
    [src/ethereum/forks/prague/vm/gas.py] ([GasCosts]), at
    https://github.com/ethereum/execution-specs commit
    ecb68f21a7d28db101c769878184f6facb319da1. The gas and refund arithmetic
    of [sstore] is transcribed below for one slot within one transaction:
    STORAGE_SET 20000, COLD_STORAGE_WRITE 5000, COLD_STORAGE_ACCESS 2100,
    WARM_ACCESS 100, REFUND_STORAGE_CLEAR 4800.

    Scope. The model tracks the gas charged and the refund counter. It omits
    the stack, the call-stipend check, static-context rejection, other slots
    and accounts, and the end-of-transaction refund cap of EIP-3529 (refund
    at most a fifth of gas used), which applies after the counter this file
    tracks.

    Read the slot through the record axis: the record is "the slot holds a
    nonzero value." Two facts follow from the specification's arithmetic.

    - Writing a record that outlives the transaction is priced. For a slot
      empty at the start of the transaction, any sequence of stores that
      leaves it nonzero has gas charged minus refund of at least 20000
      ([persistent_write_priced]).
    - Writing a record and revoking it before the transaction ends is almost
      free: set then clear costs 2300 net for a cold slot
      ([revoked_write_nearly_free]), and the refund returns the rest.

    Ethereum prices the write that persists, and refunds the write that is
    taken back. That is the shape of the finite-machine result: a record
    whose write is free is one that can be revoked. *)

(* SCOPE NOTE: standalone proof scope. This transcribes the Ethereum
   specification's storage gas arithmetic; it imports no machine semantics on
   purpose, since it is a model of another specification. *)

From Coq Require Import List ZArith Lia Bool.
Import ListNotations.
Open Scope Z_scope.

Definition STORAGE_SET : Z := 20000.
Definition COLD_STORAGE_WRITE : Z := 5000.
Definition COLD_STORAGE_ACCESS : Z := 2100.
Definition WARM_ACCESS : Z := 100.
Definition REFUND_STORAGE_CLEAR : Z := 4800.

(** Gas charged by one SSTORE, as in [sstore]. *)
Definition sstore_gas (warm : bool) (original current new : Z) : Z :=
  (if warm then 0 else COLD_STORAGE_ACCESS) +
  (if (original =? current) && negb (current =? new) then
     (if original =? 0 then STORAGE_SET
      else COLD_STORAGE_WRITE - COLD_STORAGE_ACCESS)
   else WARM_ACCESS).

(** Change to the refund counter from one SSTORE, as in [sstore]. *)
Definition sstore_refund (original current new : Z) : Z :=
  if negb (current =? new) then
    (if negb (original =? 0) && negb (current =? 0) && (new =? 0)
     then REFUND_STORAGE_CLEAR else 0) +
    (if negb (original =? 0) && (current =? 0)
     then - REFUND_STORAGE_CLEAR else 0) +
    (if original =? new then
       (if original =? 0 then STORAGE_SET - WARM_ACCESS
        else COLD_STORAGE_WRITE - COLD_STORAGE_ACCESS - WARM_ACCESS)
     else 0)
  else 0.

(** One slot within one transaction: the original value, the current value,
    whether the slot has been accessed, and the gas and refund so far. *)
Record SlotRun : Type := {
  original : Z;
  current : Z;
  warm : bool;
  gas : Z;
  refund : Z
}.

Definition store (r : SlotRun) (new : Z) : SlotRun := {|
  original := original r;
  current := new;
  warm := true;
  gas := gas r + sstore_gas (warm r) (original r) (current r) new;
  refund := refund r + sstore_refund (original r) (current r) new
|}.

Definition run_stores (r : SlotRun) (news : list Z) : SlotRun :=
  fold_left store news r.

Definition fresh_slot : SlotRun :=
  {| original := 0; current := 0; warm := false; gas := 0; refund := 0 |}.

Definition net (r : SlotRun) : Z := gas r - refund r.

(** The invariant: while the slot is empty at the start of the transaction, the net charge is at
    least STORAGE_SET whenever the slot is nonzero, and never negative. *)
Lemma empty_slot_invariant : forall news r,
  original r = 0 ->
  net r >= (if current r =? 0 then 0 else STORAGE_SET) ->
  net (run_stores r news) >= (if current (run_stores r news) =? 0 then 0 else STORAGE_SET).
Proof.
  induction news as [| v news IH]; intros r Horig Hinv; [exact Hinv |].
  simpl. apply IH; [simpl; exact Horig |].
  revert Hinv. unfold net, store. simpl.
  unfold sstore_gas, sstore_refund, STORAGE_SET, COLD_STORAGE_WRITE,
    COLD_STORAGE_ACCESS, WARM_ACCESS, REFUND_STORAGE_CLEAR.
  rewrite Horig.
  destruct (warm r);
    repeat match goal with
           | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
           end;
    simpl; lia.
Qed.

Theorem persistent_write_priced : forall news,
  current (run_stores fresh_slot news) <> 0 ->
  net (run_stores fresh_slot news) >= STORAGE_SET.
Proof.
  intros news Hne.
  assert (H0 : net fresh_slot >= (if current fresh_slot =? 0 then 0 else STORAGE_SET))
    by (vm_compute; discriminate).
  pose proof (empty_slot_invariant news fresh_slot eq_refl H0) as H.
  destruct (current (run_stores fresh_slot news) =? 0) eqn:Hc;
    [apply Z.eqb_eq in Hc; contradiction | exact H].
Qed.

Theorem revoked_write_nearly_free :
  current (run_stores fresh_slot [1; 0]) = 0 /\
  net (run_stores fresh_slot [1; 0]) = 2300 /\
  net (run_stores fresh_slot [1]) = 22100.
Proof. vm_compute. repeat split; reflexivity. Qed.

Print Assumptions persistent_write_priced.
Print Assumptions revoked_write_nearly_free.
