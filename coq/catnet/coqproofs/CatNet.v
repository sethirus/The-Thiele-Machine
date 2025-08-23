(* Formal proof of CatNet audit log chain integrity. *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Record LogEntry := {
  data : string;
  previous_hash : nat
}.

Parameter hash_entry : LogEntry -> nat.

Parameter logic_oracle : list nat -> bool.

Definition AuditLog := list LogEntry.

Fixpoint is_chain_valid_from (prev_hash : nat) (log : AuditLog) : Prop :=
  match log with
  | [] => True
  | e :: rest =>
      previous_hash e = prev_hash /\
      is_chain_valid_from (hash_entry e) rest
  end.

Definition is_chain_valid (log : AuditLog) : Prop :=
  is_chain_valid_from 0 log.

Fixpoint compute_hash_chain (prev_hash : nat) (log : AuditLog) : nat :=
  match log with
  | [] => prev_hash
  | e :: rest => compute_hash_chain (hash_entry e) rest
  end.

Definition get_last_hash (log : AuditLog) : nat :=
  compute_hash_chain 0 log.

Definition add_entry (log : AuditLog) (new_data : string) : AuditLog :=
  let prev_hash := get_last_hash log in
  let new_entry := {| data := new_data; previous_hash := prev_hash |} in
  log ++ [new_entry].

Lemma is_chain_valid_from_add_entry :
  forall log prev_hash new_data,
    is_chain_valid_from prev_hash log ->
    is_chain_valid_from prev_hash
      (log ++ [{| data := new_data;
                 previous_hash := compute_hash_chain prev_hash log |}]).
Proof.
  induction log as [|e rest IH]; intros prev_hash new_data H; simpl in *.
  - simpl. split; [reflexivity|constructor].
  - destruct H as [Hprev Hrest]. simpl.
    split; [assumption|].
    apply IH. exact Hrest.
Qed.

Theorem add_entry_preserves_chain_validity :
  forall log new_data,
    is_chain_valid log ->
    is_chain_valid (add_entry log new_data).
Proof.
  intros log new_data H.
  unfold add_entry, get_last_hash, is_chain_valid in *.
  exact (is_chain_valid_from_add_entry log 0 new_data H).
Qed.

(* --- Control extension --- *)

Record ControlledState := {
  log : AuditLog;
  paradox_detected : bool
}.

Definition controlled_step (st : ControlledState) (axioms : list nat) (data : string)
  : ControlledState :=
  let is_consistent := logic_oracle axioms in
  if is_consistent
  then {| log := add_entry st.(log) data; paradox_detected := false |}
  else {| log := st.(log); paradox_detected := true |}.

Theorem paradox_halts_execution :
  forall st axioms data,
    logic_oracle axioms = false ->
    controlled_step st axioms data = {| log := st.(log); paradox_detected := true |}.
Proof.
  intros st axioms data H.
  unfold controlled_step.
  rewrite H.
  reflexivity.
Qed.
