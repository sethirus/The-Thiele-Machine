(** SCOPE NOTE: standalone proof scope. This addressed RAM is an independent
    comparison model; a record-axis adapter is explicitly not claimed.

    Target propositions for an addressed random-access memory. *)

From Coq Require Import List Arith.PeanoNat.
Import ListNotations.

Fixpoint write_cell (address value : nat) (memory : list nat) : list nat :=
  match address, memory with
  | 0, _ :: rest => value :: rest
  | S address', cell :: rest => cell :: write_cell address' value rest
  | _, [] => []
  end.

Inductive RAMOp :=
| RAMLoad (address value : nat)
| RAMInc (address : nat)
| RAMDec (address : nat).

Record RAMState := {
  ram_memory : list nat;
  ram_pc : nat;
  ram_record : list (nat * nat)
}.

Definition cell_at (address : nat) (s : RAMState) : option nat :=
  nth_error (ram_memory s) address.

Definition next_value (op : RAMOp) (old : nat) : nat :=
  match op with RAMLoad _ value => value | RAMInc _ => S old | RAMDec _ => pred old end.

Definition op_address (op : RAMOp) : nat :=
  match op with RAMLoad a _ | RAMInc a | RAMDec a => a end.

Definition ram_base_step (op : RAMOp) (s : RAMState) : RAMState :=
  match cell_at (op_address op) s with
  | None => {| ram_memory := ram_memory s; ram_pc := S (ram_pc s);
               ram_record := ram_record s |}
  | Some old =>
      {| ram_memory := write_cell (op_address op) (next_value op old) (ram_memory s);
         ram_pc := S (ram_pc s); ram_record := ram_record s |}
  end.

Definition ram_tied_step (op : RAMOp) (s : RAMState) : RAMState :=
  match cell_at (op_address op) s with
  | None => ram_base_step op s
  | Some old =>
      let next := ram_base_step op s in
      {| ram_memory := ram_memory next; ram_pc := ram_pc next;
         ram_record := ram_record s ++ [(op_address op, old)] |}
  end.

Definition ram_untied_step := ram_base_step.

Definition ram_projection (s : RAMState) : list nat * nat :=
  (ram_memory s, ram_pc s).

Definition ram_write_reads_back : Prop :=
  forall memory address old value,
    nth_error memory address = Some old ->
    nth_error (write_cell address value memory) address = Some value.

Definition tied_ram_records_overwrite : Prop :=
  forall op s old,
    cell_at (op_address op) s = Some old ->
    ram_record (ram_tied_step op s) =
      ram_record s ++ [(op_address op, old)].

Definition untied_ram_record_unchanged : Prop :=
  forall op s, ram_record (ram_untied_step op s) = ram_record s.

Definition tied_and_untied_same_base : Prop :=
  forall op s,
    ram_projection (ram_tied_step op s) =
    ram_projection (ram_untied_step op s).
