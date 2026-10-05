(** SCOPE NOTE: standalone proof scope. These proofs close the independent RAM
    core and do not establish a bridge to a Thiele machine.

    Proofs for the list-memory RAM core. *)

From Coq Require Import List Arith.PeanoNat.
Import ListNotations.
From Kernel Require Import ConcreteRAMTarget.

Theorem concrete_ram_write_reads_back : ram_write_reads_back.
Proof.
  intros memory address. revert memory.
  induction address as [|address IH]; intros [|cell rest] old value H;
    simpl in *; try discriminate.
  - inversion H. reflexivity.
  - apply IH with (old := old). exact H.
Qed.

Theorem concrete_tied_ram_records_overwrite : tied_ram_records_overwrite.
Proof.
  intros op s old H. unfold ram_tied_step. rewrite H. reflexivity.
Qed.

Theorem concrete_untied_ram_record_unchanged : untied_ram_record_unchanged.
Proof.
  intros op s. unfold ram_untied_step, ram_base_step.
  destruct (cell_at (op_address op) s); reflexivity.
Qed.

Theorem concrete_tied_and_untied_same_base : tied_and_untied_same_base.
Proof.
  intros op s. unfold ram_tied_step, ram_untied_step.
  destruct (cell_at (op_address op) s); reflexivity.
Qed.

Example concrete_ram_two_cell_witness :
  let s := {| ram_memory := [4; 9]; ram_pc := 0; ram_record := [] |} in
  ram_memory (ram_tied_step (RAMLoad 1 7) s) = [4; 7] /\
  ram_record (ram_tied_step (RAMLoad 1 7) s) = [(1, 9)].
Proof. simpl. split; reflexivity. Qed.

Print Assumptions concrete_ram_write_reads_back.
Print Assumptions concrete_tied_ram_records_overwrite.
Print Assumptions concrete_untied_ram_record_unchanged.
Print Assumptions concrete_tied_and_untied_same_base.
Print Assumptions concrete_ram_two_cell_witness.
