(** SCOPE NOTE: standalone proof scope. This toy PCC fragment is checked on its
    own terms and has no formal bridge to a Thiele machine.

    Core model of the PCC consumer pipeline described by Necula,
    POPL 1997, Sections 2--4: policy, verification condition, certificate,
    and a small trusted proof checker.  This is a memory-access fragment,
    not the paper's full DEC Alpha case study. *)

From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

Inductive PCCInstr : Type :=
| PRead (address : nat)
| PWrite (address value : nat)
| PHalt.

Definition policy_allows (memory_limit : nat) (i : PCCInstr) : bool :=
  match i with
  | PRead a | PWrite a _ => Nat.ltb a memory_limit
  | PHalt => true
  end.

Definition verification_condition (memory_limit : nat)
    (program : list PCCInstr) : Prop :=
  Forall (fun i => policy_allows memory_limit i = true) program.

Inductive PCCProof (memory_limit : nat) : list PCCInstr -> Type :=
| PCCDone : PCCProof memory_limit []
| PCCStep : forall i program,
    policy_allows memory_limit i = true ->
    PCCProof memory_limit program ->
    PCCProof memory_limit (i :: program).

Fixpoint check_program (memory_limit : nat) (program : list PCCInstr) : bool :=
  match program with
  | [] => true
  | i :: rest => policy_allows memory_limit i && check_program memory_limit rest
  end.

Definition checker_accepts_iff_vc : Prop :=
  forall memory_limit program,
    check_program memory_limit program = true <->
    verification_condition memory_limit program.

Definition certificate_implies_vc : Prop :=
  forall memory_limit program,
    PCCProof memory_limit program -> verification_condition memory_limit program.

Definition unsafe_program_rejected : Prop :=
  check_program 2 [PRead 2; PHalt] = false.
