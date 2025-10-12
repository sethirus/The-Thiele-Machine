(* ================================================================= *)
(* Thiele Machine Basics                                             *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat.
Import ListNotations.

(* ----------------------------------------------------------------- *)
(* Thiele Machine State and Programs                                 *)
(* ----------------------------------------------------------------- *)

(* Thiele Machine state: program counter *)
Record State := {
  pc : nat
}.

(* Program: list of instructions (abstract for now) *)
Definition ThieleProgram := list nat.  (* Placeholder for instructions *)

(* Step function: execute one instruction *)
Definition thiele_step (P : ThieleProgram) (s : State) : State :=
  {| pc := S s.(pc) |}.  (* Simple increment for now *)

(* Run for n steps *)
Fixpoint thiele_run_n (P : ThieleProgram) (s : State) (n : nat) : State :=
  match n with
  | 0 => s
  | S n' => thiele_run_n P (thiele_step P s) n'
  end.

(* ----------------------------------------------------------------- *)
(* Properties                                                        *)
(* ----------------------------------------------------------------- *)
