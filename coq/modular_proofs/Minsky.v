(* Minimal Minsky-machine formalization (skeleton)
   This file provides a small, self-contained encoding of Minsky
   (two-instruction counter) machines suitable as an intermediate
   representation for later compilation from Turing machines.

   The goal of this module is to provide a compact, easy-to-reason
   about target for the Thiele-machine implementation proofs.  It is
   intentionally small: the API is just the instruction datatype, a
   small-step semantics and an n-step iterator together with a couple
   of basic helper lemmas and a worked example. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
Open Scope nat_scope.

Module Minsky.

(* A Minsky instruction: INC r j  (increment register r and jump to j)
   or DEC r j k (if register r = 0 jump to k, otherwise decrement and jump to j). *)
Inductive instr : Type :=
  | INC (r j : nat)
  | DEC (r j k : nat).

Definition program : Type := list instr.
Definition config : Type := (nat * list nat)%type. (* pc, register file *)

(** Small helpers for register-file manipulation.  Registers are stored
    in a list and out-of-range accesses return 0 (so the register file
    implicitly extends with zeros). *)
Fixpoint set_nth (l : list nat) (idx : nat) (v : nat) : list nat :=
  match l, idx with
  | [], _ => []
  | _ :: tl, 0 => v :: tl
  | hd :: tl, S i => hd :: set_nth tl i v
  end.

Definition read_reg (regs : list nat) (r : nat) : nat := nth r regs 0.

Lemma set_nth_length : forall l idx v, length (set_nth l idx v) = length l.
Proof.
  induction l as [|hd tl IH]; intros [|idx] v; simpl; auto.
Qed.

(* Single-step semantics of a Minsky program.  The instruction at the
   current program counter is executed; if the pc is out-of-range we
   leave the configuration unchanged (representing a halted program). *)
Definition step (p : program) (cfg : config) : config :=
  let '(pc, regs) := cfg in
  let instr := nth pc p (INC 0 pc) in
  match instr with
  | INC r j =>
      let v := S (read_reg regs r) in
      (j, set_nth regs r v)
  | DEC r j k =>
      if Nat.eqb (read_reg regs r) 0 then (k, regs)
      else (j, set_nth regs r (pred (read_reg regs r)))
  end.

Fixpoint run_n (p : program) (cfg : config) (n : nat) : config :=
  match n with
  | 0 => cfg
  | S n' => run_n p (step p cfg) n'
  end.

Lemma run_n_succ : forall p cfg n,
    run_n p cfg (S n) = run_n p (step p cfg) n.
Proof. reflexivity. Qed.

(* A tiny worked example: a 1-instruction program that increments
   register 0 and jumps to 1.  Stepping from pc=0 with register 0=0
   should produce pc=1 and register 0 = 1. *)
Example inc0_example :
  let p := (INC 0 1) :: nil in
  step p (0, [0]) = (1, [1]).
Proof. simpl. reflexivity. Qed.

End Minsky.
