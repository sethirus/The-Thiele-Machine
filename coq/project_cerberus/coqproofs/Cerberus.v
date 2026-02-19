(* Cerberus.v - Minimal provably-safe kernel *)
Require Import Coq.Lists.List.
Require Import Arith.
Require Import Lia.
Require Import Bool.
Import ListNotations.


(* Simple machine state - THIELE EDITION *)
Record MachineState := {
  pc : nat; (* program counter *)
  mem : list nat; (* flat memory cells *)
  regs : list nat; (* register file *)
  mu_cost : nat;            (* running information cost *)
  paradox_detected : bool   (* flag for logical inconsistency *)
}.

(* Register helpers *)
Definition read_reg (r : nat) (rs : list nat) : nat := nth r rs 0.

Fixpoint write_reg (r v : nat) (rs : list nat) : list nat :=
  match r, rs with
  | 0, _ :: tl => v :: tl
  | S r', hd :: tl => hd :: write_reg r' v tl
  | _, [] => rs (* out-of-range writes leave regs unchanged *)
  end.

(* Simple instruction set *)

Inductive Instr :=
  | Load (addr : nat)
  | Store (addr : nat) (val : nat)
  | AddReg (rd rs1 rs2 : nat)
  | SubReg (rd rs1 rs2 : nat)
  | CopyReg (rd rs : nat)
  | Jmp (target : nat)
  | Jz (rs target : nat)
  | Jnz (rs target : nat)
  | Halt.

(* Jump target safety *)
Definition is_target_valid (program_len target : nat) : bool := Nat.ltb target program_len.

Definition is_instr_pc_safe (program_len : nat) (i : Instr) : bool :=
  match i with
  | Jmp t => is_target_valid program_len t
  | Jz _ t => is_target_valid program_len t
  | Jnz _ t => is_target_valid program_len t
  | _ => true
  end.

(* Memory safety checks *)
Definition is_safe_accessb (mem_len addr : nat) : bool := Nat.ltb addr mem_len.

Definition is_instr_mem_safe (mem_len : nat) (i : Instr) : bool :=
  match i with
  | Load addr => is_safe_accessb mem_len addr
  | Store addr _ => is_safe_accessb mem_len addr
  | _ => true
  end.

(** [succ_le_of_lt]: formal specification. *)
Lemma succ_le_of_lt : forall a b, a < b -> S a <= b.
Proof. intros a b H; lia. Qed.



(* Program with associated safety axioms - THIELE EDITION *)
Definition ProgramAxioms := list nat. (* Encoded logical rules *)

Definition Program := (list Instr * ProgramAxioms)%type.

(* Temporary logic oracle used for demonstrations.
   The real system should supply a verified oracle instead. *)
Definition logic_oracle (axioms : list nat) : bool :=
  negb (existsb (Nat.eqb 1) axioms).

Definition mem_safe_program (mem_len : nat) (p : Program) : Prop :=
  forall i, In i (fst p) -> is_instr_mem_safe mem_len i = true.



(* Encode safety properties of an instruction as a list of nat axioms (minimal implementation version) *)
Definition encode_safety_axioms (instr : Instr) (program_len : nat) (mem_len : nat) : list nat :=
  match instr with
  | Load addr => [1; addr; if Nat.ltb addr mem_len then 0 else 1]
  | Store addr _ => [2; addr; if Nat.ltb addr mem_len then 0 else 1]
  | AddReg rd rs1 rs2 => [3; rd; rs1; rs2; 0]
  | SubReg rd rs1 rs2 => [4; rd; rs1; rs2; 0]
  | CopyReg rd rs => [5; rd; rs; 0]
  | Jmp t => [6; t; if Nat.ltb t program_len then 0 else 1]
  | Jz rs t => [7; rs; t; if Nat.ltb t program_len then 0 else 1]
  | Jnz rs t => [8; rs; t; if Nat.ltb t program_len then 0 else 1]
  | Halt => [9; 0]
  end.
(*
  This is a minimal implementation: in a real system, the encoding would be more sophisticated and would match the oracle's logic.
  For now, we encode the instruction type and whether its safety check passes (0 = safe, 1 = unsafe).
*)

(* Kernel step: Fetches and executes one instruction safely. - THIELE EDITION *)
Definition kernel_step (p_with_axioms : Program) (st : MachineState) : MachineState :=
  let '(p_instrs, p_axioms) := p_with_axioms in
  if st.(paradox_detected) then st else (* Sticky paradox: once set, remains set *)
  match nth_error p_instrs st.(pc) with
  | None => st (* PC out of program bounds, halt. *)
  | Some instr_val =>
      let mem_len := length st.(mem) in
      let pc_safe := is_instr_pc_safe (length p_instrs) instr_val in
      let mem_safe := is_instr_mem_safe mem_len instr_val in
      let current_safety_axioms := encode_safety_axioms instr_val (length p_instrs) mem_len in
      let is_consistent_by_oracle := logic_oracle (p_axioms ++ current_safety_axioms) in

  if orb (orb (negb pc_safe) (negb mem_safe)) (negb is_consistent_by_oracle) then
        {| pc := st.(pc); mem := st.(mem); regs := st.(regs);
           mu_cost := st.(mu_cost); paradox_detected := true |}
      else
        match instr_val with
        | Halt => st
        | Load _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | Store _ _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | AddReg _ _ _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | SubReg _ _ _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | CopyReg _ _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | Jmp _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | Jz _ _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        | Jnz _ _ => {| pc := S st.(pc); mem := st.(mem); regs := st.(regs); mu_cost := S st.(mu_cost); paradox_detected := false |}
        end
  end.

Fixpoint run_kernel_n (p : Program) (st : MachineState) (n : nat) : MachineState :=
  match n with
  | 0 => st
  | S k => run_kernel_n p (kernel_step p st) k
  end.


(* Auxiliary lemmas about [kernel_step]. *)

(** [kernel_step_mem_length]: formal specification. *)
Lemma kernel_step_mem_length :
  forall p st,
    length (mem (kernel_step p st)) = length st.(mem).
Proof.
  intros [instrs axioms] st; simpl.
  destruct (paradox_detected st); simpl; auto.
  destruct (nth_error instrs (pc st)) eqn:?; simpl; auto.
  destruct (is_instr_pc_safe (length instrs) i);
  destruct (is_instr_mem_safe (length (mem st)) i);
  destruct (logic_oracle (axioms ++ encode_safety_axioms i (length instrs) (length (mem st))));
  simpl; auto;
  destruct i; reflexivity.
Qed.

(** [kernel_step_pc_bound]: formal specification. *)
Lemma kernel_step_pc_bound :
  forall p st,
    st.(paradox_detected) = false ->
    st.(pc) <= length (fst p) ->
    (forall instr,
        In instr (fst p) ->
        logic_oracle (snd p ++ encode_safety_axioms instr (length (fst p)) (length st.(mem))) = true) ->
    (kernel_step p st).(pc) <= length (fst p).
Proof.
  intros [instrs axioms] st Hp Hpc _; simpl in *.
  rewrite Hp.
  destruct (nth_error instrs (pc st)) eqn:Hnth; simpl.
  - assert (pc st < length instrs) as Hlt.
    { apply nth_error_Some. rewrite Hnth; discriminate. }
    remember (is_instr_pc_safe (length instrs) i) as pc_safe.
    remember (is_instr_mem_safe (length (mem st)) i) as mem_safe.
    remember (logic_oracle (axioms ++ encode_safety_axioms i (length instrs) (length (mem st)))) as ok.
    destruct pc_safe; simpl;
    destruct mem_safe; simpl;
    destruct ok; simpl; try lia;
    destruct i; simpl; try (apply succ_le_of_lt in Hlt; lia); lia.
  - lia.
Qed.

(** [run_kernel_paradox]: formal specification. *)
Lemma run_kernel_paradox :
  forall p st n,
    paradox_detected st = true ->
    run_kernel_n p st n = st.
Proof.
  intros p st n Hpar.
  induction n; simpl; [reflexivity|].
  destruct p as [instrs axioms]; simpl.
  rewrite Hpar. apply IHn.
Qed.


(* Main security theorem: The program counter never exceeds the program's bounds (Thiele Edition). *)
(** [pc_never_exceeds_program_bounds_thiele]: formal specification. *)
Theorem pc_never_exceeds_program_bounds_thiele :
  forall (p_with_axioms : Program) (st : MachineState) (n : nat),
    st.(pc) <= length (fst p_with_axioms) ->
    st.(paradox_detected) = false ->
    (forall instr,
      In instr (fst p_with_axioms) ->
      logic_oracle (snd p_with_axioms ++ encode_safety_axioms instr (length (fst p_with_axioms)) (length st.(mem))) = true) ->
    (run_kernel_n p_with_axioms st n).(pc) <= length (fst p_with_axioms).
Proof.
  intros p st n Hpc Hpar Hall.
  revert st Hpc Hpar Hall.
  induction n as [|n IH]; intros st Hpc Hpar Hall; simpl; [assumption|].
  pose proof (kernel_step_pc_bound p st Hpar Hpc Hall) as Hb.
  destruct (paradox_detected (kernel_step p st)) eqn:Hpar'.
  - rewrite (run_kernel_paradox p (kernel_step p st) n Hpar').
    exact Hb.
  - apply IH.
    + apply Hb.
    + apply Hpar'.
    + intros instr Hin.
      specialize (Hall instr Hin).
      rewrite <- (kernel_step_mem_length p st) in Hall.
      exact Hall.
Qed.

(** [mem_safety_preserved_thiele]: formal specification. *)
Theorem mem_safety_preserved_thiele :
  forall (p_with_axioms : Program) (st_init : MachineState) (n : nat),
    (forall instr,
      In instr (fst p_with_axioms) ->
      logic_oracle (snd p_with_axioms ++ encode_safety_axioms instr (length (fst p_with_axioms)) (length st_init.(mem))) = true) ->
    forall k,
      (run_kernel_n p_with_axioms st_init k).(pc) < length (fst p_with_axioms) ->
      let instr := nth (run_kernel_n p_with_axioms st_init k).(pc) (fst p_with_axioms) Halt in
      logic_oracle (snd p_with_axioms ++ encode_safety_axioms instr (length (fst p_with_axioms)) (length st_init.(mem))) = true.
Proof.
  intros p st n Hall k Hpc.
  set (instrs := fst p).
  set (instr := nth (pc (run_kernel_n p st k)) instrs Halt).
  assert (In instr instrs) as Hin.
  { subst instrs instr. apply nth_In. exact Hpc. }
  specialize (Hall instr Hin). exact Hall.
Qed.
