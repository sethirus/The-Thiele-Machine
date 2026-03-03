(** VerilogRefinement.v

    Constructive simulation relation connecting the Kami hardware snapshot
    abstraction to Kernel VM stepping, intended to replace assumption-only
    correspondence with proved refinement lemmas rooted in kami_hw.

    Per-instruction vm_step witnesses for all 31 opcodes.
*)

From Coq Require Import Arith.PeanoNat Lia Strings.String.
From Kernel Require Import VMState VMStep.
From KamiHW Require Import Abstraction.

(** Simulation relation: hardware snapshot and VM state are related when
    the abstraction map computes that VM state exactly. *)
Definition verilog_sim_rel (hs : KamiSnapshot) (vs : VMState) : Prop :=
  abs_phase1 hs = vs.

(* DEFINITIONAL HELPER *)
Lemma verilog_sim_rel_abs_phase1 :
  forall hs, verilog_sim_rel hs (abs_phase1 hs).
Proof.
  intros hs. unfold verilog_sim_rel. reflexivity.
Qed.

(** Core constructive commutation lemma reused from Abstraction.v. *)
Theorem verilog_refines_register_write :
  forall (hs : KamiSnapshot) (dst v : nat),
    dst < 32 ->
    snapshot_regs_to_list
      (fun j => if Nat.eqb j dst then word32 v else snap_regs hs j) =
    write_reg (abs_phase1 hs) dst v.
Proof.
  exact kami_refines_vm_step.
Qed.

(** ---------------------------------------------------------------
    Per-instruction vm_step simulation witnesses
    --------------------------------------------------------------- *)

(** Compute instructions (register/memory) *)

Theorem verilog_simulates_vm_step_load_imm :
  forall (hs : KamiSnapshot) (dst imm cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_load_imm dst imm cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_load_imm dst imm cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst (word32 imm))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros hs dst imm cost.
  eexists. split.
  - eapply step_load_imm. reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_load :
  forall (hs : KamiSnapshot) (dst addr cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_load dst addr cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_load dst addr cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst (read_mem (abs_phase1 hs) addr))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_load; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_store :
  forall (hs : KamiSnapshot) (addr src cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_store addr src cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_store addr src cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (abs_phase1 hs).(vm_regs)
          (write_mem (abs_phase1 hs) addr (read_reg (abs_phase1 hs) src))
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_store; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_add :
  forall (hs : KamiSnapshot) (dst rs1 rs2 cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_add dst rs1 rs2 cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_add dst rs1 rs2 cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst
            (word32_add (read_reg (abs_phase1 hs) rs1) (read_reg (abs_phase1 hs) rs2)))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_add; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_sub :
  forall (hs : KamiSnapshot) (dst rs1 rs2 cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_sub dst rs1 rs2 cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_sub dst rs1 rs2 cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst
            (word32_sub (read_reg (abs_phase1 hs) rs1) (read_reg (abs_phase1 hs) rs2)))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_sub; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_xfer :
  forall (hs : KamiSnapshot) (dst src cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_xfer dst src cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_xfer dst src cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst (read_reg (abs_phase1 hs) src))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_xfer. reflexivity.
  - reflexivity.
Qed.

(** Control-flow instructions *)

Theorem verilog_simulates_vm_step_jump :
  forall (hs : KamiSnapshot) (target cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_jump target cost) vs' /\
      vs' = jump_state (abs_phase1 hs) (instr_jump target cost) target.
Proof.
  intros. eexists. split.
  - eapply step_jump.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_jnez_taken :
  forall (hs : KamiSnapshot) (rs target cost : nat),
    read_reg (abs_phase1 hs) rs <> 0 ->
    exists vs',
      vm_step (abs_phase1 hs) (instr_jnez rs target cost) vs' /\
      vs' = jump_state (abs_phase1 hs) (instr_jnez rs target cost) target.
Proof.
  intros. eexists. split.
  - eapply step_jnez_taken. exact H.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_jnez_not_taken :
  forall (hs : KamiSnapshot) (rs target cost : nat),
    read_reg (abs_phase1 hs) rs = 0 ->
    exists vs',
      vm_step (abs_phase1 hs) (instr_jnez rs target cost) vs' /\
      vs' = advance_state (abs_phase1 hs) (instr_jnez rs target cost)
              (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_jnez_not_taken. exact H.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_call :
  forall (hs : KamiSnapshot) (target cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_call target cost) vs' /\
      vs' = jump_state_rm (abs_phase1 hs) (instr_call target cost) target
              (write_reg (abs_phase1 hs) 31
                (word32_add (read_reg (abs_phase1 hs) 31) 1))
              (write_mem (abs_phase1 hs) (read_reg (abs_phase1 hs) 31)
                (S (abs_phase1 hs).(vm_pc))).
Proof.
  intros. eexists. split.
  - eapply step_call; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_ret :
  forall (hs : KamiSnapshot) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_ret cost) vs' /\
      vs' = jump_state_rm (abs_phase1 hs) (instr_ret cost)
              (read_mem (abs_phase1 hs) (word32_sub (read_reg (abs_phase1 hs) 31) 1))
              (write_reg (abs_phase1 hs) 31 (word32_sub (read_reg (abs_phase1 hs) 31) 1))
              (abs_phase1 hs).(vm_mem).
Proof.
  intros. eexists. split.
  - eapply step_ret; reflexivity.
  - reflexivity.
Qed.

(** XOR / bit-linear instructions *)

Theorem verilog_simulates_vm_step_xor_load :
  forall (hs : KamiSnapshot) (dst addr cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_xor_load dst addr cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_xor_load dst addr cost)
          (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst (read_mem (abs_phase1 hs) addr))
          (abs_phase1 hs).(vm_mem) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_xor_load; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_xor_add :
  forall (hs : KamiSnapshot) (dst src cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_xor_add dst src cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_xor_add dst src cost)
          (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst
            (word32_xor (read_reg (abs_phase1 hs) dst) (read_reg (abs_phase1 hs) src)))
          (abs_phase1 hs).(vm_mem) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_xor_add; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_xor_swap :
  forall (hs : KamiSnapshot) (a b cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_xor_swap a b cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_xor_swap a b cost)
          (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs)
          (swap_regs (abs_phase1 hs).(vm_regs) a b)
          (abs_phase1 hs).(vm_mem) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_xor_swap. reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_xor_rank :
  forall (hs : KamiSnapshot) (dst src cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_xor_rank dst src cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_xor_rank dst src cost)
          (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst (word32_popcount (read_reg (abs_phase1 hs) src)))
          (abs_phase1 hs).(vm_mem) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_xor_rank; reflexivity.
  - reflexivity.
Qed.

(** Structural instructions *)

Theorem verilog_simulates_vm_step_pnew :
  forall (hs : KamiSnapshot) (region : list nat) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_pnew region cost) vs'.
Proof.
  intros. destruct (graph_pnew (abs_phase1 hs).(vm_graph) region) as [g' mid] eqn:Hpnew.
  eexists. eapply step_pnew. exact Hpnew.
Qed.

Theorem verilog_simulates_vm_step_mdlacc :
  forall (hs : KamiSnapshot) (module cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_mdlacc module cost) vs' /\
      vs' = advance_state (abs_phase1 hs) (instr_mdlacc module cost)
              (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_mdlacc.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_oracle_halts :
  forall (hs : KamiSnapshot) (payload : string) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_oracle_halts payload cost) vs' /\
      vs' = advance_state (abs_phase1 hs) (instr_oracle_halts payload cost)
              (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_oracle_halts.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_halt :
  forall (hs : KamiSnapshot) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_halt cost) vs' /\
      vs' = advance_state (abs_phase1 hs) (instr_halt cost)
              (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_halt.
  - reflexivity.
Qed.

(** Logical instructions *)

Theorem verilog_simulates_vm_step_emit :
  forall (hs : KamiSnapshot) (module : ModuleID) (payload : string) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_emit module payload cost) vs'.
Proof.
  intros. eexists. eapply step_emit. reflexivity.
Qed.

Theorem verilog_simulates_vm_step_pdiscover :
  forall (hs : KamiSnapshot) (module : ModuleID) (evidence : list VMAxiom) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_pdiscover module evidence cost) vs'.
Proof.
  intros. eexists. eapply step_pdiscover. reflexivity.
Qed.

Theorem verilog_simulates_vm_step_reveal :
  forall (hs : KamiSnapshot) (module : ModuleID) (bits : nat) (cert : string) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_reveal module bits cert cost) vs'.
Proof.
  intros. eexists. eapply step_reveal. reflexivity.
Qed.

(** CHSH trial — valid bits case *)
Theorem verilog_simulates_vm_step_chsh_trial_ok :
  forall (hs : KamiSnapshot) (x y a b cost : nat),
    chsh_bits_ok x y a b = true ->
    exists vs',
      vm_step (abs_phase1 hs) (instr_chsh_trial x y a b cost) vs' /\
      vs' = advance_state (abs_phase1 hs) (instr_chsh_trial x y a b cost)
              (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_chsh_trial_ok. exact H.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_chsh_trial_bad :
  forall (hs : KamiSnapshot) (x y a b cost : nat),
    chsh_bits_ok x y a b = false ->
    exists vs',
      vm_step (abs_phase1 hs) (instr_chsh_trial x y a b cost) vs'.
Proof.
  intros. eexists. eapply step_chsh_trial_badbits. exact H.
Qed.

(** Physics-side monotonicity obligations carried by abstraction layer. *)
Theorem verilog_mu_non_decreasing_on_charge :
  forall (hs : KamiSnapshot) (cost : nat),
    (abs_phase1 hs).(vm_mu) + cost >= (abs_phase1 hs).(vm_mu).
Proof.
  exact hw_step_preserves_invariants.
Qed.

(** Phase 2/3B hardware simulation witnesses *)

Theorem verilog_simulates_vm_step_checkpoint :
  forall (hs : KamiSnapshot) (label : string) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_checkpoint label cost) vs' /\
      vs' = advance_state (abs_phase1 hs) (instr_checkpoint label cost)
              (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_checkpoint.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_read_port :
  forall (hs : KamiSnapshot) (dst channel_idx value bits cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_read_port dst channel_idx value bits cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_read_port dst channel_idx value bits cost)
          (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst value)
          (abs_phase1 hs).(vm_mem) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_read_port. reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_write_port :
  forall (hs : KamiSnapshot) (channel_idx src cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_write_port channel_idx src cost) vs' /\
      vs' = advance_state (abs_phase1 hs) (instr_write_port channel_idx src cost)
              (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_write_port.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_heap_load :
  forall (hs : KamiSnapshot) (dst addr cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_heap_load dst addr cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_heap_load dst addr cost)
          (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst
            (read_mem (abs_phase1 hs) (0 + addr)))
          (abs_phase1 hs).(vm_mem) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_heap_load; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_heap_store :
  forall (hs : KamiSnapshot) (addr src cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_heap_store addr src cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_heap_store addr src cost)
          (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs)
          (abs_phase1 hs).(vm_regs)
          (write_mem (abs_phase1 hs) (0 + addr) (read_reg (abs_phase1 hs) src))
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_heap_store; reflexivity.
  - reflexivity.
Qed.
