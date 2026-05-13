(** VerilogRefinement.v

    Constructive simulation relation connecting the Kami hardware snapshot
    abstraction to Kernel VM stepping, intended to replace assumption-only
    correspondence with proved refinement lemmas rooted in kami_hw.

    Per-instruction vm_step witnesses for all 46 opcodes.
*)

From Coq Require Import Arith.PeanoNat Lia Strings.String List.
Import ListNotations.
From Kernel Require Import VMState VMStep.
From KamiHW Require Import Abstraction ThieleTypes.

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
    dst < RegCount ->
    snapshot_regs_to_list
      (fun j => if Nat.eqb j dst then word64 v else snap_regs hs j) =
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
          (write_reg (abs_phase1 hs) dst (word64 imm))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros hs dst imm cost.
  eexists. split.
  - eapply step_load_imm. reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_load :
  forall (hs : KamiSnapshot) (dst rs_addr cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_load dst rs_addr cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_load dst rs_addr cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst (read_mem (abs_phase1 hs) (read_reg (abs_phase1 hs) rs_addr)))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_load; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_store :
  forall (hs : KamiSnapshot) (rs_addr src cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_store rs_addr src cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_store rs_addr src cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (abs_phase1 hs).(vm_regs)
          (write_mem (abs_phase1 hs) (read_reg (abs_phase1 hs) rs_addr) (read_reg (abs_phase1 hs) src))
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
            (word64_add (read_reg (abs_phase1 hs) rs1) (read_reg (abs_phase1 hs) rs2)))
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
            (word64_sub (read_reg (abs_phase1 hs) rs1) (read_reg (abs_phase1 hs) rs2)))
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
              (write_reg (abs_phase1 hs) 15
                (word64_add (read_reg (abs_phase1 hs) 15) 1))
              (write_mem (abs_phase1 hs) (read_reg (abs_phase1 hs) 15)
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
              (read_mem (abs_phase1 hs) (word64_sub (read_reg (abs_phase1 hs) 15) 1))
              (write_reg (abs_phase1 hs) 15 (word64_sub (read_reg (abs_phase1 hs) 15) 1))
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
            (word64_xor (read_reg (abs_phase1 hs) dst) (read_reg (abs_phase1 hs) src)))
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
          (write_reg (abs_phase1 hs) dst (word64_popcount (read_reg (abs_phase1 hs) src)))
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
  (* step_pnew witnesses graph' = fst (graph_add_module ...) — choose that witness
     and discharge the equality by reflexivity. *)
  intros. eexists. eapply step_pnew. reflexivity.
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

(** Partition graph instructions *)

Theorem verilog_simulates_vm_step_psplit :
  forall (hs : KamiSnapshot) (module : ModuleID) (left right : list nat) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_psplit module left right cost) vs'.
Proof.
  (* step_psplit witnesses graph' = graph_hw_psplit ... — choose that witness
     and discharge the equality by reflexivity. *)
  intros. eexists. eapply step_psplit. reflexivity.
Qed.

Theorem verilog_simulates_vm_step_pmerge :
  forall (hs : KamiSnapshot) (m1 m2 cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_pmerge m1 m2 cost) vs'.
Proof.
  (* step_pmerge witnesses graph' = graph_hw_pmerge ... — choose that witness
     and discharge the equality by reflexivity. *)
  intros. eexists. eapply step_pmerge. reflexivity.
Qed.

(** Logical instructions *)

Theorem verilog_simulates_vm_step_lassert :
  forall (hs : KamiSnapshot) (freg creg : nat) (kind : bool) (flen cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_lassert freg creg kind flen cost) vs'.
Proof.
  intros. eexists. eapply step_lassert.
Qed.

Theorem verilog_simulates_vm_step_ljoin :
  forall (hs : KamiSnapshot) (c1reg c2reg : nat) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_ljoin c1reg c2reg cost) vs'.
Proof.
  intros. eexists. eapply step_ljoin.
Qed.

Theorem verilog_simulates_vm_step_emit :
  forall (hs : KamiSnapshot) (module : ModuleID) (payload : string) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_emit module payload cost) vs'.
Proof.
  intros. eexists. eapply step_emit.
Qed.

Theorem verilog_simulates_vm_step_pdiscover :
  forall (hs : KamiSnapshot) (module : ModuleID) (evidence : list VMAxiom) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_pdiscover module evidence cost) vs'.
Proof.
  intros. eexists. eapply step_pdiscover.
Qed.

Theorem verilog_simulates_vm_step_reveal :
  forall (hs : KamiSnapshot) (module : ModuleID) (bits : nat) (cert : string) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_reveal module bits cert cost) vs'.
Proof.
  intros. eexists. eapply step_reveal.
Qed.

(** CHSH trial — valid bits case *)
Theorem verilog_simulates_vm_step_chsh_trial_ok :
  forall (hs : KamiSnapshot) (x y a b cost : nat),
    chsh_bits_ok x y a b = true ->
    exists vs',
      vm_step (abs_phase1 hs) (instr_chsh_trial x y a b cost) vs'.
Proof.
  intros. eexists. eapply step_chsh_trial_ok. exact H. reflexivity.
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

(** Hardware-simulation witnesses for the checkpoint, port, and heap opcodes *)

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
  forall (hs : KamiSnapshot) (dst rs_addr cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_heap_load dst rs_addr cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_heap_load dst rs_addr cost)
          (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst
            (read_mem (abs_phase1 hs)
              ((abs_phase1 hs).(vm_csrs).(csr_heap_base) + read_reg (abs_phase1 hs) rs_addr)))
          (abs_phase1 hs).(vm_mem) (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_heap_load; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_heap_store :
  forall (hs : KamiSnapshot) (rs_addr src cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_heap_store rs_addr src cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_heap_store rs_addr src cost)
          (abs_phase1 hs).(vm_graph) (abs_phase1 hs).(vm_csrs)
          (abs_phase1 hs).(vm_regs)
          (write_mem (abs_phase1 hs)
            ((abs_phase1 hs).(vm_csrs).(csr_heap_base) + read_reg (abs_phase1 hs) rs_addr)
            (read_reg (abs_phase1 hs) src))
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_heap_store; reflexivity.
  - reflexivity.
Qed.

(** Extended ALU operations *)

Theorem verilog_simulates_vm_step_and :
  forall (hs : KamiSnapshot) (dst rs1 rs2 cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_and dst rs1 rs2 cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_and dst rs1 rs2 cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst
            (word64_and (read_reg (abs_phase1 hs) rs1) (read_reg (abs_phase1 hs) rs2)))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_and; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_or :
  forall (hs : KamiSnapshot) (dst rs1 rs2 cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_or dst rs1 rs2 cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_or dst rs1 rs2 cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst
            (word64_or (read_reg (abs_phase1 hs) rs1) (read_reg (abs_phase1 hs) rs2)))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_or; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_shl :
  forall (hs : KamiSnapshot) (dst rs1 rs2 cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_shl dst rs1 rs2 cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_shl dst rs1 rs2 cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst
            (word64_shl (read_reg (abs_phase1 hs) rs1) (read_reg (abs_phase1 hs) rs2)))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_shl; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_shr :
  forall (hs : KamiSnapshot) (dst rs1 rs2 cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_shr dst rs1 rs2 cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_shr dst rs1 rs2 cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst
            (word64_shr (read_reg (abs_phase1 hs) rs1) (read_reg (abs_phase1 hs) rs2)))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_shr; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_mul :
  forall (hs : KamiSnapshot) (dst rs1 rs2 cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_mul dst rs1 rs2 cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_mul dst rs1 rs2 cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst
            (word64_mul (read_reg (abs_phase1 hs) rs1) (read_reg (abs_phase1 hs) rs2)))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_mul; reflexivity.
  - reflexivity.
Qed.

Theorem verilog_simulates_vm_step_lui :
  forall (hs : KamiSnapshot) (dst imm cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_lui dst imm cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_lui dst imm cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst (word64_shl imm 8))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_lui. reflexivity.
  - reflexivity.
Qed.

(** CERTIFY: advance PC, charge S mu_delta (structurally positive), set
    vm_certified := true. Does NOT use advance_state because it modifies
    vm_certified. The raw record matches step_certify in VMStep.v exactly. *)
Theorem verilog_simulates_vm_step_certify :
  forall (hs : KamiSnapshot) (mu_delta : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_certify mu_delta) vs' /\
      vs' =
        {| vm_graph := (abs_phase1 hs).(vm_graph);
           vm_csrs := (abs_phase1 hs).(vm_csrs);
           vm_regs := (abs_phase1 hs).(vm_regs);
           vm_mem := (abs_phase1 hs).(vm_mem);
           vm_pc := S (abs_phase1 hs).(vm_pc);
           vm_mu := (abs_phase1 hs).(vm_mu) + S mu_delta;
           vm_mu_tensor := (abs_phase1 hs).(vm_mu_tensor);
           vm_err := (abs_phase1 hs).(vm_err);
           vm_logic_acc := (abs_phase1 hs).(vm_logic_acc);
           vm_mstatus := (abs_phase1 hs).(vm_mstatus);
           vm_witness := (abs_phase1 hs).(vm_witness);
           vm_certified := true |}.
Proof.
  intros. eexists. split.
  - eapply step_certify.
  - reflexivity.
Qed.

(** ---------------------------------------------------------------
    Commutation diagram: kami_step ∘ abs commutes with vm_step on
    the hardware-observable cost (mu) field.
    --------------------------------------------------------------- *)

(** kami_step mu commutation: the abstracted mu after a hardware step
    equals the abstracted mu before plus kami_instruction_cost. *)
Theorem kami_step_mu_commutation :
  forall (hs : KamiSnapshot) (i : vm_instruction),
    (abs_phase1 (kami_step hs i)).(vm_mu) =
    (abs_phase1 hs).(vm_mu) + kami_instruction_cost i.
Proof.
  intros hs i.
  unfold abs_phase1; simpl.
  apply kami_step_mu_cost.
Qed.

(** For all instructions, exact mu agreement between
    abs_phase1 ∘ kami_step and vm_step ∘ abs_phase1.
    Since hardware now charges flen * 8 + S cost for LASSERT (matching software),
    no exclusions are needed. *)
Theorem kami_vm_mu_diamond :
  forall (hs : KamiSnapshot) (i : vm_instruction) (vs' : VMState),
    vm_step (abs_phase1 hs) i vs' ->
    vs'.(vm_mu) = (abs_phase1 (kami_step hs i)).(vm_mu).
Proof.
  intros hs i vs' Hstep.
  rewrite kami_step_mu_commutation.
  (* Goal: vs'.(vm_mu) = (abs_phase1 hs).(vm_mu) + kami_instruction_cost i.
     vm_step gives vs'.(vm_mu) = apply_cost (abs_phase1 hs) i for every branch.
     kami_instruction_cost i = instruction_cost i for all opcodes (including CERTIFY).
     apply_cost s i = s.(vm_mu) + instruction_cost i. *)
  inversion Hstep; subst;
  unfold apply_cost, kami_instruction_cost in *;
  simpl in *; try lia; try reflexivity; try contradiction;
  try (repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x; simpl; try lia; try reflexivity
  end).
Qed.

(** Hardware μ is at least software μ for every instruction whose cost fits
    under the cost ceiling. LASSERT now matches the kernel cost
    table exactly; this theorem is the conservative wrapper used downstream. *)
Theorem kami_vm_mu_conservative :
  forall (hs : KamiSnapshot) (i : vm_instruction) (vs' : VMState),
    instruction_cost i <= ORACLE_HALTS_HW_COST ->
    vm_step (abs_phase1 hs) i vs' ->
    (abs_phase1 (kami_step hs i)).(vm_mu) >= vs'.(vm_mu).
Proof.
  intros hs i vs' Hbound Hstep.
  assert (Hge : kami_instruction_cost i >= instruction_cost i).
  { apply kami_cost_ge_instruction_cost. exact Hbound. }
  inversion Hstep; subst;
  unfold abs_phase1, kami_step, kami_advance_default,
         advance_state, advance_state_rm, advance_state_reveal,
         jump_state, jump_state_rm,
         apply_cost, kami_instruction_cost, instruction_cost,
         ORACLE_HALTS_HW_COST in *;
  simpl in *;
  try lia; try contradiction;
  repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x; simpl; try lia
  end.
Qed.

(** Since hardware now charges flen * 8 + S cost for LASSERT (matching
    the kernel exactly), the LASSERT gap is zero: exact mu agreement. *)
Theorem kami_vm_mu_lassert_gap :
  forall (hs : KamiSnapshot) (freg creg : nat) (kind : bool) (flen cost : nat) (vs' : VMState),
    vm_step (abs_phase1 hs) (instr_lassert freg creg kind flen cost) vs' ->
    vs'.(vm_mu) = (abs_phase1 (kami_step hs (instr_lassert freg creg kind flen cost))).(vm_mu).
Proof.
  intros hs freg creg kind flen cost vs' Hstep.
  inversion Hstep; subst;
  unfold abs_phase1, kami_step, kami_advance_default,
         advance_state, apply_cost, instruction_cost in *;
  simpl in *; lia.
Qed.

(** TENSOR_SET: advance PC, charge mu. *)
Theorem verilog_simulates_vm_step_tensor_set :
  forall (hs : KamiSnapshot) (mid i j value cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_tensor_set mid i j value cost) vs'.
Proof.
  intros hs mid i j value cost.
  destruct (tensor_indices_ok i j) eqn:Hok.
  - eexists. eapply step_tensor_set_ok. exact Hok.
  - eexists. eapply step_tensor_set_bad. exact Hok.
Qed.

(** TENSOR_GET: advance PC, charge mu, write 0 to dst register. *)
Theorem verilog_simulates_vm_step_tensor_get :
  forall (hs : KamiSnapshot) (dst mid i j cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_tensor_get dst mid i j cost) vs'.
Proof.
  intros hs dst mid i j cost.
  destruct (tensor_indices_ok i j) eqn:Hok.
  - eexists. eapply step_tensor_get_ok.
    + exact Hok.
    + reflexivity.
  - eexists. eapply step_tensor_get_bad. exact Hok.
Qed.

(** Predicate for sequential instructions (PC advances by 1).
    LASSERT is excluded: on failure, hardware traps to LASSERT_TRAP_PC
    instead of incrementing. CHSH_LASSERT has the same trap discipline. *)
Definition verilog_increments_pc (i : vm_instruction) : bool :=
  match i with
  | instr_jump _ _ => false
  | instr_jnez _ _ _ => false
  | instr_call _ _ => false
  | instr_ret _ => false
  | instr_lassert _ _ _ _ _ => false
  | instr_chsh_lassert _ => false
  | _ => true
  end.

(** PC commutation for non-jump instructions: kami_step and vm_step
    both advance PC by 1. *)
Theorem kami_step_pc_commutation_sequential :
  forall (hs : KamiSnapshot) (i : vm_instruction),
    verilog_increments_pc i = true ->
    (abs_phase1 (kami_step hs i)).(vm_pc) = S (abs_phase1 hs).(vm_pc).
Proof.
  intros hs i Hinc.
  destruct i; simpl in Hinc; try discriminate;
  unfold abs_phase1, kami_step, kami_advance_default, kami_advance_err,
         kami_advance_reg, kami_advance_rich_morph, kami_advance_rich_noret,
         kami_advance_err_rich, kami_advance_cert_addr; simpl; try reflexivity;
  repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x; simpl; try reflexivity
    | |- context [if ?b then _ else _] => destruct b; simpl; try reflexivity
    | |- context [let (_, _) := ?x in _] => destruct x; simpl; try reflexivity
  end.
Qed.
(** ---------------------------------------------------------------
    Categorical / morphism-instruction simulation proofs.

    The hardware layer (kami_step) models morph opcodes as pure
    cost-charge + PC-advance (kami_advance_default), since the
    morphism graph state is maintained by the software extraction
    layer.  The abstract state from abs_phase1 always has
    pg_morphisms = [], so vm_step over morphism-lookup operations
    always takes the failure branch.

    For COMPOSE / MORPH_DELETE / MORPH_ASSERT / MORPH_TENSOR /
    MORPH_GET we prove the failure constructor directly.
    For MORPH / MORPH_ID we prove existence (either success or
    failure based on module presence), without claiming the
    resulting state equals the hardware snapshot.
    --------------------------------------------------------------- *)

(** Auxiliary: graph_lookup_morphism on the abs_phase1 graph always
    returns None, because snap_pt_to_graph has pg_morphisms = []. *)
Lemma abs_phase1_morphism_none :
  forall (hs : KamiSnapshot) (mid : nat),
    graph_lookup_morphism (abs_phase1 hs).(vm_graph) mid = None.
Proof.
  intros hs mid.
  unfold abs_phase1, snap_pt_to_graph.
  unfold graph_lookup_morphism. simpl.
  unfold graph_lookup_morphism_list. reflexivity.
Qed.

(** Auxiliary: graph_compose_morphisms on the abs_phase1 graph always
    returns None (both morphism lookups fail). *)
Lemma abs_phase1_compose_none :
  forall (hs : KamiSnapshot) (m1 m2 : nat),
    graph_compose_morphisms (abs_phase1 hs).(vm_graph) m1 m2 = None.
Proof.
  intros hs m1 m2.
  unfold graph_compose_morphisms.
  rewrite abs_phase1_morphism_none. reflexivity.
Qed.

(** Auxiliary: graph_delete_morphism on the abs_phase1 graph always
    returns None (existsb on empty list = false). *)
Lemma abs_phase1_delete_morphism_none :
  forall (hs : KamiSnapshot) (mid : nat),
    graph_delete_morphism (abs_phase1 hs).(vm_graph) mid = None.
Proof.
  intros hs mid.
  unfold graph_delete_morphism, abs_phase1, snap_pt_to_graph. simpl.
  reflexivity.
Qed.

(** Auxiliary: graph_tensor_morphisms on the abs_phase1 graph always
    returns None (both morphism lookups fail). *)
Lemma abs_phase1_tensor_morphisms_none :
  forall (hs : KamiSnapshot) (f g : nat),
    graph_tensor_morphisms (abs_phase1 hs).(vm_graph) f g = None.
Proof.
  intros hs f g.
  unfold graph_tensor_morphisms.
  rewrite abs_phase1_morphism_none. reflexivity.
Qed.

(** COMPOSE: abs_phase1 has no morphisms, so composition takes the error path. *)
Theorem verilog_simulates_vm_step_compose :
  forall (hs : KamiSnapshot) (dst m1 m2 cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_compose dst m1 m2 cost) vs'.
Proof.
  intros hs dst m1 m2 cost.
  eexists. eapply step_compose_bad.
  apply abs_phase1_compose_none.
Qed.

(** MORPH_DELETE: abs_phase1 has no morphisms, so deletion takes the error path. *)
Theorem verilog_simulates_vm_step_morph_delete :
  forall (hs : KamiSnapshot) (morph_id cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_morph_delete morph_id cost) vs'.
Proof.
  intros hs morph_id cost.
  eexists. eapply step_morph_delete_bad.
  apply abs_phase1_delete_morphism_none.
Qed.

(** MORPH_ASSERT: abs_phase1 has no morphisms, so assertion takes the error path. *)
Theorem verilog_simulates_vm_step_morph_assert :
  forall (hs : KamiSnapshot) (morph_id cost : nat) (property cert : string),
    exists vs',
      vm_step (abs_phase1 hs) (instr_morph_assert morph_id property cert cost) vs'.
Proof.
  intros hs morph_id cost property cert.
  eexists. eapply step_morph_assert_bad.
  apply abs_phase1_morphism_none.
Qed.

(** MORPH_TENSOR: abs_phase1 has no morphisms, so tensoring takes the error path. *)
Theorem verilog_simulates_vm_step_morph_tensor :
  forall (hs : KamiSnapshot) (dst f g cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_morph_tensor dst f g cost) vs'.
Proof.
  intros hs dst f g cost.
  eexists. eapply step_morph_tensor_bad.
  apply abs_phase1_tensor_morphisms_none.
Qed.

(** MORPH_GET: abs_phase1 has no morphisms, so reads take the error path. *)
Theorem verilog_simulates_vm_step_morph_get :
  forall (hs : KamiSnapshot) (dst morph_id selector cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_morph_get dst morph_id selector cost) vs'.
Proof.
  intros hs dst morph_id selector cost.
  eexists. eapply step_morph_get_bad.
  apply abs_phase1_morphism_none.
Qed.

(** MORPH: succeeds iff both endpoint modules are present in abs_phase1. *)
Theorem verilog_simulates_vm_step_morph :
  forall (hs : KamiSnapshot) (dst src_mod dst_mod coupling_idx cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_morph dst src_mod dst_mod coupling_idx cost) vs'.
Proof.
  intros hs dst src_mod dst_mod coupling_idx cost.
  destruct (graph_lookup (abs_phase1 hs).(vm_graph) src_mod) as [src_ms|] eqn:Hsrc.
  - destruct (graph_lookup (abs_phase1 hs).(vm_graph) dst_mod) as [dst_ms|] eqn:Hdst.
    + destruct (graph_add_morphism (abs_phase1 hs).(vm_graph) src_mod dst_mod empty_coupling_data false)
        as [graph' morph_id] eqn:Hadd.
      eexists. eapply step_morph_ok.
      * exact Hsrc.
      * exact Hdst.
      * symmetry. exact Hadd.
    + eexists. eapply step_morph_bad_dst.
      * exact Hsrc.
      * exact Hdst.
  - eexists. eapply step_morph_bad_src.
    exact Hsrc.
Qed.

(** MORPH_ID: succeeds iff the module is present in abs_phase1. *)
Theorem verilog_simulates_vm_step_morph_id :
  forall (hs : KamiSnapshot) (dst module cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_morph_id dst module cost) vs'.
Proof.
  intros hs dst module cost.
  destruct (graph_add_identity (abs_phase1 hs).(vm_graph) module) as [[graph' morph_id]|] eqn:Hid.
  - eexists. eapply step_morph_id_ok. exact Hid.
  - eexists. eapply step_morph_id_bad. exact Hid.
Qed.
