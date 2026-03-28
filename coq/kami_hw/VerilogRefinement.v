(** VerilogRefinement.v

    Constructive simulation relation connecting the Kami hardware snapshot
    abstraction to Kernel VM stepping, intended to replace assumption-only
    correspondence with proved refinement lemmas rooted in kami_hw.

    Per-instruction vm_step witnesses for all 47 opcodes.
*)

From Coq Require Import Arith.PeanoNat Lia Strings.String List.
Import ListNotations.
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
              (write_reg (abs_phase1 hs) 31
                (word64_add (read_reg (abs_phase1 hs) 31) 1))
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
              (read_mem (abs_phase1 hs) (word64_sub (read_reg (abs_phase1 hs) 31) 1))
              (write_reg (abs_phase1 hs) 31 (word64_sub (read_reg (abs_phase1 hs) 31) 1))
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

(** Partition graph instructions *)

Theorem verilog_simulates_vm_step_psplit :
  forall (hs : KamiSnapshot) (module : ModuleID) (left right : list nat) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_psplit module left right cost) vs'.
Proof.
  intros.
  destruct (graph_psplit (abs_phase1 hs).(vm_graph) module left right) as [[[g' lid] rid]|] eqn:Hps.
  - eexists. eapply step_psplit. exact Hps.
  - eexists. eapply step_psplit_failure. exact Hps.
Qed.

Theorem verilog_simulates_vm_step_pmerge :
  forall (hs : KamiSnapshot) (m1 m2 cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_pmerge m1 m2 cost) vs'.
Proof.
  intros.
  destruct (graph_pmerge (abs_phase1 hs).(vm_graph) m1 m2) as [[g' mid]|] eqn:Hpm.
  - eexists. eapply step_pmerge. exact Hpm.
  - eexists. eapply step_pmerge_failure. exact Hpm.
Qed.

(** Logical instructions *)

Theorem verilog_simulates_vm_step_lassert :
  forall (hs : KamiSnapshot) (freg creg : nat) (kind : bool) (flen cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_lassert freg creg kind flen cost) vs'.
Proof.
  intros.
  destruct kind.
  - (* SAT mode *)
    destruct (check_model
               (mem_to_string (abs_phase1 hs).(vm_mem) (read_reg (abs_phase1 hs) freg))
               (mem_to_string (abs_phase1 hs).(vm_mem) (read_reg (abs_phase1 hs) creg))) eqn:Hchk.
    + eexists. eapply step_lassert_sat; [reflexivity | reflexivity | exact Hchk | reflexivity].
    + eexists. eapply step_lassert_sat_failure; [reflexivity | reflexivity | exact Hchk].
  - (* UNSAT mode *)
    destruct (check_lrat
               (mem_to_string (abs_phase1 hs).(vm_mem) (read_reg (abs_phase1 hs) freg))
               (mem_to_string (abs_phase1 hs).(vm_mem) (read_reg (abs_phase1 hs) creg))) eqn:Hchk.
    + eexists. eapply step_lassert_unsat; [reflexivity | reflexivity | exact Hchk].
    + eexists. eapply step_lassert_unsat_failure; [reflexivity | reflexivity | exact Hchk].
Qed.

Theorem verilog_simulates_vm_step_ljoin :
  forall (hs : KamiSnapshot) (c1reg c2reg : nat) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_ljoin c1reg c2reg cost) vs'.
Proof.
  intros.
  destruct (String.eqb
             (mem_to_string (abs_phase1 hs).(vm_mem) (read_reg (abs_phase1 hs) c1reg))
             (mem_to_string (abs_phase1 hs).(vm_mem) (read_reg (abs_phase1 hs) c2reg))) eqn:Heq.
  - eexists. eapply step_ljoin_equal; [reflexivity | reflexivity | exact Heq].
  - eexists. eapply step_ljoin_mismatch; [reflexivity | reflexivity | exact Heq].
Qed.

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

    ORACLE_HALTS is a conservative refinement: hardware charges
    ORACLE_HALTS_HW_COST (1,000,000) while vm_step charges the
    user-specified cost. For all other opcodes, costs match exactly.
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

(** For non-ORACLE_HALTS, non-LASSERT instructions, exact mu agreement between
    abs_phase1 ∘ kami_step and vm_step ∘ abs_phase1.
    LASSERT is excluded because hardware charges S cost while software charges
    String.length formula + S cost (see kami_vm_mu_lassert_gap below). *)
Theorem kami_vm_mu_diamond_non_oracle :
  forall (hs : KamiSnapshot) (i : vm_instruction) (vs' : VMState),
    is_oracle_halts i = false ->
    (match i with instr_lassert _ _ _ _ _ => False | _ => True end) ->
    vm_step (abs_phase1 hs) i vs' ->
    vs'.(vm_mu) = (abs_phase1 (kami_step hs i)).(vm_mu).
Proof.
  intros hs i vs' Hnot_oracle Hl Hstep.
  inversion Hstep; subst;
  unfold apply_cost, instruction_cost, abs_phase1, kami_step,
         kami_advance_default, kami_instruction_cost,
         ORACLE_HALTS_HW_COST in *;
  simpl in *; try lia; try reflexivity; try contradiction;
  try (repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x; simpl; try lia; try reflexivity
  end).
Qed.

(** For non-LASSERT instructions with cost fitting in hardware (cost <= 1M),
    hardware mu >= software mu. This is the conservative refinement property:
    hardware never under-charges relative to the formal spec.
    LASSERT is excluded: hardware charges S cost while software charges
    String.length formula + S cost; hardware UNDER-charges by formula_length.
    See kami_vm_mu_lassert_gap for the LASSERT-specific property. *)
Theorem kami_vm_mu_conservative :
  forall (hs : KamiSnapshot) (i : vm_instruction) (vs' : VMState),
    (match i with instr_lassert _ _ _ _ _ => False | _ => True end) ->
    instruction_cost i <= ORACLE_HALTS_HW_COST ->
    vm_step (abs_phase1 hs) i vs' ->
    (abs_phase1 (kami_step hs i)).(vm_mu) >= vs'.(vm_mu).
Proof.
  intros hs i vs' Hl Hbound Hstep.
  assert (Hge : kami_instruction_cost i >= instruction_cost i).
  { apply kami_cost_ge_instruction_cost. exact Hl. exact Hbound. }
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

(** For LASSERT, the software mu exceeds hardware mu by formula length.
    This is the information-theoretic gap: formula text costs are invisible
    to hardware at decode time but enforced by the formal spec. *)
Theorem kami_vm_mu_lassert_gap :
  forall (hs : KamiSnapshot) (freg creg : nat) (kind : bool) (flen cost : nat) (vs' : VMState),
    vm_step (abs_phase1 hs) (instr_lassert freg creg kind flen cost) vs' ->
    vs'.(vm_mu) = (abs_phase1 (kami_step hs (instr_lassert freg creg kind flen cost))).(vm_mu)
                  + flen * 8.
Proof.
  intros hs freg creg kind flen cost vs' Hstep.
  inversion Hstep; subst;
  unfold abs_phase1, kami_step, kami_advance_default,
         advance_state, apply_cost, instruction_cost in *;
  simpl in *; lia.
Qed.

(** TENSOR_SET: advance PC, charge mu, update per-module tensor (in-bounds case). *)
Theorem verilog_simulates_vm_step_tensor_set :
  forall (hs : KamiSnapshot) (mid i j value cost : nat),
    (i < 4)%nat -> (j < 4)%nat ->
    exists vs',
      vm_step (abs_phase1 hs) (instr_tensor_set mid i j value cost) vs' /\
      vs' =
        advance_state (abs_phase1 hs) (instr_tensor_set mid i j value cost)
          (graph_update_module_tensor (abs_phase1 hs).(vm_graph) mid (i * 4 + j) value)
          (abs_phase1 hs).(vm_csrs)
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_tensor_set; eauto.
  - reflexivity.
Qed.

(** TENSOR_GET: advance PC, charge mu, read per-module tensor to dst register (in-bounds case). *)
Theorem verilog_simulates_vm_step_tensor_get :
  forall (hs : KamiSnapshot) (dst mid i j cost : nat),
    (i < 4)%nat -> (j < 4)%nat ->
    exists vs',
      vm_step (abs_phase1 hs) (instr_tensor_get dst mid i j cost) vs' /\
      vs' =
        advance_state_rm (abs_phase1 hs) (instr_tensor_get dst mid i j cost)
          (abs_phase1 hs).(vm_graph)
          (abs_phase1 hs).(vm_csrs)
          (write_reg (abs_phase1 hs) dst (module_tensor_entry (abs_phase1 hs) mid i j))
          (abs_phase1 hs).(vm_mem)
          (abs_phase1 hs).(vm_err).
Proof.
  intros. eexists. split.
  - eapply step_tensor_get; eauto.
  - reflexivity.
Qed.

(** Predicate for non-jump instructions (PC advances by 1). *)
Definition verilog_increments_pc (i : vm_instruction) : bool :=
  match i with
  | instr_jump _ _ => false
  | instr_jnez _ _ _ => false
  | instr_call _ _ => false
  | instr_ret _ => false
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
  unfold abs_phase1; simpl; try reflexivity;
  (* CHSH_TRIAL: nested match — all arms have same PC *)
  repeat match goal with
    | |- context [match ?x with _ => _ end] => destruct x; simpl; try reflexivity
  end.
Qed.
(** ---------------------------------------------------------------
    Categorical morphism instruction simulation proofs (Phase 6).

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

(** COMPOSE: compose always fails on the abstract state (empty morphism graph). *)
Theorem verilog_simulates_vm_step_compose :
  forall (hs : KamiSnapshot) (dst m1 m2 cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_compose dst m1 m2 cost) vs'.
Proof.
  intros. eexists. eapply step_compose_failure.
  apply abs_phase1_compose_none.
Qed.

(** MORPH_DELETE: always fails on the abstract state. *)
Theorem verilog_simulates_vm_step_morph_delete :
  forall (hs : KamiSnapshot) (morph_id cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_morph_delete morph_id cost) vs'.
Proof.
  intros. eexists. eapply step_morph_delete_failure.
  apply abs_phase1_delete_morphism_none.
Qed.

(** MORPH_ASSERT: always fails on the abstract state. *)
Theorem verilog_simulates_vm_step_morph_assert :
  forall (hs : KamiSnapshot) (morph_id cost : nat) (property cert : string),
    exists vs',
      vm_step (abs_phase1 hs) (instr_morph_assert morph_id property cert cost) vs'.
Proof.
  intros. eexists. eapply step_morph_assert_failure.
  apply abs_phase1_morphism_none.
Qed.

(** MORPH_TENSOR: always fails on the abstract state. *)
Theorem verilog_simulates_vm_step_morph_tensor :
  forall (hs : KamiSnapshot) (dst f g cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_morph_tensor dst f g cost) vs'.
Proof.
  intros. eexists. eapply step_morph_tensor_failure.
  apply abs_phase1_tensor_morphisms_none.
Qed.

(** MORPH_GET: always fails on the abstract state. *)
Theorem verilog_simulates_vm_step_morph_get :
  forall (hs : KamiSnapshot) (dst morph_id selector cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_morph_get dst morph_id selector cost) vs'.
Proof.
  intros. eexists. eapply step_morph_get_failure.
  apply abs_phase1_morphism_none.
Qed.

(** MORPH: existence — uses success or failure depending on module presence. *)
Theorem verilog_simulates_vm_step_morph :
  forall (hs : KamiSnapshot) (dst src_mod dst_mod coupling_idx cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_morph dst src_mod dst_mod coupling_idx cost) vs'.
Proof.
  intros.
  destruct (graph_lookup (abs_phase1 hs).(vm_graph) src_mod) as [ms_src|] eqn:Hsrc.
  - destruct (graph_lookup (abs_phase1 hs).(vm_graph) dst_mod) as [ms_dst|] eqn:Hdst.
    + (* Both modules exist: use success constructor *)
      destruct (graph_add_morphism (abs_phase1 hs).(vm_graph) src_mod dst_mod
                  {| coupling_pairs := []; coupling_label := "" |} false)
        as [g' mid] eqn:Hadd.
      eexists. eapply step_morph.
      * rewrite Hsrc. discriminate.
      * rewrite Hdst. discriminate.
      * symmetry. exact Hadd.
    + (* dst_mod absent: use failure constructor *)
      eexists. eapply step_morph_failure.
      right. rewrite Hdst. reflexivity.
  - (* src_mod absent: use failure constructor *)
    eexists. eapply step_morph_failure.
    left. rewrite Hsrc. reflexivity.
Qed.

(** MORPH_ID: existence — success if module present, failure otherwise. *)
Theorem verilog_simulates_vm_step_morph_id :
  forall (hs : KamiSnapshot) (dst module cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_morph_id dst module cost) vs'.
Proof.
  intros.
  destruct (graph_add_identity (abs_phase1 hs).(vm_graph) module)
    as [[g' mid]|] eqn:Hid.
  - eexists. eapply step_morph_id. exact Hid.
  - eexists. eapply step_morph_id_failure. exact Hid.
Qed.
