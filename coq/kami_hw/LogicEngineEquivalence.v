(** LogicEngineEquivalence: agreement lemmas for the on-chip logic-engine path

  This file compares the kernel and Kami treatments of LASSERT and LJOIN.
  The important fact is that both sides are driven by the same memory-backed
  formula and certificate strings, so PC, μ, and error behavior can be
  related directly to the checker outcomes.

  LASSERT now uses the same execution guard on both sides: the encoded flen
  must match the in-memory formula header and the witness check must pass.
  If either condition fails, both semantics trap and latch error.
*)

From Coq Require Import Arith.PeanoNat Lia Bool Strings.String.
From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.
From KamiHW Require Import Abstraction VerilogRefinement.

Import VMStep.VMStep.

(** Expected error flag after LASSERT

    Computes the vm_err value that vm_step will produce for an LASSERT
    instruction, given the current VMState and register indices:
    - kind = true (SAT mode): check_model; vm_err preserved iff model is valid
    - kind = false (UNSAT mode): always error (diagnostic condition — UNSAT
      means the kernel records that no new axiom can be added, which is
      treated as an informational error, regardless of proof validity) *)
Definition lassert_expected_err (s : VMState) (freg creg : nat) (kind : bool) : bool :=
  if lassert_exec_ok s freg creg kind (lassert_hw_flen s freg) then vm_err s else true.

(** Expected error flag after LJOIN

    Computes the vm_err value that vm_step will produce for an LJOIN
    instruction, given the current VMState and register indices:
    - vm_err preserved iff both cert strings are equal *)
(** LJOIN preserves vm_err unconditionally (via advance_state). *)
Definition ljoin_expected_err (s : VMState) (c1reg c2reg : nat) : bool :=
  vm_err s.

(** PC/mu commutation lemmas

    Hardware and kernel both advance PC by 1 for LASSERT only when the
    declared flen matches the in-memory header and the witness check passes;
    otherwise they trap to LASSERT_TRAP_PC. For LJOIN, kernel always
    advances PC by 1 (via advance_state).

    Mu always advances in both layers. *)

(** Definitional lemma: LASSERT PC depends on the combined execution guard,
    mu charges flen * 8 + S cost matching the kernel. *)
Theorem lassert_kami_step_pc_mu :
  forall (hs : KamiSnapshot) (freg creg : nat) (kind : bool) (flen cost : nat),
    snap_pc (kami_step hs (instr_lassert freg creg kind flen cost)) =
      (if lassert_exec_ok (abs_phase1 hs) freg creg kind flen
       then S (snap_pc hs)
       else LASSERT_TRAP_PC) /\
    snap_mu (kami_step hs (instr_lassert freg creg kind flen cost)) =
      snap_mu hs + (flen * 8 + S cost).
Proof.
  intros. unfold kami_step. simpl. auto.
Qed.

(** Definitional lemma *)
Theorem ljoin_kami_step_pc_mu :
  forall (hs : KamiSnapshot) (c1reg c2reg : nat) (cost : nat),
    snap_pc (kami_step hs (instr_ljoin c1reg c2reg cost)) = S (snap_pc hs) /\
    snap_mu (kami_step hs (instr_ljoin c1reg c2reg cost)) = snap_mu hs + S cost.
Proof.
  intros. unfold kami_step, kami_advance_default. simpl. auto.
Qed.

(** Mu always advances for LASSERT, regardless of check outcome. *)
Theorem lassert_vm_step_mu :
  forall (vs vs' : VMState) (freg creg : nat) (kind : bool) (flen cost : nat),
    vm_step vs (instr_lassert freg creg kind flen cost) vs' ->
    vm_mu vs' = vm_mu vs + (flen * 8 + S cost).
Proof.
  intros vs vs' freg creg kind flen cost Hstep.
  inversion Hstep; subst; unfold apply_cost; simpl; lia.
Qed.

(** PC for LASSERT depends on check_ok. *)
Theorem lassert_vm_step_pc :
  forall (vs vs' : VMState) (freg creg : nat) (kind : bool) (flen cost : nat),
    vm_step vs (instr_lassert freg creg kind flen cost) vs' ->
    vm_pc vs' = (if lassert_exec_ok vs freg creg kind flen
                 then S (vm_pc vs)
                 else LASSERT_TRAP_PC).
Proof.
  intros vs vs' freg creg kind flen cost Hstep.
  inversion Hstep; subst; simpl; reflexivity.
Qed.

(** Definitional lemma *)
Theorem ljoin_vm_step_pc_mu :
  forall (vs vs' : VMState) (c1reg c2reg : nat) (cost : nat),
    vm_step vs (instr_ljoin c1reg c2reg cost) vs' ->
    vm_pc vs' = S (vm_pc vs) /\
    vm_mu vs' = vm_mu vs + S cost.
Proof.
  intros vs vs' c1reg c2reg cost Hstep.
  inversion Hstep; subst; unfold advance_state, apply_cost; simpl; auto.
Qed.

(** PC commutation diamond + μ agreement theorem

    Hardware and kernel agree on PC after LASSERT only when check passes.
    For μ, both sides charge flen * 8 + S cost.

    For LJOIN: hardware and kernel always agree on both PC and mu. *)

(** PC commutation for LASSERT holds only when the combined execution guard passes. *)
Theorem lassert_pc_commutation :
  forall (hs : KamiSnapshot) (vs vs' : VMState) (freg creg : nat)
         (kind : bool) (flen cost : nat),
    abs_phase1 hs = vs ->
    vm_step vs (instr_lassert freg creg kind flen cost) vs' ->
    lassert_exec_ok vs freg creg kind flen = true ->
    snap_pc (kami_step hs (instr_lassert freg creg kind flen cost)) = vm_pc vs'.
Proof.
  intros hs vs vs' freg creg kind flen cost Habs Hstep Hcheck.
  destruct (lassert_kami_step_pc_mu hs freg creg kind flen cost) as [Hpc_hw _].
  pose proof (lassert_vm_step_pc vs vs' freg creg kind flen cost Hstep) as Hpc_vm.
  subst vs. rewrite Hpc_hw, Hcheck, Hpc_vm, Hcheck. reflexivity.
Qed.

(** Mu agreement: hardware now charges flen * 8 + S cost matching the kernel.
    The gap is zero. *)
Theorem lassert_mu_gap :
  forall (hs : KamiSnapshot) (vs vs' : VMState) (freg creg : nat)
         (kind : bool) (flen cost : nat),
    abs_phase1 hs = vs ->
    vm_step vs (instr_lassert freg creg kind flen cost) vs' ->
    vm_mu vs' = snap_mu (kami_step hs (instr_lassert freg creg kind flen cost)).
Proof.
  intros hs vs vs' freg creg kind flen cost Habs Hstep.
  destruct (lassert_kami_step_pc_mu hs freg creg kind flen cost) as [_ Hmu_hw].
  pose proof (lassert_vm_step_mu vs vs' freg creg kind flen cost Hstep) as Hmu_vm.
  subst vs. rewrite Hmu_hw, Hmu_vm.
  unfold abs_phase1. simpl. lia.
Qed.

(** Definitional lemma *)
Theorem ljoin_pc_mu_commutation :
  forall (hs : KamiSnapshot) (vs vs' : VMState) (c1reg c2reg : nat) (cost : nat),
    abs_phase1 hs = vs ->
    vm_step vs (instr_ljoin c1reg c2reg cost) vs' ->
    snap_pc (kami_step hs (instr_ljoin c1reg c2reg cost)) = vm_pc vs' /\
    snap_mu (kami_step hs (instr_ljoin c1reg c2reg cost)) = vm_mu vs'.
Proof.
  intros hs vs vs' c1reg c2reg cost Habs Hstep.
  destruct (ljoin_kami_step_pc_mu hs c1reg c2reg cost) as [Hpc_hw Hmu_hw].
  destruct (ljoin_vm_step_pc_mu vs vs' c1reg c2reg cost Hstep) as [Hpc_vm Hmu_vm].
  subst vs. rewrite Hpc_hw, Hmu_hw, Hpc_vm, Hmu_vm.
  unfold abs_phase1. simpl. auto.
Qed.

(** Error flag determination

    Given the VMState and register indices, we can predict the vm_err
    outcome of the kernel step. *)

(** Definitional lemma *)
Theorem lassert_vm_step_err :
  forall (vs vs' : VMState) (freg creg : nat) (kind : bool) (flen cost : nat),
    vm_step vs (instr_lassert freg creg kind flen cost) vs' ->
    vm_err vs' = if lassert_exec_ok vs freg creg kind flen then vm_err vs else true.
Proof.
  intros vs vs' freg creg kind flen cost Hstep.
  inversion Hstep; subst; simpl; reflexivity.
Qed.

(** Definitional lemma *)
Theorem ljoin_vm_step_err :
  forall (vs vs' : VMState) (c1reg c2reg : nat) (cost : nat),
    vm_step vs (instr_ljoin c1reg c2reg cost) vs' ->
    vm_err vs' = ljoin_expected_err vs c1reg c2reg.
Proof.
  intros vs vs' c1reg c2reg cost Hstep.
  unfold ljoin_expected_err.
  inversion Hstep; subst; unfold advance_state; simpl; reflexivity.
Qed.

(** Main theorem: on-chip logic engine equivalence

    For any hardware snapshot and logic instruction, there exists a kernel
    post-state such that the hardware step and the kernel step agree on PC
    (when check passes) and the error flag is fully determined by the
    register-indexed strings.

    For LASSERT: hardware charges flen*8 + S cost matching the kernel.
    The mu gap is zero.  PC agreement requires lassert_check_ok = true.

    For LJOIN: hardware and kernel agree on both PC and mu (no gap),
    since both steps read from the same mem_to_string operands. *)

Theorem logic_engine_equivalent_lassert :
  forall (hs : KamiSnapshot) (freg creg : nat) (kind : bool) (flen cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_lassert freg creg kind flen cost) vs' /\
      vm_mu vs' = snap_mu (kami_step hs (instr_lassert freg creg kind flen cost)) /\
      (lassert_exec_ok (abs_phase1 hs) freg creg kind flen = true ->
       snap_pc (kami_step hs (instr_lassert freg creg kind flen cost)) = vm_pc vs') /\
      vm_err vs' = if lassert_exec_ok (abs_phase1 hs) freg creg kind flen
           then vm_err (abs_phase1 hs)
           else true.
Proof.
  intros hs freg creg kind flen cost.
  destruct (verilog_simulates_vm_step_lassert hs freg creg kind flen cost)
    as [vs' Hstep].
  exists vs'. split; [exact Hstep |].
  split; [exact (lassert_mu_gap hs (abs_phase1 hs) vs' freg creg kind flen cost
                   eq_refl Hstep) |].
  split; [exact (lassert_pc_commutation hs (abs_phase1 hs) vs' freg creg kind flen cost
                   eq_refl Hstep) |].
  apply (lassert_vm_step_err (abs_phase1 hs) vs' freg creg kind flen cost Hstep).
Qed.

Theorem logic_engine_equivalent_ljoin :
  forall (hs : KamiSnapshot) (c1reg c2reg : nat) (cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_ljoin c1reg c2reg cost) vs' /\
      snap_pc (kami_step hs (instr_ljoin c1reg c2reg cost)) = vm_pc vs' /\
      snap_mu (kami_step hs (instr_ljoin c1reg c2reg cost)) = vm_mu vs' /\
      vm_err vs' = ljoin_expected_err (abs_phase1 hs) c1reg c2reg.
Proof.
  intros hs c1reg c2reg cost.
  destruct (verilog_simulates_vm_step_ljoin hs c1reg c2reg cost) as [vs' Hstep].
  exists vs'. split; [exact Hstep |].
  destruct (ljoin_pc_mu_commutation hs (abs_phase1 hs) vs' c1reg c2reg cost
              eq_refl Hstep) as [Hpc Hmu].
  split; [exact Hpc |].
  split; [exact Hmu |].
  apply (ljoin_vm_step_err (abs_phase1 hs) vs' c1reg c2reg cost Hstep).
Qed.

(** Corollary: mu-monotonicity is preserved through the on-chip logic engine

    Regardless of certificate outcome, mu only increases. *)

(** Definitional lemma *)
Corollary logic_engine_mu_monotone_lassert :
  forall (hs : KamiSnapshot) (freg creg : nat) (kind : bool) (flen cost : nat),
    snap_mu (kami_step hs (instr_lassert freg creg kind flen cost)) >= snap_mu hs.
Proof.
  intros. destruct (lassert_kami_step_pc_mu hs freg creg kind flen cost) as [_ Hmu].
  rewrite Hmu. lia.
Qed.

(** Definitional lemma *)
Corollary logic_engine_mu_monotone_ljoin :
  forall (hs : KamiSnapshot) (c1reg c2reg : nat) (cost : nat),
    snap_mu (kami_step hs (instr_ljoin c1reg c2reg cost)) >= snap_mu hs.
Proof.
  intros. destruct (ljoin_kami_step_pc_mu hs c1reg c2reg cost) as [_ Hmu].
  lia.
Qed.
