(** LogicEngineEquivalence.v

    On-chip logic engine: LASSERT/LJOIN instructions read formula and
    certificate strings directly from VM memory via register-indexed
    addresses. This file proves equivalence lemmas showing that PC, mu,
    and error flags are determined by the register contents and the
    check_model/check_lrat/String.eqb functions.

    The external coprocessor model (lassert_oracle, lassert_certificate)
    has been replaced by on-chip memory reads via mem_to_string. Formula
    and certificate pointers are stored in VM registers (freg, creg);
    the on-chip checker reads them directly at step time.

    KEY DESIGN DECISION:
    The hardware reads formula and certificate strings from VM data memory
    via register-indexed base addresses. The Coq kernel calls
    check_model/check_lrat/String.eqb inline on mem_to_string results.
    This file proves that PC, mu, and error flags are fully determined
    by the register-indexed strings and the certificate checkers.
*)

From Coq Require Import Arith.PeanoNat Lia Bool Strings.String.
From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.
From KamiHW Require Import Abstraction VerilogRefinement.

Import VMStep.VMStep.

(** * Expected error flag after LASSERT

    Computes the vm_err value that vm_step will produce for an LASSERT
    instruction, given the current VMState and register indices:
    - kind = true (SAT mode): check_model; vm_err preserved iff model is valid
    - kind = false (UNSAT mode): always error (diagnostic condition — UNSAT
      means the kernel records that no new axiom can be added, which is
      treated as an informational error, regardless of proof validity) *)
Definition lassert_expected_err (s : VMState) (freg creg : nat) (kind : bool) : bool :=
  let formula := mem_to_string (vm_mem s) (read_reg s freg) in
  let cert    := mem_to_string (vm_mem s) (read_reg s creg) in
  if kind then
    if check_model formula cert then vm_err s else true
  else
    true.

(** * Expected error flag after LJOIN

    Computes the vm_err value that vm_step will produce for an LJOIN
    instruction, given the current VMState and register indices:
    - vm_err preserved iff both cert strings are equal *)
Definition ljoin_expected_err (s : VMState) (c1reg c2reg : nat) : bool :=
  let cert1 := mem_to_string (vm_mem s) (read_reg s c1reg) in
  let cert2 := mem_to_string (vm_mem s) (read_reg s c2reg) in
  if String.eqb cert1 cert2 then vm_err s else true.

(** * PC/mu commutation lemmas

    Both hardware (kami_step) and kernel (vm_step) always advance PC by 1
    and charge mu for LASSERT/LJOIN, regardless of certificate outcome.
    Hardware charges S cost; kernel charges flen * 8 + S cost for LASSERT
    (the extra flen * 8 accounts for reading the formula string from memory). *)

(** Definitional lemma *)
Theorem lassert_kami_step_pc_mu :
  forall (hs : KamiSnapshot) (freg creg : nat) (kind : bool) (flen cost : nat),
    snap_pc (kami_step hs (instr_lassert freg creg kind flen cost)) = S (snap_pc hs) /\
    snap_mu (kami_step hs (instr_lassert freg creg kind flen cost)) = snap_mu hs + S cost.
Proof.
  intros. unfold kami_step, kami_advance_default. simpl. auto.
Qed.

(** Definitional lemma *)
Theorem ljoin_kami_step_pc_mu :
  forall (hs : KamiSnapshot) (c1reg c2reg : nat) (cost : nat),
    snap_pc (kami_step hs (instr_ljoin c1reg c2reg cost)) = S (snap_pc hs) /\
    snap_mu (kami_step hs (instr_ljoin c1reg c2reg cost)) = snap_mu hs + S cost.
Proof.
  intros. unfold kami_step, kami_advance_default. simpl. auto.
Qed.

(** Definitional lemma *)
Theorem lassert_vm_step_pc_mu :
  forall (vs vs' : VMState) (freg creg : nat) (kind : bool) (flen cost : nat),
    vm_step vs (instr_lassert freg creg kind flen cost) vs' ->
    vm_pc vs' = S (vm_pc vs) /\
    vm_mu vs' = vm_mu vs + (flen * 8 + S cost).
Proof.
  intros vs vs' freg creg kind flen cost Hstep.
  inversion Hstep; subst; unfold advance_state, apply_cost; simpl; auto.
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

(** * PC commutation diamond + mu gap theorem

    Hardware and kernel agree on PC after LASSERT/LJOIN.
    For mu, hardware charges S cost; software charges flen * 8 + S cost.
    The gap is flen * 8 bits (the physical reading cost of the formula
    that hardware pays lazily vs the kernel charging upfront). *)

(** Definitional lemma *)
Theorem lassert_pc_commutation :
  forall (hs : KamiSnapshot) (vs vs' : VMState) (freg creg : nat)
         (kind : bool) (flen cost : nat),
    abs_phase1 hs = vs ->
    vm_step vs (instr_lassert freg creg kind flen cost) vs' ->
    snap_pc (kami_step hs (instr_lassert freg creg kind flen cost)) = vm_pc vs'.
Proof.
  intros hs vs vs' freg creg kind flen cost Habs Hstep.
  destruct (lassert_kami_step_pc_mu hs freg creg kind flen cost) as [Hpc_hw _].
  destruct (lassert_vm_step_pc_mu vs vs' freg creg kind flen cost Hstep) as [Hpc_vm _].
  subst vs. rewrite Hpc_hw, Hpc_vm. auto.
Qed.

(** The mu gap: kernel charges flen * 8 more than hardware for LASSERT. *)
Theorem lassert_mu_gap :
  forall (hs : KamiSnapshot) (vs vs' : VMState) (freg creg : nat)
         (kind : bool) (flen cost : nat),
    abs_phase1 hs = vs ->
    vm_step vs (instr_lassert freg creg kind flen cost) vs' ->
    vm_mu vs' = snap_mu (kami_step hs (instr_lassert freg creg kind flen cost))
                + flen * 8.
Proof.
  intros hs vs vs' freg creg kind flen cost Habs Hstep.
  destruct (lassert_kami_step_pc_mu hs freg creg kind flen cost) as [_ Hmu_hw].
  destruct (lassert_vm_step_pc_mu vs vs' freg creg kind flen cost Hstep) as [_ Hmu_vm].
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

(** * Error flag determination

    Given the VMState and register indices, we can predict the vm_err
    outcome of the kernel step. *)

(** Definitional lemma *)
Theorem lassert_vm_step_err :
  forall (vs vs' : VMState) (freg creg : nat) (kind : bool) (flen cost : nat),
    vm_step vs (instr_lassert freg creg kind flen cost) vs' ->
    vm_err vs' = lassert_expected_err vs freg creg kind.
Proof.
  intros vs vs' freg creg kind flen cost Hstep.
  unfold lassert_expected_err.
  inversion Hstep; subst;
    unfold advance_state, latch_err; simpl;
    match goal with
    | [ H : check_model _ _ = true  |- _ ] => rewrite H; reflexivity
    | [ H : check_model _ _ = false |- _ ] => rewrite H; reflexivity
    | _ => reflexivity
    end.
Qed.

(** Definitional lemma *)
Theorem ljoin_vm_step_err :
  forall (vs vs' : VMState) (c1reg c2reg : nat) (cost : nat),
    vm_step vs (instr_ljoin c1reg c2reg cost) vs' ->
    vm_err vs' = ljoin_expected_err vs c1reg c2reg.
Proof.
  intros vs vs' c1reg c2reg cost Hstep.
  unfold ljoin_expected_err.
  inversion Hstep; subst;
    unfold advance_state, latch_err; simpl;
    match goal with
    | [ H : String.eqb _ _ = _ |- _ ] => rewrite H; reflexivity
    end.
Qed.

(** * Main theorem: on-chip logic engine equivalence

    For any hardware snapshot and logic instruction, there exists a kernel
    post-state such that the hardware step and the kernel step agree on PC
    and the error flag is fully determined by the register-indexed strings.

    For LASSERT: hardware charges S cost, kernel charges flen*8 + S cost.
    The mu gap (flen * 8) accounts for on-chip formula reading cost.

    For LJOIN: hardware and kernel agree on both PC and mu (no gap),
    since both steps read from the same mem_to_string operands. *)

Theorem logic_engine_equivalent_lassert :
  forall (hs : KamiSnapshot) (freg creg : nat) (kind : bool) (flen cost : nat),
    exists vs',
      vm_step (abs_phase1 hs) (instr_lassert freg creg kind flen cost) vs' /\
      snap_pc (kami_step hs (instr_lassert freg creg kind flen cost)) = vm_pc vs' /\
      vm_mu vs' = snap_mu (kami_step hs (instr_lassert freg creg kind flen cost))
                  + flen * 8 /\
      vm_err vs' = lassert_expected_err (abs_phase1 hs) freg creg kind.
Proof.
  intros hs freg creg kind flen cost.
  destruct (verilog_simulates_vm_step_lassert hs freg creg kind flen cost)
    as [vs' Hstep].
  exists vs'. split; [exact Hstep |].
  split; [exact (lassert_pc_commutation hs (abs_phase1 hs) vs' freg creg kind flen cost
                   eq_refl Hstep) |].
  split; [exact (lassert_mu_gap hs (abs_phase1 hs) vs' freg creg kind flen cost
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

(** * Corollary: mu-monotonicity is preserved through the on-chip logic engine

    Regardless of certificate outcome, mu only increases. *)

(** Definitional lemma *)
Corollary logic_engine_mu_monotone_lassert :
  forall (hs : KamiSnapshot) (freg creg : nat) (kind : bool) (flen cost : nat),
    snap_mu (kami_step hs (instr_lassert freg creg kind flen cost)) >= snap_mu hs.
Proof.
  intros. destruct (lassert_kami_step_pc_mu hs freg creg kind flen cost) as [_ Hmu].
  lia.
Qed.

(** Definitional lemma *)
Corollary logic_engine_mu_monotone_ljoin :
  forall (hs : KamiSnapshot) (c1reg c2reg : nat) (cost : nat),
    snap_mu (kami_step hs (instr_ljoin c1reg c2reg cost)) >= snap_mu hs.
Proof.
  intros. destruct (ljoin_kami_step_pc_mu hs c1reg c2reg cost) as [_ Hmu].
  lia.
Qed.
