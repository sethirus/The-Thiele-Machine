(** Conditional correspondence between a projected RTL execution model and
    the Coq VM. Every step observes all VMState fields, including witness
    counters and certification. [verilog_step] denotes a completed instruction;
    a hardware implementation may use several clock cycles for that step.

    The theorems require [rtl_step_correct]. A Coq VM instance of this interface
    is constructible; instantiating it for generated Verilog additionally needs
    a model of that artifact and a semantic correspondence proof. Simulation
    tests supply finite execution evidence. Extraction, the Kami printer,
    project text transforms, and the Bluespec compiler remain trusted parts
    of the artifact pipeline. The named trust propositions below label those
    external obligations; they do not imply [rtl_step_correct]. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof ThreeLayerIsomorphism HardwareBisimulation.

Section RTLCorrespondenceSection.

(* SCOPE NOTE: abstract interface section, exported theorems quantify over the implementation and its step contract. *)
Variable VerilogState : Type.

Variable verilog_step : VerilogState -> vm_instruction -> VerilogState.

Variable verilog_graph : VerilogState -> PartitionGraph.
Variable verilog_csrs  : VerilogState -> CSRState.
Variable verilog_regs  : VerilogState -> list nat.
Variable verilog_mem   : VerilogState -> list nat.
Variable verilog_pc    : VerilogState -> nat.
Variable verilog_mu    : VerilogState -> nat.
Variable verilog_mu_tensor : VerilogState -> list nat.
Variable verilog_err   : VerilogState -> bool.
Variable verilog_logic_acc : VerilogState -> nat.
Variable verilog_mstatus   : VerilogState -> nat.
Variable verilog_witness : VerilogState -> WitnessCounts.
Variable verilog_certified : VerilogState -> bool.

(* SCOPE NOTE: abstract interface section, per-instruction correspondence is an explicit theorem premise. *)
Variable rtl_step_correct :
  forall (s : VerilogState) (i : vm_instruction),
  let input := project_vmstate
                 (verilog_graph s) (verilog_csrs s)
                 (verilog_regs  s) (verilog_mem   s)
                 (verilog_pc    s) (verilog_mu     s)
                 (verilog_mu_tensor s) (verilog_err s)
                 (verilog_logic_acc s) (verilog_mstatus s)
                 (verilog_witness s) (verilog_certified s) in
  let output := vm_apply input i in
  verilog_graph (verilog_step s i) = vm_graph output /\
  verilog_csrs  (verilog_step s i) = vm_csrs  output /\
  verilog_regs  (verilog_step s i) = vm_regs  output /\
  verilog_mem   (verilog_step s i) = vm_mem   output /\
  verilog_pc    (verilog_step s i) = vm_pc    output /\
  verilog_mu    (verilog_step s i) = vm_mu    output /\
  verilog_mu_tensor (verilog_step s i) = vm_mu_tensor output /\
  verilog_err   (verilog_step s i) = vm_err   output /\
  verilog_logic_acc (verilog_step s i) = vm_logic_acc output /\
  verilog_mstatus   (verilog_step s i) = vm_mstatus   output /\
  verilog_witness (verilog_step s i) = vm_witness output /\
  verilog_certified (verilog_step s i) = vm_certified output.

(* SCOPE NOTE: abstract interface section, names of external compiler obligations. *)
Variable kami_pretty_printer_trusted : Prop.

Variable bluespec_compiler_trusted : Prop.

Definition bsc_kami_compilation_trusted : Prop :=
  kami_pretty_printer_trusted /\ bluespec_compiler_trusted.

Definition verilog_full_wire_spec : FullWireSpec := {|
  fws_state     := VerilogState;
  fws_step      := verilog_step;
  fws_graph     := verilog_graph;
  fws_csrs      := verilog_csrs;
  fws_regs      := verilog_regs;
  fws_mem       := verilog_mem;
  fws_pc        := verilog_pc;
  fws_mu        := verilog_mu;
  fws_mu_tensor := verilog_mu_tensor;
  fws_err       := verilog_err;
  fws_logic_acc := verilog_logic_acc;
  fws_mstatus   := verilog_mstatus;
  fws_witness   := verilog_witness;
  fws_certified := verilog_certified;
  fws_step_correct := rtl_step_correct
|}.

Theorem rtl_coq_single_step_bisimulation :
  forall (s_coq : VMState) (s_rtl : VerilogState) (i : vm_instruction),
  vm_graph     s_coq = verilog_graph s_rtl ->
  vm_csrs      s_coq = verilog_csrs  s_rtl ->
  vm_regs      s_coq = verilog_regs  s_rtl ->
  vm_mem       s_coq = verilog_mem   s_rtl ->
  vm_pc        s_coq = verilog_pc    s_rtl ->
  vm_mu        s_coq = verilog_mu    s_rtl ->
  vm_mu_tensor s_coq = verilog_mu_tensor s_rtl ->
  vm_err       s_coq = verilog_err   s_rtl ->
  vm_logic_acc s_coq = verilog_logic_acc s_rtl ->
  vm_mstatus   s_coq = verilog_mstatus   s_rtl ->
  vm_witness   s_coq = verilog_witness s_rtl ->
  vm_certified s_coq = verilog_certified s_rtl ->

  vm_graph     (vm_apply s_coq i) = verilog_graph (verilog_step s_rtl i) /\
  vm_csrs      (vm_apply s_coq i) = verilog_csrs  (verilog_step s_rtl i) /\
  vm_regs      (vm_apply s_coq i) = verilog_regs  (verilog_step s_rtl i) /\
  vm_mem       (vm_apply s_coq i) = verilog_mem   (verilog_step s_rtl i) /\
  vm_pc        (vm_apply s_coq i) = verilog_pc    (verilog_step s_rtl i) /\
  vm_mu        (vm_apply s_coq i) = verilog_mu    (verilog_step s_rtl i) /\
  vm_mu_tensor (vm_apply s_coq i) = verilog_mu_tensor (verilog_step s_rtl i) /\
  vm_err       (vm_apply s_coq i) = verilog_err   (verilog_step s_rtl i) /\
  vm_logic_acc (vm_apply s_coq i) = verilog_logic_acc (verilog_step s_rtl i) /\
  vm_mstatus   (vm_apply s_coq i) = verilog_mstatus   (verilog_step s_rtl i) /\
  vm_witness   (vm_apply s_coq i) = verilog_witness (verilog_step s_rtl i) /\
  vm_certified (vm_apply s_coq i) = verilog_certified (verilog_step s_rtl i).
Proof.
  intros s_coq s_rtl i Hg Hc Hr Hm Hp Hmu Hmt He Hla Hms Hwit Hcert.
  exact (full_state_single_step_bisimulation
           coq_full_wire_spec verilog_full_wire_spec
           s_coq s_rtl i Hg Hc Hr Hm Hp Hmu Hmt He Hla Hms Hwit Hcert).
Qed.

Theorem rtl_coq_trace_bisimulation :
  forall (s_coq : VMState) (s_rtl : VerilogState)
         (instrs : list vm_instruction),
  vm_graph     s_coq = verilog_graph s_rtl ->
  vm_csrs      s_coq = verilog_csrs  s_rtl ->
  vm_regs      s_coq = verilog_regs  s_rtl ->
  vm_mem       s_coq = verilog_mem   s_rtl ->
  vm_pc        s_coq = verilog_pc    s_rtl ->
  vm_mu        s_coq = verilog_mu    s_rtl ->
  vm_mu_tensor s_coq = verilog_mu_tensor s_rtl ->
  vm_err       s_coq = verilog_err   s_rtl ->
  vm_logic_acc s_coq = verilog_logic_acc s_rtl ->
  vm_mstatus   s_coq = verilog_mstatus   s_rtl ->
  vm_witness   s_coq = verilog_witness s_rtl ->
  vm_certified s_coq = verilog_certified s_rtl ->
  vm_regs      (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_regs (run_fws verilog_full_wire_spec instrs s_rtl) /\
  vm_mem       (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_mem  (run_fws verilog_full_wire_spec instrs s_rtl) /\
  vm_pc        (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_pc   (run_fws verilog_full_wire_spec instrs s_rtl) /\
  vm_mu        (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_mu   (run_fws verilog_full_wire_spec instrs s_rtl) /\
  vm_mu_tensor (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_mu_tensor (run_fws verilog_full_wire_spec instrs s_rtl) /\
  vm_err       (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_err  (run_fws verilog_full_wire_spec instrs s_rtl).
Proof.
  intros s_coq s_rtl instrs Hg Hc Hr Hm Hp Hmu Hmt He Hla Hms Hwit Hcert.
  pose proof (coq_full_bisimilar_to_any
    verilog_full_wire_spec s_coq s_rtl instrs Hg Hc Hr Hm Hp Hmu Hmt He Hla Hms Hwit Hcert)
    as (Hr2 & Hm2 & Hmu2 & Hmt2 & He2 & Hp2 & Hwit2 & Hcert2).
  cbn [fws_regs fws_mem fws_mu fws_mu_tensor fws_err fws_pc] in *.
  repeat split; assumption.
Qed.

Corollary rtl_mu_cost_correspondence :
  forall (s_coq : VMState) (s_rtl : VerilogState)
         (instrs : list vm_instruction),
  vm_graph s_coq = verilog_graph s_rtl ->
  vm_csrs  s_coq = verilog_csrs  s_rtl ->
  vm_regs  s_coq = verilog_regs  s_rtl ->
  vm_mem   s_coq = verilog_mem   s_rtl ->
  vm_pc    s_coq = verilog_pc    s_rtl ->
  vm_mu    s_coq = verilog_mu    s_rtl ->
  vm_mu_tensor s_coq = verilog_mu_tensor s_rtl ->
  vm_err   s_coq = verilog_err   s_rtl ->
  vm_logic_acc s_coq = verilog_logic_acc s_rtl ->
  vm_mstatus   s_coq = verilog_mstatus   s_rtl ->
  vm_witness   s_coq = verilog_witness s_rtl ->
  vm_certified s_coq = verilog_certified s_rtl ->
  vm_mu (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_mu (run_fws verilog_full_wire_spec instrs s_rtl).
Proof.
  intros s_coq s_rtl instrs Hg Hc Hr Hm Hp Hmu Hmt He Hla Hms Hwit Hcert.
  destruct (rtl_coq_trace_bisimulation s_coq s_rtl instrs
              Hg Hc Hr Hm Hp Hmu Hmt He Hla Hms Hwit Hcert) as (_ & _ & _ & Hmu_final & _).
  exact Hmu_final.
Qed.

Corollary rtl_pc_correspondence :
  forall (s_coq : VMState) (s_rtl : VerilogState)
         (instrs : list vm_instruction),
  vm_graph s_coq = verilog_graph s_rtl ->
  vm_csrs  s_coq = verilog_csrs  s_rtl ->
  vm_regs  s_coq = verilog_regs  s_rtl ->
  vm_mem   s_coq = verilog_mem   s_rtl ->
  vm_pc    s_coq = verilog_pc    s_rtl ->
  vm_mu    s_coq = verilog_mu    s_rtl ->
  vm_mu_tensor s_coq = verilog_mu_tensor s_rtl ->
  vm_err   s_coq = verilog_err   s_rtl ->
  vm_logic_acc s_coq = verilog_logic_acc s_rtl ->
  vm_mstatus   s_coq = verilog_mstatus   s_rtl ->
  vm_witness   s_coq = verilog_witness s_rtl ->
  vm_certified s_coq = verilog_certified s_rtl ->
  vm_pc (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_pc (run_fws verilog_full_wire_spec instrs s_rtl).
Proof.
  intros s_coq s_rtl instrs Hg Hc Hr Hm Hp Hmu Hmt He Hla Hms Hwit Hcert.
  destruct (rtl_coq_trace_bisimulation s_coq s_rtl instrs
              Hg Hc Hr Hm Hp Hmu Hmt He Hla Hms Hwit Hcert) as (_ & _ & Hpc_final & _).
  exact Hpc_final.
Qed.

Corollary rtl_err_correspondence :
  forall (s_coq : VMState) (s_rtl : VerilogState)
         (instrs : list vm_instruction),
  vm_graph s_coq = verilog_graph s_rtl ->
  vm_csrs  s_coq = verilog_csrs  s_rtl ->
  vm_regs  s_coq = verilog_regs  s_rtl ->
  vm_mem   s_coq = verilog_mem   s_rtl ->
  vm_pc    s_coq = verilog_pc    s_rtl ->
  vm_mu    s_coq = verilog_mu    s_rtl ->
  vm_mu_tensor s_coq = verilog_mu_tensor s_rtl ->
  vm_err   s_coq = verilog_err   s_rtl ->
  vm_logic_acc s_coq = verilog_logic_acc s_rtl ->
  vm_mstatus   s_coq = verilog_mstatus   s_rtl ->
  vm_witness   s_coq = verilog_witness s_rtl ->
  vm_certified s_coq = verilog_certified s_rtl ->
  vm_err (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_err (run_fws verilog_full_wire_spec instrs s_rtl).
Proof.
  intros s_coq s_rtl instrs Hg Hc Hr Hm Hp Hmu Hmt He Hla Hms Hwit Hcert.
  destruct (rtl_coq_trace_bisimulation s_coq s_rtl instrs
              Hg Hc Hr Hm Hp Hmu Hmt He Hla Hms Hwit Hcert) as (_ & _ & _ & _ & _ & Herr).
  exact Herr.
Qed.

Theorem rtl_contract_trace_agreement :
  forall (s_coq : VMState) (s_rtl : VerilogState)
         (instrs : list vm_instruction),

  vm_graph     s_coq = verilog_graph s_rtl ->
  vm_csrs      s_coq = verilog_csrs  s_rtl ->
  vm_regs      s_coq = verilog_regs  s_rtl ->
  vm_mem       s_coq = verilog_mem   s_rtl ->
  vm_pc        s_coq = verilog_pc    s_rtl ->
  vm_mu        s_coq = verilog_mu    s_rtl ->
  vm_mu_tensor s_coq = verilog_mu_tensor s_rtl ->
  vm_err       s_coq = verilog_err   s_rtl ->
  vm_logic_acc s_coq = verilog_logic_acc s_rtl ->
  vm_mstatus   s_coq = verilog_mstatus   s_rtl ->
  vm_witness   s_coq = verilog_witness s_rtl ->
  vm_certified s_coq = verilog_certified s_rtl ->

  vm_regs  (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_regs  (run_fws verilog_full_wire_spec instrs s_rtl) /\
  vm_mem   (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_mem   (run_fws verilog_full_wire_spec instrs s_rtl) /\
  vm_pc    (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_pc    (run_fws verilog_full_wire_spec instrs s_rtl) /\
  vm_mu    (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_mu    (run_fws verilog_full_wire_spec instrs s_rtl) /\
  vm_mu_tensor (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_mu_tensor (run_fws verilog_full_wire_spec instrs s_rtl) /\
  vm_err   (run_fws coq_full_wire_spec instrs s_coq) =
    verilog_err   (run_fws verilog_full_wire_spec instrs s_rtl).
Proof.
  intros s_coq s_rtl instrs Hg Hc Hr Hm Hp Hmu Hmt He Hla Hms Hwit Hcert.
  apply (rtl_coq_trace_bisimulation s_coq s_rtl instrs
           Hg Hc Hr Hm Hp Hmu Hmt He Hla Hms Hwit Hcert).
Qed.

End RTLCorrespondenceSection.
