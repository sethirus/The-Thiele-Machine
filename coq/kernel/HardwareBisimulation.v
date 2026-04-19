(** HardwareBisimulation: Cost-Level Python / Hardware Comparison

    This file proves cost-level bisimulation only: mu-accumulation is
    consistent across an abstract hardware model and Python model. The
    HardwareState here is a 4-field abstraction (pc, mu, alu_ready, overflow)
    modeling only PC+1 sequential execution and cost accumulation. It does NOT
    model register files, memory, partition graph, CSRs, mu_tensor,
    jump/branch/call/ret targets, or any instruction-specific behavior.

    For full hardware state correspondence with the Kami-extracted RTL,
    see VerilogRefinement.v which uses KamiSnapshot (13 fields) and abs_phase1
    from Abstraction.v.

    The real results here - hw_bisimulation_step, hw_bisimulation_multi_step,
    hw_step_reflects_vm_cost - are useful for reasoning about mu-accumulation
    consistency. They do NOT prove full behavioral equivalence between hardware
    and software.

    I built the same machine three times: Coq (this file + VMState.v + VMStep.v),
    Python (thielecpu/vm.py, thin wrapper over OCaml extracted runner), and
    Verilog (thiele_cpu_kami.v, generated from Kami). This file proves the
    Python/hardware cost-accounting arrow.

    Hardware state and Python state correspond when hw.pc = py.pc,
    hw.mu_accumulator = py.mu, hw.overflow = py.err. For every step with cost c:
    Python runs new_pc = old_pc + 1, new_mu = old_mu + c; hardware does the same.
    If states correspond before a step, they correspond after. By induction:
    they correspond for all execution traces.

    Cosimulation tests in tests/test_verilog_cosim.py compare snapshots across
    layers. Any divergence fails the test.

    To break this cost-accounting claim: run hardware, run the OCaml extracted
    VM, and compare the PC/mu/overflow traces that this abstraction talks
    about. Divergence there falsifies the claim. Zero project-local axioms,
    zero Admitted. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep.

(** Abstract hardware state representation.

    This record models the tiny part of hardware state used in this file.
    The Kami-extracted RTL is in thielecpu/hardware/rtl/thiele_cpu_kami.v.

    Q16.16 values are represented here as nat-scaled quantities. This is enough
    for the addition and monotonicity facts below, but it is not a full
    fixed-point semantics.
    *)

Record HardwareState := {
  hw_pc : nat;                     (* Program counter register *)
  hw_mu_accumulator : nat;         (* μ-cost accumulator as a Q16.16-scaled nat *)
  hw_alu_ready : bool;             (* ALU ready flag *)
  hw_overflow : bool               (* Overflow/saturation flag *)
}.

(** Abstract Python-side state used by this comparison. *)

Record PythonState := {
  py_pc : nat;
  py_mu : nat;
  py_err : bool;
  py_graph_modules : nat
}.

(** Hardware/Python state correspondence.
    
    This defines when a hardware state corresponds to a Python state.
    The key invariants are:
    - Program counters match
    - μ-cost accumulators match (modulo Q16.16 encoding)
    - Error flags correspond to overflow flags
    *)

Definition hw_py_states_correspond (hw : HardwareState) (py : PythonState) : Prop :=
  hw.(hw_pc) = py.(py_pc) /\
  hw.(hw_mu_accumulator) = py.(py_mu) /\
  hw.(hw_overflow) = py.(py_err).

(** Hardware bisimulation invariant.
    
    The core bisimulation property: PC and μ-cost are preserved.
    *)

Definition hw_bisimulation_invariant (hw : HardwareState) (py : PythonState) : Prop :=
  hw.(hw_pc) = py.(py_pc) /\
  hw.(hw_mu_accumulator) = py.(py_mu).

(** Abstract hardware step function.
    
    Models a single clock cycle of hardware execution.
    The hardware advances PC and accumulates μ-cost.
    *)

Definition hardware_step (hw : HardwareState) (cost : nat) : HardwareState :=
  {| hw_pc := S hw.(hw_pc);
     hw_mu_accumulator := hw.(hw_mu_accumulator) + cost;
     hw_alu_ready := true;
     hw_overflow := hw.(hw_overflow)
  |}.

(** Abstract Python step function for the same cost-only model. *)

Definition python_step (py : PythonState) (cost : nat) : PythonState :=
  {| py_pc := S py.(py_pc);
     py_mu := py.(py_mu) + cost;
     py_err := py.(py_err);
     py_graph_modules := py.(py_graph_modules)
  |}.

(** Core bisimulation theorems. *)

(** Initial states correspond *)
Theorem hw_initial_correspondence :
  forall hw py,
    hw.(hw_pc) = 0 ->
    hw.(hw_mu_accumulator) = 0 ->
    py.(py_pc) = 0 ->
    py.(py_mu) = 0 ->
    hw_bisimulation_invariant hw py.
Proof.
  intros hw py Hpc_hw Hmu_hw Hpc_py Hmu_py.
  unfold hw_bisimulation_invariant.
  split; [rewrite Hpc_hw, Hpc_py | rewrite Hmu_hw, Hmu_py]; reflexivity.
Qed.

(** Step preserves PC correspondence *)
Theorem hw_step_preserves_pc :
  forall hw py cost,
    hw_bisimulation_invariant hw py ->
    (hardware_step hw cost).(hw_pc) = (python_step py cost).(py_pc).
Proof.
  intros hw py cost [Hpc Hmu].
  simpl.
  rewrite Hpc.
  reflexivity.
Qed.

(** Step preserves μ-cost correspondence *)
Theorem hw_step_preserves_mu :
  forall hw py cost,
    hw_bisimulation_invariant hw py ->
    (hardware_step hw cost).(hw_mu_accumulator) = (python_step py cost).(py_mu).
Proof.
  intros hw py cost [Hpc Hmu].
  simpl.
  rewrite Hmu.
  reflexivity.
Qed.

(** Full bisimulation step theorem *)
Theorem hw_bisimulation_step :
  forall hw py cost,
    hw_bisimulation_invariant hw py ->
    hw_bisimulation_invariant (hardware_step hw cost) (python_step py cost).
Proof.
  intros hw py cost Hinv.
  unfold hw_bisimulation_invariant.
  split.
  - apply hw_step_preserves_pc. exact Hinv.
  - apply hw_step_preserves_mu. exact Hinv.
Qed.

(** Multi-step bisimulation. *)

(** Multi-step hardware execution *)
Fixpoint hardware_multi_step (hw : HardwareState) (costs : list nat) : HardwareState :=
  match costs with
  | [] => hw
  | cost :: costs' => hardware_multi_step (hardware_step hw cost) costs'
  end.

(** Multi-step Python execution *)
Fixpoint python_multi_step (py : PythonState) (costs : list nat) : PythonState :=
  match costs with
  | [] => py
  | cost :: costs' => python_multi_step (python_step py cost) costs'
  end.

(** Multi-step bisimulation preservation *)
Theorem hw_bisimulation_multi_step :
  forall hw py costs,
    hw_bisimulation_invariant hw py ->
    hw_bisimulation_invariant (hardware_multi_step hw costs) (python_multi_step py costs).
Proof.
  intros hw py costs.
  revert hw py.
  induction costs as [|cost costs' IH]; intros hw py Hinv.
  - simpl. exact Hinv.
  - simpl.
    apply IH.
    apply hw_bisimulation_step.
    exact Hinv.
Qed.

(** μ-cost consistency corollary. *)

Corollary hw_mu_cost_consistency :
  forall hw py costs,
    hw_bisimulation_invariant hw py ->
    (hardware_multi_step hw costs).(hw_mu_accumulator) = 
    (python_multi_step py costs).(py_mu).
Proof.
  intros hw py costs Hinv.
  pose proof (hw_bisimulation_multi_step hw py costs Hinv) as [_ Hmu].
  exact Hmu.
Qed.

(** Abstract verification chain.
    
    Despite the historical theorem name below, this theorem only establishes
    the abstract hardware/Python cost-preservation chain in this file.
    
    Combined with separately checked PythonBisimulation.v facts, it contributes
    one link toward:
    
    Coq VM (formal proofs) 
        <-> Python VM (reference implementation)
        <-> abstract hardware cost model
    
    It does not by itself transfer every Coq theorem to physical hardware.
    Claims about RTL or FPGA behavior need the refinement/cosimulation layer.
    *)

Theorem complete_verification_chain :
  (* Given initial states that correspond *)
  forall hw_init py_init,
    hw_bisimulation_invariant hw_init py_init ->
    (* For any execution trace (list of instruction costs) *)
    forall costs : list nat,
    (* The bisimulation is preserved *)
    hw_bisimulation_invariant 
      (hardware_multi_step hw_init costs) 
      (python_multi_step py_init costs) /\
    (* And μ-cost is consistent *)
    (hardware_multi_step hw_init costs).(hw_mu_accumulator) =
    (python_multi_step py_init costs).(py_mu).
Proof.
  intros hw_init py_init Hinit costs.
  split.
  - apply hw_bisimulation_multi_step. exact Hinit.
  - apply hw_mu_cost_consistency. exact Hinit.
Qed.

(** Connection to vm_step.

    The abstract hardware_step and python_step functions model a uniform
    cost-charging cycle. This theorem establishes that for any concrete
    vm_step with instruction cost c, the abstract bisimulation holds. *)

Theorem hw_step_reflects_vm_cost :
  forall coq_s coq_s' hw py instr,
    hw_bisimulation_invariant hw py ->
    vm_step coq_s instr coq_s' ->
    hw_bisimulation_invariant
      (hardware_step hw (instruction_cost instr))
      (python_step py (instruction_cost instr)).
Proof.
  intros coq_s coq_s' hw py instr Hinv Hstep.
  (* Hstep witnesses that instr is a valid vm_step transition;
     the cost is well-defined by instruction_cost. *)
  inversion Hstep; subst; apply hw_bisimulation_step; exact Hinv.
Qed.

(** Q16.16 arithmetic facts for the scaled-nat model.
    
    These lemmas establish the nat addition facts used by the abstract
    hardware mu-ALU model.
    *)

Definition q16_16_one : nat := 65536.  (* 1.0 in Q16.16 = 2^16 *)

(** Q16.16-scaled nat addition is associative. *)
Lemma q16_add_assoc :
  forall a b c : nat,
    a + (b + c) = (a + b) + c.
Proof.
  intros. lia.
Qed.

(** Q16.16-scaled nat addition is commutative. *)
Lemma q16_add_comm :
  forall a b : nat,
    a + b = b + a.
Proof.
  intros. lia.
Qed.

(** μ-cost accumulation is monotonic *)
Lemma mu_accumulation_monotonic :
  forall hw costs,
    hw.(hw_mu_accumulator) <= (hardware_multi_step hw costs).(hw_mu_accumulator).
Proof.
  intros hw costs.
  revert hw.
  induction costs as [|cost costs' IH]; intros hw.
  - simpl. lia.
  - simpl.
    assert (Hstep : hw.(hw_mu_accumulator) <= (hardware_step hw cost).(hw_mu_accumulator)).
    { simpl. lia. }
    specialize (IH (hardware_step hw cost)).
    lia.
Qed.

(** Abstract hardware/Python correctness.
    
    The theorem name is historical. The theorem proves that the abstract
    hardware stepper and abstract Python stepper keep PC and mu-cost aligned
    for a list of costs. It does not prove synthesized RTL correctness.
    *)

Theorem hardware_synthesis_correctness :
  forall hw_init py_init costs,
    hw_bisimulation_invariant hw_init py_init ->
    (* Final states correspond *)
    let hw_final := hardware_multi_step hw_init costs in
    let py_final := python_multi_step py_init costs in
    hw_bisimulation_invariant hw_final py_final /\
    (* μ-cost is preserved exactly *)
    hw_final.(hw_mu_accumulator) = py_final.(py_mu) /\
    (* PC advances correctly *)
    hw_final.(hw_pc) = py_final.(py_pc).
Proof.
  intros hw_init py_init costs Hinit hw_final py_final.
  pose proof (complete_verification_chain hw_init py_init Hinit costs) as [Hbisim Hmu].
  unfold hw_final, py_final.
  destruct Hbisim as [Hpc Hmu'].
  repeat split; assumption.
Qed.

(** Summary.

    WHAT I PROVED IN THIS FILE:

    1. Hardware-software cost bisimulation (Theorem hardware_synthesis_correctness):
       The abstract hardware model is bisimilar to the abstract software cost
       model for PC and mu-cost.

    2. mu-cost exactness (Corollary hw_mu_cost_consistency):
       mu-accounting is preserved EXACTLY across the abstract models. Not approximately,
       not within error bars - EXACTLY.

    3. Multi-step preservation (Theorem hw_bisimulation_multi_step):
       If states correspond initially, they correspond after ANY execution trace.
       By induction on trace length.

    4. Complete verification chain (Theorem complete_verification_chain):
       This file supplies the hardware/Python cost-model link. Full
       Coq-to-RTL correspondence depends on the other refinement files and
       cosimulation tests.

    Properties expressed through this file's invariant can be transferred from
    the abstract hardware model to the Python model. Stronger claims about full
    physical hardware behavior require the separate RTL/refinement assumptions to
    be stated and checked.

    1. Synthesize the Verilog to FPGA (Xilinx, Intel, Lattice, whatever)
    2. Run the same test vectors through hardware and OCaml extracted VM
    3. Compare μ-accumulator values, PC values, observable outputs
    4. If they diverge by even 1 bit, the bisimulation is false

    The cosimulation tests generate random traces, execute on all three layers,
    compare snapshots. If ANY discrepancy occurs, the tests fail.

    Passing tests support the comparison story; they should not be paraphrased
    here as an unconditional proof that every repository layer is identical.

    The lemmas in this file are proven inside the current abstract hardware
    model. The remaining risk is cross-layer mismatch in the concrete runners
    or RTL, which is why the repository still needs the cosimulation checks.
*)
