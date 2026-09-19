(** VerilogSemantics.v

    Instantiates the abstract VerilogRTLCorrespondence interface with
    KamiSnapshot and Abstraction.kami_step. The historical file/interface
    names do not make this a semantics of the generated Verilog.

    The results below concern the intermediate Gallina model and its VM
    observations. The applicable WF-driven variants carry their explicit
    representation and opcode premises. They do not prove that each physical
    clock or instruction retirement implements this model.

    The synthesizable source is ThieleCPUCore.thieleCore, a Kami module with
    actual rules. NormalizationRetirement and MorphRetirement separately
    establish selected executions of portions of that module. Their bounded
    register premises, scheduling scope, and raw-pair observation must be
    connected to an instruction-boundary invariant before claiming a full
    FSM refinement.

    CanonicalCPUProof constructs the backend AST from the actual module.
    Definitional equality of that construction is not semantic preservation
    of extraction, OCaml printing, BSV transformations, Bluespec compilation,
    Verilog transformations, synthesis, or place-and-route. The pipeline
    manifest and text-transform audit record provenance and replayed byte
    transformations; they do not prove those downstream semantic edges.

    A physical correspondence result still requires the actual FSM proof and
    an explicit classification of every downstream edge as proved, validated,
    tested, or trusted. No such edge is discharged merely by assigning the
    Gallina kami_step function to an interface field named verilog_step.
*)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From KamiHW Require Import Abstraction.
From KamiHW Require Import FullAbstraction.
From KamiHW Require Import EmbedStep.
From KamiHW Require Import FullEmbedStep.
From KamiHW Require Import GraphReconstructionBridge.

Open Scope nat_scope.

(** ** Observation functions for the Kami Coq model.

    These project the abstract VMState fields from a KamiSnapshot.
    They use abs_phase1 from Abstraction.v. *)

Definition coq_verilog_graph  (ks : KamiSnapshot) : PartitionGraph :=
  vm_graph  (abs_phase1 ks).
Definition coq_verilog_csrs   (ks : KamiSnapshot) : CSRState :=
  vm_csrs   (abs_phase1 ks).
Definition coq_verilog_regs   (ks : KamiSnapshot) : list nat :=
  vm_regs   (abs_phase1 ks).
Definition coq_verilog_mem    (ks : KamiSnapshot) : list nat :=
  vm_mem    (abs_phase1 ks).
Definition coq_verilog_pc     (ks : KamiSnapshot) : nat :=
  vm_pc     (abs_phase1 ks).
Definition coq_verilog_mu     (ks : KamiSnapshot) : nat :=
  vm_mu     (abs_phase1 ks).
Definition coq_verilog_mu_tensor (ks : KamiSnapshot) : list nat :=
  vm_mu_tensor (abs_phase1 ks).
Definition coq_verilog_err    (ks : KamiSnapshot) : bool :=
  vm_err    (abs_phase1 ks).
Definition coq_verilog_logic_acc (ks : KamiSnapshot) : nat :=
  vm_logic_acc (abs_phase1 ks).
Definition coq_verilog_mstatus (ks : KamiSnapshot) : nat :=
  vm_mstatus (abs_phase1 ks).

(** ** The core correctness theorem: kami_step satisfies rtl_step_correct.

    For any SupportedOpcode instruction i, stepping a KamiSnapshot produces
    a new KamiSnapshot whose abstract observations match vm_apply exactly.

    Proof: directly from full_embed_step_compute (already Qed without section
    variables). *)
Theorem coq_kami_model_satisfies_rtl_step_correct :
  forall (ks : KamiSnapshot) (i : vm_instruction),
    SupportedOpcode i ->
    let input := abs_full_snapshot (full_snapshot_of_snapshot ks) in
    let output := vm_apply input i in
    abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i)) = output.
Proof.
  intros ks i Hsup.
  exact (full_embed_step_compute ks i Hsup).
Qed.

(** ** Corollary: observable fields agree after any supported step. *)
Corollary coq_kami_model_mu_correct :
  forall (ks : KamiSnapshot) (i : vm_instruction),
    SupportedOpcode i ->
    vm_mu (abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i))) =
    vm_mu (vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks)) i).
Proof.
  intros ks i Hsup.
  rewrite coq_kami_model_satisfies_rtl_step_correct; [reflexivity | exact Hsup].
Qed.

Corollary coq_kami_model_pc_correct :
  forall (ks : KamiSnapshot) (i : vm_instruction),
    SupportedOpcode i ->
    vm_pc (abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i))) =
    vm_pc (vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks)) i).
Proof.
  intros ks i Hsup.
  rewrite coq_kami_model_satisfies_rtl_step_correct; [reflexivity | exact Hsup].
Qed.

Corollary coq_kami_model_regs_correct :
  forall (ks : KamiSnapshot) (i : vm_instruction),
    SupportedOpcode i ->
    vm_regs (abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i))) =
    vm_regs (vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks)) i).
Proof.
  intros ks i Hsup.
  rewrite coq_kami_model_satisfies_rtl_step_correct; [reflexivity | exact Hsup].
Qed.

(** ** Trace correctness: for a full trace of supported opcodes, the Kami
    model agrees with vm_apply at every step. *)
Theorem coq_kami_model_trace_correct :
  forall fuel trace ks,
    (forall i, List.In i trace -> SupportedOpcode i) ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_run_supported fuel trace ks)) =
    run_vm fuel trace
      (abs_full_snapshot (full_snapshot_of_snapshot ks)).
Proof.
  exact full_embed_step_trace.
Qed.

(** ** Stronger corollary: all 46 opcodes are covered under the explicit
    driver/well-formedness precondition exported by GraphReconstructionBridge.

    This is the strongest proof surface currently available inside Coq for
    Item 3: every instruction in the ISA is covered by a Qed theorem, with the
    exact side conditions made explicit rather than hidden in tests. *)
Theorem coq_kami_model_satisfies_rtl_step_correct_wf :
  forall (ks : KamiSnapshot) (i : vm_instruction),
    WFDrivenPrecondition ks i ->
    let input := abs_full_snapshot (full_snapshot_of_snapshot ks) in
    let output := vm_apply input i in
    abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i)) = output.
Proof.
  intros ks i Hwf.
  exact (driven_step_wf ks i Hwf).
Qed.

(* INQUISITOR NOTE: alias for the closure-roadmap trace surface. The proved
   theorem is [driven_trace_commutes]; this exports it under the Item 3 name. *)
Theorem coq_kami_model_trace_correct_wf :
  forall fuel trace ks,
    WFDrivenRun fuel trace ks ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_run_driven fuel trace ks)) =
    run_vm fuel trace
      (abs_full_snapshot (full_snapshot_of_snapshot ks)).
Proof.
  exact driven_trace_commutes.
Qed.

(** ** Status summary for CLOSURE_ROADMAP.md Item 3.

    CLOSED (0 Admitted, 0 Section Variables, 0 global Axioms):
    - coq_kami_model_satisfies_rtl_step_correct (Qed)
    - coq_kami_model_trace_correct (Qed)
    - coq_kami_model_satisfies_rtl_step_correct_wf (Qed)
    - coq_kami_model_trace_correct_wf (Qed)
    The first pair applies to all SupportedOpcodes.
    The second pair lifts the result to the full 46-opcode ISA under the
    explicit WFDrivenPrecondition exported by GraphReconstructionBridge.

    REMAINING SECTION VARIABLE (not Admitted):
    - bsc_kami_compilation_trusted: PP.ml / project transforms / BSC → Verilog correctness.
      Named as [True] in VerilogRTLCorrespondence.v because the claim
      cannot be stated as a Coq Prop without formalizing BSC semantics.
      Artifact provenance, tracked-RTL identity, and text-transform scope are
      pinned separately by [scripts/generate_rtl_pipeline_manifest.py --check]
      and [scripts/audit_rtl_text_transforms.py --check].

    TO FULLY CLOSE bsc_kami_compilation_trusted, implement one of:
    (a) bmodules_to_verilog : BModules -> VerilogModule in Coq
      Prove bmodules_to_verilog is correct over the existing Coq-generated
      BModules AST and extract it to produce thiele_cpu_kami.v directly.
      Then [bsc_kami_compilation_trusted] is replaced by a proved theorem.
    (b) VerilogCorrectnessProof: write a Q-valued semantics for the specific
        subset of Verilog in thiele_cpu_kami.v, and use [native_decide] to
        compute agreement with kami_step for all 46 opcodes.
        Estimated effort: ~2000 lines, fully mechanical.
*)
Definition rtl_trust_boundary_audit : Prop :=
  (* Layer 1: Coq kernel <-> Kami Coq model -- PROVED *)
  (forall ks i, SupportedOpcode i ->
    abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i)) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks)) i) /\
  (* Layer 2: Kami Coq model <-> generated Verilog -- SECTION VARIABLE *)
  (* bsc_kami_compilation_trusted covers this layer *)
  True.

(* INQUISITOR NOTE: alias for full_embed_step_compute — summary re-export for rtl_trust_boundary_audit self-documentation. *)
Theorem rtl_trust_boundary_audit_layer1 :
  (* Layer 1 is fully proved: *)
  forall ks i, SupportedOpcode i ->
    abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i)) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks)) i.
Proof.
  exact full_embed_step_compute.
Qed.
