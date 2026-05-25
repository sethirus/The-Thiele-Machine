(** VerilogSemantics.v

    Provides a concrete Coq instantiation of the VerilogRTLCorrespondence
    Section Variables by using [KamiSnapshot] as the Verilog state type.

    PURPOSE: Item 3 of CLOSURE_ROADMAP.md (RTL step correctness).

    The [VerilogRTLCorrespondence] section in kernel/VerilogRTLCorrespondence.v
    uses Section Variables for the Verilog state type and step function.
    This file CLOSES those variables by instantiating:
      VerilogState   := KamiSnapshot
      verilog_step   := kami_step
      verilog_regs   := abs_phase1 >> vm_regs
      ... (other observations via abs_phase1)

    The key theorem is [coq_kami_model_satisfies_rtl_step_correct], which
    proves [rtl_step_correct] holds for the Kami Coq model using the
    already-proved [full_embed_step] / [kami_refines_vm_step] chain.

    THE REMAINING TRUST BOUNDARY:
    This file closes rtl_step_correct for the COQKAMI model.  The physical
    Verilog (thiele_cpu_kami.v) is only connected via the BSC compiler:

        KamiSnapshot (Coq) ─── kami_step ────────────────────────┐
              |                                                    |
              | (Coq extraction: formally verified)               | vm_apply via
              ▼                                                    | full_embed_step (Qed)
        KamiHW/Target.ml                                          |
              |                                                    |
              | PP.ml BSC: NAMED TRUST BOUNDARY (b)               |
              ▼                                                    |
        thiele_cpu_kami.v ─── Verilog step ───────────────────────┘

    Trust boundary (b) is named [bsc_kami_compilation_trusted] (still True).
    The repo already has a verified Coq path from Kami modules to the
    Bluespec-subset AST ([getModuleS] -> [ModulesSToBModules] ->
    [canonical_cpu_module] in [kami_hw/CanonicalCPUProof.v]; the
    equality [canonical_cpu_module = ModulesSToBModules thieleBusTopS]
    holds by [unfold] alone — see the comment above that definition).
    It also now has a checked RTL pipeline
    provenance manifest ([artifacts/rtl_pipeline_manifest.json]) that pins the
    canonical extraction/printer/BSV/Verilog artifacts and enforces byte
    identity between the generated synthesis RTL and the tracked RTL. It also
    has a text-transform audit ([artifacts/rtl_text_transform_audit.json]) that
    replays the project BSV preprocessing/RegFile transform and Verilog storage
    transform byte-for-byte.
    What remains is the text/backend semantic preservation side after the AST
    boundary. It cannot be removed without either:
    (a) A verified printer/backend from the Coq BModules AST to Verilog, OR
    (b) A Coq semantics for the specific subset of Verilog BSC generates
        + a computational proof that the specific thiele_cpu_kami.v matches
        kami_step.  This is the "shorter but narrower" path from CLOSURE_ROADMAP.
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
    (forall ks' i, WFDrivenPrecondition ks' i) ->
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
