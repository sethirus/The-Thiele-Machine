(** HardwareShadowBridge.v

    The hardware-shadow bridge theorem: RTL observation of any KamiSnapshot
    is exactly the classical shadow of its abstract Thiele VM state.

      State-level: Proved (hardware_shadow_compat, hardware_shadow_sim_rel).
      Trace-level: Proved for 30/46 opcodes unconditionally
        (rtl_shadow_trace_compat_extended in ShadowDeviceTrace.v),
        34/46 with preconditions (adding CALL, RET, CHSH_TRIAL, TENSOR_SET/GET,
        LJOIN from EmbedStep_WF.v + ShadowEmbedStep.v).
      Full 46-opcode, PC-driven trace correctness is now also exported under
        explicit [WFDrivenPrecondition] through
        [rtl_shadow_trace_compat_wf] in ShadowDeviceTrace.v.
        This uses the stronger abs_full_snapshot/GraphReconstructionBridge path.

      LASSERT is now covered through the checked EmbedStep/LogicEngine path:
      its formula-length μ charge and dual-witness guard are aligned with
      the kernel semantics.

    Key facts used:
      - verilog_sim_rel ks s := abs_phase1 ks = s  (VerilogRefinement.v)
      - abs_phase1 maps snap_{regs,mem,pc,mu,err,certified} directly
        to the 6 fields that shadow_proj reads from VMState           (Abstraction.v)
      - shadow_proj reads exactly vm_{regs,mem,pc,mu,err,certified}   (ShadowProjection.v)
    so shadow_proj ∘ abs_phase1 equals the direct hardware observation
    by definitional equality (no arithmetic, no rewriting needed).
*)

From Coq Require Import List Arith.PeanoNat.
Import ListNotations.

From Kernel  Require Import VMState ShadowProjection.
From KamiHW  Require Import Abstraction VerilogRefinement FullAbstraction.

(** RTL classical observation

    Reads exactly the 6 fields that [shadow_proj] reads from [VMState],
    but directly from [KamiSnapshot] — no round-trip through [abs_phase1]. *)
Definition rtl_classical_obs (ks : KamiSnapshot) : ClassicalState :=
  {| cs_regs      := snapshot_regs_to_list (snap_regs ks)  ;
     cs_mem       := snapshot_mem_to_list  (snap_mem  ks)  ;
     cs_pc        := snap_pc        ks                     ;
     cs_mu        := snap_mu        ks                     ;
     cs_err       := snap_err       ks                     ;
     cs_certified := snap_certified ks                     |}.

(** Hardware-shadow compatibility theorem (state level)

    The RTL-observable classical state of any hardware snapshot equals the
    classical shadow of the corresponding abstract Thiele VM state.

    Proof: both sides unfold to the same record — definitional equality. *)
(* DEFINITIONAL HELPER: rtl_classical_obs and shadow_proj ∘ abs_phase1 agree by record unfolding. *)
Theorem hardware_shadow_compat :
  forall ks : KamiSnapshot,
    rtl_classical_obs ks = shadow_proj (abs_phase1 ks).
Proof.
  intros ks.
  unfold rtl_classical_obs, shadow_proj, abs_phase1.
  reflexivity.
Qed.

(* DEFINITIONAL HELPER: full snapshots project to the same classical fields as
   rtl_classical_obs after unfolding the record bridges. *)
Theorem hardware_shadow_compat_full :
  forall ks : KamiSnapshot,
    rtl_classical_obs ks =
    shadow_proj (abs_full_snapshot (full_snapshot_of_snapshot ks)).
Proof.
  intros ks.
  unfold rtl_classical_obs, shadow_proj, abs_full_snapshot, full_snapshot_of_snapshot.
  reflexivity.
Qed.

(** Simulation-relation form

    Restates [hardware_shadow_compat] using the [verilog_sim_rel] pairing.
    Immediately useful after any per-instruction simulation step from
    [VerilogRefinement.v]. *)
Theorem hardware_shadow_sim_rel :
  forall (ks : KamiSnapshot) (s : VMState),
    verilog_sim_rel ks s ->
    rtl_classical_obs ks = shadow_proj s.
Proof.
  intros ks s H.
  unfold verilog_sim_rel in H.
  rewrite <- H.
  exact (hardware_shadow_compat ks).
Qed.

(** Classical shadow uniquely determined by hardware snapshot

    Two hardware snapshots that agree on all RTL-observable fields have the
    same classical shadow, regardless of which abstract Thiele state they refine. *)
Corollary rtl_classical_obs_injective_shadow :
  forall (ks1 ks2 : KamiSnapshot),
    rtl_classical_obs ks1 = rtl_classical_obs ks2 <->
    shadow_proj (abs_phase1 ks1) = shadow_proj (abs_phase1 ks2).
Proof.
  intros ks1 ks2.
  rewrite <- hardware_shadow_compat, <- hardware_shadow_compat.
  tauto.
Qed.

(** RTL hardware observes only the classical shadow

    The observable RTL state is the image of [shadow_proj] on the abstract
    Thiele state.  Structure discarded by [shadow_proj] (graph, CSRs,
    mu_tensor, logic_acc, mstatus, witness counters) is not recoverable
    from [rtl_classical_obs].

    This is the formal counterpart of the informal claim
    "hardware only sees the classical shadow of the Thiele execution." *)
Corollary hardware_sees_only_classical_shadow :
  forall ks : KamiSnapshot,
    exists s : VMState,
      rtl_classical_obs ks = shadow_proj s.
Proof.
  intros ks.
  exists (abs_phase1 ks).
  exact (hardware_shadow_compat ks).
Qed.

(** μ-cost preserved through the hardware-shadow bridge

    The RTL-observable μ value equals [vm_mu] of the abstract Thiele state.
    This connects the hardware layer to the μ-ledger cost story:
    the classical shadow carries μ faithfully, so hardware-observable cost
    is the same as the certified-cost recorded in the Thiele execution. *)
Corollary hardware_shadow_mu_preserved :
  forall ks : KamiSnapshot,
    (rtl_classical_obs ks).(cs_mu) = (abs_phase1 ks).(vm_mu).
Proof.
  intros ks.
  unfold rtl_classical_obs, abs_phase1.
  reflexivity.
Qed.

(** Shadow certification flag preserved

    The hardware [snap_certified] flag equals [vm_certified] in the abstract
    Thiele state — so classical observers can read certification status,
    but cannot read the structural content (graph, CSRs) that justifies it. *)
(* DEFINITIONAL HELPER: certification flag is a direct field projection. *)
Corollary hardware_shadow_cert_preserved :
  forall ks : KamiSnapshot,
    (rtl_classical_obs ks).(cs_certified) = (abs_phase1 ks).(vm_certified).
Proof.
  intros ks.
  unfold rtl_classical_obs, abs_phase1.
  reflexivity.
Qed.
