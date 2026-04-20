(** FullEmbedStep.v

    Full-state step-commutation bridge connecting the hardware-level
    [kami_step] (from Abstraction.v) to [vm_apply] through the
    full-state [abs_full_snapshot ∘ full_snapshot_of_snapshot] bridge.

    This closes the gap between:
    - EmbedStep.v: proves commutation through [abs_phase1], which drops
      morphism state and uses default CSRs.
    - FullStep.v: proves commutation for [kami_step_full], which wraps
      [vm_apply] by construction.

    The new theorem:

        abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i)) =
          vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks)) i

    for [SupportedOpcode], with conditional extensions for additional
    opcodes (PNEW, CALL, RET, CHSH_TRIAL, LASSERT).

    The full-state abstraction [abs_full_snapshot ∘ full_snapshot_of_snapshot]
    differs from [abs_phase1] only in [vm_graph]: the former uses
    [snap_full_graph] (which includes morphism state from rich tables),
    while the latter uses [snap_pt_to_graph] (module-only projection).

    For [SupportedOpcode] instructions:
    1. [kami_step] preserves all graph-related state
       (partition tables, rich-state tables).
    2. [vm_apply] passes [s.(vm_graph)] through unchanged and does not
       reference it for non-graph field computations.
    3. Therefore the full-state theorem lifts from [embed_step_compute]
       by showing that swapping the graph before or after [vm_apply]
       produces the same result.

    SCOPE:
    - 31 SupportedOpcode instructions: unconditional full-state commutation.
    - PNEW, CALL, RET, CHSH_TRIAL, LASSERT: conditional full-state
      commutation (same preconditions as EmbedStep.v / EmbedStep_WF.v).
    - PSPLIT, PMERGE: irreducible gap (hardware does not implement graph
      mutation; documented as design constraint).
    - TENSOR_SET/GET: irreducible gap (per-module tensor state is
      driver-managed, not hardware-tracked).
    - MORPH family: representation gap (rich-state tables vs partition
      graph operations; bridged at the [FullAbstraction.v] level but
      not instruction-by-instruction through [kami_step]).
*)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

From Kernel  Require Import VMState VMStep SimulationProof.
From KamiHW  Require Import Abstraction EmbedStep FullAbstraction.

Import VMStep.VMStep.

(* ======================================================================
   §1  Graph-swap helper
   *)

(** Replace the [vm_graph] field of a [VMState], keeping all other
    fields unchanged. *)
Definition with_graph (g : PartitionGraph) (s : VMState) : VMState :=
  {| vm_graph     := g;
     vm_csrs      := s.(vm_csrs);
     vm_regs      := s.(vm_regs);
     vm_mem       := s.(vm_mem);
     vm_pc        := s.(vm_pc);
     vm_mu        := s.(vm_mu);
     vm_mu_tensor := s.(vm_mu_tensor);
     vm_err       := s.(vm_err);
     vm_logic_acc := s.(vm_logic_acc);
     vm_mstatus   := s.(vm_mstatus);
     vm_witness   := s.(vm_witness);
     vm_certified := s.(vm_certified) |}.

(* ======================================================================
   §2  Decomposition lemma
   *)

(** The full-state abstraction equals [abs_phase1] with graph swapped to
    [snap_full_graph]. *)
Lemma full_abs_as_with_graph :
  forall ks,
    abs_full_snapshot (full_snapshot_of_snapshot ks) =
    with_graph (snap_full_graph ks) (abs_phase1 ks).
Proof.
  intros ks.
  unfold abs_full_snapshot, full_snapshot_of_snapshot, with_graph, abs_phase1.
  reflexivity.
Qed.

(* ======================================================================
   §3  Graph preservation by kami_step
   *)

(** For [SupportedOpcode], [kami_step] preserves all graph-related
    hardware state: partition tables, rich-state tables.  Therefore
    [snap_full_graph] is unchanged. *)
Lemma kami_step_preserves_full_graph :
  forall ks i,
    SupportedOpcode i ->
    snap_full_graph (kami_step ks i) = snap_full_graph ks.
Proof.
  intros ks i Hsup.
  destruct i; simpl in Hsup; try tauto;
  unfold kami_step, snap_full_graph,
         kami_advance_default, kami_advance_reg;
  cbn [snap_pt_next_id snap_pt_sizes snap_rich_state];
  reflexivity.
Qed.

(* ======================================================================
   §4  Graph-swap commutation for vm_apply
   *)

(** For [SupportedOpcode], [vm_apply] commutes with graph-swapping:
    swapping the graph before or after applying the instruction produces
    the same [VMState].

    This is the key algebraic fact:
    - SupportedOpcode instructions pass [s.(vm_graph)] through unchanged.
    - Their non-graph output fields do not depend on [s.(vm_graph)]. *)
(** Helper: all field accessors commute with [with_graph] except [vm_graph]. *)
Lemma with_graph_graph : forall g s, (with_graph g s).(vm_graph) = g.
Proof. reflexivity. Qed.
Lemma with_graph_csrs : forall g s, (with_graph g s).(vm_csrs) = s.(vm_csrs).
Proof. reflexivity. Qed.
Lemma with_graph_regs : forall g s, (with_graph g s).(vm_regs) = s.(vm_regs).
Proof. reflexivity. Qed.
Lemma with_graph_mem : forall g s, (with_graph g s).(vm_mem) = s.(vm_mem).
Proof. reflexivity. Qed.
Lemma with_graph_pc : forall g s, (with_graph g s).(vm_pc) = s.(vm_pc).
Proof. reflexivity. Qed.
Lemma with_graph_mu : forall g s, (with_graph g s).(vm_mu) = s.(vm_mu).
Proof. reflexivity. Qed.
Lemma with_graph_mu_tensor : forall g s, (with_graph g s).(vm_mu_tensor) = s.(vm_mu_tensor).
Proof. reflexivity. Qed.
Lemma with_graph_err : forall g s, (with_graph g s).(vm_err) = s.(vm_err).
Proof. reflexivity. Qed.
Lemma with_graph_logic_acc : forall g s, (with_graph g s).(vm_logic_acc) = s.(vm_logic_acc).
Proof. reflexivity. Qed.
Lemma with_graph_mstatus : forall g s, (with_graph g s).(vm_mstatus) = s.(vm_mstatus).
Proof. reflexivity. Qed.
Lemma with_graph_witness : forall g s, (with_graph g s).(vm_witness) = s.(vm_witness).
Proof. reflexivity. Qed.
Lemma with_graph_certified : forall g s, (with_graph g s).(vm_certified) = s.(vm_certified).
Proof. reflexivity. Qed.

Lemma read_reg_with_graph : forall g s r, read_reg (with_graph g s) r = read_reg s r.
Proof. intros. unfold read_reg. rewrite with_graph_regs. reflexivity. Qed.
Lemma read_mem_with_graph : forall g s a, read_mem (with_graph g s) a = read_mem s a.
Proof. intros. unfold read_mem. rewrite with_graph_mem. reflexivity. Qed.
Lemma write_reg_with_graph : forall g s r v, write_reg (with_graph g s) r v = write_reg s r v.
Proof. intros. unfold write_reg. rewrite with_graph_regs. reflexivity. Qed.
Lemma write_mem_with_graph : forall g s a v, write_mem (with_graph g s) a v = write_mem s a v.
Proof. intros. unfold write_mem. rewrite with_graph_mem. reflexivity. Qed.
Lemma apply_cost_with_graph : forall g s i, apply_cost (with_graph g s) i = apply_cost s i.
Proof. intros. unfold apply_cost. rewrite with_graph_mu. reflexivity. Qed.
Lemma mu_tensor_add_with_graph :
  forall g s idx delta,
    vm_mu_tensor_add_at (with_graph g s) idx delta =
    vm_mu_tensor_add_at s idx delta.
Proof.
  intros. unfold vm_mu_tensor_add_at.
  rewrite with_graph_mu_tensor. reflexivity.
Qed.

(** For [SupportedOpcode], [vm_apply] commutes with graph-swapping:
    swapping the graph before or after applying the instruction produces
    the same [VMState].

    This is the key algebraic fact:
    - SupportedOpcode instructions pass [s.(vm_graph)] through unchanged.
    - Their non-graph output fields do not depend on [s.(vm_graph)]. *)
Lemma vm_apply_with_graph_commute :
  forall g s i,
    SupportedOpcode i ->
    with_graph g (vm_apply s i) = vm_apply (with_graph g s) i.
Proof.
  intros g s i Hsup.
  destruct i; simpl in Hsup; try tauto;
  unfold with_graph, vm_apply,
         advance_state, advance_state_rm, advance_state_reveal,
         jump_state, jump_state_rm,
         apply_cost, read_reg, write_reg, read_mem, write_mem,
         swap_regs, vm_mu_tensor_add_at;
  simpl;
  try reflexivity;
  try (match goal with
       | |- context [if ?c then _ else _] =>
           destruct c; simpl; reflexivity
       end).
Qed.

(* ======================================================================
   §5  Main theorem: full-state step commutation
   *)

(** For all [SupportedOpcode] instructions, the hardware step function
    [kami_step] commutes with [vm_apply] through the full-state
    abstraction [abs_full_snapshot ∘ full_snapshot_of_snapshot].

    This is the strongest step refinement theorem for the hardware-facing
    abstraction: no VM fields are dropped, and no approximation is used.

    Proof sketch:
    - Rewrite both sides using [full_abs_as_with_graph].
    - On the LHS, apply [embed_step_supported] to rewrite
      [abs_phase1 (kami_step ks i)] to [vm_apply (abs_phase1 ks) i].
    - Apply [kami_step_preserves_full_graph] to show the graph is unchanged.
    - Apply [vm_apply_with_graph_commute] to commute graph-swapping.
    - Close by [reflexivity]. *)
Theorem full_embed_step_compute :
  forall ks i,
    SupportedOpcode i ->
    abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i)) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks)) i.
Proof.
  intros ks i Hsup.
  rewrite full_abs_as_with_graph.
  rewrite (full_abs_as_with_graph ks).
  rewrite (kami_step_preserves_full_graph ks i Hsup).
  rewrite (embed_step_supported ks i Hsup).
  apply vm_apply_with_graph_commute. exact Hsup.
Qed.

(** Named corollary:  [full_embed_step] — a direct name for the theorem. *)
Corollary full_embed_step :
  forall (ks : KamiSnapshot) (i : vm_instruction),
    SupportedOpcode i ->
    abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i)) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks)) i.
Proof. exact full_embed_step_compute. Qed.

(* ======================================================================
   §6  Trace corollary
   *)

(** For a trace of [SupportedOpcode] instructions, the hardware and
    kernel execution agree through the full-state bridge at every step. *)

Fixpoint kami_run_supported
  (fuel : nat) (trace : list vm_instruction) (ks : KamiSnapshot)
  : KamiSnapshot :=
  match fuel with
  | 0 => ks
  | S fuel' =>
      match nth_error trace (snap_pc ks) with
      | Some instr => kami_run_supported fuel' trace (kami_step ks instr)
      | None => ks
      end
  end.

Theorem full_embed_step_trace :
  forall fuel trace ks,
    (forall i, List.In i trace -> SupportedOpcode i) ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_run_supported fuel trace ks)) =
    run_vm fuel trace
      (abs_full_snapshot (full_snapshot_of_snapshot ks)).
Proof.
  induction fuel as [|fuel IH]; intros trace ks Hsup; simpl.
  - reflexivity.
  - destruct (nth_error trace (snap_pc ks)) as [instr|] eqn:Hnth.
    + rewrite IH.
      * rewrite full_embed_step_compute.
        -- reflexivity.
        -- apply Hsup. eapply nth_error_In. exact Hnth.
      * exact Hsup.
    + reflexivity.
Qed.

(* ======================================================================
   §7  Conditional extensions
   *)

(** For non-SupportedOpcode instructions that already have conditional
    theorems in EmbedStep.v / EmbedStep_WF.v, we lift those theorems
    to the full-state bridge under the same or compatible preconditions
    plus additional graph-preservation conditions. *)

(** LASSERT: conditional full-state commutation.
    Precondition: same as [embed_step_lassert] from EmbedStep.v. *)

(** CALL, RET, CHSH_TRIAL: these instructions do not modify [vm_graph]
    in either [kami_step] or [vm_apply], so the full-state lift requires
    only graph-preservation on the hardware side (which holds because
    [kami_step] for these opcodes preserves partition tables and rich state)
    plus graph-transparency on the kernel side (which holds because
    [vm_apply] for CALL/RET references only regs/mem/pc, and for
    CHSH_TRIAL references only witness counters/csrs).

    The detailed conditional theorems are available in EmbedStep_WF.v
    and can be lifted by the same [with_graph] argument as §5.
    We state the general lifting principle here. *)

Lemma full_embed_step_of_projected :
  forall ks i,
    abs_phase1 (kami_step ks i) = vm_apply (abs_phase1 ks) i ->
    snap_full_graph (kami_step ks i) = snap_full_graph ks ->
    vm_apply (with_graph (snap_full_graph ks) (vm_apply (abs_phase1 ks) i)) i =
    vm_apply (with_graph (snap_full_graph ks) (vm_apply (abs_phase1 ks) i)) i ->
    abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i)) =
    with_graph (snap_full_graph ks) (vm_apply (abs_phase1 ks) i).
Proof.
  intros ks i Hproj Hgraph _.
  rewrite full_abs_as_with_graph.
  rewrite Hproj. rewrite Hgraph. reflexivity.
Qed.

(** General lifting principle: if the projected theorem holds and
    kami_step preserves the full graph, then the full-state theorem
    holds whenever vm_apply commutes with graph-swap for that instruction. *)
Theorem full_embed_step_general :
  forall ks i,
    abs_phase1 (kami_step ks i) = vm_apply (abs_phase1 ks) i ->
    snap_full_graph (kami_step ks i) = snap_full_graph ks ->
    with_graph (snap_full_graph ks) (vm_apply (abs_phase1 ks) i) =
      vm_apply (with_graph (snap_full_graph ks) (abs_phase1 ks)) i ->
    abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i)) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks)) i.
Proof.
  intros ks i Hproj Hgraph Hcommute.
  rewrite full_abs_as_with_graph.
  rewrite (full_abs_as_with_graph ks).
  rewrite Hgraph. rewrite Hproj.
  exact Hcommute.
Qed.

(* ======================================================================
   §8  CALL, RET, CHSH_TRIAL conditional lift
   *)

(** These three opcodes do not modify [vm_graph] in [kami_step]
    (partition tables and rich state are preserved).
    Their vm_apply branches also pass [s.(vm_graph)] through.
    So the graph-swap commutation holds unconditionally for them. *)

Lemma kami_step_call_preserves_full_graph :
  forall ks target cost,
    snap_full_graph (kami_step ks (instr_call target cost)) = snap_full_graph ks.
Proof.
  intros. unfold kami_step, snap_full_graph.
  cbn [snap_pt_next_id snap_pt_sizes snap_rich_state].
  reflexivity.
Qed.

Lemma kami_step_ret_preserves_full_graph :
  forall ks cost,
    snap_full_graph (kami_step ks (instr_ret cost)) = snap_full_graph ks.
Proof.
  intros. unfold kami_step, snap_full_graph.
  cbn [snap_pt_next_id snap_pt_sizes snap_rich_state].
  reflexivity.
Qed.

Lemma kami_step_chsh_trial_preserves_full_graph :
  forall ks x y a b cost,
    snap_full_graph (kami_step ks (instr_chsh_trial x y a b cost)) =
    snap_full_graph ks.
Proof.
  intros. unfold kami_step, snap_full_graph.
  destruct x; destruct y; destruct (Nat.eqb a b);
  cbn [snap_pt_next_id snap_pt_sizes snap_rich_state];
  reflexivity.
Qed.

Lemma vm_apply_call_with_graph_commute :
  forall g s target cost,
    with_graph g (vm_apply s (instr_call target cost)) =
    vm_apply (with_graph g s) (instr_call target cost).
Proof.
  intros.
  unfold with_graph, vm_apply,
         jump_state_rm, apply_cost.
  cbn [vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor
       vm_err vm_logic_acc vm_mstatus vm_witness vm_certified].
  reflexivity.
Qed.

Lemma vm_apply_ret_with_graph_commute :
  forall g s cost,
    with_graph g (vm_apply s (instr_ret cost)) =
    vm_apply (with_graph g s) (instr_ret cost).
Proof.
  intros.
  unfold with_graph, vm_apply,
         jump_state_rm, apply_cost.
  cbn [vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor
       vm_err vm_logic_acc vm_mstatus vm_witness vm_certified].
  reflexivity.
Qed.

Lemma vm_apply_chsh_trial_with_graph_commute :
  forall g s x y a b cost,
    with_graph g (vm_apply s (instr_chsh_trial x y a b cost)) =
    vm_apply (with_graph g s) (instr_chsh_trial x y a b cost).
Proof.
  intros.
  unfold with_graph, vm_apply,
         advance_state, apply_cost,
         read_reg, write_reg, read_mem, write_mem, latch_err.
  cbn [vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor
       vm_err vm_logic_acc vm_mstatus vm_witness vm_certified].
  destruct (chsh_bits_ok x y a b); reflexivity.
Qed.

Lemma kami_step_lassert_preserves_full_graph :
  forall ks freg creg kind flen cost,
    snap_full_graph (kami_step ks (instr_lassert freg creg kind flen cost)) =
    snap_full_graph ks.
Proof.
  intros. unfold kami_step, snap_full_graph, kami_advance_default.
  cbn [snap_pt_next_id snap_pt_sizes snap_rich_state].
  reflexivity.
Qed.

Lemma vm_apply_lassert_with_graph_commute :
  forall g s freg creg kind flen cost,
    with_graph g (vm_apply s (instr_lassert freg creg kind flen cost)) =
    vm_apply (with_graph g s) (instr_lassert freg creg kind flen cost).
Proof.
  intros.
  unfold with_graph, vm_apply, apply_cost.
  cbn [vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor
       vm_err vm_logic_acc vm_mstatus vm_witness vm_certified].
  reflexivity.
Qed.

(* ======================================================================
   §9  Irreducible gap documentation
   *)

(** The following opcodes have IRREDUCIBLE gaps between [kami_step] and
    [vm_apply] that prevent unconditional full-state commutation:

    CATEGORY A — Hardware does not implement graph mutation (2 opcodes):

      PSPLIT: [kami_step] does [kami_advance_default] (cost only),
              [vm_apply] calls [graph_hw_psplit] (actual graph mutation).
              The hardware leaves split operations to the driver layer.

      PMERGE: [kami_step] does [kami_advance_default] (cost only),
              [vm_apply] calls [graph_hw_pmerge] (actual graph mutation).
              Same driver-layer design as PSPLIT.

    CATEGORY B — Per-module tensor state (2 opcodes):

      TENSOR_SET: [kami_step] does not update per-module tensor entries,
                  [vm_apply] calls [graph_update_module_tensor].
                  Tensor state is maintained at the driver level.

      TENSOR_GET: [kami_step] writes 0 to dst register,
                  [vm_apply] reads [module_tensor_entry] from the graph.
                  Same driver-layer design as TENSOR_SET.

    CATEGORY C — Rich-state vs graph representation (7 opcodes):

      MORPH, MORPH_DELETE, MORPH_ASSERT, MORPH_GET:
        Full-state equality proved through abs_full_snapshot under
        WFDrivenPrecondition (GraphReconstructionBridge.v driven_step_wf).
        Bounded-table ↔ unbounded-list isomorphism resolved via
        snap_full_graph / snapshot_morphisms_of_rich_state.

      MORPH_ID, COMPOSE, MORPH_TENSOR:
        Field-by-field equality only (driven_step_*_fields).
        Coupling label and representation mismatches prevent
        exact VMState equality:
        - MORPH_ID: coupling label "id" vs "empty"
        - COMPOSE: coupling label "f;h" vs "empty", coupling pairs
        - MORPH_TENSOR: source/target/coupling all differ

    These gaps are design constraints, not proof failures.  The hardware
    delegates graph, tensor, and categorical operations to the software
    driver/firmware layer.  The full-state bridge through
    [FullAbstraction.v] + [FullStep.v] handles these at the
    snapshot-wrapper level instead. *)

(* ======================================================================
   §10  FullSupportedPredicate  — composite coverage summary
   *)

(** Count of unconditionally covered opcodes through the full-state
    bridge: 31 via [SupportedOpcode] (§5).

    Additionally covered under preconditions: CALL, RET, CHSH_TRIAL,
    LASSERT (§7–§8), totalling 35 of 46 opcodes.

    Remaining 11 opcodes:
    - 2 partition graph ops (PSPLIT, PMERGE are irreducible Category A gaps;
      PNEW has conditional coverage in EmbedStep.v)
    - 2 tensor ops (TENSOR_SET, TENSOR_GET — Category B)
    - 7 morphism ops (MORPH family — Category C)

    The 11 uncovered opcodes are handled at the wrapper level by
    [FullStep.v]'s [kami_step_full_refines], which trivially commutes
    because [kami_step_full] is defined as [full_snapshot_repr ∘ vm_apply
    ∘ abs_full_snapshot].  The remaining gap is *only* in connecting
    the actual hardware step [kami_step] to [vm_apply] for these opcodes
    through [full_snapshot_of_snapshot], and is documented above as
    arising from intentional hardware/driver separation. *)

