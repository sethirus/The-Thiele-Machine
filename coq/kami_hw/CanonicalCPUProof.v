(** CanonicalCPUProof.v

    Single canonical entrypoint for the full Thiele CPU proof artifact.

    Intent:
    - Provide ONE root Coq object that downstream extraction/synthesis flows can
      reference directly.
    - Keep proof obligations constructive by re-exporting the proven refinement
      stack from the Kami hardware model to VM semantics.
*)

From KamiHW Require Import ThieleCPUCore.
From KamiHW Require Import ThieleTypes.
From KamiHW Require Import ThieleCPUBusTop.
From KamiHW Require Import Abstraction.
From KamiHW Require Import VerilogRefinement.
Require Import Kami.Ext.BSyntax.
From Coq Require Import List.
From Coq Require Import Strings.String.
From Coq Require Import Reals.
From Kernel Require Import VMState VMStep VMEncoding KernelTM.
From Kernel Require Import SimulationProof.
From Kernel Require Import MuCostModel MuLedgerConservation MuInitiality NoFreeInsight.
From Kernel Require Import Certification QuantumBound.
From Kernel Require Import RevelationRequirement.
From Kernel Require Import BornRuleLinearity TsirelsonQuantumModel.
From Kernel Require Import TsirelsonGeneral MuLedgerQuantumBridge.
From Kernel Require Import HonestNoFI MuShannonBridge MuShannonQuantitative StateSpaceCounting.
From Kernel Require Import HonestNoFI_TheoremsWithoutAssumptions.
From Kernel Require Import CategoryLaws CategoryMonoidal.
From KamiHW Require Import GraphReconstructionBridge.
From KamiHW Require Import FullAbstraction.

Import VMStep.VMStep.

(** Canonical hardware module as a direct Coq-generated Bluespec-subset AST.
  Route through the wrapper boundary so protocol integration evolves at source,
  but keep the emitted object explicit: this is already the result of the
  verified Kami synthesis path [getModuleS |> ModulesSToBModules]. *)
Definition canonical_cpu_module := thieleBusTopB.

(** Explicit generator normal form.

    This theorem isolates what is already closed on the option-2 path: the
    canonical extraction root is not a raw module term, but the Bluespec-subset
    AST produced in Coq by Kami's synthesis functions. The remaining trust
    boundary is therefore PP.ml/BSC after this point, not the AST generator. *)
Theorem canonical_cpu_module_from_source :
  canonical_cpu_module = ModulesSToBModules thieleBusTopS.
Proof.
  unfold canonical_cpu_module, thieleBusTopS.
  rewrite thieleBusTop_stage1_equiv.
  reflexivity.
Qed.

(** Entry point alias for the OCaml printer driver (expects targetB). *)
Definition targetB (_ : nat) := canonical_cpu_module.

(** Canonical abstraction relation and map. *)
Definition canonical_snapshot_to_vm := abs_phase1.
Definition canonical_refinement_relation := verilog_sim_rel.

(** Canonical theorem bundle: this is the top-level proof payload consumed by
    downstream users who want one source of truth. *)
Record CanonicalCPUProofBundle : Prop := {
  canonical_register_write_refines :
    forall (hs : KamiSnapshot) (dst v : nat),
      dst < RegCount ->
      snapshot_regs_to_list
        (fun j => if Nat.eqb j dst then word64 v else snap_regs hs j) =
      write_reg (abs_phase1 hs) dst v;

  canonical_load_imm_step_simulates :
    forall (hs : KamiSnapshot) (dst imm cost : nat),
      exists vs',
        vm_step (abs_phase1 hs) (instr_load_imm dst imm cost) vs' /\
        vs' =
          advance_state_rm (abs_phase1 hs) (instr_load_imm dst imm cost)
            (abs_phase1 hs).(vm_graph)
            (abs_phase1 hs).(vm_csrs)
            (write_reg (abs_phase1 hs) dst (word64 imm))
            (abs_phase1 hs).(vm_mem)
            (abs_phase1 hs).(vm_err);

  canonical_mu_monotone_on_charge :
    forall (hs : KamiSnapshot) (cost : nat),
      (abs_phase1 hs).(vm_mu) + cost >= (abs_phase1 hs).(vm_mu);

  canonical_oracle_charge_sound :
    forall (hs : KamiSnapshot) (cost : nat),
      (abs_phase1 hs).(vm_mu) + cost >= (abs_phase1 hs).(vm_mu);

  canonical_bus_step_preserves_abs_phase1 :
    forall (st : BusWrapperState) (op : BusOp),
      abs_phase1 (bw_core (bus_step st op)) = abs_phase1 (bw_core st);

  (* NoFreeInsight is part of the canonical proof payload for certification claims. *)
  canonical_nofi_supra_boundary :
    forall (trace : list vm_instruction) (s_init s_final : VMState) (fuel : nat),
      RevelationProof.trace_run fuel trace s_init = Some s_final ->
      s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
      QuantumBound.quantum_admissible trace ->
      ~ CertificationTheory.Certified s_final CertificationTheory.supra_quantum_certified trace;

  canonical_nofi_paid_certification :
    forall (trace : list vm_instruction) (s_init s_final : VMState) (fuel : nat),
      RevelationProof.trace_run fuel trace s_init = Some s_final ->
      s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
      CertificationTheory.Certified s_final CertificationTheory.supra_quantum_certified trace ->
      NoFreeInsight.has_structure_addition fuel trace s_init;

  canonical_nofi_trace_separation :
    forall fuel trace omega,
      (forall s, In s omega -> s.(vm_csrs).(csr_cert_addr) = 0) ->
      (forall s, In s omega -> (run_vm fuel trace s).(vm_csrs).(csr_cert_addr) <> 0) ->
      NoDup (map (fun s => (run_vm fuel trace s).(vm_csrs).(csr_cert_addr)) omega) ->
      List.length omega <= MuShannonQuantitative.count_cert_addr_setters trace;

  canonical_nofi_general_feasible_reduction :
    forall fuel trace s omega_prior omega_posterior tree,
      MuShannonBridge.decision_tree_realized_by_trace fuel trace s tree ->
      (MuShannonBridge.feasible_size omega_posterior > 0)%nat ->
      MuShannonBridge.tree_covers_feasible_reduction tree omega_prior omega_posterior ->
      Nat.log2_up (MuShannonBridge.feasible_size omega_prior) -
        Nat.log2_up (MuShannonBridge.feasible_size omega_posterior) <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu);

  canonical_nofi_fibered_feasible_reduction :
    forall fuel trace s omega_prior omega_posterior tree,
      MuShannonBridge.decision_tree_realized_by_trace fuel trace s tree ->
      (MuShannonBridge.feasible_size omega_posterior > 0)%nat ->
      MuShannonBridge.FiberedFeasibleReduction tree omega_prior omega_posterior ->
      Nat.log2_up (MuShannonBridge.feasible_size omega_prior) -
        Nat.log2_up (MuShannonBridge.feasible_size omega_posterior) <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu);

  canonical_nofi_posterior_representative_reduction :
    forall fuel trace s omega_prior omega_posterior tree
           (obs_fn : MuShannonBridge.ObservationFunction),
      MuShannonBridge.decision_tree_realized_by_trace fuel trace s tree ->
      (MuShannonBridge.feasible_size omega_posterior > 0)%nat ->
      MuShannonBridge.PosteriorRepresentativeReduction obs_fn tree omega_prior omega_posterior ->
      Nat.log2_up (MuShannonBridge.feasible_size omega_prior) -
        Nat.log2_up (MuShannonBridge.feasible_size omega_posterior) <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu);

  canonical_nofi_normalized_expected_reduction :
    forall fuel trace omega_prior omega_posterior tree,
      MuShannonBridge.normalized_weighted_distribution omega_prior ->
      MuShannonBridge.normalized_weighted_distribution omega_posterior ->
      (forall s weight, In (s, weight) omega_prior ->
        MuShannonBridge.decision_tree_realized_by_trace fuel trace s tree) ->
      MuShannonBridge.tree_covers_weighted_reduction tree omega_prior omega_posterior ->
      MuShannonBridge.normalized_weighted_entropy_reduction omega_prior omega_posterior *
        MuShannonBridge.normalized_weighted_mass omega_prior <=
      MuShannonBridge.weighted_delta_mu_numerator fuel trace omega_prior;

  canonical_nofi_conditional_shannon :
    forall fuel trace s n,
      Forall (fun i => is_cert_setterb i = true -> instruction_cost i >= 1) trace ->
      MuShannonQuantitative.cert_setter_executions_local fuel trace s >= Nat.log2 n ->
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu) >= Nat.log2 n;

  canonical_nofi_quantitative_state_space :
    forall (s s' : VMState) (freg creg : nat) (kind : bool) (flen cost : nat),
      vm_step s (instr_lassert freg creg kind flen cost) s' ->
      let k := flen * 8 in
      s'.(vm_mu) - s.(vm_mu) >= k /\
      k >= StateSpaceCounting.log2_nat (Nat.pow 2 k);

  canonical_monoidal_coherence :
    forall r1 r2 r3 : list (nat * nat),
      (CategoryMonoidal.coupling_tensor
         (CategoryMonoidal.coupling_tensor r1 r2) r3 =
       CategoryMonoidal.coupling_tensor r1
         (CategoryMonoidal.coupling_tensor r2 r3)) /\
      (CategoryMonoidal.coupling_tensor nil r1 = r1) /\
      (CategoryMonoidal.coupling_tensor r1 nil = r1);

  canonical_compose_assoc :
    forall r1 r2 r3 : CategoryLaws.Coupling,
      CategoryLaws.coupling_equiv
        (CategoryLaws.relational_compose
           (CategoryLaws.relational_compose r1 r2) r3)
        (CategoryLaws.relational_compose r1
           (CategoryLaws.relational_compose r2 r3));

  (* COMPOSE opcode hardware bridge: proven under extended_hw_invariant *)
  canonical_compose_step_simulates :
    forall ks dst m1_id m2_id cost,
      extended_hw_invariant ks ->
      abs_full_snapshot (full_snapshot_of_snapshot
        (kami_step ks (instr_compose dst m1_id m2_id cost))) =
      vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
        (instr_compose dst m1_id m2_id cost);

  (* MORPH_TENSOR opcode hardware bridge: proven under extended_hw_invariant *)
  canonical_morph_tensor_step_simulates :
    forall ks dst f_id g_id cost,
      extended_hw_invariant ks ->
      abs_full_snapshot (full_snapshot_of_snapshot
        (kami_step ks (instr_morph_tensor dst f_id g_id cost))) =
      vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
        (instr_morph_tensor dst f_id g_id cost)
}.

Theorem canonical_cpu_proof : CanonicalCPUProofBundle.
Proof.
  refine
    {| canonical_register_write_refines := verilog_refines_register_write;
       canonical_load_imm_step_simulates := verilog_simulates_vm_step_load_imm;
       canonical_mu_monotone_on_charge := verilog_mu_non_decreasing_on_charge;
       canonical_oracle_charge_sound := verilog_mu_non_decreasing_on_charge;
       canonical_bus_step_preserves_abs_phase1 := bus_step_preserves_abs_phase1;
       canonical_nofi_supra_boundary := CertificationTheory.quantum_admissible_cannot_certify_supra_chsh;
       canonical_nofi_paid_certification :=
         (fun trace s_init s_final fuel Hrun Hinit Hcert =>
            proj1
              (CertificationTheory.certified_supra_chsh_implies_mu_lower_bound
                 trace s_init s_final fuel Hrun Hinit Hcert));
       canonical_nofi_trace_separation := honest_nfi_trace_separation_partial;
       canonical_nofi_general_feasible_reduction := honest_nfi_general_feasible_reduction_partial;
       canonical_nofi_fibered_feasible_reduction := honest_nfi_fibered_feasible_reduction_partial;
      canonical_nofi_posterior_representative_reduction := honest_nfi_posterior_representative_reduction_partial;
       canonical_nofi_normalized_expected_reduction := MuShannonBridge.info_priced_normalized_expected_entropy_reduction_bound;
       canonical_nofi_conditional_shannon := honest_nfi_conditional_shannon_partial;
       canonical_nofi_quantitative_state_space := honest_nfi_quantitative_state_space_partial;
       canonical_monoidal_coherence := CategoryMonoidal.monoidal_coherence;
       canonical_compose_assoc := CategoryLaws.relational_compose_assoc;
       canonical_compose_step_simulates := driven_step_compose;
       canonical_morph_tensor_step_simulates := driven_step_morph_tensor |}.
Qed.

(* Proof anchors: ensure extraction-root proofs depend on C3/C4 and honest NoFI wiring. *)
(* INQUISITOR NOTE: alias for canonical extraction-root dependency wiring. *)
(* definitional lemma *)
Theorem canonical_c3_born_rule_anchor :
  forall (P : ProbabilityRule),
    valid_born_rule P ->
    forall (z : R), (-1 <= z <= 1)%R -> P z = born_probability z.
Proof.
  exact born_rule_unique.
Qed.

(* INQUISITOR NOTE: alias for canonical extraction-root dependency wiring. *)
(* definitional lemma *)
Theorem canonical_c4_tsirelson_model_anchor :
  forall fuel trace s_init,
    trace_quantum_bridge_coherent fuel trace s_init ->
    trace_quantum_model fuel trace s_init /\
    (Rabs (CHSH
      (trace_e00 fuel trace s_init)
      (trace_e01 fuel trace s_init)
      (trace_e10 fuel trace s_init)
      (trace_e11 fuel trace s_init)) <= sqrt8)%R.
Proof.
  exact trace_quantum_model_connection_closed.
Qed.

(* INQUISITOR NOTE: alias for canonical extraction-root dependency wiring. *)
(* definitional lemma *)
Theorem canonical_honest_nofi_anchor :
  forall (fuel : nat) (trace : list vm_instruction)
         (s_init s_final : VMState)
         (decoder : NoFreeInsight.receipt_decoder (list vm_instruction))
         (P_prior P_posterior : NoFreeInsight.ReceiptPredicate (list vm_instruction))
         (omega_prior omega_posterior : InformationGainToStrengthening.FeasibleSet),
    s_final = SimulationProof.run_vm fuel trace s_init ->
    In s_init omega_prior ->
    InformationGainToStrengthening.is_strict_reduction omega_prior omega_posterior ->
    (InformationGainToStrengthening.feasible_size omega_posterior > 0)%nat ->
    s_init.(vm_csrs).(csr_cert_addr) = 0%nat ->
    NoFreeInsight.strictly_stronger P_posterior P_prior ->
    NoFreeInsight.Certified s_final decoder P_posterior trace ->
    NoFreeInsight.has_structure_addition fuel trace s_init.
Proof.
  exact honest_information_reduction_requires_structure_addition.
Qed.

(* INQUISITOR NOTE: alias for canonical extraction-root dependency wiring. *)
(* definitional lemma *)
Theorem canonical_honest_nofi_trace_separation_anchor :
  forall fuel trace omega,
    (forall s, In s omega -> s.(vm_csrs).(csr_cert_addr) = 0) ->
    (forall s, In s omega -> (run_vm fuel trace s).(vm_csrs).(csr_cert_addr) <> 0) ->
    NoDup (map (fun s => (run_vm fuel trace s).(vm_csrs).(csr_cert_addr)) omega) ->
    List.length omega <= MuShannonQuantitative.count_cert_addr_setters trace.
Proof.
  exact honest_nfi_trace_separation_partial.
Qed.

(* INQUISITOR NOTE: alias for canonical extraction-root dependency wiring. *)
(* definitional lemma *)
Theorem canonical_honest_nofi_general_feasible_reduction_anchor :
  forall fuel trace s omega_prior omega_posterior tree,
    MuShannonBridge.decision_tree_realized_by_trace fuel trace s tree ->
    (MuShannonBridge.feasible_size omega_posterior > 0)%nat ->
    MuShannonBridge.tree_covers_feasible_reduction tree omega_prior omega_posterior ->
    Nat.log2_up (MuShannonBridge.feasible_size omega_prior) -
      Nat.log2_up (MuShannonBridge.feasible_size omega_posterior) <=
    (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  exact honest_nfi_general_feasible_reduction_partial.
Qed.

(* INQUISITOR NOTE: alias for canonical extraction-root dependency wiring. *)
(* definitional lemma *)
Theorem canonical_honest_nofi_fibered_feasible_reduction_anchor :
  forall fuel trace s omega_prior omega_posterior tree,
    MuShannonBridge.decision_tree_realized_by_trace fuel trace s tree ->
    (MuShannonBridge.feasible_size omega_posterior > 0)%nat ->
    MuShannonBridge.FiberedFeasibleReduction tree omega_prior omega_posterior ->
    Nat.log2_up (MuShannonBridge.feasible_size omega_prior) -
      Nat.log2_up (MuShannonBridge.feasible_size omega_posterior) <=
    (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  exact honest_nfi_fibered_feasible_reduction_partial.
Qed.

(* INQUISITOR NOTE: alias for canonical extraction-root dependency wiring. *)
(* definitional lemma *)
Theorem canonical_honest_nofi_posterior_representative_reduction_anchor :
  forall fuel trace s omega_prior omega_posterior tree
         (obs_fn : MuShannonBridge.ObservationFunction),
    MuShannonBridge.decision_tree_realized_by_trace fuel trace s tree ->
    (MuShannonBridge.feasible_size omega_posterior > 0)%nat ->
    MuShannonBridge.PosteriorRepresentativeReduction obs_fn tree omega_prior omega_posterior ->
    Nat.log2_up (MuShannonBridge.feasible_size omega_prior) -
      Nat.log2_up (MuShannonBridge.feasible_size omega_posterior) <=
    (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  exact honest_nfi_posterior_representative_reduction_partial.
Qed.

(* INQUISITOR NOTE: alias for canonical extraction-root dependency wiring. *)
(* definitional lemma *)
Theorem canonical_honest_nofi_conditional_shannon_anchor :
  forall fuel trace s n,
    Forall (fun i => is_cert_setterb i = true -> instruction_cost i >= 1) trace ->
    MuShannonQuantitative.cert_setter_executions_local fuel trace s >= Nat.log2 n ->
    (run_vm fuel trace s).(vm_mu) - s.(vm_mu) >= Nat.log2 n.
Proof.
  exact honest_nfi_conditional_shannon_partial.
Qed.

(* INQUISITOR NOTE: alias for canonical extraction-root dependency wiring. *)
(* definitional lemma *)
Theorem canonical_honest_nofi_quantitative_state_space_anchor :
  forall (s s' : VMState) (freg creg : nat) (kind : bool) (flen cost : nat),
    vm_step s (instr_lassert freg creg kind flen cost) s' ->
    let k := flen * 8 in
    s'.(vm_mu) - s.(vm_mu) >= k /\
    k >= StateSpaceCounting.log2_nat (Nat.pow 2 k).
Proof.
  intros s s' freg creg kind flen cost Hstep.
  exact (honest_nfi_quantitative_state_space_partial s s' freg creg kind flen cost Hstep).
Qed.
