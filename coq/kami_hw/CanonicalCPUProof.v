(** CanonicalCPUProof.v

    Single canonical entrypoint for the full Thiele CPU proof artifact.

    Intent:
    - Provide ONE root Coq object that downstream extraction/synthesis flows can
      reference directly.
    - Keep proof obligations constructive by re-exporting the proven refinement
      stack from the Kami hardware model to VM semantics.
*)

From KamiHW Require Import ThieleCPUCore.
From KamiHW Require Import ThieleCPUBusTop.
From KamiHW Require Import Abstraction.
From KamiHW Require Import VerilogRefinement.
From Kernel Require Import VMState VMStep VMEncoding KernelTM.
From Kernel Require Import MuCostModel MuLedgerConservation MuInitiality NoFreeInsight.
From Kernel Require Import Certification QuantumBound.
From Kernel Require Import RevelationRequirement.

Import VMStep.VMStep.

(** Canonical hardware module (Bluespec/Kami backend input).
  Route through wrapper boundary so protocol integration evolves at source. *)
Definition canonical_cpu_module := thieleBusTopB.

(** Canonical abstraction relation and map. *)
Definition canonical_snapshot_to_vm := abs_phase1.
Definition canonical_refinement_relation := verilog_sim_rel.

(** Canonical theorem bundle: this is the top-level proof payload consumed by
    downstream users who want one source of truth. *)
Record CanonicalCPUProofBundle : Prop := {
  canonical_register_write_refines :
    forall (hs : KamiSnapshot) (dst v : nat),
      dst < 32 ->
      snapshot_regs_to_list
        (fun j => if Nat.eqb j dst then word32 v else snap_regs hs j) =
      write_reg (abs_phase1 hs) dst v;

  canonical_load_imm_step_simulates :
    forall (hs : KamiSnapshot) (dst imm cost : nat),
      exists vs',
        vm_step (abs_phase1 hs) (instr_load_imm dst imm cost) vs' /\
        vs' =
          advance_state_rm (abs_phase1 hs) (instr_load_imm dst imm cost)
            (abs_phase1 hs).(vm_graph)
            (abs_phase1 hs).(vm_csrs)
            (write_reg (abs_phase1 hs) dst (word32 imm))
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
      NoFreeInsight.has_structure_addition fuel trace s_init
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
                 trace s_init s_final fuel Hrun Hinit Hcert)) |}.
Qed.
