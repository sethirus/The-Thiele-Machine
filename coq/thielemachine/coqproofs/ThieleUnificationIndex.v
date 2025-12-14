(**
  THIELE UNIFICATION PROOF PROTOCOL — INDEX (Machine-checkable work order)

  This file is a *non-narrative* index that binds the protocol Tasks 1–12
  to concrete, machine-checkable Coq artifacts in this repository.

  Policy:
  - If a Task is discharged by an existing theorem, we re-export it here.
  - If a Task cannot be derived without extra structure, we expose the *minimal*
    missing interface as a Module Type, and we state the Task theorem *relative*
    to that interface.

  This avoids silently smuggling in physics primitives.
*)

From Coq Require Import List.

From ThieleMachine Require Import
  ThieleUnificationProtocol
  ThieleUnificationTensor
  ThieleUnificationDemo
  ThieleKernelCausality
  ThieleProofCarryingReality.

From ThieleMachine Require Import
  CoreSemantics
  AlgebraicLaws
  LogicIsomorphism
  ComputationIsomorphism
  CompositionPrimitive
  QuantumTheorems
  BellInequality
  ThieleSpaceland
  PhysicsEmbedding
  WaveEmbedding
  SpacelandProved
  SpacelandComplete.

From ThieleMachineVerification Require Import
  BridgeDefinitions
  BridgeProof.

Import ListNotations.

Module ThieleUnificationIndex.

  (** ---------------------------------------------------------------------
      TASK 1 — Substrate / Opcodes / μ-laws / Locality (NO physics)
      --------------------------------------------------------------------- *)

  Module Task1.
    Definition ThieleState := ThieleUnificationProtocol.ThieleState.
    Definition Opcode := ThieleUnificationProtocol.Opcode.
    Definition mu := ThieleUnificationProtocol.mu.

    Definition mu_monotone := ThieleUnificationProtocol.mu_monotone.
    Definition mu_ledger_conservation := ThieleUnificationProtocol.mu_ledger_conservation.
    Definition no_signaling_pdiscover_graph := ThieleUnificationProtocol.no_signaling_pdiscover_graph.
  End Task1.

  (** ---------------------------------------------------------------------
      TASK 2 — Core algebraic laws

      Note: this repo has two semantics tracks:
      - Kernel VM semantics (Kernel modules) via ThieleUnificationProtocol
      - ThieleMachine CoreSemantics (ThieleMachine.CoreSemantics)

      Where a law exists in either track, we cite it explicitly.
      --------------------------------------------------------------------- *)

  Module Task2.
    (* 2.1 Associativity of composition (PMERGE) — semantic-content notion *)
    Definition pmerge_associativity := AlgebraicLaws.pmerge_associativity.

    (* 2.2 Functoriality of execution *)
    Definition run_functorial_kernel := ThieleUnificationProtocol.run_functorial.
    Definition run_composition_core := AlgebraicLaws.run_composition.

    (* 2.4 Resource compositionality / additivity *)
    Definition mu_total_additive := AlgebraicLaws.mu_total_additive.
    Definition mu_phase_split_kernel := ThieleUnificationProtocol.mu_phase_split.

    (* 2.5 Monotonicity / boundedness of μ *)
    Definition mu_monotone_kernel := ThieleUnificationProtocol.mu_monotone.
    Definition mu_monotonicity_step_core := AlgebraicLaws.mu_monotonicity_step.

    (* 2.3 Tensorial structure of independent modules

       Discharged here for the *local per-module* instruction `instr_pdiscover`:
       discoveries on distinct module IDs commute at the observable boundary
       `graph_lookup`.
     *)
    Definition tensorial_pdiscover_commutes_lookup :=
      ThieleUnificationTensor.ThieleUnificationTensor.vm_apply_pdiscover_commutes_lookup.
  End Task2.

  (** ---------------------------------------------------------------------
      TASK 3 — Logic ≡ Computation (Curry–Howard–Thiele)
      --------------------------------------------------------------------- *)

  Module Task3.
    Definition proof_is_execution := LogicIsomorphism.proof_is_execution.
    Definition proof_equivalence := LogicIsomorphism.proof_equivalence.
  End Task3.

  (** ---------------------------------------------------------------------
      TASK 4 — Computation isomorphism (internal computability + strict embed)
      --------------------------------------------------------------------- *)

  Module Task4.
    Definition execution_is_computable := ComputationIsomorphism.execution_is_computable.
    Definition classical_embedding := ComputationIsomorphism.classical_embedding.
    Definition cost_model_divergence := ComputationIsomorphism.cost_model_divergence.
  End Task4.

  (** ---------------------------------------------------------------------
      TASK 5 — Composition is primitive
      --------------------------------------------------------------------- *)

  Module Task5.
    Definition no_independent_global_semantics := CompositionPrimitive.no_independent_global_semantics.
    Definition meaning_preserved_under_composition := CompositionPrimitive.meaning_preserved_under_composition.
  End Task5.

  (** ---------------------------------------------------------------------
      TASK 6 — Quantum mechanics features as theorems
      --------------------------------------------------------------------- *)

  Module Task6.
    Definition superposition_emergence := QuantumTheorems.superposition_emergence.
    Definition interference_emergence := QuantumTheorems.interference_emergence.
    Definition entanglement_emergence := QuantumTheorems.entanglement_emergence.
    Definition no_signaling := QuantumTheorems.no_signaling.
    Definition born_rule_derivation := QuantumTheorems.born_rule_derivation.

    (* A concrete, machine-checked non-signaling witness + receipts bridge *)
    Definition supra_quantum_witness_exists := BellInequality.supra_quantum_witness_exists.
    Definition supra_quantum_receipts_sound := BellInequality.supra_quantum_receipts_sound.
  End Task6.

  (** ---------------------------------------------------------------------
      TASK 7–10 — Relativity / Noether / Thermodynamics / Gauge

      This repository contains *embedding* and *projection* developments
      (Spaceland modules, PhysicsEmbedding, WaveEmbedding) that establish some
      conservation and gauge-style results, but a fully internal derivation of
      the physics pillars (with no additional axioms/interfaces) requires an
      explicit observation/measurement interface.

      We therefore isolate the minimal missing interface explicitly.
      --------------------------------------------------------------------- *)

  Module Type ObservationInterface.
    Parameter Obs : Type.
    Parameter observe : Task1.ThieleState -> Obs.

    (* Observational equivalence (what “no signaling” and coarse-graining use). *)
    Parameter obs_equiv : Task1.ThieleState -> Task1.ThieleState -> Prop.

    Axiom obs_equiv_refl : forall s, obs_equiv s s.
    Axiom obs_equiv_sym  : forall s1 s2, obs_equiv s1 s2 -> obs_equiv s2 s1.
    Axiom obs_equiv_trans : forall s1 s2 s3, obs_equiv s1 s2 -> obs_equiv s2 s3 -> obs_equiv s1 s3.

    Axiom obs_equiv_sound : forall s1 s2, obs_equiv s1 s2 -> observe s1 = observe s2.
  End ObservationInterface.

  Module Task7_10 (O : ObservationInterface).
    (* Task 7 (Relativity / causal structure): requires a definition of
       observables and admissible influence paths. *)
    Parameter causal_influence : Task1.ThieleState -> Task1.ThieleState -> Prop.
    Parameter light_cone : Task1.ThieleState -> list Task1.ThieleState.

    (* Kernel-level causal structure (no spacetime): a simulated light-cone for
       `instr_pdiscover` traces and a non-interference theorem. *)
    Definition kernel_instr_targets := ThieleKernelCausality.ThieleKernelCausality.instr_targets.
    Definition kernel_targets_of_trace := ThieleKernelCausality.ThieleKernelCausality.targets_of_trace.
    Definition kernel_in_light_cone_trace := ThieleKernelCausality.ThieleKernelCausality.in_light_cone_trace.
    Definition kernel_no_superluminal_influence_trace :=
      ThieleKernelCausality.ThieleKernelCausality.no_superluminal_influence_trace.

    Definition kernel_light_cone_pdiscover := ThieleKernelCausality.ThieleKernelCausality.pdiscover_targets.
    Definition kernel_causal_influence_pdiscover := ThieleKernelCausality.ThieleKernelCausality.in_light_cone.
    Definition kernel_no_superluminal_influence_pdiscover :=
      ThieleKernelCausality.ThieleKernelCausality.no_superluminal_influence_pdiscover_trace.

    (* Task 8 (Noether-style conservation): The μ gauge symmetry (shifting
       absolute μ by a constant) corresponds to the conservation law that only
       μ DIFFERENCES are observable. This is the Thiele Machine's Noether theorem.
       
       Proven components:
       - Conservation law: mu_ledger_conservation proves μ(final) = μ(init) + Σ(costs)
       - Symmetry: mu_gauge_freedom_multistep proves states differing only in
         absolute μ produce identical observable traces
       - Bridge: obs_equiv_iff_gauge proves observational equivalence ↔ gauge freedom
       
       This completes the Noether-style result: the symmetry (gauge) corresponds
       exactly to what is NOT conserved (absolute μ), while the conserved quantity
       is what breaks the symmetry (Δμ sequence). *)
    
    (* Conservation law at kernel level *)
    Definition noether_mu_conservation_kernel := ThieleUnificationProtocol.mu_ledger_conservation.
    
    (* Symmetry and its correspondence to conservation *)
    Definition noether_gauge_symmetry := SpacelandComplete.Dynamics.mu_gauge_freedom_multistep.
    Definition noether_symmetry_conservation_bridge := SpacelandComplete.ObservationalEquivalence.obs_equiv_iff_gauge.

    (* Task 9 (Thermodynamics): needs coarse-graining/quotient by obs equivalence.
       The repo’s Spaceland developments include μ gauge/observational results. *)
    Definition obs_equiv_iff_gauge := SpacelandComplete.ObservationalEquivalence.obs_equiv_iff_gauge.

     (* Concrete thermodynamic connection lives in the ThieleSpaceland instantiation.
       Note: the theorem is intentionally a physical constraint (propositional True). *)
     Definition mu_thermodynamic := ThieleSpaceland.mu_thermodynamic.
     Definition blind_reversible := ThieleSpaceland.blind_reversible.

    (* Task 10 (Gauge structure): repo has μ gauge freedom theorems. *)
    Definition mu_gauge_freedom_multistep := SpacelandComplete.Dynamics.mu_gauge_freedom_multistep.
  End Task7_10.

  (** ---------------------------------------------------------------------
      TASK 11 — Machine realization / refinement

      Coq proofs: CPU ↔ TM bridge theorems.
      RTL/Python/Extraction: enforced by executable gates elsewhere in the repo.
      --------------------------------------------------------------------- *)

  Module Task11.
    Definition cpu_tm_isomorphism := BridgeDefinitions.cpu_tm_isomorphism.
    Definition cpu_tm_general_isomorphism := BridgeProof.cpu_tm_general_isomorphism.
  End Task11.

  (** ---------------------------------------------------------------------
      TASK 12 — Proof-carrying run

      Minimal fully-in-Coq artifact: the demo trace in ThieleUnificationDemo
      with proven μ and locality properties.
      --------------------------------------------------------------------- *)

  Module Task12.
    Definition demo_no_signaling_module2 := Demo.demo_no_signaling_module2.
    Definition demo_mu_total := Demo.demo_mu_total.
    Definition supra_quantum_replay_ok :=
      ThieleProofCarryingReality.ThieleProofCarryingReality.supra_quantum_receipts_replay_ok.
  End Task12.

End ThieleUnificationIndex.
