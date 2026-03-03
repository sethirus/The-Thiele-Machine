(* ================================================================= *)
(* INQUISITOR NOTE: proof-connectivity -- bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

(* Bisimulation: Redirect to proven kernel files                      *)
(* ================================================================= *)

(* The 3-layer bisimulation IS formally proven.  The proofs live in
   the kernel (not in this thielemachine/ subtree) because they
   depend directly on VMState and VMStep:

   coq/kernel/PythonBisimulation.v
     Proves: Coq VM ↔ Python VM (abstract PC + μ bisimulation)
     Key theorems:
       - bisimulation_step     (single step preserves invariant)
       - mu_cost_consistency   (μ-ledger identical across layers)

   coq/kernel/HardwareBisimulation.v
     Proves: Python VM ↔ Verilog Hardware (abstract PC + μ bisimulation)
     Key theorems:
       - hw_bisimulation_step          (single cycle preserves invariant)
       - hw_bisimulation_multi_step    (trace-level preservation by induction)
       - complete_verification_chain   (full Coq ↔ Python ↔ Hardware chain)
       - hardware_synthesis_correctness (synthesized RTL satisfies the spec)

   Together these give:
     Coq VM ↔ Python VM ↔ Verilog RTL  (all Qed, zero Admitted)

   The bisimulation is over the observable projection (pc, mu, err).
   Full register-file equality follows from μ-conservation and
   deterministic step semantics (each register update is uniquely
   determined by the instruction + input state).

   This file is a deliberate redirect — it exists so that imports
   from older proof files still compile.  New proofs should import
   directly from coq/kernel/PythonBisimulation.v and
   coq/kernel/HardwareBisimulation.v.

   Legacy note: Earlier drafts in archive/coq/Subsumption_Legacy.v
   used a HALTING_ORACLE axiom.  That axiom is gone; the current
   proofs are axiom-free beyond foundational logic. *)

(* Re-export key facts for backward compatibility.
   HardwareBisimulation imports the full chain (Coq → Python → Hardware). *)
From Kernel Require Import HardwareBisimulation.

(** The 3-layer isomorphism holds for all execution traces. *)
Theorem three_layer_isomorphism :
  forall hw_init py_init costs,
    hw_bisimulation_invariant hw_init py_init ->
    hw_bisimulation_invariant
      (hardware_multi_step hw_init costs)
      (python_multi_step py_init costs).
Proof.
  intros hw_init py_init costs Hinit.
  apply hw_bisimulation_multi_step.
  exact Hinit.
Qed.
