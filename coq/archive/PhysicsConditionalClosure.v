(** PhysicsConditionalClosure.v — The Complete Physics Connection

    This file assembles the full relationship between the Thiele Machine's
    cost structure and the laws of physics.  Every theorem is zero Admitted.
    Physical axioms are named, scoped, and falsifiable.

    ═══════════════════════════════════════════════════════════════════════════
    PART I: UNCONDITIONAL STRUCTURAL THEOREMS
    These hold with no physical assumptions.  They are consequences of the
    machine's operational semantics and the mathematical proof apparatus.

      U1. Classical CHSH bound: no local hidden-variable model exceeds |S|=2.
      U2. No Free Insight: certification requires positive μ-cost.
      U3. Trial authenticity: N CHSH trials require N CHSH_TRIAL instructions.
      U4. Cost intrinsic: δ-μ is determined by the instruction sequence alone.
      U5. Tsirelson from PSD: any quantum-realizable correlation satisfies |S|≤2√2.

    PART II: THE PHYSICAL BRIDGE AXIOM
    One physical fact is required to connect Part I to the observable world.

      A_QM: CHSH trial outcomes from honest quantum experiments produce
            correlations whose zero-marginal NPA moment matrix is PSD
            (quantum_realizable).

    Physical content of A_QM: When Alice and Bob measure an entangled
    quantum state with observables A_x ⊗ B_y, the resulting correlation
    matrix Gram(E_xy) satisfies the PSD condition.  This is the Born rule
    plus the algebraic structure of quantum observables.  It is an empirical
    fact verified by every Bell test experiment, not derivable from Coq.

    Falsification of A_QM: find a quantum experiment where the correlation
    matrix is NOT PSD.  That would refute quantum mechanics.

    PART III: MASTER CONDITIONAL THEOREM
    Under A_QM, the full CHSH hierarchy follows from the cost structure.
    This is the honest closed form of the physics connection.

      Under A_QM:
        - Quantum correlations satisfy |S| ≤ 2√2  (Tsirelson, U5 + A_QM)
        - Classical correlations satisfy |S| ≤ 2   (U1, unconditional)
        - Supra-quantum (|S| > 2√2) is non-realizable under A_QM
        - Certifying any structural claim requires positive μ  (U2)
        - Every CHSH trial is authentic — unforgeable  (U3)
        - Every computation was always paying its μ-cost  (U4)

    PART IV: THE OPEN PROBLEM
    What is NOT proven here (and is genuinely open):

      OP-QM: Why do physical quantum correlations satisfy PSD?
             Equivalently: why is the Tsirelson bound 2√2 and not some
             other value?  Deriving the quantum bound from the μ-cost
             structure alone — without assuming the Born rule as a
             physical axiom — remains an open problem.  It is related
             to Tsirelson's original question in quantum information theory.

    ═══════════════════════════════════════════════════════════════════════════
*)

From Coq Require Import List Arith.PeanoNat Lia Reals.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof
                           MuLedgerConservation
                           AbstractNoFI
                           UniversalCertificationCost
                           QuantitativeNoFI
                           ClassicalBound
                           NPAMomentMatrix
                           MuLedgerQuantumBridge
                           TsirelsonQuantumModel
                           CHSHExtraction
                           MuInitiality.

From Coq Require Import Reals.Rbasic_fun.


(** ═══════════════════════════════════════════════════════════════════════════
    PART I: UNCONDITIONAL STRUCTURAL THEOREMS
    ═══════════════════════════════════════════════════════════════════════════ *)

(** U2 (re-export): Certification requires positive μ-cost.
    Any trace from uncertified to certified has total instruction_cost ≥ 1.
    Source: certification_requires_positive_mu (AbstractNoFI.v). *)
Theorem U2_no_free_certification :
  forall (trace : list vm_instruction) (s0 : VMState),
    thiele_cert_bool s0 = false ->
    (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) <> 0 ->
    acm_cost_total thiele_cert_machine trace >= 1.
Proof.
  intros trace s0 Hfalse Htrue.
  exact (thiele_abstract_nfi_cost trace s0 Hfalse Htrue).
Qed.

(** U3 (re-export): N CHSH trials require at least N valid CHSH_TRIAL instructions.
    The trial count is unforgeable — no other instruction can increment
    witness_total.  Source: chsh_trial_count_lower_bound (QuantitativeNoFI.v). *)
Theorem U3_trial_authenticity :
  forall (n : nat) (trace : list vm_instruction) (s0 : VMState),
    witness_total s0.(vm_witness) = 0 ->
    chsh_cert_n n (cs_run (chsh_cert_system_n n) trace s0) = true ->
    cs_total_cost (chsh_cert_system_n n) trace >= n.
Proof.
  intros n trace s0 Hinit Hcert.
  exact (chsh_trial_count_lower_bound n trace s0 Hinit Hcert).
Qed.

(** U4: The δ-μ of any instruction sequence is determined by the sequence
    alone — independent of vm_graph, vm_regs, vm_mem, vm_pc, and starting μ.
    Source: mu_accumulates_trace_cost (MuInitiality.v). *)
Theorem U4_cost_intrinsic :
  forall (trace : list vm_instruction) (s : VMState),
    (exec_trace_from s trace).(vm_mu) = s.(vm_mu) + trace_total_cost trace.
Proof.
  intros trace s.
  exact (mu_accumulates_trace_cost s trace).
Qed.

(** U5: Any quantum-realizable correlation satisfies the Tsirelson bound.
    This is a pure mathematical theorem about real numbers satisfying the
    PSD condition.  No physical assumptions.
    Source: quantum_realizable_implies_tsirelson_bound_abs (MuLedgerQuantumBridge.v). *)
(* definitional lemma: direct re-export of quantum_realizable_implies_tsirelson_bound_abs
   as a named physics bridge theorem.  Physical content is in the PSD premise. *)
Theorem U5_tsirelson_from_psd :
  forall E00 E01 E10 E11 : RealNumber,
    quantum_realizable (zero_marginal_npa E00 E01 E10 E11) ->
    Rabs (CHSH E00 E01 E10 E11) <= sqrt8.
Proof.
  intros E00 E01 E10 E11 Hqr.
  exact (quantum_realizable_implies_tsirelson_bound_abs E00 E01 E10 E11 Hqr).
Qed.


(** ═══════════════════════════════════════════════════════════════════════════
    PART II: THE PHYSICAL BRIDGE SECTION
    ═══════════════════════════════════════════════════════════════════════════ *)

Section PhysicsBridge.

(** A_QM — THE QUANTUM MEASUREMENT BRIDGE AXIOM.

    Physical content: CHSH experiments on honest quantum systems produce
    correlations whose zero-marginal NPA moment matrix is PSD (symmetric
    and positive semidefinite).

    This is the mathematical statement of the Born rule plus quantum
    observable algebra: for any quantum state ρ and observables A_x, B_y
    with eigenvalues in {±1}, the matrix Gram(E_xy) where
    E_xy = Tr(ρ · (A_x ⊗ B_y)) satisfies PSD.

    This is NOT derivable from Coq.  It is an empirical fact about physical
    reality verified by every Bell experiment.

    Falsification: find a quantum experiment where the correlation matrix
    is not PSD.  That would refute quantum mechanics.

    OPEN PROBLEM (OP-QM): A_QM asserts PSD.  Why PSD specifically?
    Why does nature use THIS algebraic condition rather than some other?
    Deriving A_QM itself from the μ-cost structure would require formalizing
    quantum mechanics (Hilbert spaces, density matrices, Born rule) from
    within the Thiele model.  That is the remaining open problem. *)

(* INQUISITOR NOTE: A_QM is the quantum measurement bridge axiom.
   Physical content: honest quantum CHSH correlations are quantum_realizable (PSD).
   Not derivable from Coq semantics — empirical fact about quantum mechanics.
   Bridge tier: (C) conditional.  Falsification: non-PSD quantum correlations. *)
Context (A_QM : forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),
  honest_quantum_chsh_execution fuel trace s_init ->
  quantum_realizable (zero_marginal_npa
    (trace_e00 fuel trace s_init)
    (trace_e01 fuel trace s_init)
    (trace_e10 fuel trace s_init)
    (trace_e11 fuel trace s_init))).


(** ═══════════════════════════════════════════════════════════════════════════
    PART III: MASTER CONDITIONAL THEOREM
    ═══════════════════════════════════════════════════════════════════════════ *)

(** MASTER THEOREM: Under A_QM, any honest quantum CHSH execution satisfies
    the Tsirelson bound.  The complete chain:

      A_QM (physical axiom)
        → quantum_realizable (PSD condition satisfied)
        → U5 (PSD → |S| ≤ 2√2, pure mathematics)
        → Tsirelson bound holds

    This is the honest closed form of the physics connection.
    The mathematical proof is complete.  The physical axiom is explicit
    and falsifiable.  This is what all good physics looks like. *)
(* definitional lemma: bundles A_QM + U5 into the named master conditional.
   No new mathematical content; all proof steps are direct applications. *)
Theorem master_tsirelson_conditional :
  forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),
    honest_quantum_chsh_execution fuel trace s_init ->
    Rabs (CHSH
      (trace_e00 fuel trace s_init)
      (trace_e01 fuel trace s_init)
      (trace_e10 fuel trace s_init)
      (trace_e11 fuel trace s_init)) <= sqrt8.
Proof.
  intros fuel trace s_init Hhonest.
  apply U5_tsirelson_from_psd.
  apply A_QM.
  exact Hhonest.
Qed.

(** COROLLARY: Under A_QM, the full CHSH hierarchy is:
    Classical (|S| ≤ 2) < Quantum (|S| ≤ 2√2) < Supra-quantum (impossible).
    The quantum regime is exactly what honest measurements can produce.
    Supra-quantum correlations are provably non-realizable under A_QM. *)
(* definitional lemma: bundles classical bound (U1) and quantum bound (master_tsirelson)
   into one summary statement.  Each conjunct is proved by direct application. *)
Theorem master_chsh_hierarchy_conditional :
  (** Classical bound holds unconditionally *)
  (forall E00 E01 E10 E11 : RealNumber,
    local_hidden_variable_model E00 E01 E10 E11 ->
    Rabs (CHSH E00 E01 E10 E11) <= 2) /\
  (** Quantum bound holds under A_QM *)
  (forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),
    honest_quantum_chsh_execution fuel trace s_init ->
    Rabs (CHSH
      (trace_e00 fuel trace s_init)
      (trace_e01 fuel trace s_init)
      (trace_e10 fuel trace s_init)
      (trace_e11 fuel trace s_init)) <= sqrt8) /\
  (** Supra-quantum is non-realizable under A_QM *)
  (forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),
    honest_quantum_chsh_execution fuel trace s_init ->
    ~ (Rabs (CHSH
        (trace_e00 fuel trace s_init)
        (trace_e01 fuel trace s_init)
        (trace_e10 fuel trace s_init)
        (trace_e11 fuel trace s_init)) > sqrt8)).
Proof.
  refine (conj _ (conj master_tsirelson_conditional _)).
  - (* Classical bound: local_hidden_variable_model → |S| ≤ 2 *)
    intros E00 E01 E10 E11 Hlhv.
    exact (classical_chsh_bound E00 E01 E10 E11 Hlhv).
  - (* Supra-quantum impossible: follows from Tsirelson *)
    intros fuel trace s_init Hhonest Hcontra.
    pose proof (master_tsirelson_conditional fuel trace s_init Hhonest) as Hle.
    lra.
Qed.

End PhysicsBridge.


(** ═══════════════════════════════════════════════════════════════════════════
    PART IV: EXPLICIT STATEMENT OF THE OPEN PROBLEM
    ═══════════════════════════════════════════════════════════════════════════ *)

(** The open problem is formally named and bounded.

    WHAT IS PROVEN:
    - U1 (classical bound ≤ 2): unconditional
    - U2 (no free certification): unconditional
    - U3 (trial authenticity): unconditional
    - U4 (cost intrinsic): unconditional
    - U5 (PSD → Tsirelson): unconditional mathematical theorem
    - Master conditional (Tsirelson under A_QM): proven, A_QM explicit

    WHAT REQUIRES A_QM:
    - The conclusion that physical quantum correlations satisfy Tsirelson.
    - A_QM is the Born rule in algebraic form.  It is an empirical fact.

    THE OPEN PROBLEM (OP-QM):
    Deriving A_QM itself from the Thiele Machine's cost structure would
    require showing that μ-cost accounting forces the PSD condition on
    correlations produced by zero-structural-revelation computations.

    Formally:
      OP-QM: forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),
        no_cert_setters_in trace ->
        quantum_realizable (zero_marginal_npa
          (trace_e00 fuel trace s_init)
          ...

    This would make A_QM a theorem rather than an axiom.  It requires either:
      (a) formalizing quantum mechanics (Hilbert spaces, density matrices,
          Born rule) from within the Thiele model, or
      (b) proving that the NPA PSD condition follows from the information-
          cost structure of the machine's CHSH_TRIAL semantics alone.

    Both are hard.  (a) is formalizing quantum mechanics in Coq.
    (b) may not be true — the machine's trial counting is adversarial and
    does not constrain PSD by itself.  The missing ingredient is that
    honest physical measurements ARE PSD — which is A_QM.

    STATUS: OP-QM is open.  The rest is proven. *)

End PhysicsConditionalClosure.
