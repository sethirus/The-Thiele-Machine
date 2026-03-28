(** =========================================================================
    QUANTUM PARTITION PSD
    =========================================================================

    THE KEY THEOREM (bidirectional):
      zero_marginal_column_contractive e00 e01 e10 e11
        ↔  PSD5 (nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)))

    One direction (→) was already proven in MuLedgerQuantumBridge.v as
    zero_marginal_npa_column_contractive_implies_psd.

    This file proves the REVERSE direction (←): PSD of the NPA moment matrix
    implies column contractivity, closing the biconditional.

    MATHEMATICAL CONTENT — SCHUR COMPLEMENT:
    The zero-marginal NPA matrix has block structure:

        M = diag(1) ⊕ [[I₂, C], [C^T, I₂]]

    where C = [[e00, e01], [e10, e11]] is the 2×2 correlator matrix.

    By the Schur complement theorem:
        [[I₂, C], [C^T, I₂]] ≥ 0  ↔  I₂ − C^T C ≥ 0

    And I₂ − C^T C ≥ 0 is EXACTLY zero_marginal_column_contractive.

    PROOF TECHNIQUE — TEST VECTORS:
    Instead of invoking abstract Schur complement theory, we extract each
    condition directly by instantiating PSD5 on concrete test vectors.

    Test vector for condition 1 (1 − e00² − e10² ≥ 0):
        v₁ = [0; −e00; −e10; 1; 0]
        Computes to: quad5 M v₁ = 1 − e00² − e10²

    Test vector for condition 2 (1 − e01² − e11² ≥ 0):
        v₂ = [0; −e01; −e11; 0; 1]
        Computes to: quad5 M v₂ = 1 − e01² − e11²

    Test vector for condition 3 (det(I − C^T C) ≥ 0):
        v₃(t) = [0; −(e00·t + e01); −(e10·t + e11); t; 1]
        Computes to: quad5 M v₃(t) = p·t² − 2s·t + q  for all t
        where p = 1−e00²−e10², q = 1−e01²−e11², s = e00e01+e10e11
        Apply quadratic_nonneg_discriminant: s² ≤ p·q, i.e. p·q − s² ≥ 0.

    This gives all three conditions of zero_marginal_column_contractive. □

    STATUS: ZERO PROJECT-LOCAL AXIOMS. ZERO ADMITS.
    ========================================================================= *)

(* INQUISITOR NOTE: proof-connectivity — closes PSD ↔ column_contractive gap. *)

From Kernel Require Import VMState VMStep.
From Kernel Require Import NPAMomentMatrix.
From Kernel Require Import ConstructivePSD.
From Kernel Require Import MuLedgerQuantumBridge.

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.NArith.BinNatDef.

Local Open Scope R_scope.

(** =========================================================================
    SECTION 1: Quadratic Form Computation Lemmas
    =========================================================================

    We compute quad5 M v for each test vector by unfolding and ring. These
    are pure arithmetic identities about the NPA matrix structure. *)

(** Test vector 1: v = [0; −e00; −e10; 1; 0]
    Extracts: quad5 M v = 1 − e00² − e10² *)
Lemma npa_quad5_test_col0 :
  forall e00 e01 e10 e11 : R,
  let M := nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)) in
  let v : Vec5 := fun i =>
    match proj1_sig (Fin.to_nat i) with
    | 1%nat => -e00
    | 2%nat => -e10
    | 3%nat => 1
    | _     => 0
    end in
  quad5 M v = 1 - e00 * e00 - e10 * e10.
Proof.
  intros e00 e01 e10 e11.
  unfold quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, zero_marginal_npa.
  simpl.
  ring.
Qed.

(** Test vector 2: v = [0; −e01; −e11; 0; 1]
    Extracts: quad5 M v = 1 − e01² − e11² *)
Lemma npa_quad5_test_col1 :
  forall e00 e01 e10 e11 : R,
  let M := nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)) in
  let v : Vec5 := fun i =>
    match proj1_sig (Fin.to_nat i) with
    | 1%nat => -e01
    | 2%nat => -e11
    | 4%nat => 1
    | _     => 0
    end in
  quad5 M v = 1 - e01 * e01 - e11 * e11.
Proof.
  intros e00 e01 e10 e11.
  unfold quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, zero_marginal_npa.
  simpl.
  ring.
Qed.

(** Test vector family 3: v(t) = [0; −(e00t+e01); −(e10t+e11); t; 1]
    Extracts: quad5 M v(t) = p·t² − 2s·t + q
    where p = 1−e00²−e10², q = 1−e01²−e11², s = e00·e01+e10·e11 *)
Lemma npa_quad5_test_schur :
  forall e00 e01 e10 e11 t : R,
  let M := nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)) in
  let v : Vec5 := fun i =>
    match proj1_sig (Fin.to_nat i) with
    | 1%nat => -(e00 * t + e01)
    | 2%nat => -(e10 * t + e11)
    | 3%nat => t
    | 4%nat => 1
    | _     => 0
    end in
  quad5 M v =
    (1 - e00*e00 - e10*e10) * t * t
    - 2 * (e00*e01 + e10*e11) * t
    + (1 - e01*e01 - e11*e11).
Proof.
  intros e00 e01 e10 e11 t.
  unfold quad5, sum_fin5, nat_matrix_to_fin5, npa_to_matrix, zero_marginal_npa.
  simpl.
  ring.
Qed.

(** =========================================================================
    SECTION 2: Main Reverse Direction
    =========================================================================

    From PSD5 of the NPA matrix, extract all three column-contractivity
    conditions via the test vectors above. *)

Theorem npa_psd_implies_column_contractive :
  forall e00 e01 e10 e11 : R,
    PSD5 (nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11))) ->
    zero_marginal_column_contractive e00 e01 e10 e11.
Proof.
  intros e00 e01 e10 e11 Hpsd.
  unfold zero_marginal_column_contractive.

  (* ---- Condition 1: 1 − e00² − e10² ≥ 0 -------------------------------- *)
  assert (Hc0 : 1 - e00 * e00 - e10 * e10 >= 0).
  {
    pose proof Hpsd (fun i =>
      match proj1_sig (Fin.to_nat i) with
      | 1%nat => -e00
      | 2%nat => -e10
      | 3%nat => 1
      | _     => 0
      end) as Hv1.
    rewrite npa_quad5_test_col0 in Hv1.
    exact Hv1.
  }

  (* ---- Condition 2: 1 − e01² − e11² ≥ 0 -------------------------------- *)
  assert (Hc1 : 1 - e01 * e01 - e11 * e11 >= 0).
  {
    pose proof Hpsd (fun i =>
      match proj1_sig (Fin.to_nat i) with
      | 1%nat => -e01
      | 2%nat => -e11
      | 4%nat => 1
      | _     => 0
      end) as Hv2.
    rewrite npa_quad5_test_col1 in Hv2.
    exact Hv2.
  }

  (* ---- Condition 3: det(I − C^T C) ≥ 0 --------------------------------- *)
  assert (Hdet : (1 - e00 * e00 - e10 * e10) * (1 - e01 * e01 - e11 * e11) -
                 (e00 * e01 + e10 * e11) * (e00 * e01 + e10 * e11) >= 0).
  {
    (* The parametric family v(t) gives a quadratic ≥ 0 for all t.
       Apply quadratic_nonneg_discriminant to extract the det condition. *)
    assert (Hquad : forall t : R,
      (1 - e00*e00 - e10*e10) * t * t
      - 2 * (e00*e01 + e10*e11) * t
      + (1 - e01*e01 - e11*e11) >= 0).
    {
      intro t.
      pose proof Hpsd (fun i =>
        match proj1_sig (Fin.to_nat i) with
        | 1%nat => -(e00 * t + e01)
        | 2%nat => -(e10 * t + e11)
        | 3%nat => t
        | 4%nat => 1
        | _     => 0
        end) as Hvt.
      rewrite npa_quad5_test_schur in Hvt.
      exact Hvt.
    }
    (* Rewrite to match quadratic_nonneg_discriminant signature:
       ∀t, a + 2*b*t + c*t² ≥ 0 → b² ≤ a*c
       Here a = (1−e01²−e11²), b = −(e00e01+e10e11), c = (1−e00²−e10²) *)
    assert (Hform : forall t : R,
      (1 - e01*e01 - e11*e11)
      + 2 * (-(e00*e01 + e10*e11)) * t
      + (1 - e00*e00 - e10*e10) * t * t >= 0).
    {
      intro t. specialize (Hquad t). lra.
    }
    apply quadratic_nonneg_discriminant in Hform.
    nra.
  }

  exact (conj Hc0 (conj Hc1 Hdet)).
Qed.

(** =========================================================================
    SECTION 3: The Biconditional
    =========================================================================

    Combining the forward direction (already in MuLedgerQuantumBridge) with
    the reverse direction proven above. *)

Theorem npa_psd_iff_column_contractive :
  forall e00 e01 e10 e11 : R,
    PSD5 (nat_matrix_to_fin5 (npa_to_matrix (zero_marginal_npa e00 e01 e10 e11)))
    <->
    zero_marginal_column_contractive e00 e01 e10 e11.
Proof.
  intros e00 e01 e10 e11.
  split.
  - apply npa_psd_implies_column_contractive.
  - intros [Hc0 [Hc1 Hdet]].
    apply zero_marginal_npa_column_contractive_implies_psd;
      assumption.
Qed.

(** =========================================================================
    SECTION 4: Physical Interpretation
    =========================================================================

    The biconditional has a clean physical reading:

    A set of CHSH trial outcomes (e00, e01, e10, e11) is QUANTUM REALIZABLE
    (i.e., can be produced by measurements on some entangled quantum state
    with bounded observables) if and only if the induced NPA moment matrix
    is positive semidefinite.

    This is the NPA characterization theorem at level 1 for binary bipartite
    correlators with zero marginals. The Tsirelson bound 2√2 is the algebraic
    maximum of the CHSH expression over all PSD-satisfying correlators,
    computed by Cauchy-Schwarz in TsirelsonFromAlgebra.v.

    WHAT THIS MEANS FOR THE THIELE MACHINE:
    The VM records CHSH_TRIAL outcomes. The quantum_realizable predicate
    (PSD of NPA matrix) is CHECKABLE from the recorded data — it does not
    require additional quantum machinery. The CERTIFY opcode (with nonzero
    μ-cost) formalises the act of certifying this PSD condition.

    WHAT PSPLIT CONTRIBUTES:
    A proper PSPLIT with μ > 0 establishes bipartite structure between Alice
    and Bob modules. Classical independent outputs (after PSPLIT, μ = 0 for
    CHSH_TRIAL) give rank-1 correlation matrices, which have CHSH ≤ 2
    (proven in MinorConstraints.v). To violate the classical bound (CHSH > 2),
    the source must be quantum-entangled — requiring the bipartite partition
    to have been prepared via a quantum channel, which costs μ > 0 (by NoFI).
    Once the NPA-PSD certificate is verified, Tsirelson ≤ 2√2 follows. □ *)

(** Corollary: quantum realizability is equivalent to column contractivity. *)
Corollary column_contractive_iff_quantum_realizable :
  forall e00 e01 e10 e11 : R,
    zero_marginal_column_contractive e00 e01 e10 e11
    <->
    quantum_realizable (zero_marginal_npa e00 e01 e10 e11).
Proof.
  intros e00 e01 e10 e11.
  unfold quantum_realizable.
  split.
  - intros [Hc0 [Hc1 Hdet]].
    split.
    + apply npa_to_matrix_symmetric.
    + apply zero_marginal_npa_column_contractive_implies_psd;
        assumption.
  - intros [_ Hpsd].
    apply npa_psd_implies_column_contractive.
    exact Hpsd.
Qed.

(** =========================================================================
    SECTION 5: Connection to Trace-Level Predicates
    =========================================================================

    Lift the algebraic result to the trace-level predicates used in
    MasterSummary and the rest of the kernel. *)

Theorem trace_column_contractive_iff_trace_quantum_model :
  forall fuel trace s_init,
    trace_column_contractive fuel trace s_init
    <->
    quantum_realizable (trace_zero_marginal_npa fuel trace s_init).
Proof.
  intros fuel trace s_init.
  unfold trace_column_contractive, trace_zero_marginal_npa.
  set (e00 := trace_e00 fuel trace s_init).
  set (e01 := trace_e01 fuel trace s_init).
  set (e10 := trace_e10 fuel trace s_init).
  set (e11 := trace_e11 fuel trace s_init).
  apply column_contractive_iff_quantum_realizable.
Qed.
