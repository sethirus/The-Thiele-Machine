(** * HolevoDimensional: a classical dimensional bound shaped like Holevo.

    Holevo's theorem says: from an [n]-dimensional quantum system, the
    accessible classical information is bounded by [log_2 n]. For a
    classical (diagonal-density-matrix) substrate this reduces to the
    statement that [log_2 n] yes/no questions are needed in the worst
    case to distinguish [n] outcomes — the standard binary-decision-tree
    depth bound.

    The Thiele framework as it stands is classical: the VM is
    deterministic, and the framework explicitly does not include
    density matrices or von Neumann entropy. (See the comment in
    [HonestMeasurementImpliesNPA.v]: "the quantum cost ledger
    (Holevo-style payment for state preparation and measurement) must be
    modelled explicitly, which requires Hilbert-space machinery beyond
    the kernel's current quantum surface.") That comment is the reason
    full Holevo is NOT derivable in the present framework.

    This file proves the classical-floor version of the bound: the
    dimensional dependence [log_2 n] falls out of the framework's
    existing decision-tree machinery (in [MuShannonBridge.v]) plus the
    framework's existing cert-setter-execution cost floor. The bound
    has Holevo's *shape*: linear in [log_2 (substrate dimension)]. It
    does NOT have Holevo's full content: for non-commuting observables,
    Holevo is strictly tighter than the classical floor, and that
    tightening is not derived here.

    What falls out:
      - The dimensional dependence [log_2 n] is derived. For a trace
        that discriminates [n] outcomes, [Delta mu >= log_2 n], where
        [n] is the substrate's effective dimension (the number of
        distinguishable classical outcomes).
      - The derivation uses real ingredients: the decision-tree depth
        bound [decision_tree_log2_leaf_bound] from [MuShannonBridge.v],
        plus the cert-setter cost floor [cert_executions_le_ledger].
        Both are already proven in the framework — no new axioms here.

    What does NOT fall out:
      - The genuinely quantum tightening (Holevo with non-commuting
        observables / mixed quantum states). The framework has no
        Hilbert-space machinery, no density matrices, and explicitly
        admits that adding them is out of scope.
      - The bridge from a generic VM trace to a decision-tree witness
        is supplied as a hypothesis ([decision_tree_realizes]).
        [MuShannonBridge.v] documents this as the bridge step that is
        not derived in general: "The actual missing piece ... is
        deriving the tree/posterior witness from general VM-side
        reduction data."

    The classical floor of Holevo is a theorem here. The quantum
    tightening is a gap of the same kind as the Boltzmann gap in
    [LandauerJoules.v] — it requires substrate structure (Hilbert
    space) that the VM cost ledger does not provide. *)

From Coq Require Import List Lia Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import SimulationProof.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import MuShannonBridge.

(** ** Section 1 — the classical Holevo statement.

    For a classical substrate of effective dimension [n] (an
    [n]-element feasible set), the accessible classical information,
    measured in bits, is bounded by [log_2 n]. The Holevo bound for
    diagonal density matrices [rho = sum p_i |i><i|] saturates here.

    The headline theorem [classical_holevo_bound] proves the matching
    cost-floor: any VM trace that fully discriminates such a substrate
    must accumulate [mu]-cost at least [log_2 n]. *)

(** [substrate_dimension] is the size of the feasible set the VM is
    discriminating over. For a classical substrate this is the number
    of orthogonal pure states. For Holevo's purpose this is the
    dimensionality of the Hilbert space. *)
Definition substrate_dimension (omega : FeasibleSet) : nat :=
  feasible_size omega.

(** [accessible_classical_information] is the maximum number of
    classical bits extractable from a substrate of given dimension.
    Floor-log: this is the classical Holevo bound. *)
Definition accessible_classical_information (omega : FeasibleSet) : nat :=
  Nat.log2 (substrate_dimension omega).

(** ** Section 2 — headline.

    The classical Holevo bound: for any VM trace that discriminates a
    feasible set of [n] outcomes via a decision-tree-realized
    computation, [mu]-cost is at least [log_2 n].

    Hypotheses:
      - [omega] has at least one element (so [log_2] is well-defined).
      - The trace realizes a decision tree of at least [log_2 n] depth
        (this is the decision-tree witness the framework admits is not
        automatically derivable from arbitrary VM traces).
      - The tree has enough leaves to cover the substrate dimension.

    The proof composes three existing facts:
      (i)   [decision_tree_log2_leaf_bound]: depth >= log_2(leaves).
      (ii)  [decision_tree_realized_by_trace]: realization gives
            depth <= cert_setter_executions trace.
      (iii) [cert_executions_le_ledger]: cert_setter_executions <= Delta mu.

    Composition: log_2(leaves) <= depth <= cert_executions <= Delta mu.
    If leaves >= substrate_dimension, then log_2(substrate_dimension)
    <= Delta mu. *)

Theorem classical_holevo_bound :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState)
         (omega : FeasibleSet) (tree : DecisionTree),
    decision_tree_realized_by_trace fuel trace s tree ->
    substrate_dimension omega <= decision_tree_leaf_count tree ->
    accessible_classical_information omega <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  intros fuel trace s omega tree Hrealized Hcover.
  unfold accessible_classical_information, substrate_dimension in *.
  (* Step 1: log_2(feasible_size omega) <= log_2(leaves tree) *)
  assert (Hlog : Nat.log2 (feasible_size omega) <=
                 Nat.log2 (decision_tree_leaf_count tree)).
  { apply log2_le_mono. exact Hcover. }
  (* Step 2: log_2(leaves tree) <= depth tree *)
  pose proof (decision_tree_log2_leaf_bound tree) as Hdepth.
  (* Step 3: depth tree <= cert_setter_executions fuel trace s *)
  unfold decision_tree_realized_by_trace in Hrealized.
  (* Step 4: cert_setter_executions <= Delta mu *)
  pose proof (info_priced_cert_executions_bound fuel trace s) as Hledger.
  (* Compose: log_2(omega) <= log_2(leaves) <= depth <= cert_execs <= Delta mu *)
  lia.
Qed.

(** ** Section 3 — specialisation to n-qubit-shaped substrate.

    An [n]-qubit substrate has dimension [2^n]; the classical Holevo
    bound on accessible information is then [log_2(2^n) = n] bits. This
    is the textbook statement "n classical bits from n qubits", in the
    classical-floor sense. *)

(** A substrate with [n]-bit dimensional capacity has feasible-set size
    [2^n]. We do not construct such a set here; we just assume one is
    given. *)
Lemma classical_holevo_n_qubits :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState)
         (omega : FeasibleSet) (tree : DecisionTree) (n : nat),
    substrate_dimension omega = 2 ^ n ->
    decision_tree_realized_by_trace fuel trace s tree ->
    substrate_dimension omega <= decision_tree_leaf_count tree ->
    n <= (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  intros fuel trace s omega tree n Hdim Hrealized Hcover.
  pose proof (classical_holevo_bound fuel trace s omega tree Hrealized Hcover)
    as Hbound.
  unfold accessible_classical_information, substrate_dimension in *.
  rewrite Hdim in Hbound.
  rewrite Nat.log2_pow2 in Hbound by lia.
  exact Hbound.
Qed.

(** ** Section 4 — what the substrate would need for full Holevo.

    The classical floor here is saturated by classical substrates and
    by quantum substrates whose density matrices commute with the
    measurement basis. For genuinely non-commuting measurements,
    quantum Holevo is strictly tighter: the accessible information is
    bounded by the Holevo quantity chi = S(rho) - sum p_i S(rho_i),
    which can be strictly less than log_2(dim).

    The gap between the classical floor proved here and the full
    quantum statement requires:

      1. Density matrices (positive operators of trace 1 on a Hilbert
         space) as a substrate object.
      2. Von Neumann entropy S(rho) = -tr(rho log rho) as a numerical
         quantity.
      3. The Holevo inequality chi(ensemble) >= I(X:Y) for any
         classical-to-quantum encoding-decoding scheme.

    None of these are present in the kernel's current quantum surface.
    [HonestMeasurementImpliesNPA.v] explicitly flags this as the
    obstruction. This file therefore stops at the classical floor and
    names the gap. *)

(** Print Assumptions on the headline should report only the standard
    framework axioms (no new project-local axioms introduced here). *)
Print Assumptions classical_holevo_bound.
Print Assumptions classical_holevo_n_qubits.
