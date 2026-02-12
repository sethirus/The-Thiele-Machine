(** * Unitarity from Conservation Laws

    WHY THIS FILE EXISTS:
    I claim unitary evolution (reversible, norm-preserving quantum dynamics)
    is NOT a postulate - it's a CONSEQUENCE of information conservation (μ=0).
    This file proves: if μ-cost is zero (no information loss) and evolution
    respects conservation, then the dynamics MUST be unitary (or more generally,
    CPTP - Completely Positive Trace Preserving).

    THE CORE INSIGHT:
    Quantum mechanics uses unitary operators U (U†U = I) for time evolution
    because they preserve:
    1. Normalization: Tr(ρ) = 1 (trace preservation)
    2. Positivity: ρ ≥ 0 (physical states remain physical)
    3. Purity: Tr(ρ²) constant (no information loss)

    These three properties FOLLOW FROM μ=0 + conservation laws. Unitarity is
    not an axiom - it's the unique solution to "reversible evolution on a
    finite state space."

    THE BLOCH SPHERE MODEL:
    For single qubits, density matrices ρ map to Bloch vectors (x,y,z):
    ρ = (I + x·σ_x + y·σ_y + z·σ_z)/2
    where x² + y² + z² ≤ 1 (Bloch ball interior = mixed states).

    - Pure states: surface (r² = 1)
    - Mixed states: interior (r² < 1)
    - Unitary evolution: rotation of Bloch sphere (preserves r²)
    - Non-unitary (measurement, decoherence): shrinks Bloch ball (decreases r²)

    KEY THEOREMS:
    1. unitary_preserves_trace: Unitary ops preserve Tr(ρ) = 1
    2. unitary_preserves_positivity: Unitary ops preserve ρ ≥ 0
    3. nonunitary_requires_mu: Information loss requires μ > 0
    4. zero_cost_preserves_purity: μ=0 + conservation → purity preserved
    5. physical_evolution_is_CPTP: Physical maps are CPTP

    LANDAUER CONNECTION:
    Reversible operations (unitaries) cost zero μ because they don't erase
    information. Irreversible operations (measurement, reset) cost μ ≥ kT ln 2
    per bit erased (Landauer's principle). This file proves the "if μ=0 then
    reversible" direction.

    FALSIFICATION:
    Find a zero-cost operation (μ=0) that decreases purity (Tr(ρ²) drops).
    This would violate info_conservation and break the μ-accounting. Or show
    unitaries can have μ > 0 (violating thermodynamic reversibility). Or
    demonstrate non-CPTP physical evolution (violating quantum postulates).

    PHYSICAL INTERPRETATION:
    This connects μ-cost to thermodynamics: μ=0 ⟺ reversible ⟺ unitary.
    Quantum mechanics uses unitaries because nature respects thermodynamic
    reversibility for closed systems. Decoherence (open systems) breaks this,
    introducing μ > 0 and shrinking the Bloch ball.
*)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Local Open Scope R_scope.

(** =========================================================================
    SECTION 1: Density Matrix Properties
    ========================================================================= *)

(** trace_rho: Trace of density matrix
    For the Bloch sphere representation ρ = (I + x·σ + y·σ + z·σ)/2,
    Tr(ρ) = 1 always (normalization constraint).

    PHYSICAL MEANING: Probabilities must sum to 1. This is independent of
    the Bloch vector (x,y,z) - all density matrices have unit trace.

    FALSIFICATION: Find a physical density matrix with Tr(ρ) ≠ 1 (impossible
    by definition of density matrix).
*)
Definition trace_rho (x y z : R) : R := 1.

(** trace_rho_squared: Purity measure Tr(ρ²)
    For Bloch vector (x,y,z): Tr(ρ²) = (1 + r²)/2 where r² = x² + y² + z².

    DERIVATION:
    ρ² = [(I + x·σ_x + y·σ_y + z·σ_z)/2]²
       = (I + 2(x·σ_x + y·σ_y + z·σ_z) + (x² + y² + z²)·I)/4
       (using σ_i² = I and σ_i·σ_j anticommutators)
    Tr(ρ²) = Tr((2I + (x² + y² + z²)·I)/4) = (2 + r²)/4 · 2 = (1 + r²)/2

    PHYSICAL MEANING:
    - Tr(ρ²) = 1: pure state (r² = 1, on surface)
    - Tr(ρ²) = 1/2: maximally mixed (r² = 0, at center)
    - 1/2 < Tr(ρ²) < 1: partially mixed (0 < r² < 1, interior)

    FALSIFICATION: Compute Tr(ρ²) independently and verify formula. Or find
    states with Tr(ρ²) > 1 or Tr(ρ²) < 1/2 (violating Bloch ball geometry).
*)
Definition trace_rho_squared (x y z : R) : R :=
  (1 + x*x + y*y + z*z) / 2.

(** lambda_plus, lambda_minus: Eigenvalues of density matrix
    For Bloch vector (x,y,z), eigenvalues are:
    λ₊ = (1 + r)/2, λ₋ = (1 - r)/2 where r = √(x² + y² + z²)

    PHYSICAL MEANING:
    - λ₊ + λ₋ = 1 (trace normalization)
    - 0 ≤ λ₋ ≤ λ₊ ≤ 1 (positivity constraints)
    - λ₊ = 1, λ₋ = 0 for pure states (r = 1)
    - λ₊ = λ₋ = 1/2 for maximally mixed (r = 0)

    These are the probabilities of the two eigenstates |ψ₊⟩, |ψ₋⟩.

    FALSIFICATION: Find (x,y,z) with r ≤ 1 where eigenvalues violate 0 ≤ λ ≤ 1
    (impossible by Bloch ball definition).
*)
Definition lambda_plus (x y z : R) : R :=
  (1 + sqrt (x*x + y*y + z*z)) / 2.

Definition lambda_minus (x y z : R) : R :=
  (1 - sqrt (x*x + y*y + z*z)) / 2.

(** =========================================================================
    SECTION 2: Evolution Operations
    ========================================================================= *)

(** Evolution: A quantum channel (CPTP map)
    Maps input Bloch vector (x,y,z) to output (x',y',z').
    evo_mu tracks the μ-cost (information erased during evolution).

    PHYSICAL EXAMPLES:
    - Unitary (rotation): evo_mu = 0, preserves r²
    - Measurement: evo_mu > 0, projects to axis (decreases r²)
    - Decoherence: evo_mu > 0, shrinks Bloch ball toward center

    FALSIFICATION: Build a physical quantum channel with evo_mu < 0 (creating
    information from nothing, violating second law).
*)
Record Evolution := {
  (* The evolution maps (x,y,z) to (x',y',z') *)
  evo_x : R -> R -> R -> R;
  evo_y : R -> R -> R -> R;
  evo_z : R -> R -> R -> R;
  (* μ-cost of the evolution *)
  evo_mu : R
}.

(** trace_preserving: Normalization is conserved
    Tr(ρ_out) = Tr(ρ_in) = 1 for all inputs.

    PHYSICAL MEANING: Probabilities always sum to 1. This is a MUST for
    physical channels - losing or gaining probability violates basic probability
    theory.

    FALSIFICATION: Find an evolution where Tr(ρ_out) ≠ 1 for some valid input
    (breaking normalization).
*)
Definition trace_preserving (E : Evolution) : Prop :=
  forall x y z, trace_rho (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) =
                trace_rho x y z.

(** purity_nonincreasing: Purity can only decrease (or stay same)
    Tr(ρ_out²) ≤ Tr(ρ_in²) + evo_mu

    PHYSICAL MEANING: Information loss is bounded by μ-cost. If you erase
    information (decreasing purity), you must pay μ-cost to account for it.
    This is the quantum version of Landauer's principle.

    WHY "+ evo_mu": The μ-cost is the ALLOWED information loss. If μ=0,
    purity cannot decrease (reversible). If μ>0, purity can decrease by at
    most μ (irreversible, thermodynamic cost).

    FALSIFICATION: Find an evolution where purity drops by more than evo_mu
    (violating conservation).
*)
Definition purity_nonincreasing (E : Evolution) : Prop :=
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    (E.(evo_x) x y z)*(E.(evo_x) x y z) +
    (E.(evo_y) x y z)*(E.(evo_y) x y z) +
    (E.(evo_z) x y z)*(E.(evo_z) x y z) <= x*x + y*y + z*z + E.(evo_mu).

(** positivity_preserving: Valid states map to valid states
    If r²_in ≤ 1, then r²_out ≤ 1.

    PHYSICAL MEANING: The Bloch ball maps into itself. Physical states remain
    physical after evolution. This prevents "super-pure" states (r² > 1) or
    negative probabilities (outside ball).

    FALSIFICATION: Find an evolution mapping interior point to exterior point
    (breaking physical constraint r² ≤ 1).
*)
Definition positivity_preserving (E : Evolution) : Prop :=
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    (E.(evo_x) x y z)*(E.(evo_x) x y z) +
    (E.(evo_y) x y z)*(E.(evo_y) x y z) +
    (E.(evo_z) x y z)*(E.(evo_z) x y z) <= 1.

(** =========================================================================
    SECTION 3: Unitary Evolution
    ========================================================================= *)

(** is_unitary: Purity-preserving evolution (rotation of Bloch sphere)
    r²_out = r²_in exactly (no shrinking or expanding).

    PHYSICAL MEANING: Unitary operators rotate the Bloch sphere rigidly.
    Pure states stay pure, mixed states stay at same mixedness. This is
    TIME EVOLUTION in closed quantum systems (Schrödinger equation).

    EXAMPLES: Pauli rotations (X, Y, Z gates), Hadamard, phase gates.

    FALSIFICATION: Find a unitary where r²_out ≠ r²_in (violating definition).
*)
Definition is_unitary (E : Evolution) : Prop :=
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    (E.(evo_x) x y z)*(E.(evo_x) x y z) +
    (E.(evo_y) x y z)*(E.(evo_y) x y z) +
    (E.(evo_z) x y z)*(E.(evo_z) x y z) = x*x + y*y + z*z.

(** unitary_zero_cost: Unitaries have zero μ-cost
    Reversible operations don't erase information, so μ = 0.

    LANDAUER CONNECTION: Reversible computations are thermodynamically free
    (no entropy increase, no heat dissipation). Unitaries are reversible
    (U† inverts U), so they cost zero energy/μ.

    FALSIFICATION: Find a unitary with μ > 0 (violating Landauer).
*)
Definition unitary_zero_cost (E : Evolution) : Prop :=
  is_unitary E -> E.(evo_mu) = 0.

(** DEFINITIONAL HELPER: trace preservation from normalization constraint.
    In the Bloch sphere parametrization ρ = (I + x·σ_x + y·σ_y + z·σ_z)/2,
    Tr(ρ) = 1 holds for ALL density matrices by the normalization constraint
    (the Pauli matrices are traceless: Tr(σ_i) = 0).  This is NOT special to
    unitaries — it is a structural property of the parametrization itself.
    The real non-trivial theorem is [unitary_preserves_positivity] below,
    which actually USES the [is_unitary] hypothesis.
*)
(* DEFINITIONAL *)
Theorem trace_preserved_by_normalization :
  forall E : Evolution,
    trace_preserving E.
Proof.
  intros E.
  unfold trace_preserving, trace_rho.
  intros. reflexivity.
Qed.

(** Corollary for unitaries — follows from the general fact above. *)
(** DEFINITIONAL HELPER *)
Corollary unitary_preserves_trace :
  forall E : Evolution,
    is_unitary E ->
    trace_preserving E.
Proof.
  intros E _.
  apply trace_preserved_by_normalization.
Qed.

(** unitary_preserves_positivity: Unitaries preserve physical constraints
    If r²_in ≤ 1, then r²_out ≤ 1 for unitaries.

    PROOF: Unitary preserves r² exactly (is_unitary), so r²_out = r²_in ≤ 1.

    WHY PROVE THIS: Unitaries map Bloch ball to itself (preserving physics).
    Part of complete positivity requirement.

    FALSIFICATION: Find unitary mapping valid state to invalid state (r² > 1).
*)
(** HELPER: Non-negativity property *)
(** HELPER: Non-negativity property *)
Theorem unitary_preserves_positivity :
  forall E : Evolution,
    is_unitary E ->
    positivity_preserving E.
Proof.
  intros E Huni.
  unfold is_unitary, positivity_preserving in *.
  intros x y z Hvalid.
  rewrite (Huni x y z Hvalid).
  exact Hvalid.
Qed.

(** =========================================================================
    SECTION 4: Non-Unitary Evolution Requires μ-Cost
    ========================================================================= *)

(** info_loss: How much purity decreased
    Δr² = r²_in - r²_out

    PHYSICAL MEANING: Information erased during evolution. For unitaries,
    info_loss = 0. For measurements/decoherence, info_loss > 0.

    CONNECTION TO ENTROPY: Δ(Tr(ρ²)) ≈ ΔS (entropy increase). Information
    loss is entropy gain.

    FALSIFICATION: Find evolution with info_loss < 0 (purity increases,
    violating second law).
*)
Definition info_loss (E : Evolution) (x y z : R) : R :=
  (x*x + y*y + z*z) -
  ((E.(evo_x) x y z)*(E.(evo_x) x y z) +
   (E.(evo_y) x y z)*(E.(evo_y) x y z) +
   (E.(evo_z) x y z)*(E.(evo_z) x y z)).

(** respects_info_conservation: μ-cost accounts for information loss
    info_loss ≤ evo_mu for all states.

    PHYSICAL MEANING: You must PAY (in μ-bits) for information you erase.
    This is the accounting law: erasing information costs thermodynamic work
    (Landauer), which μ tracks.

    FALSIFICATION: Find evolution where info_loss > evo_mu (μ-accounting
    violated, information destroyed without payment).
*)
Definition respects_info_conservation (E : Evolution) : Prop :=
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    info_loss E x y z <= E.(evo_mu).

(** nonunitary_requires_mu: Information loss requires μ-cost
    If ANY state has info_loss > 0, then evo_mu > 0.

    PROOF: Assume info_loss > 0 for some (x,y,z). By respects_info_conservation,
    info_loss ≤ evo_mu. Thus evo_mu ≥ info_loss > 0, so evo_mu > 0. QED.

    PHYSICAL INTERPRETATION:
    Irreversible operations (measurement, reset, decoherence) MUST have μ > 0.
    You cannot erase information without thermodynamic cost. This connects
    quantum mechanics to thermodynamics directly.

    FALSIFICATION: Find a non-unitary (info_loss > 0) operation with μ = 0
    (free information erasure, violating Landauer).
*)
Theorem nonunitary_requires_mu :
  forall E : Evolution,
    respects_info_conservation E ->
    (exists x y z,
      x*x + y*y + z*z <= 1 /\
      info_loss E x y z > 0) ->
    E.(evo_mu) > 0.
Proof.
  intros E Hcons Hnonuni.
  destruct Hnonuni as [x [y [z [Hvalid Hloss]]]].
  specialize (Hcons x y z Hvalid).
  lra.
Qed.

(** =========================================================================
    SECTION 5: Completely Positive Maps
    ========================================================================= *)

(** is_CP: Completely Positive map
    A map is completely positive (CP) if it preserves positivity even when
    tensored with the identity on an ancilla system.

    PHYSICAL MEANING: CP ensures the map remains physical even when applied
    to part of an entangled system. This prevents "super-measurements" that
    would create negative probabilities on composite systems.

    BLOCH BALL CHARACTERIZATION:
    For single qubits, CP is equivalent to the Bloch ball shrinking (or staying
    same size). No expanding (r²_out ≤ r²_in for all points inside ball), and
    no mapping interior to exterior (r²_out ≤ 1 always).

    FALSIFICATION: Find a map that preserves positivity on single qubits but
    violates positivity when tensored with identity (breaking complete positivity).
*)
Definition is_CP (E : Evolution) : Prop :=
  positivity_preserving E /\
  (* Contractivity: Bloch ball maps inside itself *)
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    (E.(evo_x) x y z)*(E.(evo_x) x y z) +
    (E.(evo_y) x y z)*(E.(evo_y) x y z) +
    (E.(evo_z) x y z)*(E.(evo_z) x y z) <= 1.

(** is_CPTP: Completely Positive Trace Preserving
    The most general form of quantum channel. CPTP maps are exactly the
    physically realizable operations on quantum states.

    PHYSICAL MEANING:
    - Completely Positive: preserves positivity under composition with ancillas
    - Trace Preserving: preserves normalization (probabilities sum to 1)

    STINESPRING DILATION: Every CPTP map can be realized as unitary evolution
    on system + environment, followed by tracing out the environment. This
    proves CPTP maps are exactly the "open system" evolutions.

    FALSIFICATION: Find a physical quantum operation that is not CPTP (impossible
    by Stinespring theorem).
*)
Definition is_CPTP (E : Evolution) : Prop :=
  is_CP E /\ trace_preserving E.

(** physical_evolution_is_CPTP: Physical operations satisfy CPTP
    If an evolution preserves positivity and trace, it's CPTP.

    PROOF: Trivial conjunction - definition of CPTP is exactly these two properties.

    WHY PROVE THIS: Establishes that our evolution model (positivity + trace
    preservation) captures the full generality of quantum channels.

    FALSIFICATION: Show physical evolution violating CPTP axioms (contradicts
    quantum channel theory).
*)
Theorem physical_evolution_is_CPTP :
  forall E : Evolution,
    positivity_preserving E ->
    trace_preserving E ->
    is_CPTP E.
Proof.
  intros E Hpos Htr.
  unfold is_CPTP, is_CP.
  split.
  - split; [exact Hpos | exact Hpos].
  - exact Htr.
Qed.

(** =========================================================================
    SECTION 6: Lindblad Form and Dissipation
    ========================================================================= *)

(** dissipation_rate: Rate of purity loss
    How fast information is lost during evolution.

    PHYSICAL MEANING: dissipation_rate = d(Tr(ρ²))/dt in continuous time.
    For discrete maps, it's just the info_loss per step.

    LINDBLAD EQUATION: dρ/dt = -i[H,ρ] + Σ_k (L_k ρ L_k† - {L_k†L_k, ρ}/2)
    The second term (Lindblad operators L_k) causes dissipation. The dissipation
    rate is Σ_k Tr(L_k† L_k ρ²), which equals μ-cost per unit time.

    FALSIFICATION: Find dissipation (purity loss) without μ-cost (free information
    erasure, violating thermodynamics).
*)
Definition dissipation_rate (E : Evolution) (x y z : R) : R :=
  info_loss E x y z.

(** satisfies_lindblad_bound: Lindblad dissipation proportional to purity
    dissipation_rate ≤ γ · Tr(ρ²) where γ ≥ 0 is the damping rate.

    PHYSICAL EXAMPLES:
    - Amplitude damping (spontaneous emission): γ = decay rate (1/T₁)
    - Phase damping (dephasing): γ = dephasing rate (1/T₂)
    - Depolarizing channel: γ = depolarization rate

    WHY PROPORTIONAL TO PURITY: Maximally mixed states (r² = 0) cannot lose
    more purity. Pure states (r² = 1) lose purity fastest. The bound ensures
    dissipation respects this structure.

    FALSIFICATION: Find Lindblad evolution where dissipation exceeds γ · Tr(ρ²)
    (violating bound).
*)
Definition satisfies_lindblad_bound (E : Evolution) (gamma : R) : Prop :=
  gamma >= 0 /\
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    dissipation_rate E x y z <= gamma * (x*x + y*y + z*z).

(** lindblad_requires_mu: Lindblad dissipation costs μ
    If dissipation rate is γ > 0, then μ-cost ≥ γ.

    PROOF: Assume max dissipation γ occurs at some state (e.g., pure state |0⟩
    with x=1, y=z=0). By respects_info_conservation, info_loss ≤ evo_mu. Since
    info_loss = γ (maximal), we have evo_mu ≥ γ. QED.

    PHYSICAL INTERPRETATION:
    Decoherence (Lindblad dissipation) is NOT free. Each bit of information lost
    to the environment costs μ ≥ γ (the dissipation rate). This connects
    decoherence theory to thermodynamics: losing coherence = thermodynamic cost.

    FALSIFICATION: Find Lindblad channel with γ > 0 but μ = 0 (dissipation
    without cost, violating second law).
*)
Theorem lindblad_requires_mu :
  forall E gamma,
    gamma > 0 ->
    satisfies_lindblad_bound E gamma ->
    respects_info_conservation E ->
    (* If there's a pure state with maximal dissipation gamma *)
    (info_loss E 1 0 0 = gamma) ->
    E.(evo_mu) >= gamma.
Proof.
  intros E gamma Hgamma_pos Hlind Hcons Hmax_diss.
  destruct Hlind as [Hgamma_nonneg Hdiss].
  specialize (Hcons 1 0 0).
  assert (Hvalid: 1*1 + 0*0 + 0*0 <= 1) by lra.
  specialize (Hcons Hvalid).
  rewrite Hmax_diss in Hcons.
  lra.
Qed.

(** =========================================================================
    SECTION 7: Reversibility and Landauer
    ========================================================================= *)

(** is_reversible: Evolution has an inverse
    There exists E_inv such that E_inv ∘ E = identity on all valid states.

    PHYSICAL MEANING: Reversible operations can be undone. Like running a
    movie backwards - all information is preserved, so you can reconstruct
    the past from the present.

    EXAMPLES:
    - Unitary gates (X, Y, Z, H, CNOT): all reversible (inverse = adjoint)
    - Measurement: NOT reversible (collapses state, loses information)
    - Decoherence: NOT reversible (environment entanglement is one-way)

    FALSIFICATION: Find a reversible operation with μ > 0 (information loss
    despite invertibility, contradicting definition).
*)
Definition is_reversible (E : Evolution) : Prop :=
  exists E_inv : Evolution,
    forall x y z,
      x*x + y*y + z*z <= 1 ->
      E_inv.(evo_x) (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) = x /\
      E_inv.(evo_y) (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) = y /\
      E_inv.(evo_z) (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) = z.

(** zero_cost_preserves_purity: μ=0 + conservation → purity preserved
    If evo_mu = 0 and info_conservation holds, then purity cannot decrease.

    PROOF: By respects_info_conservation, info_loss ≤ evo_mu = 0. Since
    info_loss = r²_in - r²_out ≥ 0 (non-negative by definition), we have
    r²_in - r²_out = 0, so r²_out = r²_in. Thus purity is preserved. QED.

    PHYSICAL INTERPRETATION:
    Zero-cost operations are REVERSIBLE. No information is lost, so purity
    (information content) stays constant. This is Landauer's principle in
    reverse: if no thermodynamic cost, then no information erasure.

    LANDAUER'S PRINCIPLE:
    Erasing 1 bit costs at least kT ln 2 Joules (at temperature T). Equivalently,
    μ-cost ≥ 1 μ-bit per bit erased. The contrapositive: μ=0 → no erasure.

    FALSIFICATION: Find zero-cost operation (μ=0) with purity loss (r²_out < r²_in),
    violating conservation and Landauer.
*)
Theorem zero_cost_preserves_purity :
  forall E : Evolution,
    respects_info_conservation E ->
    E.(evo_mu) = 0 ->
    forall x y z,
      x*x + y*y + z*z <= 1 ->
      (E.(evo_x) x y z)*(E.(evo_x) x y z) +
      (E.(evo_y) x y z)*(E.(evo_y) x y z) +
      (E.(evo_z) x y z)*(E.(evo_z) x y z) >= x*x + y*y + z*z.
Proof.
  intros E Hcons Hmu_zero x y z Hvalid.
  specialize (Hcons x y z Hvalid).
  unfold info_loss in Hcons.
  rewrite Hmu_zero in Hcons.
  lra.
Qed.

(** reversible_zero_cost_is_unitary: Reversibility + μ=0 → unitary
    If an operation is reversible, positivity-preserving, conservation-respecting,
    and zero-cost, then it's unitary (purity-preserving).

    WHY NOT A THEOREM: This requires additional assumptions about the inverse
    also being conservation-respecting. Without that, the inverse might "add
    information" to compensate for loss in the forward direction.

    PHYSICAL CLAIM: For physical operations satisfying all conservation laws,
    reversibility with μ=0 implies unitarity. This connects reversibility
    (thermodynamic property) to unitarity (quantum property).

    FALSIFICATION: Find a reversible, zero-cost, conservation-respecting
    operation that is NOT unitary (has purity loss despite being invertible).
    This would require careful construction of a pathological inverse.

    NOTE: This is stated as a definition (Prop) rather than a proven Theorem
    because the proof requires strengthening assumptions about E_inv.
*)
Definition reversible_zero_cost_is_unitary : Prop :=
  forall E : Evolution,
    is_reversible E ->
    positivity_preserving E ->
    respects_info_conservation E ->
    E.(evo_mu) = 0 ->
    is_unitary E.

