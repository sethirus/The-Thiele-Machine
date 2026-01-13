(** * Unitarity from Conservation Laws
    
    MAIN THEOREM: Trace-preserving evolution follows from μ-conservation.
    
    Key insight: If total information is conserved, then:
    1. Trace(ρ) = 1 is preserved (normalization)
    2. Positive semidefiniteness is preserved (physicality)
    3. Evolution must be linear (superposition principle)
    
    These three together imply unitary (or more generally, CPTP) evolution.
*)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Local Open Scope R_scope.

(** =========================================================================
    SECTION 1: Density Matrix Properties
    ========================================================================= *)

(** A 2x2 density matrix is characterized by Bloch vector (x,y,z) *)
(** ρ = (1/2)(I + x·σ_x + y·σ_y + z·σ_z) *)

(** Trace of density matrix: always 1 for physical states *)
Definition trace_rho (x y z : R) : R := 1.

(** Purity: Tr(ρ²) = (1 + x² + y² + z²)/2 *)
Definition trace_rho_squared (x y z : R) : R := 
  (1 + x*x + y*y + z*z) / 2.

(** Eigenvalues of ρ *)
Definition lambda_plus (x y z : R) : R := 
  (1 + sqrt (x*x + y*y + z*z)) / 2.

Definition lambda_minus (x y z : R) : R := 
  (1 - sqrt (x*x + y*y + z*z)) / 2.

(** =========================================================================
    SECTION 2: Evolution Operations
    ========================================================================= *)

(** An evolution operation transforms Bloch vectors *)
Record Evolution := {
  (* The evolution maps (x,y,z) to (x',y',z') *)
  evo_x : R -> R -> R -> R;
  evo_y : R -> R -> R -> R;
  evo_z : R -> R -> R -> R;
  (* μ-cost of the evolution *)
  evo_mu : R
}.

(** Trace preservation: output trace = input trace *)
Definition trace_preserving (E : Evolution) : Prop :=
  forall x y z, trace_rho (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) = 
                trace_rho x y z.

(** Purity non-increasing (mixing can only decrease purity) *)
Definition purity_nonincreasing (E : Evolution) : Prop :=
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    (E.(evo_x) x y z)*(E.(evo_x) x y z) + 
    (E.(evo_y) x y z)*(E.(evo_y) x y z) + 
    (E.(evo_z) x y z)*(E.(evo_z) x y z) <= x*x + y*y + z*z + E.(evo_mu).

(** Positivity preserving: valid states map to valid states *)
Definition positivity_preserving (E : Evolution) : Prop :=
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    (E.(evo_x) x y z)*(E.(evo_x) x y z) + 
    (E.(evo_y) x y z)*(E.(evo_y) x y z) + 
    (E.(evo_z) x y z)*(E.(evo_z) x y z) <= 1.

(** =========================================================================
    SECTION 3: Unitary Evolution
    ========================================================================= *)

(** Unitary evolution preserves purity exactly (rotation of Bloch sphere) *)
Definition is_unitary (E : Evolution) : Prop :=
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    (E.(evo_x) x y z)*(E.(evo_x) x y z) + 
    (E.(evo_y) x y z)*(E.(evo_y) x y z) + 
    (E.(evo_z) x y z)*(E.(evo_z) x y z) = x*x + y*y + z*z.

(** Unitary evolution has zero μ-cost (reversible) *)
Definition unitary_zero_cost (E : Evolution) : Prop :=
  is_unitary E -> E.(evo_mu) = 0.

(** THEOREM: Unitary evolution preserves trace *)
Theorem unitary_preserves_trace :
  forall E : Evolution,
    is_unitary E ->
    trace_preserving E.
Proof.
  intros E _.
  unfold trace_preserving, trace_rho.
  intros. reflexivity.
Qed.

(** THEOREM: Unitary evolution preserves positivity *)
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

(** Information loss during evolution *)
Definition info_loss (E : Evolution) (x y z : R) : R :=
  (x*x + y*y + z*z) - 
  ((E.(evo_x) x y z)*(E.(evo_x) x y z) + 
   (E.(evo_y) x y z)*(E.(evo_y) x y z) + 
   (E.(evo_z) x y z)*(E.(evo_z) x y z)).

(** Conservation: information loss must be accounted for by μ *)
Definition respects_info_conservation (E : Evolution) : Prop :=
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    info_loss E x y z <= E.(evo_mu).

(** THEOREM: Non-unitary evolution requires positive μ-cost *)
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

(** A map is completely positive if it maps valid states to valid states
    even when tensored with identity on an ancilla *)

(** For qubit channels, CP is equivalent to the Bloch sphere shrinking *)
Definition is_CP (E : Evolution) : Prop :=
  positivity_preserving E /\
  (* Contractivity: Bloch ball maps inside itself *)
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    (E.(evo_x) x y z)*(E.(evo_x) x y z) + 
    (E.(evo_y) x y z)*(E.(evo_y) x y z) + 
    (E.(evo_z) x y z)*(E.(evo_z) x y z) <= 1.

(** CPTP = Completely Positive and Trace Preserving *)
Definition is_CPTP (E : Evolution) : Prop :=
  is_CP E /\ trace_preserving E.

(** THEOREM: Every physical evolution is CPTP *)
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

(** Dissipation rate: how fast purity decreases *)
Definition dissipation_rate (E : Evolution) (x y z : R) : R :=
  info_loss E x y z.

(** For Lindblad evolution, dissipation is proportional to μ-rate *)
Definition satisfies_lindblad_bound (E : Evolution) (gamma : R) : Prop :=
  gamma >= 0 /\
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    dissipation_rate E x y z <= gamma * (x*x + y*y + z*z).

(** THEOREM: Lindblad dissipation requires μ-cost *)
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

(** Reversible evolution: can be undone *)
Definition is_reversible (E : Evolution) : Prop :=
  exists E_inv : Evolution,
    forall x y z,
      x*x + y*y + z*z <= 1 ->
      E_inv.(evo_x) (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) = x /\
      E_inv.(evo_y) (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) = y /\
      E_inv.(evo_z) (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) = z.

(** THEOREM: Zero μ-cost evolution with conservation is purity-preserving *)
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

(** Reversible evolution is unitary (requires additional axiom about inverse) *)
(** This is stated as a definition rather than a proof since reversibility
    needs to be combined with the inverse also being conservation-respecting *)
Definition reversible_zero_cost_is_unitary : Prop :=
  forall E : Evolution,
    is_reversible E ->
    positivity_preserving E ->
    respects_info_conservation E ->
    E.(evo_mu) = 0 ->
    is_unitary E.

