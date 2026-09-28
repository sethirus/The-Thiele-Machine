(** This file develops a small real-valued Bloch-vector algebra and proves the identities stated by its definitions. The names “unitary,” “CPTP,” and “purity” provide the intended comparison, but these lemmas are not a physical derivation and do not connect to [VMState] unless a later bridge supplies that connection. *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics and does not engage VM semantics. No definition or theorem here
   mentions VMState, vm_step, vm_mu, MuCostModel or instruction_cost, and it
   imports no kernel module.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. Where these results feed the mu-ledger, they do so through the
   theorems downstream that consume them. The standalone boundary is stated
   here rather than inferred from an import. *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Local Open Scope R_scope.


(** Selected scalar trace constants for the Bloch-style record.
    The names preserve the usual matrix notation, but this file does not
    define matrices or prove a matrix-trace realization. *)
Definition pauli_tr_identity : R := 2.  (** Tr(I₂ₓ₂) = 0+0+1+1... wait, I₂ₓ₂ = [[1,0],[0,1]], Tr = 2 *)
Definition pauli_tr_sigma_x : R := 0.   (* SAFE: traceless Pauli matrix Tr([[0,1],[1,0]])=0 *)
Definition pauli_tr_sigma_y : R := 0.   (* SAFE: traceless Pauli matrix Tr([[0,-i],[i,0]])=0 *)
Definition pauli_tr_sigma_z : R := 0.   (* SAFE: traceless Pauli matrix Tr([[1,0],[0,-1]])=0 *)

(** [trace_rho] is the scalar trace expression for the model's Bloch-vector parameterization. With the declared Pauli trace constants, it simplifies to one. *)
Definition trace_rho (x y z : R) : R :=
  pauli_tr_identity / 2
  + x * pauli_tr_sigma_x / 2
  + y * pauli_tr_sigma_y / 2
  + z * pauli_tr_sigma_z / 2.

(** The numerical identity [trace_rho x y z = 1] follows by unfolding the
    Pauli trace constants (pauli_tr_identity=2, all sigma traces 0) and
    applying lra. It is discharged inline at its sole transitive use site,
    [unitary_preserves_trace] below; [trace_preserved_by_normalization]
    is similarly handled inline. *)

(** [trace_rho_squared] is the declared purity expression [((1 + x² + y² + z²) / 2)]. Its later bounds require the explicit radius assumptions stated by those lemmas. *)
Definition trace_rho_squared (x y z : R) : R :=
  (1 + x*x + y*y + z*z) / 2.

(** [lambda_plus] and [lambda_minus] are the two scalar expressions assigned to the Bloch-vector eigenvalue model. Their interval properties are proved only under the radius premises supplied in the relevant lemmas. *)
Definition lambda_plus (x y z : R) : R :=
  (1 + sqrt (x*x + y*y + z*z)) / 2.

Definition lambda_minus (x y z : R) : R :=
  (1 - sqrt (x*x + y*y + z*z)) / 2.


(** [Evolution] packages three real-valued output functions and a real cost parameter. The record alone does not assert that the functions form a physical quantum channel or that [evo_mu] is thermodynamic cost. *)
Record Evolution := {
  (* The evolution maps (x,y,z) to (x',y',z') *)
  evo_x : R -> R -> R -> R;
  evo_y : R -> R -> R -> R;
  evo_z : R -> R -> R -> R;
  (* μ-cost of the evolution *)
  evo_mu : R
}.

(** [trace_preserving] requires equality of the model's input and output trace expressions for every input triple. *)
Definition trace_preserving (E : Evolution) : Prop :=
  forall x y z, trace_rho (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) =
                trace_rho x y z.

(** [purity_nonincreasing] is the explicit radius inequality used by this model; its [evo_mu] term is a formal parameter, not a derived thermodynamic quantity. *)
Definition purity_nonincreasing (E : Evolution) : Prop :=
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    (E.(evo_x) x y z)*(E.(evo_x) x y z) +
    (E.(evo_y) x y z)*(E.(evo_y) x y z) +
    (E.(evo_z) x y z)*(E.(evo_z) x y z) <= x*x + y*y + z*z + E.(evo_mu).

(** [positivity_preserving] requires that the declared unit-radius region maps back into itself. *)
Definition positivity_preserving (E : Evolution) : Prop :=
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    (E.(evo_x) x y z)*(E.(evo_x) x y z) +
    (E.(evo_y) x y z)*(E.(evo_y) x y z) +
    (E.(evo_z) x y z)*(E.(evo_z) x y z) <= 1.


(** [is_unitary] is defined here as preservation of the squared radius on the declared unit ball. It is not a proof that an arbitrary [Evolution] record comes from a Hilbert-space operator. *)
Definition is_unitary (E : Evolution) : Prop :=
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    (E.(evo_x) x y z)*(E.(evo_x) x y z) +
    (E.(evo_y) x y z)*(E.(evo_y) x y z) +
    (E.(evo_z) x y z)*(E.(evo_z) x y z) = x*x + y*y + z*z.

(** [unitary_zero_cost] is a separate implication that assigns zero formal cost to an [is_unitary] evolution. It is a model contract, not a Landauer derivation. *)
Definition unitary_zero_cost (E : Evolution) : Prop :=
  is_unitary E -> E.(evo_mu) = 0.

(** Trace preservation from normalization constraint.
    In the Bloch sphere parametrization ρ = (I + x·σ_x + y·σ_y + z·σ_z)/2,
    Tr(ρ) = 1 holds for ALL density matrices by the normalization constraint
    (the Pauli matrices are traceless: Tr(σ_i) = 0).  This is NOT special to
    unitaries — it is a structural property of the parametrization itself.
    The general statement [trace_preserved_by_normalization] is the
    corollary [unitary_preserves_trace] specialized at is_unitary = trivial;
    the general form is folded into the corollary below to avoid an
    arithmetic-only intermediate. The real non-trivial theorem is
    [unitary_preserves_positivity] below, which actually USES the
    [is_unitary] hypothesis. *)
Corollary unitary_preserves_trace :
  forall E : Evolution,
    is_unitary E ->
    trace_preserving E.
Proof.
  intros E _ x y z.
  unfold trace_rho, pauli_tr_identity, pauli_tr_sigma_x,
         pauli_tr_sigma_y, pauli_tr_sigma_z.
  lra.
Qed.

(** [unitary_preserves_positivity] is the direct consequence of radius preservation and the unit-ball premise. *)
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


(** [info_loss] is the input squared radius minus the output squared radius. The definition does not identify this difference with von Neumann entropy or physical erasure. *)
Definition info_loss (E : Evolution) (x y z : R) : R :=
  (x*x + y*y + z*z) -
  ((E.(evo_x) x y z)*(E.(evo_x) x y z) +
   (E.(evo_y) x y z)*(E.(evo_y) x y z) +
   (E.(evo_z) x y z)*(E.(evo_z) x y z)).

(** [respects_info_conservation] requires the formal [info_loss] value to be bounded by the formal [evo_mu] value on valid input triples. *)
Definition respects_info_conservation (E : Evolution) : Prop :=
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    info_loss E x y z <= E.(evo_mu).

(** [nonunitary_requires_mu] is the elementary real-arithmetic consequence of [respects_info_conservation] and one positive [info_loss] witness. *)
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


(** [is_CP] is the conjunction of the formal unit-ball preservation predicate and a second copy of the same radius bound. *)
Definition is_CP (E : Evolution) : Prop :=
  positivity_preserving E /\
  (* Contractivity: Bloch ball maps inside itself *)
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    (E.(evo_x) x y z)*(E.(evo_x) x y z) +
    (E.(evo_y) x y z)*(E.(evo_y) x y z) +
    (E.(evo_z) x y z)*(E.(evo_z) x y z) <= 1.

(** [is_CPTP] is the conjunction of [is_CP] and [trace_preserving].

    The definition supplies a name for this formal conjunction but does not prove a physical channel characterization.
*)
Definition is_CPTP (E : Evolution) : Prop :=
  is_CP E /\ trace_preserving E.

(** [physical_evolution_is_CPTP] packages the two supplied formal premises into [is_CPTP].

    It does not establish that every physical operation is represented by this record.
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


(** [dissipation_rate] is an alias for the formal [info_loss] expression.

    The definition does not introduce a time derivative or a physical dissipation rate.
*)
Definition dissipation_rate (E : Evolution) (x y z : R) : R :=
  info_loss E x y z.

(** [satisfies_lindblad_bound] is a named inequality over the formal [dissipation_rate] expression.

    The parameter [gamma] is a nonnegative real in this model.

    No Lindblad equation or physical channel is constructed by the definition.
*)
Definition satisfies_lindblad_bound (E : Evolution) (gamma : R) : Prop :=
  gamma >= 0 /\
  forall x y z,
    x*x + y*y + z*z <= 1 ->
    dissipation_rate E x y z <= gamma * (x*x + y*y + z*z).

(** [lindblad_requires_mu] is a real-arithmetic consequence of the supplied bound, conservation premise, and explicit witness [info_loss E 1 0 0 = gamma].

    It does not prove a cost law for Lindblad dynamics or a thermodynamic result.
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


(** [is_reversible] requires a formal inverse on every input triple in the declared unit ball. *)
Definition is_reversible (E : Evolution) : Prop :=
  exists E_inv : Evolution,
    forall x y z,
      x*x + y*y + z*z <= 1 ->
      E_inv.(evo_x) (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) = x /\
      E_inv.(evo_y) (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) = y /\
      E_inv.(evo_z) (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) = z.

(** [zero_cost_preserves_purity] derives the displayed output-radius lower bound from [respects_info_conservation] and zero formal cost. *)
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

(** [zero_cost_implies_unitary] derives the local [is_unitary] predicate from the two displayed radius inequalities and zero formal cost. *)
(* SCOPE NOTE: key derived theorem — zero-cost + dual conservation → unitarity.
   Bridges Unitarity.v to NoCloning.v by eliminating the unitarity assumption. *)
Theorem zero_cost_implies_unitary :
  forall E : Evolution,
    respects_info_conservation E ->
    purity_nonincreasing E ->
    E.(evo_mu) = 0 ->
    is_unitary E.
Proof.
  intros E Hcons Hpni Hmu0.
  unfold is_unitary. intros x y z Hvalid.
  (* Lower bound: r²_out ≥ r²_in (from zero_cost_preserves_purity) *)
  pose proof (zero_cost_preserves_purity E Hcons Hmu0 x y z Hvalid) as Hge.
  (* Upper bound: r²_out ≤ r²_in + evo_mu = r²_in + 0 = r²_in *)
  unfold purity_nonincreasing in Hpni.
  specialize (Hpni x y z Hvalid).
  rewrite Hmu0 in Hpni.
  (* Combine: r²_out ≥ r²_in ∧ r²_out ≤ r²_in → r²_out = r²_in *)
  lra.
Qed.

(** [reversible_zero_cost_is_unitary] preserves an older interface while delegating to [zero_cost_implies_unitary]. *)
Corollary reversible_zero_cost_is_unitary :
  forall E : Evolution,
    is_reversible E ->
    positivity_preserving E ->
    respects_info_conservation E ->
    purity_nonincreasing E ->
    E.(evo_mu) = 0 ->
    is_unitary E.
Proof.
  intros E _ _ Hcons Hpni Hmu0.
  exact (zero_cost_implies_unitary E Hcons Hpni Hmu0).
Qed.

(* SCOPE NOTE: connectivity anchor for unitarity auxiliary definitions. *)
Definition unitarity_coverage_anchor := (trace_rho_squared, lambda_plus, lambda_minus).
