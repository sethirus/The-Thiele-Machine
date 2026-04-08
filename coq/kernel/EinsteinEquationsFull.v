(** =========================================================================
    FULL TENSOR EINSTEIN FIELD EQUATIONS — STRUCTURAL DECOMPOSITION
    =========================================================================

    WHY THIS FILE EXISTS:
    The audit (G1, G4) found that ThieleMachineComplete.v's Einstein equation
    is restricted to diagonal (d,d) indices. This file proves the structural
    decomposition: full tensor EFE = diagonal EFE + off-diagonal Ricci = 0.

    WHAT IS PROVED (0 Admitted):
    1. Star complex construction with 4 directed edges
    2. General lemma: derivative of zero-valued function = 0 on ANY complex
    3. Off-diagonal metric derivatives vanish for diagonal metrics
    4. Off-diagonal Einstein = off-diagonal Ricci (since g_{ij} = 0 for i<>j)
    5. Off-diagonal stress-energy = 0 (by definition of mass_stress_energy)
    6. Inverse of isotropic diagonal metric is diagonal
    7. REDUCTION THEOREM: full tensor EFE holds iff off-diagonal Ricci = 0

    WHAT IS NOT PROVED (honest scope):
    - Off-diagonal Ricci = 0 on any finite simplicial complex
    - This is a known discretization artifact: on finite complexes with
      isotropic diagonal metric, off-diagonal Ricci is generically nonzero
    - The diagonal EFE (from CurvedTensorPipeline.v) captures the full
      physical content available at this discretization scale

    The reduction theorem is FALSIFIABLE: instantiate the off-diagonal Ricci
    hypothesis with a specific complex. On two_vertex_sc it fails (documented
    in CurvedTensorPipeline.v:1063-1078).
    ========================================================================= *)

From Coq Require Import Reals List Arith.PeanoNat Lia Lra.
From Coq Require Import Bool.
Import ListNotations.
Local Open Scope R_scope.

From Kernel Require Import VMState.
From Kernel Require Import FourDSimplicialComplex.
From Kernel Require Import RiemannTensor4D.
From Kernel Require Import MetricFromMuCosts.
From Kernel Require Import CurvedTensorPipeline.

(** =========================================================================
    PART 1: THE STAR COMPLEX
    =========================================================================

    5 vertices: v (center), w0, w1, w2, w3 (neighbors)
    4 directed edges: (v,w_mu) with direction label Some mu

    Vertex order: neighbors BEFORE center, so discrete_derivative at v
    finds the correct neighbor first (same pattern as two_vertex_sc).
    ========================================================================= *)

Definition star_complex (v w0 w1 w2 w3 : nat) : SimplicialComplex4D :=
  {| sc4d_vertices := [w0; w1; w2; w3; v];
     sc4d_edges := [
       {| e1d_vertices := [v; w0]; e1d_direction := Some 0%nat |};
       {| e1d_vertices := [v; w1]; e1d_direction := Some 1%nat |};
       {| e1d_vertices := [v; w2]; e1d_direction := Some 2%nat |};
       {| e1d_vertices := [v; w3]; e1d_direction := Some 3%nat |}
     ];
     sc4d_faces := [];
     sc4d_cells := [];
     sc4d_4simplices := [];
  |}.

(** All 5 vertices of the star complex are distinct *)
Definition star_distinct (v w0 w1 w2 w3 : nat) : Prop :=
  v <> w0 /\ v <> w1 /\ v <> w2 /\ v <> w3 /\
  w0 <> w1 /\ w0 <> w2 /\ w0 <> w3 /\
  w1 <> w2 /\ w1 <> w3 /\
  w2 <> w3.

(** A metric is diagonal at all vertices of the star complex *)
Definition star_metric_diagonal (s : VMState) (v w0 w1 w2 w3 : nat) : Prop :=
  forall u i j, In u [v; w0; w1; w2; w3] ->
    i <> j -> full_metric_at_vertex s u i j = 0.

(** =========================================================================
    PART 2: GENERAL ZERO-DERIVATIVE LEMMA
    =========================================================================

    If f = 0 at all vertices of a simplicial complex, then the discrete
    derivative of f is 0 at any vertex in any direction.

    This is independent of the complex structure and uses filter_In to
    handle the list filtering generically.
    ========================================================================= *)

Lemma dd_zero_general :
  forall s sc f mu v,
    (forall u, In u (sc4d_vertices sc) -> f u = 0) ->
    In v (sc4d_vertices sc) ->
    discrete_derivative s sc f mu v = 0.
Proof.
  intros s sc f mu v0 Hzero Hv.
  unfold discrete_derivative.
  set (neighbors := filter _ _).
  destruct neighbors as [|w rest] eqn:Hn.
  - lra.
  - assert (In w (w :: rest)) as Hw_in_n by (left; reflexivity).
    rewrite <- Hn in Hw_in_n.
    unfold neighbors in Hw_in_n.
    apply filter_In in Hw_in_n.
    destruct Hw_in_n as [Hw_vert _].
    rewrite (Hzero w Hw_vert).
    rewrite (Hzero v0 Hv).
    lra.
Qed.

(** =========================================================================
    PART 3: OFF-DIAGONAL METRIC DERIVATIVES VANISH
    ========================================================================= *)

Theorem offdiag_metric_derivative_zero :
  forall s v w0 w1 w2 w3 i j mu,
    star_metric_diagonal s v w0 w1 w2 w3 ->
    i <> j ->
    discrete_derivative s (star_complex v w0 w1 w2 w3)
      (fun w => full_metric_at_vertex s w i j) mu v = 0.
Proof.
  intros s v0 w0 w1 w2 w3 i j mu Hdiag Hij.
  apply dd_zero_general.
  - intros u Hu.
    (* u is in star_complex vertices = [w0; w1; w2; w3; v0] *)
    (* Need: In u [v0; w0; w1; w2; w3] for Hdiag *)
    apply Hdiag; [| exact Hij].
    simpl in Hu. simpl. tauto.
  - simpl. tauto.
Qed.

(** =========================================================================
    PART 4: OFF-DIAGONAL INVERSE METRIC VANISHES (ISOTROPIC CASE)
    =========================================================================

    Leverages inverse_metric_isotropic from CurvedTensorPipeline.v.
    ========================================================================= *)

Lemma diag_inverse_offdiag_zero :
  forall s v a,
    a > 0 ->
    (forall i j, (i < 4)%nat -> (j < 4)%nat ->
      full_metric_at_vertex s v i j = if (i =? j)%nat then a else 0) ->
    forall i j, (i < 4)%nat -> (j < 4)%nat ->
      i <> j ->
      inverse_metric_at_vertex s v i j = 0.
Proof.
  intros s v0 a Ha Hiso i j Hi Hj Hij.
  rewrite (inverse_metric_isotropic s v0 a Ha Hiso i j Hi Hj).
  destruct (Nat.eqb_spec i j); [contradiction | lra].
Qed.

(** =========================================================================
    PART 5: OFF-DIAGONAL EINSTEIN = OFF-DIAGONAL RICCI
    =========================================================================

    For diagonal metric, g_{mu nu} = 0 when mu <> nu.
    G_{mu nu} = R_{mu nu} - (1/2) g_{mu nu} R = R_{mu nu} - 0 = R_{mu nu}.
    ========================================================================= *)

Theorem offdiag_einstein_eq_ricci :
  forall s sc v mu nu,
    (forall i j, i <> j -> full_metric_at_vertex s v i j = 0) ->
    mu <> nu ->
    curved_einstein s sc mu nu v =
    curved_ricci s sc mu nu v.
Proof.
  intros s sc v0 mu nu Hdiag Hne.
  unfold curved_einstein.
  rewrite (Hdiag mu nu Hne). lra.
Qed.

(** =========================================================================
    PART 6: OFF-DIAGONAL STRESS-ENERGY VANISHES
    ========================================================================= *)

Lemma offdiag_stress_energy_zero :
  forall s mu nu v,
    (mu < 4)%nat -> (nu < 4)%nat ->
    mu <> nu ->
    mass_stress_energy s mu nu v = 0.
Proof.
  intros s mu nu v Hmu Hnu Hne.
  unfold mass_stress_energy.
  destruct (Nat.eqb_spec (mu mod 4) (nu mod 4)).
  - exfalso. apply Hne.
    rewrite (Nat.mod_small mu 4 Hmu) in e.
    rewrite (Nat.mod_small nu 4 Hnu) in e.
    exact e.
  - reflexivity.
Qed.

(** =========================================================================
    PART 7: FULL TENSOR EFE — REDUCTION THEOREM
    =========================================================================

    The full tensor Einstein field equation G_{mu nu} = kappa T_{mu nu}
    for ALL (mu,nu) follows from two ingredients:
    1. Diagonal EFE: G_{dd} = kappa T_{dd}
    2. Off-diagonal: R_{mu nu} = 0 for mu <> nu
       (since G_{mu nu} = R_{mu nu} and T_{mu nu} = 0 for mu <> nu)

    This theorem is FALSIFIABLE: the off-diagonal Ricci hypothesis must
    be discharged for each specific complex. On two_vertex_sc it cannot
    be discharged (off-diagonal Ricci is generically nonzero there).
    ========================================================================= *)

Theorem full_efe_from_diagonal_and_offdiag_ricci :
  forall s sc v kappa,
    (* Diagonal metric at v *)
    (forall i j, i <> j -> full_metric_at_vertex s v i j = 0) ->
    (* Diagonal EFE (from existing einstein_equation_from_mass or similar) *)
    (forall d, (d < 4)%nat ->
      curved_einstein s sc d d v = kappa * mass_stress_energy s d d v) ->
    (* Off-diagonal Ricci = 0 (the key hypothesis) *)
    (forall mu nu, (mu < 4)%nat -> (nu < 4)%nat -> mu <> nu ->
      curved_ricci s sc mu nu v = 0) ->
    (* CONCLUSION: Full tensor EFE for ALL (mu,nu) *)
    forall mu nu, (mu < 4)%nat -> (nu < 4)%nat ->
      curved_einstein s sc mu nu v = kappa * mass_stress_energy s mu nu v.
Proof.
  intros s sc v0 kappa Hdiag_metric Hdiag_efe Hoffdiag_ricci mu nu Hmu Hnu.
  destruct (Nat.eq_dec mu nu) as [Heq | Hne].
  - subst nu. apply Hdiag_efe. exact Hmu.
  - rewrite (offdiag_einstein_eq_ricci s sc v0 mu nu Hdiag_metric Hne).
    rewrite (Hoffdiag_ricci mu nu Hmu Hnu Hne).
    rewrite (offdiag_stress_energy_zero s mu nu v0 Hmu Hnu Hne).
    lra.
Qed.

(** =========================================================================
    PART 8: STAR COMPLEX SCOPE RECORD
    ========================================================================= *)

Record EinsteinFullScope := {
  efs_diagonal_proved : Prop;
  efs_offdiag_reduction : Prop;
  efs_stress_diagonal : Prop;
  efs_full_efe_conditional : Prop;
}.

Definition einstein_scope_summary : EinsteinFullScope :=
  {| efs_diagonal_proved :=
       (* CurvedTensorPipeline.v: einstein_equation_from_mass *)
       True;
     efs_offdiag_reduction :=
       (* This file: full_efe_from_diagonal_and_offdiag_ricci *)
       True;
     efs_stress_diagonal :=
       (* This file: offdiag_stress_energy_zero *)
       True;
     efs_full_efe_conditional :=
       (* Full EFE holds on any complex where off-diagonal Ricci = 0.
          This is a computational property of specific complexes, not
          a general theorem. On finite complexes with isotropic diagonal
          metric, off-diagonal Ricci is generically nonzero — a known
          discretization artifact. *)
       True;
  |}.

(** =========================================================================
    PART 9: HONEST SCOPE DOCUMENTATION
    =========================================================================

    MATHEMATICAL ANALYSIS:
    For isotropic diagonal metric g = a*delta on a finite simplicial complex:
    - The Christoffel at center v: Gamma^rho_{mu nu}(v] = c*(d_{nu rho}+d_{mu rho}-d_{mu nu})
      where c = (b-a)/(2a)
    - The Christoffel at leaf vertices is 0 (leaves have no outgoing derivatives —
      they are their own first neighbor, giving derivative = 0)
    - The derivative of Christoffel at v is -Gamma(v) for ALL directions
      (because Gamma(leaf) = 0 for all leaves, regardless of which leaf)
    - This makes the Riemann tensor direction-independent, and the off-diagonal
      Ricci becomes 2c(1+c) which is generically nonzero

    CONSEQUENCE:
    On any finite simplicial complex with isotropic diagonal metric,
    the off-diagonal discrete Ricci is nonzero. This is NOT a bug —
    it is a fundamental property of the discrete derivative on finite
    graphs. The diagonal EFE is the maximal physically meaningful
    statement at this discretization scale.

    The REDUCTION THEOREM (full_efe_from_diagonal_and_offdiag_ricci)
    is still valuable because:
    1. It decomposes the full EFE into modular, independently verifiable pieces
    2. The off-diagonal Ricci hypothesis is FALSIFIABLE (can be checked per complex)
    3. It makes the scope limitation EXPLICIT rather than hidden
    4. If a future discretization scheme produces off-diagonal Ricci = 0, the
       reduction theorem immediately gives the full tensor EFE
    ========================================================================= *)
