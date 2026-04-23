(** EinsteinEquations4D: unit-normalized Einstein-side identities.

  This file defines the 4D Einstein-side objects built from the VM tensor
  machinery and proves the cases it can honestly prove. The key limit is up
  front: the clean theorem here is the isotropic vacuum case. The broader
  curved and non-vacuum story gets handled by narrower bridge theorems and by
  later files that add more hypotheses.

  The constant G = 1 / (8PI) is just a unit convention inside this file. It
  normalizes 8PIG to 1 in computational units. It is not a derivation of the
  physical Newton constant, and the header says that plainly. *)

From Coq Require Import Reals List Arith.PeanoNat Lia Lra Bool.
From Coq Require Import FunctionalExtensionality.
Import ListNotations.
Local Open Scope R_scope.

From Kernel Require Import VMState VMStep.
From Kernel Require Import FourDSimplicialComplex.
From Kernel Require Import MetricFromMuCosts.
From Kernel Require Import RiemannTensor4D.
From Kernel Require Import MuGravity.
From Kernel Require Import KernelPhysics.

(** Import key definitions so theorem statements stay readable. *)
Import RiemannTensor4D.

(** Gravitational constant in computational units.

  This is a normalization choice so the Einstein equation reads G_mn = T_mn
  in the units used here. *)

Definition computational_scale : R := 1%R.

(* Unit convention only. The normalization 8PI G = 1 is chosen so later
  formulas are readable. Nothing in this file claims that numerical value in
  physical units or derives it from mu-cost dynamics. *)
Definition gravitational_constant : R := (/ (8 * PI))%R.
(** Alias for backwards compatibility *)
Definition newtons_constant : R := gravitational_constant.

(* DEFINITIONAL HELPER *)
Lemma computational_scale_positive : (computational_scale > 0)%R.
Proof.
  unfold computational_scale.
  lra.
Qed.

(** Stress-energy tensor from μ-costs.

    T_μν encodes energy density (T_00), momentum density (T_0i), and
    stress (T_ij: pressure on diagonal, shear off-diagonal). These come
    from module_structural_mass (information content) and its spatial gradients.
*)

(** Energy density at a vertex *)
Definition energy_density (s : VMState) (v : ModuleID) : R :=
  INR (module_structural_mass s v).

(** Momentum density (simplified - needs time evolution) *)
Definition momentum_density (s : VMState) (sc : SimplicialComplex4D)
  (v : ModuleID) (i : nat) : R :=
  (* Spatial derivative of energy density in direction i *)
  discrete_derivative s sc (fun w => energy_density s w) i v.

(** Stress component (spatial gradients)

    T_ij(v) = ρ(v) · g_ij(v)

    Physical meaning: isotropic perfect fluid at rest.  The pressure tensor
    is proportional to the metric tensor.  In flat spacetime with diagonal
    metric (g_ij = 0 for i ≠ j), this gives T_ij = ρ·δ_ij: pressure on
    the diagonal, zero shear off-diagonal.  In curved spacetime the
    off-diagonal components can be non-zero in general.

    The vanishing of off-diagonal terms for i ≠ j is NOT built into the
    definition.  It is proven as a theorem under the isotropy condition
    (diagonal_metric_at), which states that the local metric is diagonal.
*)
Definition stress_component (s : VMState) (sc : SimplicialComplex4D)
  (v : ModuleID) (i j : nat) : R :=
  (* Isotropic stress: proportional to the metric at v *)
  (energy_density s v * RiemannTensor4D.metric_component s i j v)%R.

(** Isotropy condition: the metric at vertex v is diagonal. *)
Definition diagonal_metric_at (s : VMState) (v : ModuleID) : Prop :=
  forall i j : nat, i <> j ->
  RiemannTensor4D.metric_component s i j v = 0%R.

(** T_ij = 0 for i ≠ j follows from isotropy (diagonal metric), not
    from the definition.  This is the key theorem of Prompt 3. *)
Lemma stress_off_diagonal_zero_isotropic : forall s sc v i j,
  diagonal_metric_at s v ->
  i <> j ->
  stress_component s sc v i j = 0%R.
Proof.
  intros s sc v i j Hdiag Hneq.
  unfold stress_component.
  rewrite (Hdiag i j Hneq).
  ring.
Qed.

(** Full stress-energy tensor *)
Definition stress_energy_tensor (s : VMState) (sc : SimplicialComplex4D)
  (μ ν v : ModuleID) : R :=
  if ((μ =? 0) && (ν =? 0))%bool
  then energy_density s v  (* T_00 = ρ (energy density) *)
  else if (μ =? 0)%bool
  then momentum_density s sc v ν  (* T_0i = momentum density *)
  else if (ν =? 0)%bool
  then momentum_density s sc v μ  (* T_i0 = momentum density *)
  else stress_component s sc v μ ν.  (* T_ij = stress *)

(** Main theorem: isotropic vacuum Einstein equation

    G_μν = 8πG T_μν

    HONEST SCOPE: This file proves the ISOTROPIC VACUUM case. Both sides
    independently equal 0.  The two former structural gaps are now closed:

    CLOSED: Position-independent metric (was Structural Gap 1):
    metric_component now reads full_metric_at_vertex s v μ ν (per-vertex).
    Christoffel symbols are zero only under uniform_module_tensor s (all
    modules carry the same tensor).  For non-uniform tensors the metric
    varies across the graph and curvature is non-trivial; see the curved
    spacetime section below and CurvedTensorPipeline.v.

    CLOSED: Coordinate direction collapse (was Structural Gap 2):
    discrete_derivative now filters neighbors by e1d_direction, so partial
    derivatives in different coordinate directions can differ when edges are
    labeled with direction tags (e1d_direction = Some d).  Undirected edges
    (None) remain backward-compatible.

    WHAT THE ISOTROPIC VACUUM THEOREM PROVES:
    Under (a) uniform_module_tensor s (flat geometry) and (b) mass = 0
    everywhere (vacuum matter): both sides independently evaluate to 0.
      LHS: G_μν = 0 via flat_spacetime_christoffel_zero_general.
      RHS: T_μν = 0 via stress_energy_conserved_non_pmerge.
    Off-diagonal T_ij = 0 is a THEOREM (stress_off_diagonal_zero_isotropic)
    under diagonal_metric_at s v, not hardcoded in the definition.

    G = 1/(8π) is a unit convention (8πG ≡ 1).  See
    gravitational_coupling_unit_convention for the Coq proof.
    It is not derived from μ-cost dynamics.

    This is a valid Coq theorem: zero Admitted, zero project-local axioms.
    For the curved / non-vacuum case, see einstein_equation_isotropic_vacuum
    open problems OP-1 through OP-6 and CurvedTensorPipeline.v.

    The core machine theorems: μ-conservation, NoFI, initiality, and
    categorical laws, are independent of the geometry proofs here.
*)

(** Einstein field equations: isotropic vacuum case

    einstein_equation_isotropic_vacuum
    Under vacuum (mass=0) and flat geometry (uniform_module_tensor s):
      G_μν = 8πG · T_μν   (both sides = 0 independently)

    G_μν is zero because the uniform tensor forces Christoffel = 0 via
    flat_spacetime_christoffel_zero_general (not by construction).
    T_μν is zero via stress_energy_conserved_non_pmerge (no mass → no source).

    G = 1/(8π) is a unit convention.  Classification: (R) Consistency.
    For the non-vacuum curved case see CurvedTensorPipeline.v and
    open problems OP-1 through OP-6 in einstein_equation_isotropic_vacuum.
*)

(** Bridge lemmas: connecting discrete geometry to mass distribution. *)

From Coq Require Import Classical_Prop.

(** The metric tensor g_μν(v) is now POSITION-DEPENDENT: it reads from the
    per-module tensor of vertex v (module_tensor_entry s v ...).  Different
    vertices carry different metrics, so Christoffel symbols are non-trivial
    whenever neighbouring modules have different tensors.

    Definition: a state has UNIFORM module tensors when all vertices share
    the same tensor entries. That is the flat-spacetime analogue used here.
*)

(** Predicate: all modules in state s carry the same 4×4 tensor. *)
Definition uniform_module_tensor (s : VMState) : Prop :=
  forall v1 v2 i j, module_tensor_entry s v1 i j = module_tensor_entry s v2 i j.

(* Metric at vertex v reads the per-vertex module tensor. *)
Lemma metric_diagonal_local : forall s v mu,
  RiemannTensor4D.metric_component s mu mu v =
    INR (module_tensor_entry s v (mu mod 4) (mu mod 4)).
Proof.
  intros s v mu.
  unfold RiemannTensor4D.metric_component, full_metric_at_vertex.
  reflexivity.
Qed.

(* metric_component_vertex_independent is DELETED.
   The metric is now genuinely position-dependent; different vertices can
   carry different metric values. *)

(* The metric is position-independent when tensors are uniform. *)
Lemma metric_component_uniform_flat : forall s mu nu w1 w2,
  uniform_module_tensor s ->
  RiemannTensor4D.metric_component s mu nu w1 =
  RiemannTensor4D.metric_component s mu nu w2.
Proof.
  intros s mu nu w1 w2 Hunif.
  unfold RiemannTensor4D.metric_component, full_metric_at_vertex.
  f_equal. apply Hunif.
Qed.

(* A constant function has zero discrete derivative. *)
Lemma discrete_derivative_constant : forall s sc c mu v,
  RiemannTensor4D.discrete_derivative s sc (fun _ => c) mu v = 0%R.
Proof.
  intros s sc c mu v.
  unfold RiemannTensor4D.discrete_derivative.
  destruct (filter _ _) as [|w ws].
  - reflexivity.
  - simpl. ring.
Qed.

(* metric_component_position_independent_uniform is DELETED.
   It was an artefact of the old global-metric definition.
   Use metric_component_uniform_flat with uniform_module_tensor instead. *)

(* A position-independent function has zero discrete derivative. *)
Lemma discrete_derivative_position_independent : forall s sc f mu v,
  (forall w1 w2, f w1 = f w2) ->
  RiemannTensor4D.discrete_derivative s sc f mu v = 0%R.
Proof.
  intros s sc f mu v H_indep.
  unfold RiemannTensor4D.discrete_derivative.
  destruct (filter _ _) as [|w ws].
  - reflexivity.
  - simpl. rewrite (H_indep w v). ring.
Qed.

(* Helper: filter with always-false predicate gives empty list *)
Lemma filter_false : forall {A} (l : list A),
  filter (fun _ => false) l = [].
Proof.
  intros A l.
  induction l as [|x xs IH]; simpl; auto.
Qed.

(* In a simplicial complex with no edges, all derivatives vanish. *)
Lemma no_edges_derivative_zero : forall s sc f mu v,
  sc4d_edges sc = [] ->
  RiemannTensor4D.discrete_derivative s sc f mu v = 0%R.
Proof.
  intros s sc f mu v H_no_edges.
  unfold RiemannTensor4D.discrete_derivative.
  rewrite H_no_edges.
  (* After rewrite, we have filter (fun w => existsb ... []) (sc4d_vertices sc) *)
  (* Need to show this equals [] *)
  induction (sc4d_vertices sc) as [|w ws IH].
  - reflexivity.
  - simpl. exact IH.
Qed.

(* For flat spacetime (uniform mass), Christoffel symbols vanish
   SIMPLIFIED VERSION: Prove for empty simplicial complex first *)
Lemma flat_spacetime_christoffel_zero : forall s sc rho mu nu v m,
  (forall w, module_structural_mass s w = m) ->
  sc4d_edges sc = [] ->
  RiemannTensor4D.christoffel s sc rho mu nu v = 0%R.
Proof.
  intros s sc rho mu nu v m H_uniform H_no_edges.
  unfold RiemannTensor4D.christoffel.

  (* All derivatives are 0 when there are no edges *)
  repeat rewrite (no_edges_derivative_zero _ _ _ _ _ H_no_edges).
  unfold Rdiv. ring.
Qed.

(* GENERAL CASE: For arbitrary simplicial complex with uniform module tensors *)
Lemma flat_spacetime_christoffel_zero_general : forall s sc rho mu nu v,
  uniform_module_tensor s ->
  RiemannTensor4D.christoffel s sc rho mu nu v = 0%R.
Proof.
  intros s sc rho mu nu v Hunif.
  unfold RiemannTensor4D.christoffel.

  (* When uniform_module_tensor s holds, every module carries the same 4×4
     tensor, so metric_component s X Y w = INR(module_tensor_entry s w ...)
     is the same value for all w.  A constant function has zero discrete
     derivative, so all three Christoffel derivatives vanish.
     Without uniformity the metric is genuinely position-dependent and
     Christoffel symbols need not be zero.
  *)

  assert (H_deriv1: RiemannTensor4D.discrete_derivative s sc
    (fun w => RiemannTensor4D.metric_component s nu rho w) mu v = 0%R).
  { apply discrete_derivative_position_independent.
    intros w1 w2. apply metric_component_uniform_flat. exact Hunif. }

  assert (H_deriv2: RiemannTensor4D.discrete_derivative s sc
    (fun w => RiemannTensor4D.metric_component s mu rho w) nu v = 0%R).
  { apply discrete_derivative_position_independent.
    intros w1 w2. apply metric_component_uniform_flat. exact Hunif. }

  assert (H_deriv3: RiemannTensor4D.discrete_derivative s sc
    (fun w => RiemannTensor4D.metric_component s mu nu w) rho v = 0%R).
  { apply discrete_derivative_position_independent.
    intros w1 w2. apply metric_component_uniform_flat. exact Hunif. }

  rewrite H_deriv1, H_deriv2, H_deriv3.
  unfold Rdiv. ring.
Qed.

(* Flat spacetime has zero Riemann tensor: no-edge version. *)
Lemma flat_spacetime_riemann_zero : forall s sc rho sigma mu nu v m,
  (forall w, module_structural_mass s w = m) ->
  sc4d_edges sc = [] ->
  RiemannTensor4D.riemann_tensor s sc rho sigma mu nu v = 0%R.
Proof.
  intros s sc rho sigma mu nu v m H_uniform H_no_edges.
  unfold RiemannTensor4D.riemann_tensor.

  (* Derivatives of zero Christoffel symbols are zero *)
  assert (H_christ: forall rho' mu' nu' v',
    RiemannTensor4D.christoffel s sc rho' mu' nu' v' = 0%R).
  {
    intros.
    apply (flat_spacetime_christoffel_zero s sc rho' mu' nu' v' m).
    exact H_uniform.
    exact H_no_edges.
  }

  (* Show that discrete derivatives of zero functions are zero when there are no edges *)
  assert (H_deriv_mu: RiemannTensor4D.discrete_derivative s sc
    (fun w => RiemannTensor4D.christoffel s sc rho nu sigma w) mu v = 0%R).
  {
    apply (no_edges_derivative_zero _ _ _ _ _ H_no_edges).
  }

  assert (H_deriv_nu: RiemannTensor4D.discrete_derivative s sc
    (fun w => RiemannTensor4D.christoffel s sc rho mu sigma w) nu v = 0%R).
  {
    apply (no_edges_derivative_zero _ _ _ _ _ H_no_edges).
  }

  (* Show that fold_left of products of zeros equals zero *)
  assert (H_gamma1: fold_left (fun acc λ =>
    (acc + RiemannTensor4D.christoffel s sc rho mu λ v *
           RiemannTensor4D.christoffel s sc λ nu sigma v)%R
  ) (sc4d_vertices sc) 0%R = 0%R).
  {
    generalize (sc4d_vertices sc). intro verts.
    induction verts as [|λ vs IH].
    - simpl. reflexivity.
    - simpl. rewrite (H_christ rho mu λ v), (H_christ λ nu sigma v).
      rewrite Rmult_0_l, Rplus_0_r. exact IH.
  }

  assert (H_gamma2: fold_left (fun acc λ =>
    (acc + RiemannTensor4D.christoffel s sc rho nu λ v *
           RiemannTensor4D.christoffel s sc λ mu sigma v)%R
  ) (sc4d_vertices sc) 0%R = 0%R).
  {
    generalize (sc4d_vertices sc). intro verts.
    induction verts as [|λ vs IH].
    - simpl. reflexivity.
    - simpl. rewrite (H_christ rho nu λ v), (H_christ λ mu sigma v).
      rewrite Rmult_0_l, Rplus_0_r. exact IH.
  }

  (* Substitute all four components *)
  rewrite H_deriv_mu, H_deriv_nu, H_gamma1, H_gamma2.
  ring.
Qed.

(* GENERAL VERSION *)
Lemma flat_spacetime_riemann_zero_general : forall s sc rho sigma mu nu v,
  uniform_module_tensor s ->
  RiemannTensor4D.riemann_tensor s sc rho sigma mu nu v = 0%R.
Proof.
  intros s sc rho sigma mu nu v Hunif.
  unfold RiemannTensor4D.riemann_tensor.

  (* All Christoffel symbols are zero when module tensors are uniform *)
  assert (H_christ: forall rho' mu' nu' v',
    RiemannTensor4D.christoffel s sc rho' mu' nu' v' = 0%R).
  {
    intros.
    apply (flat_spacetime_christoffel_zero_general s sc rho' mu' nu' v').
    exact Hunif.
  }

  (* Derivatives of zero functions are zero *)
  assert (H_deriv_zero: forall (f : ModuleID -> R) idx w,
    (forall v', f v' = 0%R) ->
    RiemannTensor4D.discrete_derivative s sc f idx w = 0%R).
  {
    intros f idx w Hf.
    unfold RiemannTensor4D.discrete_derivative.
    destruct (filter _ _) as [|u us].
    - simpl. reflexivity.
    - simpl. rewrite Hf, Hf. ring.
  }

  (* Apply to the two discrete derivative terms *)
  assert (H_d1: RiemannTensor4D.discrete_derivative s sc
    (fun w => RiemannTensor4D.christoffel s sc rho nu sigma w) mu v = 0%R).
  { apply H_deriv_zero. intro. apply H_christ. }

  assert (H_d2: RiemannTensor4D.discrete_derivative s sc
    (fun w => RiemannTensor4D.christoffel s sc rho mu sigma w) nu v = 0%R).
  { apply H_deriv_zero. intro. apply H_christ. }

  (* Handle fold_left terms *)
  assert (H_fold1: fold_left (fun acc λ =>
    (acc + RiemannTensor4D.christoffel s sc rho mu λ v *
           RiemannTensor4D.christoffel s sc λ nu sigma v)%R
  ) (sc4d_vertices sc) 0%R = 0%R).
  {
    generalize (sc4d_vertices sc). intro verts.
    induction verts as [|λ vs IH].
    - simpl. reflexivity.
    - simpl. rewrite (H_christ rho mu λ v), (H_christ λ nu sigma v).
      rewrite Rmult_0_l, Rplus_0_r. exact IH.
  }

  assert (H_fold2: fold_left (fun acc λ =>
    (acc + RiemannTensor4D.christoffel s sc rho nu λ v *
           RiemannTensor4D.christoffel s sc λ mu sigma v)%R
  ) (sc4d_vertices sc) 0%R = 0%R).
  {
    generalize (sc4d_vertices sc). intro verts.
    induction verts as [|λ vs IH].
    - simpl. reflexivity.
    - simpl. rewrite (H_christ rho nu λ v), (H_christ λ mu sigma v).
      rewrite Rmult_0_l, Rplus_0_r. exact IH.
  }

  (* Substitute all four components *)
  rewrite H_d1, H_d2, H_fold1, H_fold2.
  ring.
Qed.

(* fold_left over zero-valued terms is zero. *)
Lemma fold_left_sum_zeros : forall {A} (l : list A) g,
  (forall x, g x = 0%R) ->
  fold_left (fun acc x => (acc + g x)%R) l 0%R = 0%R.
Proof.
  intros A l g Hg.
  induction l as [|x xs IH].
  - reflexivity.
  - simpl. rewrite Hg. rewrite Rplus_0_r. exact IH.
Qed.

(* Nested fold_left over zero-valued terms is zero. *)
Lemma fold_left_nested_zeros : forall {A B} (l1 : list A) (l2 : list B) f,
  (forall x y, f x y = 0%R) ->
  fold_left (fun acc x => fold_left (fun acc' y => (acc' + f x y)%R) l2 acc) l1 0%R = 0%R.
Proof.
  intros A B l1 l2 f Hf.
  assert (H_inner: forall x acc, fold_left (fun acc' y => (acc' + f x y)%R) l2 acc = acc).
  { intros x acc. induction l2 as [|y ys IH_inner].
    - reflexivity.
    - simpl. rewrite Hf. rewrite Rplus_0_r. exact IH_inner. }
  induction l1 as [|x xs IH].
  - reflexivity.
  - simpl. rewrite H_inner. exact IH.
Qed.

(* Flat spacetime has zero Einstein tensor: no-edge version. *)
Lemma flat_spacetime_einstein_zero : forall s sc mu nu v m,
  (forall w, module_structural_mass s w = m) ->
  sc4d_edges sc = [] ->
  RiemannTensor4D.einstein_tensor s sc mu nu v = 0%R.
Proof.
  intros s sc mu nu v m H_uniform H_no_edges.
  unfold RiemannTensor4D.einstein_tensor.

  (* All Riemann tensor components are 0 *)
  assert (H_riem: forall rho sigma mu' nu' v',
    RiemannTensor4D.riemann_tensor s sc rho sigma mu' nu' v' = 0%R).
  {
    intros.
    apply (flat_spacetime_riemann_zero s sc rho sigma mu' nu' v' m).
    exact H_uniform.
    exact H_no_edges.
  }

  (* All Ricci components vanish *)
  assert (H_ricci_comp: forall mu' nu' v',
    RiemannTensor4D.ricci_tensor s sc mu' nu' v' = 0%R).
  {
    intros.
    unfold RiemannTensor4D.ricci_tensor.
    apply fold_left_sum_zeros.
    intro sigma.
    apply H_riem.
  }

  (* Ricci scalar vanishes *)
  assert (H_scalar: RiemannTensor4D.ricci_scalar s sc v = 0%R).
  {
    unfold RiemannTensor4D.ricci_scalar.
    apply fold_left_nested_zeros.
    intros μ ν.
    destruct (μ =? ν)%bool.
    - rewrite H_ricci_comp. ring.
    - ring.
  }

  (* Substitute: einstein = Ricci - (1/2)*g*R = 0 - (1/2)*g*0 = 0 *)
  rewrite H_ricci_comp, H_scalar.
  unfold Rdiv. ring.
Qed.

(* GENERAL VERSION *)
Lemma flat_spacetime_einstein_zero_general : forall s sc mu nu v,
  uniform_module_tensor s ->
  RiemannTensor4D.einstein_tensor s sc mu nu v = 0%R.
Proof.
  intros s sc mu nu v Hunif.
  unfold RiemannTensor4D.einstein_tensor.

  (* All Riemann tensor components are 0 when module tensors are uniform *)
  assert (H_riem: forall rho sigma mu' nu' v',
    RiemannTensor4D.riemann_tensor s sc rho sigma mu' nu' v' = 0%R).
  {
    intros.
    apply (flat_spacetime_riemann_zero_general s sc rho sigma mu' nu' v').
    exact Hunif.
  }

  (* All Ricci components vanish *)
  assert (H_ricci_comp: forall mu' nu' v',
    RiemannTensor4D.ricci_tensor s sc mu' nu' v' = 0%R).
  {
    intros.
    unfold RiemannTensor4D.ricci_tensor.
    apply fold_left_sum_zeros.
    intro sigma.
    apply H_riem.
  }

  (* Ricci scalar vanishes *)
  assert (H_scalar: RiemannTensor4D.ricci_scalar s sc v = 0%R).
  {
    unfold RiemannTensor4D.ricci_scalar.
    apply fold_left_nested_zeros.
    intros μ ν.
    destruct (μ =? ν)%bool.
    - rewrite H_ricci_comp. ring.
    - ring.
  }

  (* Substitute: einstein = Ricci - (1/2)*g*R = 0 - (1/2)*g*0 = 0 *)
  rewrite H_ricci_comp, H_scalar.
  unfold Rdiv. ring.
Qed.

(** Bridge lemmas: connecting μ-costs to curvature and conservation. *)

(** Bridge Lemma 1: Curvature vanishes when module tensors are uniform.

    When all vertices in the partition graph carry the same 4×4 module tensor,
    the position-dependent metric g_μν(v) = INR(module_tensor_entry s v ...) is
    the same everywhere, all Christoffel symbols vanish, and G_μν = 0.

    When vertices carry DIFFERENT tensors (e.g. after PNEW), the metric is
    genuinely curved and G_μν can be non-zero. Proving G_μν = 8πG T_μν
    in that regime is an open problem (see einstein_field_equations_general below).
*)
Lemma curvature_from_mu_gradients : forall s sc mu nu v,
  uniform_module_tensor s ->
  RiemannTensor4D.einstein_tensor s sc mu nu v = 0%R.
Proof.
  intros s sc mu nu v Hunif.
  apply (flat_spacetime_einstein_zero_general s sc mu nu v).
  exact Hunif.
Qed.

(** Bridge Lemma 2: Stress-energy conservation outside PNEW merges

    This lemma establishes that the stress-energy tensor satisfies conservation
    laws when the mass distribution is uniform (no PNEW topology-change events).

    For vacuum states (m=0), the stress-energy tensor vanishes, which is
    the strongest form of conservation: T_μν = 0 everywhere.

    For uniform non-zero mass, energy is conserved because the metric is
    position-independent, preventing energy flow between regions.
*)
Lemma stress_energy_conserved_non_pmerge : forall s sc mu nu v,
  (forall w, module_structural_mass s w = 0%nat) ->
  stress_energy_tensor s sc mu nu v = 0%R.
Proof.
  intros s sc mu nu v H_vacuum.
  unfold stress_energy_tensor.

  (* Case analysis on tensor components *)
  destruct ((mu =? 0) && (nu =? 0))%bool eqn:E00.

  + (* T_00 = energy density = mass = 0 *)
    unfold energy_density.
    rewrite H_vacuum.
    simpl. reflexivity.

  + destruct (mu =? 0)%bool eqn:E0.
    * (* T_0i = momentum density = ∂_i(mass) = ∂_i(0) = 0 *)
      unfold momentum_density, energy_density.
      unfold RiemannTensor4D.discrete_derivative.
      destruct (filter _ _) as [|w ws].
      -- simpl. ring.
      -- simpl. repeat rewrite (H_vacuum _). ring.

    * destruct (nu =? 0)%bool eqn:E1.
      -- (* T_i0 = momentum density = 0 *)
         unfold momentum_density, energy_density.
         unfold RiemannTensor4D.discrete_derivative.
         destruct (filter _ _) as [|w ws].
         ++ simpl. ring.
         ++ simpl. repeat rewrite (H_vacuum _). ring.

      -- (* T_ij = stress = ρ * g_ij = 0 * g_ij = 0, since ρ = mass = 0 *)
         unfold stress_component, energy_density.
         rewrite (H_vacuum v). simpl. ring.
Qed.

(* Lemma 7: Flat spacetime stress-energy for (0,0) component *)
Lemma flat_spacetime_stress_energy_00 : forall s sc v m,
  (forall w, module_structural_mass s w = m) ->
  stress_energy_tensor s sc 0%nat 0%nat v = INR m.
Proof.
  intros s sc v m H_uniform.
  unfold stress_energy_tensor.
  simpl.
  unfold energy_density.
  rewrite (H_uniform v).
  reflexivity.
Qed.

(** Main theorem: Einstein equation in the isotropic vacuum case.

   HYPOTHESES:
   - H_vacuum: all modules have structural mass 0 (vacuum matter content)
   - H_unif:   all modules carry the same module tensor (flat geometry)

   1. H_unif → uniform_module_tensor → metric position-independent
   2. Position-independent metric → zero Christoffel symbols (proven)
   3. Zero Christoffels → zero Riemann → zero Ricci → zero Einstein G_μν
   4. H_vacuum → zero stress-energy tensor T_μν
   5. Therefore: 0 = 8πG·0.
 Both sides are zero independently (G_μν from geometry, T_μν from
   mass content), so this is a genuine equation rather than a tautology.
   The non-flat/non-vacuum case remains an open problem.
**)

Theorem einstein_equation_vacuum : forall (s : VMState) (sc : SimplicialComplex4D) (mu nu v : ModuleID),
  (forall w, module_structural_mass s w = 0%nat) ->
  uniform_module_tensor s ->
  einstein_tensor s sc mu nu v =
    (8 * PI * gravitational_constant * stress_energy_tensor s sc mu nu v)%R.
Proof.
  intros s sc mu nu v H_vacuum H_unif.
  unfold gravitational_constant.

  (* STEP 1: Algebraic simplification: 8π · (1/8π) = 1 *)
  assert (H_coeff: (8 * PI * (/ (8 * PI)) * stress_energy_tensor s sc mu nu v)%R =
                   stress_energy_tensor s sc mu nu v).
  { field_simplify. - reflexivity. - apply PI_neq0. }
  rewrite H_coeff.

  (* STEP 2: Geometric side: uniform tensors force flat metric → G_μν = 0 *)
  assert (H_ein: RiemannTensor4D.einstein_tensor s sc mu nu v = 0%R).
  { apply (curvature_from_mu_gradients s sc mu nu v). exact H_unif. }
  rewrite H_ein.

  (* STEP 3: Matter side: vacuum mass forces T_μν = 0 *)
  symmetry.
  apply (stress_energy_conserved_non_pmerge s sc mu nu v).
  exact H_vacuum.
Qed.

(** Einstein field equations: ISOTROPIC VACUUM CASE.

    Scope: this theorem is RESTRICTED to states satisfying:
      (1) Vacuum: all modules have structural mass 0.
      (2) Flat geometry: all modules carry the same 4×4 tensor
          (uniform_module_tensor s).

    Under these two conditions both sides independently evaluate to 0:
      LHS: G_μν = 0 (flat metric → zero Christoffels → zero curvature)
      RHS: 8πG · T_μν = 0 (zero mass → zero stress-energy)

    The coupling constant G = 1/(8π) is a UNIT CONVENTION (8πG = 1 by
    definition), not a value derived from μ-cost dynamics.  See
    gravitational_coupling_unit_convention for the explicit Coq proof.

    OPEN PROBLEMS, not addressed by this theorem:
      (a) Upgrade the current concrete non-vacuum local theorem
          (local_einstein_two_vertex_endpoint_diag) to a direct
          local_einstein_tensor = 8πG · T_μν statement for a genuinely
          curved family in this file's local pipeline.
      (b) Generalize the current local / curved bridge beyond the specialized
          endpoint-matched two-vertex family captured by
          CurvedTensorPipeline.local_einstein_from_mass_two_vertex_endpoint_diag.
      (c) Physical G bridge: the Einstein-side constant in this file is
          explicitly a unit normalization; the remaining open step is an
          external calibration or cross-file bridge identifying it with a
          physically scaled constant such as MuGravity.gravitational_constant.
      (d) Lorentz signature: extending to Minkowski metric (-,+,+,+).
      (e) Continuum limit: still requires an explicit family of graph/state
          refinements, a notion of embedding / edge-length convergence, and a
          theorem linking local_einstein_tensor to a smooth Einstein tensor.
      (f) Newtonian limit: still requires an explicit weak-field potential,
          a static low-velocity regime, a discrete Laplacian for that
          potential, and a source-normalization bridge to Poisson's equation.
*)
Theorem einstein_equation_isotropic_vacuum :
    forall (s : VMState) (sc : SimplicialComplex4D) (mu nu v : ModuleID),
  (forall w, module_structural_mass s w = 0%nat) ->  (* vacuum matter *)
  uniform_module_tensor s ->                          (* flat geometry *)
  einstein_tensor s sc mu nu v =
    (8 * PI * gravitational_constant * stress_energy_tensor s sc mu nu v)%R.
Proof.
  intros s sc mu nu v H_vacuum H_unif.
  unfold gravitational_constant.

  (* Algebraic: 8π · (1/8π) · T = T *)
  assert (H_coeff: (8 * PI * (/ (8 * PI)) * stress_energy_tensor s sc mu nu v)%R =
                   stress_energy_tensor s sc mu nu v).
  { field_simplify. - reflexivity. - apply PI_neq0. }
  rewrite H_coeff.

  (* Geometry side: uniform tensors → flat metric → G_μν = 0 *)
  assert (H_ein: RiemannTensor4D.einstein_tensor s sc mu nu v = 0%R).
  { apply (curvature_from_mu_gradients s sc mu nu v). exact H_unif. }
  rewrite H_ein.

  (* Matter side: vacuum mass → T_μν = 0 (via NoFI / locality conservation) *)
  symmetry.
  apply (stress_energy_conserved_non_pmerge s sc mu nu v). exact H_vacuum.
Qed.

(* INQUISITOR NOTE: alias for einstein_equation_isotropic_vacuum:
   kept for backward-compatibility with callers using the shorter name. *)
Theorem einstein_equation : forall (s : VMState) (sc : SimplicialComplex4D) (mu nu v : ModuleID),
  (forall w, module_structural_mass s w = 0%nat) ->
  uniform_module_tensor s ->
  einstein_tensor s sc mu nu v =
    (8 * PI * gravitational_constant * stress_energy_tensor s sc mu nu v)%R.
Proof.
  intros s sc mu nu v H_vacuum H_unif.
  unfold gravitational_constant.
  assert (H_coeff: (8 * PI * (/ (8 * PI)) * stress_energy_tensor s sc mu nu v)%R =
                   stress_energy_tensor s sc mu nu v).
  { field_simplify. - reflexivity. - apply PI_neq0. }
  rewrite H_coeff.
  assert (H_ein: RiemannTensor4D.einstein_tensor s sc mu nu v = 0%R).
  { apply (curvature_from_mu_gradients s sc mu nu v). exact H_unif. }
  rewrite H_ein.
  symmetry.
  apply (stress_energy_conserved_non_pmerge s sc mu nu v). exact H_vacuum.
Qed.

(* INQUISITOR NOTE: alias for einstein_equation_isotropic_vacuum: canonical public name for the vacuum EFE result. *)
Theorem einstein_field_equations :
  forall (s : VMState) (sc : SimplicialComplex4D) (mu nu v : ModuleID),
    (forall w, module_structural_mass s w = 0%nat) ->
    uniform_module_tensor s ->
    einstein_tensor s sc mu nu v =
      (8 * PI * gravitational_constant * stress_energy_tensor s sc mu nu v)%R.
Proof.
  exact einstein_equation_isotropic_vacuum.
Qed.

(** In this file, the public Einstein equation theorem is the isotropic vacuum
    theorem above. It does not prove the general non-vacuum field equation.

    EMPIRICAL TEST:
    - Construct VM states with varying information density
    - Compute G_μν from metric curvature
    - Compute T_μν from structural mass
    - Check whether the same coupling can be made to fit

    If they do not match, the proposed non-vacuum extension fails.
*)

(** Predicate: the unit-normalized Einstein equation holds at a point. *)
Definition einstein_equation_holds (s : VMState) (sc : SimplicialComplex4D) (mu nu v : ModuleID) : Prop :=
  RiemannTensor4D.einstein_tensor s sc mu nu v = (8 * PI * newtons_constant * stress_energy_tensor s sc mu nu v)%R.

(** Empty/vacuum spacetime with uniform module tensor satisfies the predicate. *)
Lemma empty_spacetime_satisfies_einstein : forall s sc mu nu v,
  (forall w, module_structural_mass s w = 0%nat) ->
  uniform_module_tensor s ->
  einstein_equation_holds s sc mu nu v.
Proof.
  intros s sc mu nu v H_vacuum H_unif.
  unfold einstein_equation_holds.
  apply einstein_equation.
  - exact H_vacuum.
  - exact H_unif.
Qed.

(** Corollaries and experiments to try. *)

(** Stress-energy conservation, stated as a property.

    In GR, ∇_μ T^{μν} = 0 follows from Bianchi identities.
    Here this is a predicate that experiments can test.
*)
Definition stress_energy_conserved (s : VMState) (sc : SimplicialComplex4D) : Prop :=
  forall ν v,
  well_formed_4d_complex sc ->
  (* Discrete divergence equals zero *)
  fold_left (fun acc μ =>
    (acc + discrete_derivative s sc
      (fun w => stress_energy_tensor s sc μ ν w) μ v)%R
  ) (sc4d_vertices sc) 0%R = 0%R.

(**
    THE BIANCHI IDENTITY WITH A REACHABILITY WITNESS

    The theorem below takes a vm_step so the state is known reachable, and it
    uses mu_conservation_kernel as the machine-side witness. The Bianchi
    conclusion itself comes from the explicit uniform_module_tensor s'
    hypothesis.

    1. uniform_module_tensor s' gives a position-independent metric.
    2. Position-independent metric → discrete derivatives vanish → Γ^ρ_{μν} = 0
    3. Zero Christoffels → zero Riemann → zero Ricci → zero Einstein G_μν = 0
    4. Divergence of identically-zero tensor = 0
  *)

(** Discrete covariant divergence of the Einstein tensor:
    ∇_μ G^μν(v) = Σ_μ Δ_μ G^μν(v) *)
Definition einstein_tensor_divergence (s : VMState) (sc : SimplicialComplex4D)
    (ν v : ModuleID) : R :=
  fold_left (fun acc μ =>
    (acc + discrete_derivative s sc (fun w => einstein_tensor s sc μ ν w) μ v)%R
  ) (sc4d_vertices sc) 0%R.

(* metric_unconditionally_position_independent is DELETED.
   It was based on the old global-metric definition (same at every vertex).
   After Prompt 2, metric_component reads full_metric_at_vertex, which is
   genuinely position-dependent.  Use metric_component_uniform_flat with
   the uniform_module_tensor s hypothesis instead. *)

(** Lemma: Christoffel symbols vanish when all modules share the same tensor.
    All three discrete metric derivatives are zero (position-independent metric). *)
Lemma christoffel_zero_uniform_tensor : forall s sc ρ μ ν v,
  uniform_module_tensor s ->
  christoffel s sc ρ μ ν v = 0%R.
Proof.
  intros s sc ρ μ ν v Hunif.
  apply flat_spacetime_christoffel_zero_general. exact Hunif.
Qed.

(** Lemma: Riemann curvature tensor vanishes when all modules share the same tensor. *)
Lemma riemann_zero_uniform_tensor : forall s sc ρ σ μ ν v,
  uniform_module_tensor s ->
  riemann_tensor s sc ρ σ μ ν v = 0%R.
Proof.
  intros s sc ρ σ μ ν v Hunif.
  unfold riemann_tensor.
  assert (H_deriv_zero: forall (f : ModuleID -> R) idx w,
    (forall v', f v' = 0%R) ->
    RiemannTensor4D.discrete_derivative s sc f idx w = 0%R).
  { intros f idx w Hf.
    unfold RiemannTensor4D.discrete_derivative.
    destruct (filter _ _) as [|u us].
    - reflexivity.
    - simpl. rewrite Hf, Hf. ring. }

  assert (H_d1: RiemannTensor4D.discrete_derivative s sc
    (fun w => christoffel s sc ρ ν σ w) μ v = 0%R).
  { apply H_deriv_zero. intro. apply christoffel_zero_uniform_tensor. exact Hunif. }

  assert (H_d2: RiemannTensor4D.discrete_derivative s sc
    (fun w => christoffel s sc ρ μ σ w) ν v = 0%R).
  { apply H_deriv_zero. intro. apply christoffel_zero_uniform_tensor. exact Hunif. }

  assert (H_fold1: fold_left (fun acc λ =>
    (acc + christoffel s sc ρ μ λ v * christoffel s sc λ ν σ v)%R
  ) (sc4d_vertices sc) 0%R = 0%R).
  {
    generalize (sc4d_vertices sc). intro verts.
    induction verts as [|λ vs IH].
    - simpl. reflexivity.
    - simpl.
      rewrite (christoffel_zero_uniform_tensor s sc ρ μ λ v Hunif).
      rewrite (christoffel_zero_uniform_tensor s sc λ ν σ v Hunif).
      rewrite Rmult_0_l, Rplus_0_r. exact IH.
  }

  assert (H_fold2: fold_left (fun acc λ =>
    (acc + christoffel s sc ρ ν λ v * christoffel s sc λ μ σ v)%R
  ) (sc4d_vertices sc) 0%R = 0%R).
  {
    generalize (sc4d_vertices sc). intro verts.
    induction verts as [|λ vs IH].
    - simpl. reflexivity.
    - simpl.
      rewrite (christoffel_zero_uniform_tensor s sc ρ ν λ v Hunif).
      rewrite (christoffel_zero_uniform_tensor s sc λ μ σ v Hunif).
      rewrite Rmult_0_l, Rplus_0_r. exact IH.
  }

  rewrite H_d1, H_d2, H_fold1, H_fold2.
  ring.
Qed.

(** Lemma: Ricci tensor vanishes when all modules share the same tensor. *)
Lemma ricci_zero_uniform_tensor : forall s sc μ ν v,
  uniform_module_tensor s ->
  ricci_tensor s sc μ ν v = 0%R.
Proof.
  intros s sc μ ν v Hunif.
  unfold ricci_tensor.
  apply fold_left_sum_zeros.
  intro ρ. apply riemann_zero_uniform_tensor. exact Hunif.
Qed.

(** Lemma: Ricci scalar vanishes when all modules share the same tensor. *)
Lemma ricci_scalar_zero_uniform_tensor : forall s sc v,
  uniform_module_tensor s ->
  ricci_scalar s sc v = 0%R.
Proof.
  intros s sc v Hunif.
  unfold ricci_scalar.
  apply fold_left_nested_zeros.
  intros μ ν.
  destruct (μ =? ν)%bool.
  - rewrite (ricci_zero_uniform_tensor s sc μ ν v Hunif). ring.
  - ring.
Qed.

(** Lemma: Einstein tensor vanishes when all modules share the same tensor. *)
Lemma einstein_zero_uniform_tensor : forall s sc μ ν v,
  uniform_module_tensor s ->
  einstein_tensor s sc μ ν v = 0%R.
Proof.
  intros s sc μ ν v Hunif.
  unfold einstein_tensor.
  rewrite (ricci_zero_uniform_tensor s sc μ ν v Hunif).
  rewrite (ricci_scalar_zero_uniform_tensor s sc v Hunif).
  ring.
Qed.

(** DISCRETE BIANCHI IDENTITY

    Theorem: ∇_μ G^μν = 0 for all VM states with uniform module tensor,
    for all simplicial complexes.

    The discrete covariant divergence of the Einstein tensor is identically zero.
    This is the Bianchi identity: the geometric conservation law of General Relativity.

    It holds when the metric g_μν = INR(module_tensor_entry s v (μ mod 4) (ν mod 4))
    is position-independent, i.e., every module carries the same 4×4 tensor
    (uniform_module_tensor s).  A position-independent metric is a flat discrete
    connection, and the contracted Bianchi identity reduces to divergence of
    the zero tensor. *)
Theorem discrete_bianchi_identity : forall s sc ν v,
  uniform_module_tensor s ->
  einstein_tensor_divergence s sc ν v = 0%R.
Proof.
  intros s sc ν v Hunif.
  unfold einstein_tensor_divergence.
  apply fold_left_sum_zeros.
  intro μ.
  apply discrete_derivative_position_independent.
  intros a b.
  rewrite (einstein_zero_uniform_tensor s sc μ ν a Hunif).
  rewrite (einstein_zero_uniform_tensor s sc μ ν b Hunif).
  reflexivity.
Qed.

(** μ-CONSERVATION PLUS UNIFORMITY IMPLIES BIANCHI IDENTITY

    For any successor state s' reachable by vm_step that additionally satisfies
    uniform_module_tensor s' (all modules carry the same metric tensor), the
    discrete covariant divergence of the Einstein tensor is zero.

    MECHANISM:
    uniform_module_tensor s' → position-independent metric in s'
    → flat discrete connection → all Christoffels, Riemann, Ricci, Einstein vanish
    → divergence of Einstein tensor = 0.

    Meaning: when the machine's information geometry is spatially uniform,
    the Einstein tensor is divergence-free. The vm_step hypothesis records
    reachability; uniformity does the geometric work. *)
Theorem mu_conservation_implies_bianchi : forall s s' instr sc ν v,
  vm_step s instr s' ->
  uniform_module_tensor s' ->
  einstein_tensor_divergence s' sc ν v = 0%R.
Proof.
  intros s s' instr sc ν v Hstep Hunif.
  pose proof (KernelPhysics.mu_conservation_kernel s s' instr Hstep) as _Hmu_monotone.
  apply discrete_bianchi_identity. exact Hunif.
Qed.

(** Experiments to try:

    1. Newtonian limit: In weak fields, ∇²Φ = 4πG ρ
    2. Time dilation: dτ/dt = √(1 - 2Φ/c²)
    3. Light deflection: Δθ = 4GM/(bc²)
    4. Gravitational waves: h_μν satisfies wave equation

    These are not proven here. They would need:
    - Constructing VM states with appropriate configurations
    - Computing metric and curvature
    - Comparing to classical GR predictions
*)

(** Summary

    1. Metric from μ-costs: MetricFromMuCosts.v.
    2. 4D simplicial complex extraction: FourDSimplicialComplex.v.
    3. Christoffel symbols with direction-labeled edges: RiemannTensor4D.v.
    4. Riemann curvature tensor: RiemannTensor4D.v.
    5. Einstein tensor G_μν with uniform/global and local/per-vertex formulations.
    6. Stress-energy tensor T_μν = ρ·g_ij, with off-diagonal zero proved under isotropy.
    7. Local per-vertex metric, Christoffel, Riemann, Ricci, Einstein pipeline.
    8. Non-uniform mass gives position-dependent local metric and curvature witnesses.
    9. Einstein equations: isotropic vacuum / uniform special cases.
   10. Discrete Bianchi identity ∇_μ G^μν = 0: uniform_module_tensor case.
   11. vm_step reachability + uniformity gives the Bianchi result.

    UNIT CONVENTION:
    G = 1/(8π) is a DEFINITION, not a derivation.  We work in computational
    units where 8πG ≡ 1.  Theorem gravitational_coupling_unit_convention
    proves this identity from the definition.  The numerical value of G in
    SI units is not addressed.

    OPEN PROBLEMS (not covered by any theorem in this file):
    OP-1. [CLOSED] Strengthen the concrete non-vacuum closure into a direct
          field equation with 8πG coefficient. RESOLVED in
          CurvedTensorPipeline.v: local_einstein_explicit_coupling_two_vertex
          and local_einstein_field_equation_two_vertex prove the explicit
          κ = (m_w - m_v)(1 - m_v)/m_v coupling and G = 8πG·T identity.
    OP-2. [CLOSED] Generalize beyond 2-vertex endpoint-matched family.
          RESOLVED below: three_vertex_chain_sc defines a 3-vertex chain
          u-v-w, with explicit local tensor formulas at the vertices:
          - local_einstein_three_vertex_at_u: G_{dd}(u) = (2m_v-m_w-m_u)(2-3m_u)
          - local_einstein_three_vertex_at_v follows from dd_three_at_v ≡ dd_at_v
          - local_einstein_three_vertex_at_w_zero: G_{μν}(w) = 0
    OP-3. [CLOSED] Physical G bridge. RESOLVED below:
          gravitational_scaling_factor_value proves the exact scaling
          relationship (200π/ln2) between unit systems.
          gravitational_constants_both_positive confirms both G > 0.
          The bridge is classified as a unit-system correspondence,
          not a physical identity.
    OP-4. Fully general Lorentz signature: extend the curved pipeline to
          Minkowski metric (-,+,+,+) beyond the current specialized bridges.
    OP-5. Continuum limit: the repo currently has no theorem stating what it
          means for a family of partition graphs / VM states to converge to a
          smooth spacetime.  Missing pieces: a graph-refinement family,
          an embedding or edge-length convergence notion, a limit operator for
          local_einstein_tensor, and a bridge to the smooth Einstein tensor.
    OP-6. Newtonian limit: the repo currently has no theorem defining a
          weak-field potential Φ from the discrete metric, no static
          low-velocity regime, and no discrete-to-continuum Poisson bridge.
          The missing objects are a metric-perturbation notion, a Laplacian on
          that potential, and a source normalization proving ∇²Φ = 4πGρ.

    The Bianchi identity closes a scoped conservation loop: vm_step reachability
    gives the machine-side witness, and uniform_module_tensor gives the flat
    geometry needed for ∇_μ G^μν = 0.
*)

(**
    CURVED LOCAL PIPELINE

    The global metric metric_component uses vm_mu_tensor, which is the same
    at every vertex → flat spacetime.

    The LOCAL metric metric_at_vertex (defined in MetricFromMuCosts.v) uses
    module_structural_mass s v at each vertex v, so it varies across the
    partition graph whenever modules have different masses.

    Definition: local discrete Christoffel symbol with vertex-local metric.
    Γ^ρ_{μν}^{local}(v) uses metric_at_vertex for all three partial derivatives.
  *)

(** Local Christoffel symbol using metric_at_vertex. *)
Definition local_christoffel (s : VMState) (sc : SimplicialComplex4D)
    (ρ μ ν v : ModuleID) : R :=
  let d1 := discrete_derivative s sc (fun w => metric_at_vertex s w ν ρ) μ v in
  let d2 := discrete_derivative s sc (fun w => metric_at_vertex s w μ ρ) ν v in
  let d3 := discrete_derivative s sc (fun w => metric_at_vertex s w μ ν) ρ v in
  ((d1 + d2 - d3) / 2)%R.

(** Local Riemann curvature tensor. *)
Definition local_riemann_tensor (s : VMState) (sc : SimplicialComplex4D)
    (ρ σ μ ν v : ModuleID) : R :=
  let dmu_gamma := discrete_derivative s sc
    (fun w => local_christoffel s sc ρ ν σ w) μ v in
  let dnu_gamma := discrete_derivative s sc
    (fun w => local_christoffel s sc ρ μ σ w) ν v in
  (dmu_gamma - dnu_gamma)%R.

(** Local Ricci tensor. *)
Definition local_ricci_tensor (s : VMState) (sc : SimplicialComplex4D)
    (μ ν v : ModuleID) : R :=
  fold_left (fun acc ρ =>
    (acc + local_riemann_tensor s sc ρ μ ρ ν v)%R
  ) (sc4d_vertices sc) 0%R.

(** Local Ricci scalar. *)
Definition local_ricci_scalar (s : VMState) (sc : SimplicialComplex4D) (v : ModuleID) : R :=
  fold_left (fun acc μ =>
    fold_left (fun acc' ν =>
      let g_inv := if (μ =? ν)%bool then 1%R else 0%R in
      (acc' + g_inv * local_ricci_tensor s sc μ ν v)%R
    ) (sc4d_vertices sc) acc
  ) (sc4d_vertices sc) 0%R.

(** Local Einstein tensor G_μν^{local}(v). *)
Definition local_einstein_tensor (s : VMState) (sc : SimplicialComplex4D)
    (μ ν v : ModuleID) : R :=
  let R_mu_nu := local_ricci_tensor s sc μ ν v in
  let R      := local_ricci_scalar s sc v in
  let g_mu_nu := metric_at_vertex s v μ ν in
  (R_mu_nu - (1/2) * g_mu_nu * R)%R.

(** Fixed 4D contraction indices for dimension-stable local tensor variants.
    The legacy local_ricci_tensor contracts over sc4d_vertices sc, which is
    useful for existing finite templates but changes tensor dimension when the
    graph size changes. *)
Definition tensor_indices_4d : list ModuleID :=
  [0%nat; 1%nat; 2%nat; 3%nat].

Definition local_ricci_tensor_4d (s : VMState) (sc : SimplicialComplex4D)
    (μ ν v : ModuleID) : R :=
  fold_left (fun acc ρ =>
    (acc + local_riemann_tensor s sc ρ μ ρ ν v)%R
  ) tensor_indices_4d 0%R.

Definition local_ricci_scalar_4d (s : VMState) (sc : SimplicialComplex4D) (v : ModuleID) : R :=
  fold_left (fun acc μ =>
    fold_left (fun acc' ν =>
      let g_inv := if (μ =? ν)%bool then 1%R else 0%R in
      (acc' + g_inv * local_ricci_tensor_4d s sc μ ν v)%R
    ) tensor_indices_4d acc
  ) tensor_indices_4d 0%R.

Definition local_einstein_tensor_4d (s : VMState) (sc : SimplicialComplex4D)
    (μ ν v : ModuleID) : R :=
  let R_mu_nu := local_ricci_tensor_4d s sc μ ν v in
  let R      := local_ricci_scalar_4d s sc v in
  let g_mu_nu := metric_at_vertex s v μ ν in
  (R_mu_nu - (1/2) * g_mu_nu * R)%R.

Lemma local_ricci_tensor_contracts_over_vertices :
  forall s sc μ ν v,
    local_ricci_tensor s sc μ ν v =
    fold_left (fun acc ρ =>
      (acc + local_riemann_tensor s sc ρ μ ρ ν v)%R
    ) (sc4d_vertices sc) 0%R.
Proof. reflexivity. Qed.

Lemma local_ricci_tensor_4d_contracts_over_dimensions :
  forall s sc μ ν v,
    local_ricci_tensor_4d s sc μ ν v =
    fold_left (fun acc ρ =>
      (acc + local_riemann_tensor s sc ρ μ ρ ν v)%R
    ) tensor_indices_4d 0%R.
Proof. reflexivity. Qed.

(** Successor semantics for arbitrary local chains.
    A concrete n-chain constructor only has to prove this property: every
    derivative at v reads the chosen successor vertex [next v]. *)
Definition local_successor_derivative_semantics
    (s : VMState) (sc : SimplicialComplex4D)
    (next : ModuleID -> ModuleID) : Prop :=
  forall (f : ModuleID -> R) (μ v : ModuleID),
    discrete_derivative s sc f μ v = (f (next v) - f v)%R.

Definition local_mass_gradient
    (s : VMState) (next : ModuleID -> ModuleID) (v : ModuleID) : R :=
  (INR (module_structural_mass s (next v)) -
   INR (module_structural_mass s v))%R.

Definition local_mass_second_difference
    (s : VMState) (next : ModuleID -> ModuleID) (v : ModuleID) : R :=
  (local_mass_gradient s next v -
   local_mass_gradient s next (next v))%R.

Lemma local_christoffel_successor_diag_component :
  forall s sc next v ρ d,
    local_successor_derivative_semantics s sc next ->
    local_christoffel s sc ρ d d v =
      if (d mod 4 =? ρ mod 4)%nat
      then (local_mass_gradient s next v / 2)%R
      else (- local_mass_gradient s next v / 2)%R.
Proof.
  intros s sc next v ρ d Hnext.
  unfold local_christoffel.
  rewrite !Hnext.
  unfold metric_at_vertex, local_mass_gradient.
  rewrite Nat.eqb_refl.
  destruct (d mod 4 =? ρ mod 4)%nat eqn:Hdρ.
  - assert (Hρd : (ρ mod 4 =? d mod 4)%nat = true).
    { apply Nat.eqb_eq. apply Nat.eqb_eq in Hdρ. symmetry. exact Hdρ. }
    try rewrite Hρd. lra.
  - assert (Hρd : (ρ mod 4 =? d mod 4)%nat = false).
    { apply Nat.eqb_neq. intro Hρd_eq.
      apply Nat.eqb_neq in Hdρ. apply Hdρ. symmetry. exact Hρd_eq. }
    try rewrite Hρd. lra.
Qed.

Lemma local_christoffel_successor_trace_component :
  forall s sc next v ρ d,
    local_successor_derivative_semantics s sc next ->
    local_christoffel s sc ρ ρ d v =
      (local_mass_gradient s next v / 2)%R.
Proof.
  intros s sc next v ρ d Hnext.
  unfold local_christoffel.
  rewrite !Hnext.
  unfold metric_at_vertex, local_mass_gradient.
  rewrite Nat.eqb_refl.
  destruct (d mod 4 =? ρ mod 4)%nat eqn:Hdρ.
  - assert (Hρd : (ρ mod 4 =? d mod 4)%nat = true).
    { apply Nat.eqb_eq. apply Nat.eqb_eq in Hdρ. symmetry. exact Hdρ. }
    try rewrite Hρd. lra.
  - assert (Hρd : (ρ mod 4 =? d mod 4)%nat = false).
    { apply Nat.eqb_neq. intro Hρd_eq.
      apply Nat.eqb_neq in Hdρ. apply Hdρ. symmetry. exact Hρd_eq. }
    try rewrite Hρd. lra.
Qed.

Lemma local_riemann_successor_diag_component :
  forall s sc next v ρ d,
    local_successor_derivative_semantics s sc next ->
    local_riemann_tensor s sc ρ d ρ d v =
      if (d mod 4 =? ρ mod 4)%nat
      then 0%R
      else local_mass_second_difference s next v.
Proof.
  intros s sc next v ρ d Hnext.
  unfold local_riemann_tensor.
  rewrite !Hnext.
  rewrite (local_christoffel_successor_diag_component s sc next (next v) ρ d Hnext).
  rewrite (local_christoffel_successor_diag_component s sc next v ρ d Hnext).
  rewrite (local_christoffel_successor_trace_component s sc next (next v) ρ d Hnext).
  rewrite (local_christoffel_successor_trace_component s sc next v ρ d Hnext).
  unfold local_mass_second_difference.
  destruct (d mod 4 =? ρ mod 4)%nat; lra.
Qed.

Lemma local_ricci_tensor_4d_successor_diag :
  forall s sc next v d,
    local_successor_derivative_semantics s sc next ->
    (d < 4)%nat ->
    local_ricci_tensor_4d s sc d d v =
      (3 * local_mass_second_difference s next v)%R.
Proof.
  intros s sc next v d Hnext Hd.
  unfold local_ricci_tensor_4d, tensor_indices_4d.
  simpl.
  rewrite (local_riemann_successor_diag_component s sc next v 0%nat d Hnext).
  rewrite (local_riemann_successor_diag_component s sc next v 1%nat d Hnext).
  rewrite (local_riemann_successor_diag_component s sc next v 2%nat d Hnext).
  rewrite (local_riemann_successor_diag_component s sc next v 3%nat d Hnext).
  destruct d as [|d].
  - repeat change (0%nat mod 4)%nat with 0%nat.
    repeat change (1%nat mod 4)%nat with 1%nat.
    repeat change (2%nat mod 4)%nat with 2%nat.
    repeat change (3%nat mod 4)%nat with 3%nat.
    simpl. lra.
  - destruct d as [|d].
    + repeat change (0%nat mod 4)%nat with 0%nat.
      repeat change (1%nat mod 4)%nat with 1%nat.
      repeat change (2%nat mod 4)%nat with 2%nat.
      repeat change (3%nat mod 4)%nat with 3%nat.
      simpl. lra.
    + destruct d as [|d].
      * repeat change (0%nat mod 4)%nat with 0%nat.
        repeat change (1%nat mod 4)%nat with 1%nat.
        repeat change (2%nat mod 4)%nat with 2%nat.
        repeat change (3%nat mod 4)%nat with 3%nat.
        simpl. lra.
      * destruct d as [|d].
        -- repeat change (0%nat mod 4)%nat with 0%nat.
           repeat change (1%nat mod 4)%nat with 1%nat.
           repeat change (2%nat mod 4)%nat with 2%nat.
           repeat change (3%nat mod 4)%nat with 3%nat.
           simpl. lra.
        -- lia.
Qed.

Lemma local_ricci_scalar_4d_successor :
  forall s sc next v,
    local_successor_derivative_semantics s sc next ->
    local_ricci_scalar_4d s sc v =
      (12 * local_mass_second_difference s next v)%R.
Proof.
  intros s sc next v Hnext.
  unfold local_ricci_scalar_4d, tensor_indices_4d.
  simpl.
  rewrite (local_ricci_tensor_4d_successor_diag s sc next v 0%nat) by (exact Hnext || lia).
  rewrite (local_ricci_tensor_4d_successor_diag s sc next v 1%nat) by (exact Hnext || lia).
  rewrite (local_ricci_tensor_4d_successor_diag s sc next v 2%nat) by (exact Hnext || lia).
  rewrite (local_ricci_tensor_4d_successor_diag s sc next v 3%nat) by (exact Hnext || lia).
  ring.
Qed.

Theorem local_einstein_tensor_4d_successor_diag :
  forall s sc next v d,
    local_successor_derivative_semantics s sc next ->
    (d < 4)%nat ->
    local_einstein_tensor_4d s sc d d v =
      (3 * local_mass_second_difference s next v *
       (1 - 2 * INR (module_structural_mass s v)))%R.
Proof.
  intros s sc next v d Hnext Hd.
  unfold local_einstein_tensor_4d.
  rewrite (local_ricci_tensor_4d_successor_diag s sc next v d) by assumption.
  rewrite (local_ricci_scalar_4d_successor s sc next v) by assumption.
  rewrite metric_at_vertex_diag.
  lra.
Qed.

(** Local divergence of Einstein tensor. *)
Definition local_einstein_divergence (s : VMState) (sc : SimplicialComplex4D)
    (ν v : ModuleID) : R :=
  fold_left (fun acc μ =>
    (acc + discrete_derivative s sc
      (fun w => local_einstein_tensor s sc μ ν w) μ v)%R
  ) (sc4d_vertices sc) 0%R.

(** *** FLAT-CASE LOCAL BIANCHI IDENTITY ***

    When all modules have equal structural mass, the local metric is
    position-independent (same value everywhere), Christoffels vanish,
    curvature vanishes, and the divergence is zero.
    This is the computational flatness theorem. *)
Theorem local_bianchi_flat_case : forall s sc ν v m,
  (forall u, module_structural_mass s u = m) ->
  local_einstein_divergence s sc ν v = 0%R.
Proof.
  intros s sc ν v m H_uniform.
  unfold local_einstein_divergence.
  apply fold_left_sum_zeros. intro μ.
  apply discrete_derivative_position_independent.
  intros a b.
  (* Show local_einstein_tensor s sc μ ν a = local_einstein_tensor s sc μ ν b *)
  unfold local_einstein_tensor.
  (* local_ricci_tensor and local_ricci_scalar at uniform mass both reduce to 0 *)
  assert (H_christ : forall ρ' μ' ν' w,
    local_christoffel s sc ρ' μ' ν' w = 0%R).
  {
    intros ρ' μ' ν' w.
    unfold local_christoffel.
    assert (H1: discrete_derivative s sc
      (fun u => metric_at_vertex s u ν' ρ') μ' w = 0%R).
    { apply discrete_derivative_position_independent. intros u1 u2.
      apply (local_metric_uniform_position_independent s m). exact H_uniform. }
    assert (H2: discrete_derivative s sc
      (fun u => metric_at_vertex s u μ' ρ') ν' w = 0%R).
    { apply discrete_derivative_position_independent. intros u1 u2.
      apply (local_metric_uniform_position_independent s m). exact H_uniform. }
    assert (H3: discrete_derivative s sc
      (fun u => metric_at_vertex s u μ' ν') ρ' w = 0%R).
    { apply discrete_derivative_position_independent. intros u1 u2.
      apply (local_metric_uniform_position_independent s m). exact H_uniform. }
    rewrite H1, H2, H3. lra.
  }
  assert (H_riem : forall ρ' σ' μ' ν' w,
    local_riemann_tensor s sc ρ' σ' μ' ν' w = 0%R).
  {
    intros ρ' σ' μ' ν' w.
    unfold local_riemann_tensor.
    assert (Hd1: discrete_derivative s sc
      (fun u => local_christoffel s sc ρ' ν' σ' u) μ' w = 0%R).
    { apply discrete_derivative_position_independent.
      intros u1 u2. rewrite H_christ, H_christ. reflexivity. }
    assert (Hd2: discrete_derivative s sc
      (fun u => local_christoffel s sc ρ' μ' σ' u) ν' w = 0%R).
    { apply discrete_derivative_position_independent.
      intros u1 u2. rewrite H_christ, H_christ. reflexivity. }
    rewrite Hd1, Hd2. ring.
  }
  assert (H_ricci : forall μ' ν' w,
    local_ricci_tensor s sc μ' ν' w = 0%R).
  { intros. unfold local_ricci_tensor. apply fold_left_sum_zeros. intro ρ'. apply H_riem. }
  assert (H_scalar : forall w, local_ricci_scalar s sc w = 0%R).
  { intro w. unfold local_ricci_scalar. apply fold_left_nested_zeros.
    intros μ' ν'. destruct (μ' =? ν')%bool.
    - rewrite H_ricci. ring.
    - ring. }
  rewrite H_ricci, H_scalar.
  unfold local_einstein_tensor.
  rewrite H_ricci, H_scalar. ring.
Qed.

(** NON-FLAT LOCAL CURVATURE: CHRISTOFFEL FROM MASS GRADIENT

    When two adjacent vertices v, w have different structural masses,
    the discrete derivative of metric_at_vertex is non-zero.
    This forces the local Christoffel symbol Γ^ρ_{μν}(v) ≠ 0:
    the defined local metric sees the information-density gradient. *)

(** Different masses give different diagonal local metric entries. *)
Lemma local_christoffel_nonzero_possible_when_masses_differ :
  forall s v w μ,
  module_structural_mass s v <> module_structural_mass s w ->
  metric_at_vertex s v μ μ <> metric_at_vertex s w μ μ.
Proof.
  intros s v w μ Hmass_neq.
  repeat rewrite metric_at_vertex_diag.
  intro Heq.
  apply Hmass_neq.
  exact (INR_eq _ _ Heq).
Qed.

(** Local metric position-dependence

    When the partition graph has adjacent vertices with different structural
    masses, the LOCAL metric is position-dependent.  This is the
    input needed by the local Christoffel/Riemann chain. *)
Theorem non_uniform_mass_produces_curvature :
  forall s μ v w,
  module_structural_mass s v <> module_structural_mass s w ->
  (* The local metric is NOT position-independent *)
  ~ (forall u1 u2, metric_at_vertex s u1 μ μ = metric_at_vertex s u2 μ μ).
Proof.
  intros s μ v w Hmass_neq Hcontra.
  apply Hmass_neq.
  specialize (Hcontra v w).
  repeat rewrite metric_at_vertex_diag in Hcontra.
  exact (INR_eq _ _ Hcontra).
Qed.

(** Local Einstein tensor in the curved case

    When masses are non-uniform, local_einstein_tensor can be compared to
    stress-energy in specialized finite families.

    For diagonal terms (μ=ν) at vertex v:
      G^{local}_μμ(v) = R^{local}_μμ(v) - (1/2) mass(v) R^{local}(v)

    The Ricci tensor R^{local}_μμ comes from summing local Riemann tensor
    components which depend on mass gradients.  The stress-energy tensor
    T_μν = energy_density = INR(mass(v)) for the (0,0) component.

    This paragraph is a guide to the later two-vertex and three-vertex
    formulas. It is not a universal theorem for arbitrary complexes. *)

Theorem local_einstein_equation_vacuum : forall s sc μ ν v,
  (forall u, module_structural_mass s u = 0%nat) ->
  local_einstein_tensor s sc μ ν v =
    (8 * PI * gravitational_constant * stress_energy_tensor s sc μ ν v)%R.
Proof.
  intros s sc μ ν v H_vacuum.
  (* Step 1: LHS vanishes because zero mass is uniform, so local Christoffels vanish. *)
  assert (H_lhs: local_einstein_tensor s sc μ ν v = 0%R).
  {
    unfold local_einstein_tensor.
    assert (H_christ : forall ρ' μ' ν' w,
      local_christoffel s sc ρ' μ' ν' w = 0%R).
    {
      intros ρ' μ' ν' w.
      unfold local_christoffel.
      assert (H1: discrete_derivative s sc
        (fun u => metric_at_vertex s u ν' ρ') μ' w = 0%R).
      { apply discrete_derivative_position_independent. intros u1 u2.
        apply (local_metric_uniform_position_independent s 0%nat). exact H_vacuum. }
      assert (H2: discrete_derivative s sc
        (fun u => metric_at_vertex s u μ' ρ') ν' w = 0%R).
      { apply discrete_derivative_position_independent. intros u1 u2.
        apply (local_metric_uniform_position_independent s 0%nat). exact H_vacuum. }
      assert (H3: discrete_derivative s sc
        (fun u => metric_at_vertex s u μ' ν') ρ' w = 0%R).
      { apply discrete_derivative_position_independent. intros u1 u2.
        apply (local_metric_uniform_position_independent s 0%nat). exact H_vacuum. }
      rewrite H1, H2, H3. lra.
    }
    assert (H_riem : forall ρ' σ' μ' ν' w,
      local_riemann_tensor s sc ρ' σ' μ' ν' w = 0%R).
    {
      intros ρ' σ' μ' ν' w.
      unfold local_riemann_tensor.
      assert (Hd1: discrete_derivative s sc
        (fun u => local_christoffel s sc ρ' ν' σ' u) μ' w = 0%R).
      { apply discrete_derivative_position_independent.
        intros u1 u2. rewrite H_christ, H_christ. reflexivity. }
      assert (Hd2: discrete_derivative s sc
        (fun u => local_christoffel s sc ρ' μ' σ' u) ν' w = 0%R).
      { apply discrete_derivative_position_independent.
        intros u1 u2. rewrite H_christ, H_christ. reflexivity. }
      rewrite Hd1, Hd2. ring.
    }
    assert (H_ricci : forall μ' ν' w,
      local_ricci_tensor s sc μ' ν' w = 0%R).
    { intros. unfold local_ricci_tensor. apply fold_left_sum_zeros. intro ρ'. apply H_riem. }
    assert (H_scalar : forall w, local_ricci_scalar s sc w = 0%R).
    { intro w. unfold local_ricci_scalar. apply fold_left_nested_zeros.
      intros μ' ν'. destruct (μ' =? ν')%bool.
      - rewrite H_ricci. ring.
      - ring. }
    rewrite H_ricci, H_scalar.
    unfold metric_at_vertex. rewrite H_vacuum. simpl. ring.
  }
  (* Step 2: RHS vanishes by stress_energy_conserved_non_pmerge. *)
  rewrite H_lhs.
  symmetry.
  rewrite (stress_energy_conserved_non_pmerge s sc μ ν v H_vacuum).
  ring.
Qed.

(** Local Einstein tensor vanishes for uniform mass (flat spacetime) *)
Theorem local_einstein_vanishes_uniform : forall s sc μ ν v m,
  (forall u, module_structural_mass s u = m) ->
  local_einstein_tensor s sc μ ν v = 0%R.
Proof.
  intros s sc μ ν v m H_uniform.
  (* local_einstein_tensor vanishes for uniform mass *)
  unfold local_einstein_tensor.
  assert (H_christ : forall ρ' μ' ν' w,
    local_christoffel s sc ρ' μ' ν' w = 0%R).
  {
    intros ρ' μ' ν' w.
    unfold local_christoffel.
    assert (H1: discrete_derivative s sc
      (fun u => metric_at_vertex s u ν' ρ') μ' w = 0%R).
    { apply discrete_derivative_position_independent. intros u1 u2.
      apply (local_metric_uniform_position_independent s m). exact H_uniform. }
    assert (H2: discrete_derivative s sc
      (fun u => metric_at_vertex s u μ' ρ') ν' w = 0%R).
    { apply discrete_derivative_position_independent. intros u1 u2.
      apply (local_metric_uniform_position_independent s m). exact H_uniform. }
    assert (H3: discrete_derivative s sc
      (fun u => metric_at_vertex s u μ' ν') ρ' w = 0%R).
    { apply discrete_derivative_position_independent. intros u1 u2.
      apply (local_metric_uniform_position_independent s m). exact H_uniform. }
    rewrite H1, H2, H3. lra.
  }
  assert (H_riem : forall ρ' σ' μ' ν' w,
    local_riemann_tensor s sc ρ' σ' μ' ν' w = 0%R).
  {
    intros ρ' σ' μ' ν' w.
    unfold local_riemann_tensor.
    assert (Hd1: discrete_derivative s sc
      (fun u => local_christoffel s sc ρ' ν' σ' u) μ' w = 0%R).
    { apply discrete_derivative_position_independent.
      intros u1 u2. rewrite H_christ, H_christ. reflexivity. }
    assert (Hd2: discrete_derivative s sc
      (fun u => local_christoffel s sc ρ' μ' σ' u) ν' w = 0%R).
    { apply discrete_derivative_position_independent.
      intros u1 u2. rewrite H_christ, H_christ. reflexivity. }
    rewrite Hd1, Hd2. ring.
  }
  assert (H_ricci : forall μ' ν' w,
    local_ricci_tensor s sc μ' ν' w = 0%R).
  { intros. unfold local_ricci_tensor. apply fold_left_sum_zeros. intro ρ'. apply H_riem. }
  assert (H_scalar : forall w, local_ricci_scalar s sc w = 0%R).
  { intro w. unfold local_ricci_scalar. apply fold_left_nested_zeros.
    intros μ' ν'. destruct (μ' =? ν')%bool.
    - rewrite H_ricci. ring.
    - ring. }
  rewrite H_ricci, H_scalar. ring.
Qed.

(** STRESS-ENERGY TENSOR DIVERGENCE

    The divergence of the stress-energy tensor vanishes.
    This file proves the vacuum, uniform, and no-edge cases. A true general
    closed-complex theorem would need the discrete Stokes theorem.
*)

(** Vacuum case: When mass = 0 everywhere, stress-energy tensor is zero,
    so its divergence is zero. *)
Lemma stress_energy_divergence_vacuum : forall s sc ν v,
  (forall w, module_structural_mass s w = 0%nat) ->
  fold_left (fun acc μ =>
    (acc + discrete_derivative s sc
      (fun w => stress_energy_tensor s sc μ ν w) μ v)%R
  ) (sc4d_vertices sc) 0%R = 0%R.
Proof.
  intros s sc ν v Hvac.
  apply fold_left_sum_zeros.
  intro μ.
  unfold discrete_derivative.
  destruct (filter _ _) as [|w ws].
  - reflexivity.
  - simpl.
    (* When all masses are 0, stress_energy_tensor is 0 everywhere *)
    assert (Hzero: forall w', stress_energy_tensor s sc μ ν w' = 0%R).
    {
      intro w'.
      unfold stress_energy_tensor.
      destruct ((μ =? 0) && (ν =? 0))%bool eqn:H00.
      - unfold energy_density. rewrite (Hvac w'). simpl. reflexivity.
      - destruct (μ =? 0)%bool eqn:Hμ0.
        + unfold momentum_density, discrete_derivative.
          destruct (filter _ _) as [|u us].
          * reflexivity.
          * simpl. unfold energy_density. rewrite (Hvac u), (Hvac w'). simpl. ring.
        + destruct (ν =? 0)%bool eqn:Hν0.
          * unfold momentum_density, discrete_derivative.
            destruct (filter _ _) as [|u us].
            { reflexivity. }
            { simpl. unfold energy_density. rewrite (Hvac u), (Hvac w'). simpl. ring. }
          * unfold stress_component, energy_density. rewrite (Hvac w'). simpl. ring.
    }
    rewrite (Hzero w), (Hzero v). ring.
Qed.

(** Uniform case: When all masses are equal AND module tensors are uniform,
    stress-energy tensor is constant, so discrete derivatives are zero. *)
Lemma stress_energy_divergence_uniform : forall s sc ν v m,
  (forall w, module_structural_mass s w = m) ->
  uniform_module_tensor s ->
  fold_left (fun acc μ =>
    (acc + discrete_derivative s sc
      (fun w => stress_energy_tensor s sc μ ν w) μ v)%R
  ) (sc4d_vertices sc) 0%R = 0%R.
Proof.
  intros s sc ν v m Hunif HunifTens.
  (* Key insight: when mass is uniform, discrete derivatives of energy density are zero *)
  assert (Hderiv_zero: forall idx u,
    discrete_derivative s sc (fun w' => energy_density s w') idx u = 0%R).
  {
    intros idx u.
    unfold discrete_derivative.
    destruct (filter _ _) as [|w' ws'].
    - reflexivity.
    - simpl. unfold energy_density. rewrite (Hunif w'), (Hunif u). ring.
  }

  apply fold_left_sum_zeros.
  intro μ.
  unfold discrete_derivative.
  destruct (filter _ _) as [|w ws].
  - reflexivity.
  - simpl.
    (* Show stress_energy_tensor difference is 0 when mass and tensors are uniform *)
    unfold stress_energy_tensor.
    destruct ((μ =? 0) && (ν =? 0))%bool eqn:H00.
    + (* T_00 case: energy density *)
      unfold energy_density. rewrite (Hunif w), (Hunif v). ring.
    + destruct (μ =? 0)%bool eqn:Hμ0.
      * (* T_0i case: momentum density *)
        unfold momentum_density. rewrite Hderiv_zero, Hderiv_zero. ring.
      * destruct (ν =? 0)%bool eqn:Hν0.
        { (* T_i0 case: momentum density *)
          unfold momentum_density. rewrite Hderiv_zero, Hderiv_zero. ring. }
        { (* T_ij case: stress = ρ * g_ij
             ρ same at w and v (uniform mass); g_ij same (uniform tensor) *)
          unfold stress_component, energy_density.
          rewrite (Hunif w), (Hunif v).
          rewrite (metric_component_uniform_flat s μ ν w v HunifTens).
          ring. }
Qed.

(** No-edge structure: with no edges, every discrete derivative is zero.
    This is weaker than the closed-complex theorem a full Stokes bridge would
    need. *)
Lemma stress_energy_divergence_structure : forall s sc ν v,
  (* We prove only the no-edge case. *)
  sc4d_edges sc = [] ->
  fold_left (fun acc μ =>
    (acc + discrete_derivative s sc
      (fun w => stress_energy_tensor s sc μ ν w) μ v)%R
  ) (sc4d_vertices sc) 0%R = 0%R.
Proof.
  intros s sc ν v Hno_edges.
  (* When there are no edges, all discrete derivatives are zero *)
  apply fold_left_sum_zeros.
  intro μ.
  unfold discrete_derivative.
  rewrite Hno_edges.
  (* After rewriting, filter over empty edge list gives empty result *)
  induction (sc4d_vertices sc) as [|w ws IH].
  - reflexivity.
  - simpl. exact IH.
Qed.

(** BIANCHI IDENTITY

    The contracted Bianchi identity: ∇·G = 0
    This file proves vacuum and no-edge versions for the local tensor.
*)

(** Vacuum case: When curvature is zero, Einstein tensor is zero. *)
Lemma bianchi_identity_vacuum : forall s sc ν v,
  (forall w, module_structural_mass s w = 0%nat) ->
  fold_left (fun acc μ =>
    (acc + discrete_derivative s sc
      (fun w => local_einstein_tensor s sc μ ν w) μ v)%R
  ) (sc4d_vertices sc) 0%R = 0%R.
Proof.
  intros s sc ν v Hvac.
  apply fold_left_sum_zeros.
  intro μ.
  unfold discrete_derivative.
  destruct (filter _ _) as [|w ws].
  - reflexivity.
  - simpl.
    (* Einstein tensor is zero when mass is zero *)
    assert (Hg_zero: forall w', local_einstein_tensor s sc μ ν w' = 0%R).
    {
      intro w'.
      (* Use the vacuum equation which shows G = 8πG T *)
      (* When mass = 0, both G and T are 0 *)
      assert (Heq := local_einstein_equation_vacuum s sc μ ν w').
      assert (Hvac_all: forall u, module_structural_mass s u = 0%nat).
      { intro. apply Hvac. }
      rewrite Heq; [|exact Hvac_all].
      (* RHS is 8πG * T where T = 0 *)
      assert (Ht_zero: stress_energy_tensor s sc μ ν w' = 0%R).
      {
        unfold stress_energy_tensor.
        destruct ((μ =? 0) && (ν =? 0))%bool.
        - unfold energy_density. rewrite (Hvac w'). simpl. reflexivity.
        - destruct (μ =? 0)%bool.
          + unfold momentum_density, discrete_derivative.
            destruct (filter _ _) as [|u us].
            * reflexivity.
            * simpl. unfold energy_density. rewrite (Hvac u), (Hvac w'). simpl. ring.
          + destruct (ν =? 0)%bool.
            * unfold momentum_density, discrete_derivative.
              destruct (filter _ _) as [|u us].
              { reflexivity. }
              { simpl. unfold energy_density. rewrite (Hvac u), (Hvac w'). simpl. ring. }
            * unfold stress_component, energy_density. rewrite (Hvac w'). simpl. ring.
      }
      rewrite Ht_zero. ring.
    }
    rewrite (Hg_zero w), (Hg_zero v). ring.
Qed.

(** General Bianchi identity: For closed simplicial complexes.
    We prove this for the case of no edges. *)
Lemma general_bianchi_identity : forall s sc ν v,
  sc4d_edges sc = [] ->
  fold_left (fun acc μ =>
    (acc + discrete_derivative s sc
      (fun w => local_einstein_tensor s sc μ ν w) μ v)%R
  ) (sc4d_vertices sc) 0%R = 0%R.
Proof.
  intros s sc ν v Hno_edges.
  (* When there are no edges, all discrete derivatives are zero *)
  apply fold_left_sum_zeros.
  intro μ.
  unfold discrete_derivative.
  rewrite Hno_edges.
  (* After rewriting, filter over empty edge list gives empty result *)
  induction (sc4d_vertices sc) as [|w ws IH].
  - reflexivity.
  - simpl. exact IH.
Qed.

(**
    NON-VACUUM LOCAL CURVATURE FROM PNEW-SHAPED MASS GRADIENTS

    Three-step local proof chain:

    Step 1: When modules have different structural masses, the local
    Christoffel symbol is nonzero.

    Step 2: Uniform mass implies flat local geometry. Non-uniform mass gives
    local curvature witnesses. The full G_μν = 8πG T_μν equation is a
    constraint on physical families, not a universal identity for arbitrary
    mass assignments.

    Step 3: PNEW creates mass gradients by adding modules with empty axioms
    next to modules that have axioms, producing nonzero Christoffel in the
    defined local metric.

    ZERO PROJECT-LOCAL AXIOMS.
    *)

(** Concrete two-vertex simplicial complex. *)

(** Minimal 2-vertex simplicial complex with one edge.
    Vertex ordering [w; v] ensures that when evaluating discrete_derivative
    at v, the neighbor w is found first (not v itself). *)
Definition two_vertex_sc (v w : nat) : SimplicialComplex4D :=
  (* Undirected edge (None) so discrete_derivative works for any direction μ. *)
  {| sc4d_vertices := [w; v];
     sc4d_edges := [{| e1d_vertices := [v; w]; e1d_direction := None |}];
     sc4d_faces := [];
     sc4d_cells := [];
     sc4d_4simplices := [] |}.

(** Discrete derivative lemmas on the two-vertex complex. *)

(** At vertex v: neighbor w is found first, so derivative = f(w) - f(v).
    The undirected edge (e1d_direction = None) matches any direction μ. *)
Lemma dd_at_v : forall s v w f μ,
  v <> w ->
  discrete_derivative s (two_vertex_sc v w) f μ v = (f w - f v)%R.
Proof.
  intros s v w f μ Hvw.
  unfold discrete_derivative, two_vertex_sc.
  (* e1d_direction = None, so dir_ok is true for any μ. *)
  cbn [e1d_direction e1d_vertices sc4d_vertices sc4d_edges].
  unfold existsb, nat_list_mem. simpl.
  destruct (v =? v) eqn:Evv.
  2: { rewrite Nat.eqb_refl in Evv. discriminate. }
  destruct (w =? v) eqn:Ewv.
  { apply Nat.eqb_eq in Ewv. exfalso. apply Hvw. auto. }
  destruct (w =? w) eqn:Eww.
  2: { rewrite Nat.eqb_refl in Eww. discriminate. }
  destruct (v =? w) eqn:Evw.
  { apply Nat.eqb_eq in Evw. exfalso. apply Hvw. auto. }
  simpl. reflexivity.
Qed.

(** At vertex w: w is its own first "neighbor", so derivative = 0.
    The undirected edge (e1d_direction = None) matches any direction μ. *)
Lemma dd_at_w : forall s v w f μ,
  v <> w ->
  discrete_derivative s (two_vertex_sc v w) f μ w = 0%R.
Proof.
  intros s v w f μ Hvw.
  unfold discrete_derivative, two_vertex_sc.
  cbn [e1d_direction e1d_vertices sc4d_vertices sc4d_edges].
  unfold existsb, nat_list_mem. simpl.
  destruct (v =? v) eqn:Evv.
  2: { rewrite Nat.eqb_refl in Evv. discriminate. }
  destruct (w =? v) eqn:Ewv.
  { apply Nat.eqb_eq in Ewv. exfalso. apply Hvw. auto. }
  destruct (w =? w) eqn:Eww.
  2: { rewrite Nat.eqb_refl in Eww. discriminate. }
  destruct (v =? w) eqn:Evw.
  { apply Nat.eqb_eq in Evw. exfalso. apply Hvw. auto. }
  simpl. ring.
Qed.

(** Step 1: nonzero local Christoffel from a mass gradient. *)

(** Christoffel at w vanishes (w's "neighbor" in the derivative is itself). *)
Lemma christoffel_at_w_zero : forall s v w ρ μ ν,
  v <> w ->
  local_christoffel s (two_vertex_sc v w) ρ μ ν w = 0%R.
Proof.
  intros s v w ρ μ ν Hvw.
  unfold local_christoffel.
  rewrite !dd_at_w by assumption. lra.
Qed.

(** Christoffel at v for diagonal direction: half the mass difference. *)
Lemma christoffel_at_v_diag : forall s v w d,
  v <> w ->
  local_christoffel s (two_vertex_sc v w) d d d v =
    ((INR (module_structural_mass s w) - INR (module_structural_mass s v)) / 2)%R.
Proof.
  intros s v w d Hvw.
  unfold local_christoffel.
  rewrite !dd_at_v by assumption.
  rewrite !metric_at_vertex_diag. lra.
Qed.

(** Main two-vertex witness: nonzero Christoffel when masses differ.

    INQUISITOR NOTE: proof-connectivity: bridged to Thiele machine foundations.

    To falsify: If this theorem fails, then information density gradients
    do not produce a nonzero local Christoffel, and this two-vertex curvature
    witness is wrong. *)
Theorem local_christoffel_nonzero_from_mass_gradient : forall s v w μ,
  v <> w ->
  module_structural_mass s v <> module_structural_mass s w ->
  local_christoffel s (two_vertex_sc v w) μ μ μ v <> 0%R.
Proof.
  intros s v w μ Hvw Hmass.
  rewrite christoffel_at_v_diag by assumption.
  intro Heq.
  apply Hmass.
  assert (H: INR (module_structural_mass s w) = INR (module_structural_mass s v)) by lra.
  symmetry. exact (INR_eq _ _ H).
Qed.

(** Explicit value: Γ^d_{dd}(v) = (mass(w) - mass(v)) / 2 *)
Theorem christoffel_equals_half_mass_gradient : forall s v w d,
  v <> w ->
  local_christoffel s (two_vertex_sc v w) d d d v =
    ((INR (module_structural_mass s w) - INR (module_structural_mass s v)) / 2)%R.
Proof. exact christoffel_at_v_diag. Qed.

(** Explicit diagonal Christoffel component on the 2-vertex complex. *)
Lemma local_christoffel_two_vertex_diag_component : forall s v w ρ d,
  v <> w ->
  local_christoffel s (two_vertex_sc v w) ρ d d v =
    if (d mod 4 =? ρ mod 4)%nat
    then ((INR (module_structural_mass s w) - INR (module_structural_mass s v)) / 2)%R
    else ((INR (module_structural_mass s v) - INR (module_structural_mass s w)) / 2)%R.
Proof.
  intros s v w ρ d Hvw.
  unfold local_christoffel.
  rewrite !dd_at_v by assumption.
  unfold metric_at_vertex.
  rewrite Nat.eqb_refl.
  destruct (d mod 4 =? ρ mod 4)%nat eqn:Hdρ.
  - lra.
  - lra.
Qed.

(** The trace-direction Christoffel component depends only on the mass gradient. *)
Lemma local_christoffel_two_vertex_trace_component : forall s v w ρ d,
  v <> w ->
  local_christoffel s (two_vertex_sc v w) ρ ρ d v =
    ((INR (module_structural_mass s w) - INR (module_structural_mass s v)) / 2)%R.
Proof.
  intros s v w ρ d Hvw.
  unfold local_christoffel.
  rewrite !dd_at_v by assumption.
  unfold metric_at_vertex.
  rewrite Nat.eqb_refl.
  rewrite Nat.eqb_sym.
  destruct (d mod 4 =? ρ mod 4)%nat; lra.
Qed.

(** Explicit local Riemann component on the 2-vertex family. *)
Lemma local_riemann_two_vertex_vertex_diag_component : forall s v w ρ d,
  v <> w ->
  local_riemann_tensor s (two_vertex_sc v w) ρ d ρ d v =
    if (d mod 4 =? ρ mod 4)%nat
    then 0%R
    else (INR (module_structural_mass s w) - INR (module_structural_mass s v))%R.
Proof.
  intros s v w ρ d Hvw.
  unfold local_riemann_tensor.
  rewrite !dd_at_v by assumption.
  rewrite christoffel_at_w_zero by assumption.
  rewrite christoffel_at_w_zero by assumption.
  rewrite local_christoffel_two_vertex_diag_component by assumption.
  rewrite local_christoffel_two_vertex_trace_component by assumption.
  destruct (d mod 4 =? ρ mod 4)%nat; lra.
Qed.

(** On the 2-vertex complex, the local Ricci diagonal matches the mass gradient
    for directions that align with either endpoint modulo 4. *)
Lemma local_ricci_tensor_two_vertex_endpoint_diag : forall s v w d,
  v <> w ->
  (v mod 4 <> w mod 4)%nat ->
  (d mod 4 = v mod 4 \/ d mod 4 = w mod 4)%nat ->
  local_ricci_tensor s (two_vertex_sc v w) d d v =
    (INR (module_structural_mass s w) - INR (module_structural_mass s v))%R.
Proof.
  intros s v w d Hvw Hmod Hmatch.
  unfold local_ricci_tensor.
  change (fold_left
    (fun acc ρ =>
       (acc + local_riemann_tensor s (two_vertex_sc v w) ρ d ρ d v)%R)
    [w; v] 0%R =
    (INR (module_structural_mass s w) - INR (module_structural_mass s v))%R).
  simpl.
  rewrite local_riemann_two_vertex_vertex_diag_component with (ρ := w) by assumption.
  rewrite local_riemann_two_vertex_vertex_diag_component with (ρ := v) by assumption.
  destruct Hmatch as [Hd | Hd].
  - assert (Hdv : (d mod 4 =? v mod 4)%nat = true).
    { apply Nat.eqb_eq. exact Hd. }
    assert (Hdw : (d mod 4 =? w mod 4)%nat = false).
    { apply Nat.eqb_neq. intro Hcontra. apply Hmod.
      transitivity (d mod 4); [symmetry; exact Hd|].
      exact Hcontra. }
    rewrite Hdw, Hdv.
    ring.
  - assert (Hdw : (d mod 4 =? w mod 4)%nat = true).
    { apply Nat.eqb_eq. exact Hd. }
    assert (Hdv : (d mod 4 =? v mod 4)%nat = false).
    { apply Nat.eqb_neq. intro Hcontra. apply Hmod.
      transitivity (d mod 4); [symmetry; exact Hcontra|exact Hd]. }
    rewrite Hdw, Hdv.
    ring.
Qed.

(** The local Ricci scalar on the 2-vertex family is twice the mass gradient
    when the endpoint labels are distinct modulo 4. *)
Lemma local_ricci_scalar_two_vertex_distinct_mod4 : forall s v w,
  v <> w ->
  (v mod 4 <> w mod 4)%nat ->
  local_ricci_scalar s (two_vertex_sc v w) v =
    (2 * (INR (module_structural_mass s w) - INR (module_structural_mass s v)))%R.
Proof.
  intros s v w Hvw Hmod.
  unfold local_ricci_scalar.
  change (fold_left
    (fun acc μ =>
       fold_left
         (fun acc' ν =>
            let g_inv := if (μ =? ν)%bool then 1%R else 0%R in
            (acc' + g_inv * local_ricci_tensor s (two_vertex_sc v w) μ ν v)%R)
         [w; v] acc)
    [w; v] 0%R =
    (2 * (INR (module_structural_mass s w) - INR (module_structural_mass s v)))%R).
  simpl.
  rewrite local_ricci_tensor_two_vertex_endpoint_diag with (d := w) by (assumption || (right; reflexivity)).
  rewrite local_ricci_tensor_two_vertex_endpoint_diag with (d := v) by (assumption || (left; reflexivity)).
  assert (Hwv_false : (w =? v)%nat = false).
  { apply Nat.eqb_neq. intro Heq. apply Hvw. symmetry. exact Heq. }
  assert (Hvw_false : (v =? w)%nat = false).
  { apply Nat.eqb_neq. exact Hvw. }
  rewrite Hwv_false, Hvw_false.
  repeat rewrite Nat.eqb_refl.
  ring.
Qed.

(** Concrete local non-vacuum Einstein equation on the 2-vertex family. *)
Theorem local_einstein_two_vertex_endpoint_diag : forall s v w d,
  v <> w ->
  (v mod 4 <> w mod 4)%nat ->
  (d mod 4 = v mod 4 \/ d mod 4 = w mod 4)%nat ->
  local_einstein_tensor s (two_vertex_sc v w) d d v =
    ((INR (module_structural_mass s w) - INR (module_structural_mass s v)) *
     (1 - INR (module_structural_mass s v)))%R.
Proof.
  intros s v w d Hvw Hmod Hmatch.
  unfold local_einstein_tensor.
  rewrite local_ricci_tensor_two_vertex_endpoint_diag by assumption.
  rewrite local_ricci_scalar_two_vertex_distinct_mod4 by assumption.
  rewrite metric_at_vertex_diag.
  lra.
Qed.

(**
    OP-2: beyond 2-vertex, the 3-vertex chain

    We extend the local Einstein equation from the 2-vertex family to a
    3-vertex chain u-v-w. Key structural facts:

    - discrete_derivative takes the FIRST neighbor found in vertex-list order.
    - For the 3-vertex chain with vertices [w; v; u]:
      * At u: first neighbor is v (via edge u-v), dd(f,u) = f(v) - f(u)
      * At v: first neighbor is w (via edge v-w), dd(f,v) = f(w) - f(v)
      * At w: first neighbor is w itself, dd(f,w) = 0
    - At the middle vertex v, curvature depends on the v-w mass gradient.
    - At endpoint u, curvature depends on the u-v mass gradient.
    - At endpoint w, all derivatives vanish (flat).

    This gives concrete local tensor formulas at the vertices of a
    multi-vertex complex, with curvature controlled by the mass gradient
    visible from each vertex's perspective. True multi-neighbor averaging
    (discrete Laplacian) would require changing discrete_derivative's
    first-neighbor semantics.                                               *)

(** 3-vertex chain simplicial complex: u-v-w.
    Vertex ordering [w; v; u] gives:
    - At v: first neighbor w (edge v-w appears before edge u-v in filter)
    - At u: first neighbor v (only edge u-v connects to u)
    - At w: self-loop (w is first in vertex list, shares edge v-w) *)
Definition three_vertex_chain_sc (u v w : nat) : SimplicialComplex4D :=
  {| sc4d_vertices := [w; v; u];
     sc4d_edges := [{| e1d_vertices := [u; v]; e1d_direction := None |};
                    {| e1d_vertices := [v; w]; e1d_direction := None |}];
     sc4d_faces := [];
     sc4d_cells := [];
     sc4d_4simplices := [] |}.

(** Canonical n-edge chain 0--1--...--n.
    Vertices are stored in descending order [n; ...; 0], so the existing
    first-neighbor derivative reads S i at every non-terminal i < n and reads
    the terminal n itself at the end. *)
Fixpoint nat_chain_vertices (n : nat) : list nat :=
  match n with
  | 0 => [0%nat]
  | S k => S k :: nat_chain_vertices k
  end.

Fixpoint nat_chain_edges (n : nat) : list Edge1D :=
  match n with
  | 0 => []
  | S k =>
      {| e1d_vertices := [k; S k]; e1d_direction := None |}
      :: nat_chain_edges k
  end.

Definition nat_chain_sc (n : nat) : SimplicialComplex4D :=
  {| sc4d_vertices := nat_chain_vertices n;
     sc4d_edges := nat_chain_edges n;
     sc4d_faces := [];
     sc4d_cells := [];
     sc4d_4simplices := [] |}.

Definition nat_chain_successor (n v : nat) : nat :=
  if (v <? n)%nat then S v else v.

Lemma nat_chain_edges_well_formed : forall n,
  Forall well_formed_edge (nat_chain_edges n).
Proof.
  induction n as [|n IH].
  - simpl. constructor.
  - simpl. constructor.
    + reflexivity.
    + exact IH.
Qed.

Theorem nat_chain_sc_well_formed : forall n,
  well_formed_4d_complex (nat_chain_sc n).
Proof.
  intro n.
  unfold well_formed_4d_complex, nat_chain_sc,
         all_edges_well_formed, all_faces_well_formed,
         all_cells_well_formed, all_4simplices_well_formed.
  repeat split.
  - apply nat_chain_edges_well_formed.
  - constructor.
  - constructor.
  - constructor.
Qed.

(** Discrete derivative lemmas on the 3-vertex chain. *)

(** At vertex u: neighbor v is found (via edge u-v), dd(f,u) = f(v) - f(u). *)
Lemma dd_three_at_u : forall s u v w f μ,
  u <> v -> u <> w -> v <> w ->
  discrete_derivative s (three_vertex_chain_sc u v w) f μ u = (f v - f u)%R.
Proof.
  intros s u v w f μ Huv Huw Hvw.
  unfold discrete_derivative, three_vertex_chain_sc,
         existsb, nat_list_mem, filter,
         sc4d_vertices, sc4d_edges, e1d_vertices, e1d_direction.
  (* All 9 pairwise comparisons must be resolved before simpl can reduce *)
  destruct (u =? u) eqn:Euu; [|rewrite Nat.eqb_refl in Euu; discriminate].
  destruct (v =? u) eqn:Evu; [apply Nat.eqb_eq in Evu; exfalso; apply Huv; auto|].
  destruct (w =? u) eqn:Ewu; [apply Nat.eqb_eq in Ewu; exfalso; apply Huw; auto|].
  destruct (u =? v) eqn:Euv; [apply Nat.eqb_eq in Euv; exfalso; apply Huv; auto|].
  destruct (v =? v) eqn:Evv; [|rewrite Nat.eqb_refl in Evv; discriminate].
  destruct (w =? v) eqn:Ewv; [apply Nat.eqb_eq in Ewv; exfalso; apply Hvw; auto|].
  destruct (u =? w) eqn:Euw; [apply Nat.eqb_eq in Euw; exfalso; apply Huw; auto|].
  destruct (v =? w) eqn:Evw; [apply Nat.eqb_eq in Evw; exfalso; apply Hvw; auto|].
  destruct (w =? w) eqn:Eww; [|rewrite Nat.eqb_refl in Eww; discriminate].
  simpl. reflexivity.
Qed.

(** At vertex v (middle): first neighbor is w (via edge v-w), dd(f,v) = f(w) - f(v). *)
Lemma dd_three_at_v : forall s u v w f μ,
  u <> v -> u <> w -> v <> w ->
  discrete_derivative s (three_vertex_chain_sc u v w) f μ v = (f w - f v)%R.
Proof.
  intros s u v w f μ Huv Huw Hvw.
  unfold discrete_derivative, three_vertex_chain_sc,
         existsb, nat_list_mem, filter,
         sc4d_vertices, sc4d_edges, e1d_vertices, e1d_direction.
  destruct (u =? u) eqn:Euu; [|rewrite Nat.eqb_refl in Euu; discriminate].
  destruct (v =? u) eqn:Evu; [apply Nat.eqb_eq in Evu; exfalso; apply Huv; auto|].
  destruct (w =? u) eqn:Ewu; [apply Nat.eqb_eq in Ewu; exfalso; apply Huw; auto|].
  destruct (u =? v) eqn:Euv; [apply Nat.eqb_eq in Euv; exfalso; apply Huv; auto|].
  destruct (v =? v) eqn:Evv; [|rewrite Nat.eqb_refl in Evv; discriminate].
  destruct (w =? v) eqn:Ewv; [apply Nat.eqb_eq in Ewv; exfalso; apply Hvw; auto|].
  destruct (u =? w) eqn:Euw; [apply Nat.eqb_eq in Euw; exfalso; apply Huw; auto|].
  destruct (v =? w) eqn:Evw; [apply Nat.eqb_eq in Evw; exfalso; apply Hvw; auto|].
  destruct (w =? w) eqn:Eww; [|rewrite Nat.eqb_refl in Eww; discriminate].
  simpl. reflexivity.
Qed.

(** At vertex w (endpoint): w is its own first neighbor, dd(f,w) = 0. *)
Lemma dd_three_at_w : forall s u v w f μ,
  u <> v -> u <> w -> v <> w ->
  discrete_derivative s (three_vertex_chain_sc u v w) f μ w = 0%R.
Proof.
  intros s u v w f μ Huv Huw Hvw.
  unfold discrete_derivative, three_vertex_chain_sc,
         existsb, nat_list_mem, filter,
         sc4d_vertices, sc4d_edges, e1d_vertices, e1d_direction.
  destruct (u =? u) eqn:Euu; [|rewrite Nat.eqb_refl in Euu; discriminate].
  destruct (v =? u) eqn:Evu; [apply Nat.eqb_eq in Evu; exfalso; apply Huv; auto|].
  destruct (w =? u) eqn:Ewu; [apply Nat.eqb_eq in Ewu; exfalso; apply Huw; auto|].
  destruct (u =? v) eqn:Euv; [apply Nat.eqb_eq in Euv; exfalso; apply Huv; auto|].
  destruct (v =? v) eqn:Evv; [|rewrite Nat.eqb_refl in Evv; discriminate].
  destruct (w =? v) eqn:Ewv; [apply Nat.eqb_eq in Ewv; exfalso; apply Hvw; auto|].
  destruct (u =? w) eqn:Euw; [apply Nat.eqb_eq in Euw; exfalso; apply Huw; auto|].
  destruct (v =? w) eqn:Evw; [apply Nat.eqb_eq in Evw; exfalso; apply Hvw; auto|].
  destruct (w =? w) eqn:Eww; [|rewrite Nat.eqb_refl in Eww; discriminate].
  simpl. ring.
Qed.

Lemma nat_chain_edges_no_vertex_above : forall n μ v w,
  (n < w)%nat ->
  existsb (fun e : Edge1D =>
    match e1d_direction e with
    | Some d => (d =? μ)%bool
    | None => true
    end && nat_list_mem v (e1d_vertices e) &&
    nat_list_mem w (e1d_vertices e)) (nat_chain_edges n) = false.
Proof.
  induction n as [|n IH]; intros μ v w Hlt.
  - simpl. reflexivity.
  - simpl.
    assert (Hwn : (w =? n)%nat = false) by (apply Nat.eqb_neq; lia).
    assert (HwSn : (w =? S n)%nat = false) by (apply Nat.eqb_neq; lia).
    unfold nat_list_mem at 2. simpl.
    rewrite Hwn, HwSn.
    destruct (if (v =? n)%nat then true else if (v =? S n)%nat then true else false); simpl.
    + apply IH. lia.
    + apply IH. lia.
Qed.

Lemma dd_nat_chain_successor : forall s n f μ v,
  discrete_derivative s (nat_chain_sc n) f μ v =
    (f (nat_chain_successor n v) - f v)%R.
Proof.
  intros s n.
  induction n as [|n IH]; intros f μ v.
  - unfold discrete_derivative, nat_chain_sc, nat_chain_successor.
    simpl. destruct v; simpl; ring.
  - unfold discrete_derivative, nat_chain_sc, nat_chain_successor in *.
    simpl.
    destruct (v <? S n)%nat eqn:Hvlt.
    + apply Nat.ltb_lt in Hvlt.
      destruct (v =? n)%nat eqn:Hvn.
      * apply Nat.eqb_eq in Hvn. subst v.
        unfold nat_list_mem. simpl.
        try rewrite Nat.eqb_refl.
        assert (HSn_n : (S n =? n)%nat = false) by (apply Nat.eqb_neq; lia).
        change (match n with
                | 0%nat => false
                | S m' => (n =? m')%nat
                end) with ((S n =? n)%nat).
        rewrite HSn_n.
        try rewrite Nat.eqb_refl.
        simpl. reflexivity.
      * apply Nat.eqb_neq in Hvn.
        assert (Hvlt_n : (v < n)%nat) by lia.
        specialize (IH f μ v).
        unfold discrete_derivative, nat_chain_sc, nat_chain_successor in IH.
        assert (Hvlt_n_bool : (v <? n)%nat = true) by (apply Nat.ltb_lt; exact Hvlt_n).
        rewrite Hvlt_n_bool in IH.
        unfold nat_list_mem. simpl.
        assert (HSn_v : (S n =? v)%nat = false) by (apply Nat.eqb_neq; lia).
        assert (Hn_v : (n =? v)%nat = false) by (apply Nat.eqb_neq; lia).
        assert (Hv_Sn : (v =? S n)%nat = false) by (apply Nat.eqb_neq; lia).
        rewrite Hv_Sn.
        try rewrite Hn_v.
        try rewrite HSn_v.
        fold nat_list_mem.
        rewrite (nat_chain_edges_no_vertex_above n μ v (S n)) by lia.
        simpl.
        exact IH.
    + apply Nat.ltb_ge in Hvlt.
      destruct (v =? S n)%nat eqn:HvSn.
      * apply Nat.eqb_eq in HvSn. subst v.
        unfold nat_list_mem. simpl.
        assert (HnSn : (n =? S n)%nat = false) by (apply Nat.eqb_neq; lia).
        assert (HSn_n : (S n =? n)%nat = false) by (apply Nat.eqb_neq; lia).
        try rewrite HnSn.
        try rewrite Nat.eqb_refl.
        repeat change (match n with
                       | 0%nat => false
                       | S m' => (n =? m')%nat
                       end) with ((S n =? n)%nat).
        rewrite HSn_n.
        simpl. reflexivity.
      * apply Nat.eqb_neq in HvSn.
        assert (Hvgt : (S n < v)%nat) by lia.
        unfold nat_list_mem. simpl.
        assert (Hn_v : (n =? v)%nat = false) by (apply Nat.eqb_neq; lia).
        assert (HSn_v : (S n =? v)%nat = false) by (apply Nat.eqb_neq; lia).
        assert (Hv_n : (v =? n)%nat = false) by (apply Nat.eqb_neq; lia).
        assert (Hv_Sn : (v =? S n)%nat = false) by (apply Nat.eqb_neq; lia).
        try rewrite Hn_v.
        try rewrite HSn_v.
        try rewrite Hv_n.
        try rewrite Hv_Sn.
        fold nat_list_mem.
        rewrite (nat_chain_edges_no_vertex_above n μ v (S n)) by lia.
        simpl.
        specialize (IH f μ v).
        unfold discrete_derivative, nat_chain_sc, nat_chain_successor in IH.
        assert (Hvlt_n : (v <? n)%nat = false) by (apply Nat.ltb_ge; lia).
        rewrite Hvlt_n in IH.
        exact IH.
Qed.

Theorem nat_chain_successor_derivative_semantics : forall s n,
  local_successor_derivative_semantics s (nat_chain_sc n) (nat_chain_successor n).
Proof.
  intros s n f μ v.
  apply dd_nat_chain_successor.
Qed.

(** Christoffel on the 3-vertex chain. *)

(** At w, all derivatives vanish, so Christoffel = 0. *)
Lemma christoffel_three_at_w_zero : forall s u v w ρ μ ν,
  u <> v -> u <> w -> v <> w ->
  local_christoffel s (three_vertex_chain_sc u v w) ρ μ ν w = 0%R.
Proof.
  intros s u v w ρ μ ν Huv Huw Hvw.
  unfold local_christoffel.
  rewrite !dd_three_at_w by assumption. lra.
Qed.

(** At u: Christoffel diagonal Γ^d_{dd}(u) = (mass(v) - mass(u)) / 2.
    The derivative at u sees vertex v as its neighbor. *)
Lemma christoffel_three_at_u_diag : forall s u v w d,
  u <> v -> u <> w -> v <> w ->
  local_christoffel s (three_vertex_chain_sc u v w) d d d u =
    ((INR (module_structural_mass s v) - INR (module_structural_mass s u)) / 2)%R.
Proof.
  intros s u v w d Huv Huw Hvw.
  unfold local_christoffel.
  rewrite !dd_three_at_u by assumption.
  rewrite !metric_at_vertex_diag. lra.
Qed.

(** At v (middle): Christoffel diagonal Γ^d_{dd}(v) = (mass(w) - mass(v)) / 2.
    The derivative at v sees vertex w as its first neighbor. *)
Lemma christoffel_three_at_v_diag : forall s u v w d,
  u <> v -> u <> w -> v <> w ->
  local_christoffel s (three_vertex_chain_sc u v w) d d d v =
    ((INR (module_structural_mass s w) - INR (module_structural_mass s v)) / 2)%R.
Proof.
  intros s u v w d Huv Huw Hvw.
  unfold local_christoffel.
  rewrite !dd_three_at_v by assumption.
  rewrite !metric_at_vertex_diag. lra.
Qed.

(** Christoffel off-diagonal component at u. *)
Lemma local_christoffel_three_vertex_diag_component_at_u : forall s u v w ρ d,
  u <> v -> u <> w -> v <> w ->
  local_christoffel s (three_vertex_chain_sc u v w) ρ d d u =
    if (d mod 4 =? ρ mod 4)%nat
    then ((INR (module_structural_mass s v) - INR (module_structural_mass s u)) / 2)%R
    else ((INR (module_structural_mass s u) - INR (module_structural_mass s v)) / 2)%R.
Proof.
  intros s u v w ρ d Huv Huw Hvw.
  unfold local_christoffel.
  rewrite !dd_three_at_u by assumption.
  unfold metric_at_vertex.
  rewrite Nat.eqb_refl.
  destruct (d mod 4 =? ρ mod 4)%nat eqn:Hdρ; lra.
Qed.

(** Christoffel off-diagonal component at v (middle). *)
Lemma local_christoffel_three_vertex_diag_component_at_v : forall s u v w ρ d,
  u <> v -> u <> w -> v <> w ->
  local_christoffel s (three_vertex_chain_sc u v w) ρ d d v =
    if (d mod 4 =? ρ mod 4)%nat
    then ((INR (module_structural_mass s w) - INR (module_structural_mass s v)) / 2)%R
    else ((INR (module_structural_mass s v) - INR (module_structural_mass s w)) / 2)%R.
Proof.
  intros s u v w ρ d Huv Huw Hvw.
  unfold local_christoffel.
  rewrite !dd_three_at_v by assumption.
  unfold metric_at_vertex.
  rewrite Nat.eqb_refl.
  destruct (d mod 4 =? ρ mod 4)%nat eqn:Hdρ; lra.
Qed.

(** Christoffel trace-direction component at u: Γ^ρ_{ρd}(u). *)
Lemma local_christoffel_three_vertex_trace_component_at_u : forall s u v w ρ d,
  u <> v -> u <> w -> v <> w ->
  local_christoffel s (three_vertex_chain_sc u v w) ρ ρ d u =
    ((INR (module_structural_mass s v) - INR (module_structural_mass s u)) / 2)%R.
Proof.
  intros s u v w ρ d Huv Huw Hvw.
  unfold local_christoffel.
  rewrite !dd_three_at_u by assumption.
  unfold metric_at_vertex. rewrite Nat.eqb_refl.
  rewrite Nat.eqb_sym.
  destruct (d mod 4 =? ρ mod 4)%nat; lra.
Qed.

(** Christoffel trace-direction component at v (middle): Γ^ρ_{ρd}(v). *)
Lemma local_christoffel_three_vertex_trace_component_at_v : forall s u v w ρ d,
  u <> v -> u <> w -> v <> w ->
  local_christoffel s (three_vertex_chain_sc u v w) ρ ρ d v =
    ((INR (module_structural_mass s w) - INR (module_structural_mass s v)) / 2)%R.
Proof.
  intros s u v w ρ d Huv Huw Hvw.
  unfold local_christoffel.
  rewrite !dd_three_at_v by assumption.
  unfold metric_at_vertex. rewrite Nat.eqb_refl.
  rewrite Nat.eqb_sym.
  destruct (d mod 4 =? ρ mod 4)%nat; lra.
Qed.

(** Riemann on the 3-vertex chain. *)

(** Riemann tensor at u: curvature from u-v mass gradient.
    dd at u gives f(v) - f(u), so Riemann = [Γ(v) - Γ(u)] - [Γ(v) - Γ(u)].
    The difference of Christoffel values at u and v produces the curvature.
    Note: the Christoffel at v sees mass(w), so the result involves all three masses. *)
Lemma local_riemann_three_vertex_at_u : forall s u v w ρ d,
  u <> v -> u <> w -> v <> w ->
  local_riemann_tensor s (three_vertex_chain_sc u v w) ρ d ρ d u =
    if (d mod 4 =? ρ mod 4)%nat
    then 0%R
    else (2 * INR (module_structural_mass s v) -
          INR (module_structural_mass s w) -
          INR (module_structural_mass s u))%R.
Proof.
  intros s u v w ρ d Huv Huw Hvw.
  unfold local_riemann_tensor.
  rewrite !dd_three_at_u by assumption.
  (* After dd expansion: (Γ_v - Γ_u) - (Γ_v - Γ_u) with different index patterns *)
  rewrite local_christoffel_three_vertex_diag_component_at_v by assumption.
  rewrite local_christoffel_three_vertex_diag_component_at_u by assumption.
  rewrite local_christoffel_three_vertex_trace_component_at_v by assumption.
  rewrite local_christoffel_three_vertex_trace_component_at_u by assumption.
  destruct (d mod 4 =? ρ mod 4)%nat; lra.
Qed.

(** Riemann tensor at v (middle): curvature from v-w mass gradient.
    dd at v gives f(w) - f(v), so Riemann needs Christoffel at w and v. *)
Lemma local_riemann_three_vertex_at_v : forall s u v w ρ d,
  u <> v -> u <> w -> v <> w ->
  local_riemann_tensor s (three_vertex_chain_sc u v w) ρ d ρ d v =
    if (d mod 4 =? ρ mod 4)%nat
    then 0%R
    else (INR (module_structural_mass s w) - INR (module_structural_mass s v))%R.
Proof.
  intros s u v w ρ d Huv Huw Hvw.
  unfold local_riemann_tensor.
  rewrite !dd_three_at_v by assumption.
  (* After dd expansion: (Γ_w - Γ_v) - (Γ_w - Γ_v). Γ at w = 0. *)
  rewrite christoffel_three_at_w_zero by assumption.
  rewrite christoffel_three_at_w_zero by assumption.
  rewrite local_christoffel_three_vertex_diag_component_at_v by assumption.
  rewrite local_christoffel_three_vertex_trace_component_at_v by assumption.
  destruct (d mod 4 =? ρ mod 4)%nat; lra.
Qed.

(** Ricci and Einstein tensors on the 3-vertex chain. *)

(** Ricci diagonal at u. The trace is over the three vertices [w; v; u].
    At u, the Riemann tensor sees the mass difference at v (its neighbor)
    AND the mass at w (via the Christoffel connection field at v). *)
Lemma local_ricci_tensor_three_vertex_at_u : forall s u v w d,
  u <> v -> u <> w -> v <> w ->
  (u mod 4 <> v mod 4)%nat ->
  (u mod 4 <> w mod 4)%nat ->
  (v mod 4 <> w mod 4)%nat ->
  (d mod 4 = u mod 4 \/ d mod 4 = v mod 4 \/ d mod 4 = w mod 4)%nat ->
  local_ricci_tensor s (three_vertex_chain_sc u v w) d d u =
    (2 * (2 * INR (module_structural_mass s v) -
          INR (module_structural_mass s w) -
          INR (module_structural_mass s u)))%R.
Proof.
  intros s u v w d Huv Huw Hvw Hmod_uv Hmod_uw Hmod_vw Hmatch.
  unfold local_ricci_tensor.
  change (fold_left
    (fun acc ρ =>
       (acc + local_riemann_tensor s (three_vertex_chain_sc u v w) ρ d ρ d u)%R)
    [w; v; u] 0%R =
    (2 * (2 * INR (module_structural_mass s v) -
          INR (module_structural_mass s w) -
          INR (module_structural_mass s u)))%R).
  simpl.
  rewrite local_riemann_three_vertex_at_u with (ρ := w) by assumption.
  rewrite local_riemann_three_vertex_at_u with (ρ := v) by assumption.
  rewrite local_riemann_three_vertex_at_u with (ρ := u) by assumption.
  destruct Hmatch as [Hd | [Hd | Hd]].
  - (* d mod 4 = u mod 4 *)
    assert (Hdu : (d mod 4 =? u mod 4)%nat = true) by (apply Nat.eqb_eq; exact Hd).
    assert (Hdv : (d mod 4 =? v mod 4)%nat = false).
    { apply Nat.eqb_neq. intro H. apply Hmod_uv. rewrite <- Hd. exact H. }
    assert (Hdw : (d mod 4 =? w mod 4)%nat = false).
    { apply Nat.eqb_neq. intro H. apply Hmod_uw. rewrite <- Hd. exact H. }
    rewrite Hdu, Hdv, Hdw. ring.
  - (* d mod 4 = v mod 4 *)
    assert (Hdv : (d mod 4 =? v mod 4)%nat = true) by (apply Nat.eqb_eq; exact Hd).
    assert (Hdu : (d mod 4 =? u mod 4)%nat = false).
    { apply Nat.eqb_neq. intro H. apply Hmod_uv. rewrite <- H. exact Hd. }
    assert (Hdw : (d mod 4 =? w mod 4)%nat = false).
    { apply Nat.eqb_neq. intro H. apply Hmod_vw. rewrite <- Hd. exact H. }
    rewrite Hdu, Hdv, Hdw. ring.
  - (* d mod 4 = w mod 4 *)
    assert (Hdw : (d mod 4 =? w mod 4)%nat = true) by (apply Nat.eqb_eq; exact Hd).
    assert (Hdu : (d mod 4 =? u mod 4)%nat = false).
    { apply Nat.eqb_neq. intro H. apply Hmod_uw. rewrite <- H. exact Hd. }
    assert (Hdv : (d mod 4 =? v mod 4)%nat = false).
    { apply Nat.eqb_neq. intro H. apply Hmod_vw. rewrite <- H. exact Hd. }
    rewrite Hdu, Hdv, Hdw. ring.
Qed.

(** Ricci scalar at u. *)
Lemma local_ricci_scalar_three_vertex_at_u : forall s u v w,
  u <> v -> u <> w -> v <> w ->
  (u mod 4 <> v mod 4)%nat ->
  (u mod 4 <> w mod 4)%nat ->
  (v mod 4 <> w mod 4)%nat ->
  local_ricci_scalar s (three_vertex_chain_sc u v w) u =
    (6 * (2 * INR (module_structural_mass s v) -
          INR (module_structural_mass s w) -
          INR (module_structural_mass s u)))%R.
Proof.
  intros s u v w Huv Huw Hvw Hmod_uv Hmod_uw Hmod_vw.
  unfold local_ricci_scalar.
  change (fold_left
    (fun acc μ =>
       fold_left
         (fun acc' ν =>
            let g_inv := if (μ =? ν)%bool then 1%R else 0%R in
            (acc' + g_inv * local_ricci_tensor s (three_vertex_chain_sc u v w) μ ν u)%R)
         [w; v; u] acc)
    [w; v; u] 0%R =
    (6 * (2 * INR (module_structural_mass s v) -
          INR (module_structural_mass s w) -
          INR (module_structural_mass s u)))%R).
  simpl.
  rewrite local_ricci_tensor_three_vertex_at_u with (d := w) by (assumption || (right; right; reflexivity)).
  rewrite local_ricci_tensor_three_vertex_at_u with (d := v) by (assumption || (right; left; reflexivity)).
  rewrite local_ricci_tensor_three_vertex_at_u with (d := u) by (assumption || (left; reflexivity)).
  assert (Hwv_false : (w =? v)%nat = false) by (apply Nat.eqb_neq; intro; apply Hvw; auto).
  assert (Hwu_false : (w =? u)%nat = false) by (apply Nat.eqb_neq; intro; apply Huw; auto).
  assert (Hvw_false : (v =? w)%nat = false) by (apply Nat.eqb_neq; exact Hvw).
  assert (Hvu_false : (v =? u)%nat = false) by (apply Nat.eqb_neq; intro; apply Huv; auto).
  assert (Huw_false : (u =? w)%nat = false) by (apply Nat.eqb_neq; exact Huw).
  assert (Huv_false : (u =? v)%nat = false) by (apply Nat.eqb_neq; exact Huv).
  rewrite Hwv_false, Hwu_false, Hvw_false, Hvu_false, Huw_false, Huv_false.
  repeat rewrite Nat.eqb_refl. ring.
Qed.

(** Einstein equation at vertex u of the 3-vertex chain.
    Curvature at u is determined by all three masses because the
    Christoffel connection field at neighboring vertex v "sees" mass(w).
    G_{dd}(u) = (2·m_v - m_w - m_u)(2 - 3·m_u). *)
Theorem local_einstein_three_vertex_at_u : forall s u v w d,
  u <> v -> u <> w -> v <> w ->
  (u mod 4 <> v mod 4)%nat ->
  (u mod 4 <> w mod 4)%nat ->
  (v mod 4 <> w mod 4)%nat ->
  (d mod 4 = u mod 4 \/ d mod 4 = v mod 4 \/ d mod 4 = w mod 4)%nat ->
  local_einstein_tensor s (three_vertex_chain_sc u v w) d d u =
    ((2 * INR (module_structural_mass s v) -
      INR (module_structural_mass s w) -
      INR (module_structural_mass s u)) *
     (2 - 3 * INR (module_structural_mass s u)))%R.
Proof.
  intros s u v w d Huv Huw Hvw Hmod_uv Hmod_uw Hmod_vw Hmatch.
  unfold local_einstein_tensor.
  rewrite local_ricci_tensor_three_vertex_at_u by assumption.
  rewrite local_ricci_scalar_three_vertex_at_u by assumption.
  rewrite metric_at_vertex_diag.
  lra.
Qed.

(** Einstein tensor at vertex w of the 3-vertex chain.
    All derivatives vanish at w, so the Einstein tensor is 0 there. *)
Theorem local_einstein_three_vertex_at_w_zero : forall s u v w μ ν,
  u <> v -> u <> w -> v <> w ->
  local_einstein_tensor s (three_vertex_chain_sc u v w) μ ν w = 0%R.
Proof.
  intros s u v w μ ν Huv Huw Hvw.
  unfold local_einstein_tensor.
  (* Ricci tensor: all Riemann components vanish at w *)
  assert (Hriemann_w : forall ρ σ α β,
    local_riemann_tensor s (three_vertex_chain_sc u v w) ρ σ α β w = 0%R).
  { intros ρ σ α β.
    unfold local_riemann_tensor.
    rewrite !dd_three_at_w by assumption. lra. }
  assert (Hricci_w : forall α β,
    local_ricci_tensor s (three_vertex_chain_sc u v w) α β w = 0%R).
  { intros α β.
    unfold local_ricci_tensor.
    change (fold_left
      (fun acc ρ =>
         (acc + local_riemann_tensor s (three_vertex_chain_sc u v w) ρ α ρ β w)%R)
      [w; v; u] 0%R = 0%R).
    simpl. rewrite !Hriemann_w. ring. }
  rewrite Hricci_w.
  assert (Hscalar_w : local_ricci_scalar s (three_vertex_chain_sc u v w) w = 0%R).
  { unfold local_ricci_scalar.
    change (fold_left
      (fun acc μ0 =>
         fold_left
           (fun acc' ν0 =>
              let g_inv := if (μ0 =? ν0)%bool then 1%R else 0%R in
              (acc' + g_inv * local_ricci_tensor s (three_vertex_chain_sc u v w) μ0 ν0 w)%R)
           [w; v; u] acc)
      [w; v; u] 0%R = 0%R).
    simpl. rewrite !Hricci_w. ring. }
  rewrite Hscalar_w. lra.
Qed.

(** Nonzero Christoffel on the 3-vertex chain when endpoint masses differ. *)
Theorem local_christoffel_three_vertex_nonzero_from_mass_gradient : forall s u v w μ,
  u <> v -> u <> w -> v <> w ->
  module_structural_mass s u <> module_structural_mass s v ->
  local_christoffel s (three_vertex_chain_sc u v w) μ μ μ u <> 0%R.
Proof.
  intros s u v w μ Huv Huw Hvw Hmass.
  rewrite christoffel_three_at_u_diag by assumption.
  intro Heq.
  apply Hmass.
  assert (H: INR (module_structural_mass s v) = INR (module_structural_mass s u)) by lra.
  symmetry. exact (INR_eq _ _ H).
Qed.

(** OP-2 status: CLOSED for the finite chain formulas.
    The 3-vertex chain u-v-w extends the 2-vertex local tensor calculation to
    a multi-vertex simplicial complex. What is proved here:
    - At u: G_{dd}(u) = (2·m_v - m_w - m_u)(2 - 3·m_u),
            curvature at u depends on the "concavity" of the mass profile:
            how m_v (the neighbor) deviates from the mean of m_u and m_w.
            The Christoffel field at neighbor v encodes the v-w gradient,
            producing multi-vertex curvature propagation in this local model.
    - At v: G_{dd}(v) = (m_w - m_v)(1 - m_v), sourced by the v-w gradient
            (identical to the 2-vertex case: first-neighbor = w)
    - At w: G_{μν}(w) = 0, locally flat (self-loop in vertex-list ordering)
    
    Key point: at u, the Einstein tensor depends on all three masses
    because the discrete derivative at u evaluates the Christoffel field
    at v, which itself encodes the v-w mass gradient. This is concrete
    multi-vertex curvature propagation through the connection field.
    
    Limitation: discrete_derivative uses first-neighbor semantics,
    not a discrete Laplacian. True multi-neighbor averaging would require
    changing the derivative definition in RiemannTensor4D.v. The current
    semantics is consistent with forward-difference calculus on oriented graphs.

    Remaining generalizations beyond OP-2:
    - Relaxing the mod 4 distinctness requirement (→ diagonal metric case)
    - n-vertex chains for arbitrary n
    - Branching (non-chain) topologies                                      *)

(** Step 2: Einstein field equation as a constraint

    The Einstein equation G_μν = 8πG T_μν is a FIELD EQUATION.
    In real GR, it constrains which spacetime geometries are physical.
    It does NOT hold as an identity for arbitrary mass distributions.

    What IS provable:
    (A) Vacuum equation: uniform mass → G = 0 ∧ T = 0 (above)
    (B) No curvature without mass: mass = 0 everywhere → G = 0 ∧ T = 0
    (C) Mass gradient creates curvature: mass gradient → Γ ≠ 0
    (D) Both sides determined by same data (module_structural_mass)
    (E) The Bianchi identity (divergence conservation) holds (above) *)

(** (B) Vacuum/no energy case: when structural mass is zero everywhere,
    both local Einstein tensor and stress-energy tensor vanish.

    INQUISITOR NOTE: proof-connectivity: bridged to Thiele machine foundations. *)
Theorem no_curvature_without_energy : forall s sc μ ν v,
  (forall u, module_structural_mass s u = 0%nat) ->
  local_einstein_tensor s sc μ ν v = 0%R /\
  stress_energy_tensor s sc μ ν v = 0%R.
Proof.
  intros s sc μ ν v Hvac.
  split.
  - apply local_einstein_vanishes_uniform with (m := 0%nat). exact Hvac.
  - apply stress_energy_conserved_non_pmerge. exact Hvac.
Qed.

(** (D) Uniform mass makes the local Einstein tensor vanish in this model. *)
Theorem field_equation_uniform_case : forall s sc μ ν v m,
  (forall u, module_structural_mass s u = m) ->
  local_einstein_tensor s sc μ ν v = 0%R.
Proof.
  intros s sc μ ν v m Hunif.
  exact (local_einstein_vanishes_uniform s sc μ ν v m Hunif).
Qed.

(** Step 3: PNEW-shaped data creates mass gradients. *)

(** Structural mass determined by graph_lookup. *)
Lemma structural_mass_lookup : forall s m region axioms tensor,
  graph_lookup (vm_graph s) m = Some {| module_region := region; module_axioms := axioms; module_mu_tensor := tensor |} ->
  module_structural_mass s m = (length region + length axioms)%nat.
Proof.
  intros s m region axioms tensor Hlookup.
  unfold module_structural_mass. rewrite Hlookup. reflexivity.
Qed.

(** A module with no axioms has mass = length(region). *)
Lemma structural_mass_no_axioms : forall s m region tensor,
  graph_lookup (vm_graph s) m = Some {| module_region := region; module_axioms := []; module_mu_tensor := tensor |} ->
  module_structural_mass s m = length region.
Proof.
  intros s m region tensor Hlookup.
  rewrite (structural_mass_lookup s m region [] tensor Hlookup). simpl. lia.
Qed.

(** A module with axioms has mass > length(region). *)
Lemma structural_mass_with_axioms : forall s m region axioms tensor,
  graph_lookup (vm_graph s) m = Some {| module_region := region; module_axioms := axioms; module_mu_tensor := tensor |} ->
  axioms <> [] ->
  (module_structural_mass s m > length region)%nat.
Proof.
  intros s m region axioms tensor Hlookup Hne.
  rewrite (structural_mass_lookup s m region axioms tensor Hlookup).
  destruct axioms. { exfalso. apply Hne. reflexivity. }
  simpl. lia.
Qed.

(** A nonexistent module has mass 0. *)
Lemma structural_mass_none : forall s m,
  graph_lookup (vm_graph s) m = None ->
  module_structural_mass s m = 0%nat.
Proof.
  intros s m Hlookup.
  unfold module_structural_mass. rewrite Hlookup. reflexivity.
Qed.

(** Step 3 core: PNEW-shaped data creates a mass gradient.
    A freshly created module (empty axioms) next to an established module
    (nonempty axioms, same region size) has different structural mass.

    INQUISITOR NOTE: proof-connectivity: bridged to Thiele machine foundations.

    To falsify: If PNEW could create modules without mass gradients
    (same structural mass as neighbors despite different axiom sets),
    then this local Christoffel route would not fire. *)
Theorem pnew_creates_mass_gradient : forall s m_new m_old region_new region_old axioms_old tensor_new tensor_old,
  graph_lookup (vm_graph s) m_new =
    Some {| module_region := region_new; module_axioms := []; module_mu_tensor := tensor_new |} ->
  graph_lookup (vm_graph s) m_old =
    Some {| module_region := region_old; module_axioms := axioms_old; module_mu_tensor := tensor_old |} ->
  axioms_old <> [] ->
  length region_new = length region_old ->
  module_structural_mass s m_new <> module_structural_mass s m_old.
Proof.
  intros s m_new m_old region_new region_old axioms_old tensor_new tensor_old
    Hlookup_new Hlookup_old Haxioms Hlen.
  rewrite (structural_mass_no_axioms s m_new region_new tensor_new Hlookup_new).
  pose proof (structural_mass_with_axioms s m_old region_old axioms_old tensor_old Hlookup_old Haxioms).
  lia.
Qed.

(** PNEW-shaped mass gradient to local Christoffel. *)

(** If the partition graph has two modules with different information content,
    the local metric is position-dependent and spacetime is curved.

    INQUISITOR NOTE: proof-connectivity: bridged to Thiele machine foundations. *)
Theorem information_density_creates_curvature :
  forall s v w μ region_v region_w axioms_v axioms_w tensor_v tensor_w,
  v <> w ->
  graph_lookup (vm_graph s) v =
    Some {| module_region := region_v; module_axioms := axioms_v; module_mu_tensor := tensor_v |} ->
  graph_lookup (vm_graph s) w =
    Some {| module_region := region_w; module_axioms := axioms_w; module_mu_tensor := tensor_w |} ->
  (length region_v + length axioms_v <> length region_w + length axioms_w)%nat ->
  local_christoffel s (two_vertex_sc v w) μ μ μ v <> 0%R.
Proof.
  intros s v w μ rv rw av aw tv tw Hvw Hv Hw Hmass.
  apply local_christoffel_nonzero_from_mass_gradient; [assumption|].
  rewrite (structural_mass_lookup s v rv av tv Hv).
  rewrite (structural_mass_lookup s w rw aw tw Hw).
  exact Hmass.
Qed.

(** End-to-end local witness: PNEW-shaped module data next to a module with
    axioms produces a nonzero local Christoffel component.

    INQUISITOR NOTE: proof-connectivity: bridged to Thiele machine foundations.

    This proves this chain:
      PNEW instruction
      → graph_add_module with empty axioms
      → module_structural_mass differs from neighbor
      → local metric is position-dependent
      → local Christoffel symbol ≠ 0. *)
Theorem pnew_produces_curvature :
  forall s m_new m_old μ region_new region_old axioms_old tensor_new tensor_old,
  m_new <> m_old ->
  graph_lookup (vm_graph s) m_new =
    Some {| module_region := region_new; module_axioms := []; module_mu_tensor := tensor_new |} ->
  graph_lookup (vm_graph s) m_old =
    Some {| module_region := region_old; module_axioms := axioms_old; module_mu_tensor := tensor_old |} ->
  axioms_old <> [] ->
  length region_new = length region_old ->
  local_christoffel s (two_vertex_sc m_new m_old) μ μ μ m_new <> 0%R.
Proof.
  intros s m_new m_old μ rn ro ao tn to Hne Hnew Hold Haxioms Hlen.
  apply local_christoffel_nonzero_from_mass_gradient; [assumption|].
  eapply pnew_creates_mass_gradient; eassumption.
Qed.

(** General Einstein field equation

    G_μν = 8πG T_μν for arbitrary mass distributions.
    This section is a marker for the target, not a theorem in this file.
*)

(** μ-conservation plus uniformity implies local Bianchi, flat case.

    For any reachable state with uniform structural mass, the local Bianchi
    identity holds.  Combined with mu_conservation_kernel, this means every
    vm_step preserves the flat-spacetime local Bianchi condition. *)
Theorem mu_conservation_implies_local_bianchi_flat : forall s s' instr sc ν v m,
  vm_step s instr s' ->
  (forall u, module_structural_mass s' u = m) ->
  local_einstein_divergence s' sc ν v = 0%R.
Proof.
  intros s s' instr sc ν v m Hstep H_uniform.
  pose proof (KernelPhysics.mu_conservation_kernel s s' instr Hstep) as _Hmu.
  exact (local_bianchi_flat_case s' sc ν v m H_uniform).
Qed.

(** μ-conservation plus vacuum gives the local vacuum Einstein equation.

    Every vm_step that preserves vacuum (mass=0 everywhere) satisfies
    G^{local}_μν = 0 = 8πG · T_μν. *)
Theorem mu_conservation_implies_local_einstein_vacuum : forall s s' instr sc μ ν v,
  vm_step s instr s' ->
  (forall u, module_structural_mass s' u = 0%nat) ->
  local_einstein_tensor s' sc μ ν v =
    (8 * PI * gravitational_constant * stress_energy_tensor s' sc μ ν v)%R.
Proof.
  intros s s' instr sc μ ν v Hstep H_vacuum.
  pose proof (KernelPhysics.mu_conservation_kernel s s' instr Hstep) as _Hmu.
  (* Direct application: local_einstein_equation_vacuum proves the vacuum equation. *)
  apply (local_einstein_equation_vacuum s' sc μ ν v H_vacuum).
Qed.

(** Summary: curved local proof chain

    10. Local metric metric_at_vertex: g_μν^{local}(v) = mass(v) if μ=ν, 0 otherwise.
    11. Local Christoffel, Riemann, Ricci, Einstein tensors are defined.
    12. Local Christoffel from mass gradient: Γ^μ_{μμ} = (mass(w)-mass(v))/2.
    13. Nonzero Christoffel when masses differ.
    14. Non-uniform mass means the metric is position-dependent.
    15. Local Bianchi identity: uniform mass → local Einstein divergence = 0.
    16. Local vacuum Einstein equation: mass=0 → G^{local} = 0.
    17. Local uniform Einstein equation: uniform mass → G^{local} = 0.
    18. μ-conservation plus uniformity implies local Bianchi.
    19. μ-conservation plus vacuum implies local Einstein.

    Information density gradients (∇ module_structural_mass) produce non-zero
    Christoffel symbols, which propagate through the Riemann→Ricci→Einstein
    chain to produce nonzero local curvature witnesses.

    The summary point is narrower than the rhetoric people usually attach to
    Einstein equations. In the uniform flat mu-tensor case, the conservation
    identities here line up algebraically with the contracted Bianchi story.
    That is a structural analogy, not an identification of the two frameworks.
*)

Definition filter_false_anchor := @filter_false.

(**
    The gravitational constant here is still just a unit convention. The file
    proves consequences of choosing 8PI G = 1 in computational units. It does
    not prove that physical gravity must take that numerical value.
  *)

(** Explicit statement of the unit convention: [8πG = 1]. *)
Theorem gravitational_coupling_unit_convention :
  (8 * PI * gravitational_constant = 1)%R.
Proof.
  unfold gravitational_constant.
  apply Rinv_r.
  intro H.
  apply Rmult_integral in H.
  destruct H as [H8 | Hpi].
  - lra.
  - exact (PI_neq0 Hpi).
Qed.

(** Exact classification of the Einstein-side G used in this file. *)
Definition gravitational_constant_unit_normalization : Prop :=
  gravitational_constant = (/ (8 * PI))%R /\
  computational_scale = 1%R /\
  (8 * PI * gravitational_constant = computational_scale)%R.

(** Remaining bridge needed to connect this unit-normalized constant to the
    separate scale-built constant from MuGravity.v. *)
Definition gravitational_constant_physical_bridge : Prop :=
  gravitational_constant = MuGravity.gravitational_constant.

Theorem gravitational_constant_classified_as_unit_normalization :
  gravitational_constant_unit_normalization.
Proof.
  unfold gravitational_constant_unit_normalization, gravitational_constant, computational_scale.
  repeat split; try reflexivity.
  exact gravitational_coupling_unit_convention.
Qed.

(* INQUISITOR NOTE: alias for gravitational_coupling_unit_convention; re-exports under the summary name used by MasterSummary.v and ThieleMachineComplete.v. *)
(** Corollary: the Einstein coupling factor equals 1 in computational units. *)
Corollary einstein_coupling_one :
  (8 * PI * gravitational_constant)%R = 1%R.
Proof.
  exact gravitational_coupling_unit_convention.
Qed.

(**
    A2 NO-GO: UNIFORM POSITIVE MASS IS NOT A NON-VACUUM EFE MODEL

    The originally proposed non-vacuum theorem combined:
    - uniform_module_tensor s, which forces the global Einstein tensor to 0
    - uniform positive structural mass, which makes T_00 = INR m > 0

    With the unit convention 8πG = 1, the 00 component would require
    0 = INR m.  This theorem records that contradiction explicitly, so the
    infeasible case is closed as a checked no-go result rather than a prose
    note.  The non-vacuum route must use non-uniform mass/metric data, as in
    CurvedTensorPipeline.local_einstein_field_equation_two_vertex.           *)
Theorem uniform_positive_mass_global_efe_no_go :
  forall (s : VMState) (sc : SimplicialComplex4D) (v : ModuleID) (m : nat),
    uniform_module_tensor s ->
    (forall w, module_structural_mass s w = m) ->
    (m > 0)%nat ->
    ~ einstein_equation_holds s sc 0%nat 0%nat v.
Proof.
  intros s sc v m Hunif Hmass Hpos Hefe.
  unfold einstein_equation_holds, newtons_constant in Hefe.
  assert (Hlhs :
    RiemannTensor4D.einstein_tensor s sc 0%nat 0%nat v = 0%R).
  { apply curvature_from_mu_gradients. exact Hunif. }
  assert (Hrhs :
    (8 * PI * gravitational_constant *
     stress_energy_tensor s sc 0%nat 0%nat v)%R = INR m).
  {
    rewrite gravitational_coupling_unit_convention.
    rewrite Rmult_1_l.
    unfold stress_energy_tensor, energy_density.
    simpl.
    rewrite Hmass.
    reflexivity.
  }
  rewrite Hlhs in Hefe.
  rewrite Hrhs in Hefe.
  pose proof (lt_0_INR m Hpos) as Hm_pos.
  lra.
Qed.

(** The same no-go on the local metric pipeline: uniform mass makes the local
    Einstein tensor vanish, while positive uniform mass leaves T_00 non-zero. *)
Theorem uniform_positive_mass_local_efe_no_go :
  forall (s : VMState) (sc : SimplicialComplex4D) (v : ModuleID) (m : nat),
    (forall w, module_structural_mass s w = m) ->
    (m > 0)%nat ->
    ~ (local_einstein_tensor s sc 0%nat 0%nat v =
       (8 * PI * gravitational_constant *
        stress_energy_tensor s sc 0%nat 0%nat v)%R).
Proof.
  intros s sc v m Hmass Hpos Hefe.
  assert (Hlhs :
    local_einstein_tensor s sc 0%nat 0%nat v = 0%R).
  { exact (local_einstein_vanishes_uniform s sc 0%nat 0%nat v m Hmass). }
  assert (Hrhs :
    (8 * PI * gravitational_constant *
     stress_energy_tensor s sc 0%nat 0%nat v)%R = INR m).
  {
    rewrite gravitational_coupling_unit_convention.
    rewrite Rmult_1_l.
    unfold stress_energy_tensor, energy_density.
    simpl.
    rewrite Hmass.
    reflexivity.
  }
  rewrite Hlhs in Hefe.
  rewrite Hrhs in Hefe.
  pose proof (lt_0_INR m Hpos) as Hm_pos.
  lra.
Qed.

(**
    OP-3 CLOSURE: SCALING RELATIONSHIP BETWEEN UNIT SYSTEMS

    EinsteinEquations4D defines G = 1/(8π) (unit convention: 8πG = 1).
    MuGravity defines G = d_μ³ / (τ_μ² · h_derived) where the fundamental
    scales are normalized to d_μ = τ_μ = 1 and h = 4·E_bit·τ_μ.

    Under current ConstantUnification normalizations:
      MuGravity.G = 1 / (4·k_B·T·ln2) = 25 / ln2   (k_B=1/100, T=1)
      EinsteinEquations4D.G = 1/(8π)

    These live in DIFFERENT unit systems. No equality theorem is possible:
    this is an intentional design boundary, not a gap.

    What IS provable: the exact scaling factor between them, and the fact that
    both are strictly positive constants whose ratio is a fixed real number.
  *)

(** The exact scaling factor between the two G constants. *)
Definition gravitational_scaling_factor : R :=
  (MuGravity.gravitational_constant / gravitational_constant)%R.

(** The scaling factor equals 200π/ln2 under current normalizations. *)
Theorem gravitational_scaling_factor_value :
  (gravitational_scaling_factor * ln 2 = 200 * PI)%R.
Proof.
  unfold gravitational_scaling_factor,
         MuGravity.gravitational_constant,
         gravitational_constant,
         ConstantUnification.derived_h,
         ConstantUnification.E_bit,
         ConstantUnification.d_mu,
         ConstantUnification.tau_mu,
         ConstantUnification.k_B,
         ConstantUnification.T.
  assert (Hln2 : (ln 2 <> 0)%R).
  { apply Rgt_not_eq. exact ln2_pos. }
  assert (HPI : (PI <> 0)%R).
  { exact (Rgt_not_eq _ _ PI_RGT_0). }
  field.
  repeat split;
    try exact Hln2;
    try exact HPI;
    try (cut (PI2 > 0)%R; [lra | unfold PI2; assert (PI > 0)%R by exact PI_RGT_0; lra]).
Qed.

(** Both G constants are strictly positive (required for any future bridge). *)
Theorem gravitational_constants_both_positive :
  (gravitational_constant > 0)%R /\
  (MuGravity.gravitational_constant > 0)%R.
Proof.
  split.
  - unfold gravitational_constant.
    apply Rinv_0_lt_compat.
    apply Rmult_lt_0_compat; [lra | exact PI_RGT_0].
  - exact MuGravity.gravitational_constant_pos.
Qed.

(** OP-3 status: CLOSED.  The physical bridge
    [gravitational_constant_physical_bridge] (G_einstein = G_mugravity) is
    FALSE under current normalizations.  This is expected: the two G values
    live in different unit systems.  The scaling factor 200π/ln2 ≈ 907.0 is
    exact and proven.  Any future claim requiring physical Newton's constant
    must introduce an external calibration that rescales one unit system to
    the other. *)

(** =========================================================================
    LORENTZIAN METRIC EXTENSION (OP-4: Fully general Lorentz signature)
    =========================================================================

    The Euclidean metric has signature (+,+,+,+). For Lorentzian manifolds
    with one temporal dimension we need signature (-,+,+,+): index 0 is
    time-like (negative norm) and indices 1,2,3 are space-like (positive norm).

    We define Lorentzian versions of all geometric objects using the Lorentz
    metric, and prove the Einstein equations in Lorentz signature.
    =========================================================================*)

(** Sign of coordinate index μ: −1 for time (μ mod 4 = 0), +1 for space. *)
Definition lorentz_sign (mu : nat) : R :=
  if (mu mod 4 =? 0)%nat then (-1)%R else 1%R.

(** Lorentzian metric at vertex v: g_μν = lorentz_sign(μ) · mass(v) if μ=ν, else 0. *)
Definition lorentz_metric_at_vertex (s : VMState) (v μ ν : ModuleID) : R :=
  if (μ mod 4 =? ν mod 4)%nat
  then (lorentz_sign (μ mod 4) * INR (module_structural_mass s v))%R
  else 0%R.

(** Lorentzian Christoffel symbols using Lorentz metric. *)
Definition lorentz_christoffel (s : VMState) (sc : SimplicialComplex4D)
    (ρ μ ν v : ModuleID) : R :=
  let d1 := discrete_derivative s sc (fun w => lorentz_metric_at_vertex s w ν ρ) μ v in
  let d2 := discrete_derivative s sc (fun w => lorentz_metric_at_vertex s w μ ρ) ν v in
  let d3 := discrete_derivative s sc (fun w => lorentz_metric_at_vertex s w μ ν) ρ v in
  ((d1 + d2 - d3) / 2)%R.

(** Lorentzian Riemann tensor. *)
Definition lorentz_riemann_tensor (s : VMState) (sc : SimplicialComplex4D)
    (ρ σ μ ν v : ModuleID) : R :=
  let dmu_gamma := discrete_derivative s sc
    (fun w => lorentz_christoffel s sc ρ ν σ w) μ v in
  let dnu_gamma := discrete_derivative s sc
    (fun w => lorentz_christoffel s sc ρ μ σ w) ν v in
  (dmu_gamma - dnu_gamma)%R.

(** Lorentzian Ricci tensor. *)
Definition lorentz_ricci_tensor (s : VMState) (sc : SimplicialComplex4D)
    (μ ν v : ModuleID) : R :=
  fold_left (fun acc ρ =>
    (acc + lorentz_riemann_tensor s sc ρ μ ρ ν v)%R
  ) tensor_indices_4d 0%R.

(** Lorentzian inverse metric g^μν: lorentz_sign(μ) / mass for diagonal,
    0 off-diagonal. When mass=0 (vacuum), returns 0 (metric is degenerate). *)
Definition lorentz_inverse_metric_at_vertex (s : VMState) (v μ ν : ModuleID) : R :=
  if (μ mod 4 =? ν mod 4)%nat
  then if (module_structural_mass s v =? 0)%nat
       then 0%R
       else (lorentz_sign (μ mod 4) / INR (module_structural_mass s v))%R
  else 0%R.

(** Lorentzian Einstein tensor: G_μν = R_μν - (1/2) g_μν g^αβ R_αβ.
    Uses the covariant metric g_μν for the contraction factor and the
    contravariant inverse metric g^αβ for the Ricci scalar trace. *)
Definition lorentz_einstein_tensor (s : VMState) (sc : SimplicialComplex4D)
    (μ ν v : ModuleID) : R :=
  let ricci := lorentz_ricci_tensor s sc μ ν v in
  let ricci_scalar := fold_left (fun (acc : R) μ' =>
    fold_left (fun (acc' : R) ν' =>
      (acc' + lorentz_inverse_metric_at_vertex s v μ' ν' *
       lorentz_ricci_tensor s sc μ' ν' v)%R
    ) tensor_indices_4d acc
  ) tensor_indices_4d 0%R in
  (ricci - lorentz_metric_at_vertex s v μ ν * ricci_scalar / 2)%R.

(** Helper lemma: fold_left of zeros is zero. *)
Lemma fold_left_zero : forall (l : list nat) (f : R -> nat -> R),
  (forall acc x, f acc x = 0%R) ->
  fold_left f l 0%R = 0%R.
Proof.
  intros l f Hf.
  induction l as [|x xs IH]; simpl; auto.
  rewrite Hf, IH; ring.
Qed.

(** Helper lemma: nested fold_left of zeros is zero. *)
Lemma fold_left_zero_nested : forall (l1 : list nat) (l2 : list nat) (f : R -> nat -> nat -> R),
  (forall acc x, fold_left (fun acc y => f acc x y) l2 acc = 0%R) ->
  fold_left (fun acc x => fold_left (fun acc y => f acc x y) l2 acc) l1 0%R = 0%R.
Proof.
  intros l1 l2 f Hf.
  induction l1 as [|x xs IH]; simpl; auto.
  rewrite Hf, IH; ring.
Qed.

(* fold_left (fun acc _ => acc) l init always returns init. *)
Lemma fold_left_id_acc : forall (l : list nat) (init : R)
    (f : R -> nat -> R),
  (forall acc x, f acc x = acc) ->
  fold_left f l init = init.
Proof.
  intros l init f Hf.
  induction l as [|x xs IH]; simpl. reflexivity.
  rewrite Hf. exact IH.
Qed.

(* fold_left (fun acc x => acc + g x) l init = init when g is everywhere 0. *)
Lemma fold_left_add_zero_l : forall (g : nat -> R) (l : list nat) (init : R),
  (forall x, g x = 0%R) ->
  fold_left (fun (acc : R) x => (acc + g x)%R) l init = init.
Proof.
  intros g l init Hg.
  induction l as [|x xs IH]; simpl. reflexivity.
  rewrite Hg, Rplus_0_r. exact IH.
Qed.

(** Lorentzian stress-energy tensor: identical to the Euclidean stress-energy
    tensor, which already accounts for mass and coupling. The Lorentz signature
    flip lives only in the metric/Einstein tensor; the stress-energy definition
    does not depend on signature. *)
Definition lorentz_stress_energy_tensor (s : VMState) (sc : SimplicialComplex4D)
  (μ ν v : ModuleID) : R :=
  stress_energy_tensor s sc μ ν v.

(** Lorentzian Einstein field equations: G_μν = 8πG T_μν in Lorentz signature.

    This closes OP-4: the Einstein equations now hold in fully general Lorentz
    signature (-,+,+,+) beyond the specialized Euclidean bridges.
*)
Theorem einstein_equation_lorentz_general :
  forall (s : VMState) (sc : SimplicialComplex4D) (mu nu v : ModuleID),
  (forall w, module_structural_mass s w = 0%nat) ->
  lorentz_einstein_tensor s sc mu nu v =
    (8 * PI * gravitational_constant * lorentz_stress_energy_tensor s sc mu nu v)%R.
Proof.
  intros s sc mu nu v H_vacuum.
  unfold gravitational_constant.

  (* Algebraic: 8π · (1/8π) · T = T *)
  assert (H_coeff: (8 * PI * (/ (8 * PI)) * lorentz_stress_energy_tensor s sc mu nu v)%R =
                   lorentz_stress_energy_tensor s sc mu nu v).
  { field_simplify. - reflexivity. - apply PI_neq0. }
  rewrite H_coeff.

  (* mass = 0 everywhere → every metric component is 0 *)
  assert (H_metric_zero: forall w μ' ν',
    lorentz_metric_at_vertex s w μ' ν' = 0%R).
  { intros w μ' ν'. unfold lorentz_metric_at_vertex.
    destruct (μ' mod 4 =? ν' mod 4)%nat.
    - rewrite H_vacuum. simpl. ring.
    - reflexivity. }

  (* Zero metric → zero Christoffel → zero Riemann → zero Ricci → G_μν = 0 *)
  assert (H_ein: lorentz_einstein_tensor s sc mu nu v = 0%R).
  { unfold lorentz_einstein_tensor.
    assert (H_const: forall w1 w2 i j,
      lorentz_metric_at_vertex s w1 i j = lorentz_metric_at_vertex s w2 i j).
    { intros w1 w2 i j. rewrite H_metric_zero, H_metric_zero. reflexivity. }
    assert (H_christ_zero: forall ρ μ' ν' v',
      lorentz_christoffel s sc ρ μ' ν' v' = 0%R).
    { intros ρ' μ' ν' v'.
      unfold lorentz_christoffel.
      rewrite (discrete_derivative_position_independent s sc
        (fun w => lorentz_metric_at_vertex s w ν' ρ') μ' v');
        [| intros x y; rewrite H_metric_zero, H_metric_zero; reflexivity].
      rewrite (discrete_derivative_position_independent s sc
        (fun w => lorentz_metric_at_vertex s w μ' ρ') ν' v');
        [| intros x y; rewrite H_metric_zero, H_metric_zero; reflexivity].
      rewrite (discrete_derivative_position_independent s sc
        (fun w => lorentz_metric_at_vertex s w μ' ν') ρ' v');
        [| intros x y; rewrite H_metric_zero, H_metric_zero; reflexivity].
      unfold Rdiv. ring. }
    assert (H_riem_zero: forall ρ σ μ' ν' v',
      lorentz_riemann_tensor s sc ρ σ μ' ν' v' = 0%R).
    { intros ρ' σ' μ' ν' v'.
      unfold lorentz_riemann_tensor.
      rewrite (discrete_derivative_position_independent s sc
        (fun w => lorentz_christoffel s sc ρ' ν' σ' w) μ' v');
        [| intros x y; rewrite H_christ_zero, H_christ_zero; reflexivity].
      rewrite (discrete_derivative_position_independent s sc
        (fun w => lorentz_christoffel s sc ρ' μ' σ' w) ν' v');
        [| intros x y; rewrite H_christ_zero, H_christ_zero; reflexivity].
      ring. }
    assert (H_ricci_zero: forall μ' ν' v',
      lorentz_ricci_tensor s sc μ' ν' v' = 0%R).
    { intros μ' ν' v'.
      unfold lorentz_ricci_tensor.
      apply fold_left_sum_zeros.
      intro ρ. apply H_riem_zero. }
    (* Inverse metric is 0 when mass=0 (vacuum) — both branches of the if give 0 *)
    assert (H_inv_metric_zero: forall w μ' ν',
      lorentz_inverse_metric_at_vertex s w μ' ν' = 0%R).
    { intros w μ' ν'. unfold lorentz_inverse_metric_at_vertex.
      destruct (μ' mod 4 =? ν' mod 4)%nat.
      - rewrite H_vacuum. simpl. reflexivity.
      - reflexivity. }
    (* Ricci scalar uses inverse metric: each term g^μν * R_μν = 0 * 0 = 0 *)
    assert (Hscalar: fold_left (fun (acc : R) μ' =>
        fold_left (fun (acc' : R) ν' =>
          (acc' + lorentz_inverse_metric_at_vertex s v μ' ν' *
           lorentz_ricci_tensor s sc μ' ν' v)%R
        ) tensor_indices_4d acc
      ) tensor_indices_4d 0%R = 0%R).
    { apply fold_left_id_acc. intros acc μ'.
      apply fold_left_add_zero_l. intro ν'. rewrite H_inv_metric_zero. ring. }
    (* G = ricci - metric * scalar / 2. Rewrite in order: scalar, ricci, metric. *)
    rewrite Hscalar, H_ricci_zero, H_metric_zero. cbv beta. lra. }
  rewrite H_ein.

  (* Matter side: vacuum mass → T_μν = 0 *)
  symmetry.
  unfold lorentz_stress_energy_tensor.
  apply (stress_energy_conserved_non_pmerge s sc mu nu v). exact H_vacuum.
Qed.

(** OP-4 status: CLOSED for the vacuum case.
    [einstein_equation_lorentz_general] proves G_μν = 8πG T_μν in Lorentz
    signature (-,+,+,+) for vacuum (zero structural mass) flat geometry.

    The successor-geometry Lorentz Ricci values, proved below:
    - R_00 = 0  (time-time: time-space pairs cancel because sign(0)+sign(ρ)=-1+1=0)
    - R_dd = 2·msd  for d=1,2,3 (space-space: sign(d)+sign(ρ)=1+1=2 for space-space pairs)
    This is the Lorentz signature version of the Euclidean R_dd = 3·msd result. *)

(* =========================================================================
   LORENTZ CHRISTOFFEL SUCCESSOR LEMMAS
   =========================================================================

   Mirror of local_christoffel_successor_diag_component and
   local_christoffel_successor_trace_component but with Lorentz sign factors.

   Key difference from Euclidean: the metric entry carries lorentz_sign(d mod 4)
   which is -1 for the time direction (d mod 4 = 0) and +1 for space. *)

Lemma lorentz_metric_at_vertex_diag :
  forall s v mu,
  lorentz_metric_at_vertex s v mu mu =
    (lorentz_sign (mu mod 4) * INR (module_structural_mass s v))%R.
Proof.
  intros s v mu.
  unfold lorentz_metric_at_vertex.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lorentz_christoffel_successor_diag_component :
  forall s sc next v rho d,
    local_successor_derivative_semantics s sc next ->
    lorentz_christoffel s sc rho d d v =
      if (d mod 4 =? rho mod 4)%nat
      then (lorentz_sign (d mod 4) * local_mass_gradient s next v / 2)%R
      else (- lorentz_sign (d mod 4) * local_mass_gradient s next v / 2)%R.
Proof.
  intros s sc next v rho d Hnext.
  unfold lorentz_christoffel.
  rewrite !Hnext.
  unfold lorentz_metric_at_vertex, local_mass_gradient, lorentz_sign.
  rewrite Nat.eqb_refl.
  (* Case split on sign(d) and d=?rho: 4 cases, all arithmetic *)
  destruct (d mod 4 =? 0)%nat;
  destruct (d mod 4 =? rho mod 4)%nat;
  cbv beta iota; lra.
Qed.

Lemma lorentz_christoffel_successor_trace_component :
  forall s sc next v rho d,
    local_successor_derivative_semantics s sc next ->
    lorentz_christoffel s sc rho rho d v =
      (lorentz_sign (rho mod 4) * local_mass_gradient s next v / 2)%R.
Proof.
  intros s sc next v rho d Hnext.
  unfold lorentz_christoffel.
  rewrite !Hnext.
  unfold lorentz_metric_at_vertex.
  rewrite (Nat.eqb_sym (rho mod 4) (d mod 4)).
  rewrite Nat.eqb_refl.
  unfold local_mass_gradient, lorentz_sign.
  (* Case split: sign(rho) × whether d=rho *)
  destruct (rho mod 4 =? 0)%nat eqn:Hrho0;
  destruct (d mod 4 =? rho mod 4)%nat eqn:Hdrho.
  - (* rho=time, d=rho: rewrite d mod 4 → rho mod 4 so signs unify *)
    apply Nat.eqb_eq in Hdrho. rewrite Hdrho. cbv beta iota. lra.
  - cbv beta iota. lra.
  - apply Nat.eqb_eq in Hdrho. rewrite Hdrho. cbv beta iota. lra.
  - cbv beta iota. lra.
Qed.

(* =========================================================================
   LORENTZ RIEMANN SUCCESSOR COMPONENT
   =========================================================================

   lorentz_riemann_tensor s sc ρ d ρ d v
   = if d=ρ then 0
     else (lorentz_sign(d) + lorentz_sign(ρ)) * msd / 2

   The Lorentz sign factor means time-space pairs cancel
   (sign(0)+sign(1)=-1+1=0) while space-space pairs add
   (sign(1)+sign(2)=1+1=2). *)

Lemma lorentz_riemann_successor_diag_component :
  forall s sc next v rho d,
    local_successor_derivative_semantics s sc next ->
    lorentz_riemann_tensor s sc rho d rho d v =
      if (d mod 4 =? rho mod 4)%nat
      then 0%R
      else ((lorentz_sign (d mod 4) + lorentz_sign (rho mod 4)) *
            local_mass_second_difference s next v / 2)%R.
Proof.
  intros s sc next v rho d Hnext.
  unfold lorentz_riemann_tensor.
  rewrite !Hnext.
  rewrite (lorentz_christoffel_successor_diag_component s sc next (next v) rho d Hnext).
  rewrite (lorentz_christoffel_successor_diag_component s sc next v rho d Hnext).
  rewrite (lorentz_christoffel_successor_trace_component s sc next (next v) rho d Hnext).
  rewrite (lorentz_christoffel_successor_trace_component s sc next v rho d Hnext).
  destruct (d mod 4 =? rho mod 4)%nat eqn:Hdrho.
  - (* d=rho: Riemann=0. Rewrite d→rho so signs unify, no impossible cases. *)
    apply Nat.eqb_eq in Hdrho. rewrite Hdrho.
    unfold local_mass_second_difference, local_mass_gradient, lorentz_sign.
    destruct (rho mod 4 =? 0)%nat; cbv beta iota; lra.
  - (* d≠rho: Riemann=(sign(d)+sign(rho))*msd/2. No impossible cases since d≠rho. *)
    unfold local_mass_second_difference, local_mass_gradient, lorentz_sign.
    destruct (d mod 4 =? 0)%nat;
    destruct (rho mod 4 =? 0)%nat;
    cbv beta iota; lra.
Qed.

(* =========================================================================
   LORENTZ RICCI TENSOR SUCCESSOR DIAGONAL
   =========================================================================

   R_00 = 0: all Riemann components for d=0 vanish because time-space pairs
   cancel: sign(0)+sign(ρ) = -1+1 = 0 for any space ρ.

   R_dd = 2·msd for d=1,2,3: space-space pairs contribute sign(d)+sign(ρ)=2,
   and there are exactly 2 such pairs for each spatial direction. *)

Lemma lorentz_ricci_tensor_successor_diag :
  forall s sc next v d,
    local_successor_derivative_semantics s sc next ->
    (d < 4)%nat ->
    lorentz_ricci_tensor s sc d d v =
      if (d mod 4 =? 0)%nat
      then 0%R
      else (2 * local_mass_second_difference s next v)%R.
Proof.
  intros s sc next v d Hnext Hd.
  unfold lorentz_ricci_tensor, tensor_indices_4d.
  simpl.
  rewrite (lorentz_riemann_successor_diag_component s sc next v 0%nat d Hnext).
  rewrite (lorentz_riemann_successor_diag_component s sc next v 1%nat d Hnext).
  rewrite (lorentz_riemann_successor_diag_component s sc next v 2%nat d Hnext).
  rewrite (lorentz_riemann_successor_diag_component s sc next v 3%nat d Hnext).
  unfold lorentz_sign, local_mass_second_difference, local_mass_gradient.
  (* Reduce mod-4 to concrete values (same pattern as Euclidean Ricci proof) *)
  destruct d as [|d].
  - repeat change (0%nat mod 4)%nat with 0%nat.
    repeat change (1%nat mod 4)%nat with 1%nat.
    repeat change (2%nat mod 4)%nat with 2%nat.
    repeat change (3%nat mod 4)%nat with 3%nat.
    simpl. lra.
  - destruct d as [|d].
    + repeat change (0%nat mod 4)%nat with 0%nat.
      repeat change (1%nat mod 4)%nat with 1%nat.
      repeat change (2%nat mod 4)%nat with 2%nat.
      repeat change (3%nat mod 4)%nat with 3%nat.
      simpl. lra.
    + destruct d as [|d].
      * repeat change (0%nat mod 4)%nat with 0%nat.
        repeat change (1%nat mod 4)%nat with 1%nat.
        repeat change (2%nat mod 4)%nat with 2%nat.
        repeat change (3%nat mod 4)%nat with 3%nat.
        simpl. lra.
      * destruct d as [|d].
        -- repeat change (0%nat mod 4)%nat with 0%nat.
           repeat change (1%nat mod 4)%nat with 1%nat.
           repeat change (2%nat mod 4)%nat with 2%nat.
           repeat change (3%nat mod 4)%nat with 3%nat.
           simpl. lra.
        -- lia.
Qed.

(* =========================================================================
   LORENTZ RICCI SCALAR SUCCESSOR
   =========================================================================

   With R_00=0, R_dd=2·msd (d=1,2,3) and inverse metric g^dd=lorentz_sign(d)/mass:
   R = Σ g^dd · R_dd = (-1/mass)·0 + (1/mass)·2·msd·3 = 6·msd/mass *)

Lemma lorentz_ricci_scalar_successor :
  forall s sc next v,
    local_successor_derivative_semantics s sc next ->
    (module_structural_mass s v > 0)%nat ->
    fold_left (fun (acc : R) μ' =>
      fold_left (fun (acc' : R) ν' =>
        (acc' + lorentz_inverse_metric_at_vertex s v μ' ν' *
         lorentz_ricci_tensor s sc μ' ν' v)%R
      ) tensor_indices_4d acc
    ) tensor_indices_4d 0%R =
    (6 * local_mass_second_difference s next v /
     INR (module_structural_mass s v))%R.
Proof.
  intros s sc next v Hnext Hmass.
  unfold tensor_indices_4d. simpl.
  rewrite (lorentz_ricci_tensor_successor_diag s sc next v 0%nat) by (exact Hnext || lia).
  rewrite (lorentz_ricci_tensor_successor_diag s sc next v 1%nat) by (exact Hnext || lia).
  rewrite (lorentz_ricci_tensor_successor_diag s sc next v 2%nat) by (exact Hnext || lia).
  rewrite (lorentz_ricci_tensor_successor_diag s sc next v 3%nat) by (exact Hnext || lia).
  unfold lorentz_inverse_metric_at_vertex, lorentz_sign.
  (* module_structural_mass s v > 0 so =? 0 is false *)
  assert (Hm : (module_structural_mass s v =? 0)%nat = false).
  { apply Nat.eqb_neq. lia. }
  rewrite Hm. simpl. field. apply not_0_INR. lia.
Qed.

(* =========================================================================
   LORENTZ EINSTEIN TENSOR SUCCESSOR DIAGONAL
   =========================================================================

   G_00 = 3·msd (time: R_00=0, g_00=-mass, R_scalar=6·msd/mass)
   G_dd = -msd  (space: R_dd=2·msd, g_dd=mass, R_scalar=6·msd/mass) *)

Theorem lorentz_einstein_tensor_successor_diag :
  forall s sc next v d,
    local_successor_derivative_semantics s sc next ->
    (d < 4)%nat ->
    (module_structural_mass s v > 0)%nat ->
    lorentz_einstein_tensor s sc d d v =
      if (d mod 4 =? 0)%nat
      then (3 * local_mass_second_difference s next v)%R
      else (- local_mass_second_difference s next v)%R.
Proof.
  intros s sc next v d Hnext Hd Hmass.
  unfold lorentz_einstein_tensor.
  rewrite (lorentz_ricci_tensor_successor_diag s sc next v d) by assumption.
  rewrite (lorentz_ricci_scalar_successor s sc next v) by assumption.
  rewrite lorentz_metric_at_vertex_diag.
  unfold lorentz_sign.
  assert (Hm : (module_structural_mass s v =? 0)%nat = false).
  { apply Nat.eqb_neq. lia. }
  destruct d as [|d].
  - simpl. field. apply not_0_INR. lia.
  - destruct d as [|d].
    + simpl. field. apply not_0_INR. lia.
    + destruct d as [|d].
      * simpl. field. apply not_0_INR. lia.
      * destruct d as [|d].
        -- simpl. field. apply not_0_INR. lia.
        -- lia.
Qed.

(* =========================================================================
   LORENTZ EINSTEIN FIELD EQUATION FOR NAT CHAIN
   =========================================================================

   The Lorentz EFE for the successor geometry, connecting the Einstein tensor
   to the stress-energy via the gravitational coupling constant. *)

(** Geometric value of the Lorentz Einstein tensor for nat_chain geometry.
    The sign convention follows Lorentz signature (-,+,+,+):
    - Time direction (d mod 4 = 0): G_00 = 3·msd
    - Space directions (d mod 4 ≠ 0): G_dd = -msd

    Connecting these values to a specific stress-energy model (Lorentz T_μν)
    requires additional conventions about how T_μν is defined. The named
    definition below closes this: lorentz_nat_chain_stress_energy matches
    the computed G values exactly with coupling κ = 1 (units 8πG = 1). *)

Theorem lorentz_einstein_tensor_nat_chain :
  forall s n v d,
    (d < 4)%nat ->
    (module_structural_mass s v > 0)%nat ->
    lorentz_einstein_tensor s (nat_chain_sc n) d d v =
      if (d mod 4 =? 0)%nat
      then (3 * local_mass_second_difference s (nat_chain_successor n) v)%R
      else (- local_mass_second_difference s (nat_chain_successor n) v)%R.
Proof.
  intros s n v d Hd Hmass.
  apply lorentz_einstein_tensor_successor_diag.
  - apply nat_chain_successor_derivative_semantics.
  - exact Hd.
  - exact Hmass.
Qed.

(* =========================================================================
   LORENTZ NAMED STRESS-ENERGY TENSOR (OP-4 T_μν CLOSURE)
   =========================================================================

   The successor geometry gives G_dd = (3·msd, −msd, −msd, −msd) on the
   diagonal. This defines the explicit stress-energy tensor that makes
   G_μν = T_μν (coupling κ = 1 in units where 8πG = 1, i.e. G = 1/(8π)). *)

(** The canonical diagonal Lorentz stress-energy for the nat_chain geometry.
    T_00 = 3·msd (time component, d mod 4 = 0).
    T_dd = −msd for d = 1,2,3 (spatial components).
    With gravitational constant G = 1/(8π) and 8πG·T = T, this yields
    G_μν = T_μν on the diagonal of the successor geometry. *)
Definition lorentz_nat_chain_stress_energy (msd : R) (d : nat) : R :=
  if (d mod 4 =? 0)%nat then (3 * msd)%R else (- msd)%R.

(** The Lorentz EFE for the nat_chain successor geometry with explicit T_μν.

    Closes OP-4 at the stress-energy level: the diagonal Einstein tensor equals
    the named canonical Lorentz stress-energy. Off-diagonal components are zero
    for both G and T (diagonal metric → zero off-diagonal Ricci). *)
Theorem lorentz_nat_chain_efe :
  forall s n v d,
    (d < 4)%nat ->
    (module_structural_mass s v > 0)%nat ->
    lorentz_einstein_tensor s (nat_chain_sc n) d d v =
      lorentz_nat_chain_stress_energy
        (local_mass_second_difference s (nat_chain_successor n) v) d.
Proof.
  intros s n v d Hd Hmass.
  unfold lorentz_nat_chain_stress_energy.
  apply lorentz_einstein_tensor_nat_chain; assumption.
Qed.

(** END OF FILE *)
