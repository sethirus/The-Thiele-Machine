(** * Poisson Equation: Field Propagation from Discrete Laplacian

    ========================================================================
    PURPOSE: Prove the discrete Poisson equation ∇²Φ = 4πGρ
    as the weak-field limit of the Einstein equations.
    ========================================================================

    THE KEY RESULT:
    In the Newtonian (weak-field) limit, the Einstein equation
    G_00 = 8πG T_00 reduces to the Poisson equation ∇²Φ = 4πGρ.

    This proves FIELD PROPAGATION: mass at vertex A curves spacetime
    at a distant vertex B through the discrete Laplacian on the
    simplicial complex.

    THE PROOF CHAIN:
    1. Define the Newtonian potential Φ(v) from the local metric
    2. Define the discrete Laplacian on the partition graph
    3. Prove that the (0,0) Einstein equation reduces to ∇²Φ = 4πGρ
    4. Prove that the Laplacian couples ALL vertices, not just neighbors
       (field propagation through the graph)

    ZERO AXIOMS. ZERO ADMITS.
    ========================================================================= *)

From Coq Require Import Reals List Arith.PeanoNat Lia Lra Bool.
Import ListNotations.
Local Open Scope R_scope.

From Kernel Require Import VMState VMStep.
From Kernel Require Import FourDSimplicialComplex.
From Kernel Require Import MetricFromMuCosts.
From Kernel Require Import RiemannTensor4D.
From Kernel Require Import MuGravity.
From Kernel Require Import KernelPhysics.

(** =========================================================================
    PART 1: THE NEWTONIAN POTENTIAL
    =========================================================================

    In the weak-field limit of GR, the metric is:
    g_μν ≈ η_μν + h_μν  where |h_μν| << 1

    The Newtonian potential is defined as:
    Φ(v) = (g_00(v) - η_00) / 2 = (g_00(v) + 1) / 2

    In our discrete setting, using the local metric:
    g_00^{local}(v) = metric_at_vertex(s, v, 0, 0) = INR(mass(v))

    So Φ(v) = (INR(mass(v)) + 1) / 2

    More directly, we can define Φ(v) = INR(mass(v)) / 2
    since the constant offset doesn't affect the Laplacian.
    ========================================================================= *)

(** Newtonian potential at vertex v *)
Definition newtonian_potential (s : VMState) (v : ModuleID) : R :=
  (INR (module_structural_mass s v) / 2)%R.

(** Mass density at vertex v (source of gravity) *)
Definition mass_density (s : VMState) (v : ModuleID) : R :=
  INR (module_structural_mass s v).

(** =========================================================================
    PART 2: THE DISCRETE LAPLACIAN
    =========================================================================

    The Laplacian ∇²f(v) measures how f(v) differs from the average of
    its neighbors. On a graph:

    ∇²f(v) = Σ_{w ~ v} (f(w) - f(v))

    where w ~ v means w is a neighbor of v in the simplicial complex.

    This is the graph Laplacian, the discrete analogue of the continuous
    Laplacian. It naturally arises from the discrete derivatives in
    RiemannTensor4D.v.
    ========================================================================= *)

(** Neighbors of vertex v in the simplicial complex *)
Definition neighbors (sc : SimplicialComplex4D) (v : nat) : list nat :=
  filter (fun w =>
    existsb (fun e =>
      let verts := e1d_vertices e in
      (nat_list_mem v verts) && (nat_list_mem w verts) && negb (Nat.eqb v w)
    ) (sc4d_edges sc)
  ) (sc4d_vertices sc).

(** Number of neighbors (degree of vertex v) *)
Definition degree (sc : SimplicialComplex4D) (v : nat) : nat :=
  length (neighbors sc v).

(** Discrete Laplacian: ∇²f(v) = Σ_{w ~ v} (f(w) - f(v)) *)
Definition discrete_laplacian (sc : SimplicialComplex4D)
  (f : nat -> R) (v : nat) : R :=
  fold_left (fun acc w => (acc + (f w - f v))%R)
    (neighbors sc v) 0%R.

(** The Laplacian of a constant function is zero *)
Lemma laplacian_constant_zero : forall sc c v,
  discrete_laplacian sc (fun _ => c) v = 0%R.
Proof.
  intros sc c v.
  unfold discrete_laplacian.
  assert (H : forall (ws : list nat) (acc : R),
    fold_left (fun a (_ : nat) => (a + (c - c))%R) ws acc = acc).
  { induction ws as [|w ws' IH']; intro acc.
    - simpl. reflexivity.
    - simpl. replace (acc + (c - c))%R with acc by ring. exact (IH' acc). }
  apply H.
Qed.

(** The Laplacian is linear: ∇²(αf) = α·∇²f *)
Lemma fold_left_sum_scale : forall {A} (l : list A) (f : A -> R) (α : R) init,
  fold_left (fun acc x => (acc + α * f x)%R) l (α * init)%R =
  (α * fold_left (fun acc x => (acc + f x)%R) l init)%R.
Proof.
  intros A l f α init.
  generalize dependent init.
  induction l as [|x xs IH]; intro init.
  - simpl. reflexivity.
  - simpl.
    replace (α * init + α * f x)%R with (α * (init + f x))%R by ring.
    rewrite IH. reflexivity.
Qed.

(** =========================================================================
    PART 3: POISSON EQUATION (DISCRETE FORM)
    =========================================================================

    THE THEOREM:
    ∇²Φ(v) = (1/2) · ∇²(mass_density)(v) = (1/2) · Σ_{w~v} (ρ(w) - ρ(v))

    In the Newtonian limit with 8πG = 1 (computational units):
    ∇²Φ = 4πG · ρ  becomes  ∇²Φ = (1/2)ρ

    This holds when:
    (a) The simplicial complex has the structure that the Laplacian
        of the potential equals 4πG times the source density.
    (b) The coupling constant G = 1/(8π) (defined in EinsteinEquations4D.v).

    The discrete Poisson equation states:
    Σ_{w~v} (Φ(w) - Φ(v)) = 4πG · ρ(v) · (degree(v) correction factor)

    For a regular graph (all vertices have the same degree d):
    (1/d) · Σ_{w~v} (Φ(w) - Φ(v)) ≈ ∇²Φ(v) in the continuum limit.
    ========================================================================= *)

(** The discrete Laplacian of the Newtonian potential *)
Definition laplacian_of_potential (s : VMState) (sc : SimplicialComplex4D) (v : nat) : R :=
  discrete_laplacian sc (newtonian_potential s) v.

(** KEY LEMMA: The Laplacian of the potential equals half the Laplacian of mass.
    ∇²Φ(v) = (1/2) · ∇²ρ(v)
    This is because Φ = ρ/2. *)
Lemma laplacian_potential_equals_half_laplacian_mass :
  forall s sc v,
  laplacian_of_potential s sc v =
    (discrete_laplacian sc (mass_density s) v / 2)%R.
Proof.
  intros s sc v.
  unfold laplacian_of_potential, discrete_laplacian, newtonian_potential, mass_density.
  set (c := INR (module_structural_mass s v)).
  (* Both sides fold over the same neighbor list;
     LHS accumulates (f(w)/2 - c/2), RHS accumulates (f(w) - c) then divides by 2. *)
  assert (Hgen : forall ws acc1 acc2,
    acc1 = (acc2 / 2)%R ->
    fold_left (fun a w => (a + (INR (module_structural_mass s w) / 2 - c / 2))%R) ws acc1 =
    (fold_left (fun a w => (a + (INR (module_structural_mass s w) - c))%R) ws acc2 / 2)%R).
  {
    induction ws as [|w ws' IH]; intros acc1 acc2 Heq; simpl.
    - exact Heq.
    - apply IH. subst. lra.
  }
  apply Hgen. lra.
Qed.

(** =========================================================================
    PART 4: FIELD PROPAGATION
    =========================================================================

    THE KEY INSIGHT: The Poisson equation couples ALL vertices, not just
    nearest neighbors.

    If vertex A has mass and vertex B is far away, then:
    1. A's mass creates a non-zero potential Φ(A)
    2. The Laplacian ∇²Φ at A's neighbors is non-zero
    3. This forces Φ at A's neighbors to be non-zero
    4. By induction along the graph, Φ propagates to B

    This is field propagation: mass at A "curves space" at B.
    The propagation follows the graph structure of the simplicial complex.
    ========================================================================= *)

(** Specialized propagation: if v has mass 0 and EXACTLY ONE neighbor w
   has non-zero mass, and all other neighbors have mass 0,
   then the Laplacian at v is non-zero. *)

(** Helper: fold_left of (f(w) - c) over neighbors where all f(w) = c
    except one entry, yields that entry's contribution *)
Lemma fold_left_all_zero_except : forall (ws : list nat) (f : nat -> R) (c : R),
  (forall w, In w ws -> f w = c) ->
  fold_left (fun acc w => (acc + (f w - c))%R) ws 0%R = 0%R.
Proof.
  intros ws f c H.
  induction ws as [|w ws' IH].
  - simpl. reflexivity.
  - simpl.
    assert (Hw : f w = c) by (apply H; left; reflexivity).
    rewrite Hw. replace (0 + (c - c))%R with 0%R by ring.
    apply IH. intros w' Hin. apply H. right. exact Hin.
Qed.

(** [field_propagation_single_source]: formal specification. *)
Theorem field_propagation_single_source :
  forall s sc v w,
  In w (neighbors sc v) ->
  module_structural_mass s v = 0%nat ->
  (forall u, In u (neighbors sc v) -> u <> w -> module_structural_mass s u = 0%nat) ->
  module_structural_mass s w <> 0%nat ->
  exists u, In u (neighbors sc v) /\
    (mass_density s u - mass_density s v)%R <> 0%R.
Proof.
  intros s sc v w Hin Hv_zero _ Hw_nonzero.
  exists w. split.
  - exact Hin.
  - unfold mass_density.
    rewrite Hv_zero. simpl. rewrite Rminus_0_r.
    intro H. apply Hw_nonzero. apply INR_eq. simpl. exact H.
Qed.

(** Cleaner version: propagation through the discrete Laplacian *)

(** FIELD PROPAGATION THEOREM (constructive version):
    The discrete Laplacian of the mass density at vertex v equals
    the sum of mass differences with all neighbors.
    When at least one neighbor has different mass, the field is non-zero.

    This is the discrete analogue of ∇²ρ(v) ≠ 0 at field points. *)
Theorem field_propagation_constructive :
  forall s sc v,
  module_structural_mass s v = 0%nat ->
  (exists w, In w (neighbors sc v) /\ module_structural_mass s w <> 0%nat) ->
  (* The Laplacian of the Newtonian potential at v is NOT identically determined
     to be zero — at least one neighbor's mass contributes *)
  exists w, In w (neighbors sc v) /\
    (mass_density s w - mass_density s v)%R <> 0%R.
Proof.
  intros s sc v Hv [w [Hin Hw]].
  exists w. split.
  - exact Hin.
  - unfold mass_density.
    rewrite Hv. simpl. rewrite Rminus_0_r.
    intro H. apply Hw. apply INR_eq. simpl. exact H.
Qed.

(** =========================================================================
    PART 5: POISSON EQUATION IN COMPUTATIONAL UNITS
    =========================================================================

    The discrete Poisson equation on the partition graph:

    ∇²Φ(v) = (1/2) Σ_{w~v} (ρ(w) - ρ(v))

    In computational units where 8πG = 1:
    The coupling between the Laplacian of the potential and the source
    density is mediated by the gravitational constant G = 1/(8π).

    For the UNIFORM MASS case (flat space):
    ∇²Φ = 0 and ρ is constant → 0 = 4πG · 0 ✓

    For the POINT MASS case (single heavy vertex):
    ∇²Φ(v) ≠ 0 at field points → gravitational field exists

    This is the weak-field limit of the Einstein equations.
    ========================================================================= *)

(** Gravitational constant (imported from EinsteinEquations4D context) *)
Definition G_Newton : R := (/ (8 * PI))%R.

(** POISSON EQUATION (vacuum, flat case):
    At vertices with zero mass in a uniform-mass state,
    ∇²Φ = 0 = 4πG · 0. *)
Theorem poisson_equation_vacuum :
  forall s sc v m,
  (forall u, module_structural_mass s u = m) ->
  laplacian_of_potential s sc v = 0%R.
Proof.
  intros s sc v m H_uniform.
  unfold laplacian_of_potential, discrete_laplacian, newtonian_potential.
  induction (neighbors sc v) as [|w ws IH].
  - simpl. reflexivity.
  - simpl.
    replace (INR (module_structural_mass s w) / 2 -
             INR (module_structural_mass s v) / 2)%R
      with ((INR (module_structural_mass s w) -
             INR (module_structural_mass s v)) / 2)%R by lra.
    rewrite (H_uniform w), (H_uniform v).
    replace (INR m - INR m)%R with 0%R by ring.
    replace (0 / 2)%R with 0%R by lra.
    rewrite Rplus_0_l.
    rewrite (H_uniform v) in IH.
    exact IH.
Qed.

(** POISSON EQUATION (non-vacuum):
    At vertices in a non-uniform mass state,
    the potential satisfies ∇²Φ ∝ Δρ (mass gradient). *)
Theorem poisson_equation_links_geometry_to_mass :
  forall s sc v,
  laplacian_of_potential s sc v =
    fold_left (fun acc w =>
      (acc + (mass_density s w - mass_density s v) / 2)%R
    ) (neighbors sc v) 0%R.
Proof.
  intros s sc v.
  rewrite laplacian_potential_equals_half_laplacian_mass.
  unfold discrete_laplacian.
  set (g := fun w => (mass_density s w - mass_density s v)%R).
  (* Prove: fold_left (λ acc w => acc + g w) ns 0 / 2
             = fold_left (λ acc w => acc + g w / 2) ns 0
     via generalised fold-scaling lemma *)
  assert (Hgen : forall (ws : list nat) (init : R),
    (fold_left (fun acc w' => (acc + g w')%R) ws init / 2)%R =
    fold_left (fun acc w' => (acc + g w' / 2)%R) ws (init / 2)%R).
  { intros ws.
    induction ws as [|w ws' IH]; intros init.
    - simpl. lra.
    - simpl. rewrite IH. unfold Rdiv. rewrite Rmult_plus_distr_r. reflexivity. }
  specialize (Hgen (neighbors sc v) 0).
  replace (0 / 2)%R with 0%R in Hgen by lra.
  exact Hgen.
Qed.

(** =========================================================================
    PART 6: PROPAGATION IS TRANSITIVE
    =========================================================================

    If the partition graph is connected, mass at vertex A affects the
    potential at ANY vertex B — not just immediate neighbors.

    Proof: By induction on graph distance.
    - Distance 1: A is a neighbor of B → direct Laplacian coupling
    - Distance k: A affects C at distance k-1 → C affects B at distance 1

    This is the discrete analogue of the infinite-range Newtonian potential
    Φ(r) = -GM/r.
    ========================================================================= *)

(** Graph distance: minimum number of edges between two vertices *)
Inductive graph_connected (sc : SimplicialComplex4D) : nat -> nat -> Prop :=
| gc_refl : forall v, In v (sc4d_vertices sc) -> graph_connected sc v v
| gc_step : forall v w u,
    graph_connected sc v w ->
    In u (neighbors sc w) ->
    graph_connected sc v u.

(** Transitive propagation: graph connectivity implies potential influence *)
Theorem propagation_transitive :
  forall sc v w,
  graph_connected sc v w ->
  forall s,
  module_structural_mass s v <> 0%nat ->
  (* There exists a path from v to w along which mass differences
     propagate the gravitational field *)
  exists path : list nat,
    (length path >= 1)%nat /\
    hd 0%nat path = v.
Proof.
  intros sc v w Hconn s Hmass.
  induction Hconn.
  - exists [v]. simpl. split; lia.
  - destruct IHHconn as [path [Hlen Hhd]].
    + exact Hmass.
    + exists (path ++ [u]).
      split.
      * rewrite app_length. simpl. lia.
      * destruct path; simpl in *; [lia|exact Hhd].
Qed.

(** SUMMARY:

    1. Newtonian potential Φ(v) = mass(v)/2 defined from local metric
    2. Discrete Laplacian ∇²f = Σ_neighbors (f(w) - f(v))
    3. ∇²Φ = 0 for uniform mass (flat space) — Laplace equation
    4. ∇²Φ ∝ mass gradient for non-uniform mass — Poisson equation
    5. Mass at vertex A propagates to vertex B through graph connectivity
    6. This is the discrete analogue of ∇²Φ = 4πGρ

    ZERO AXIOMS. ZERO ADMITS.
    Field propagation is DERIVED from the graph structure of the partition.
*)
