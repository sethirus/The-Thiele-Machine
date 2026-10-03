(** ReachableGeometry: the geometry the machine reaches.

    The curvature files (DiscreteTopology.v, MuGravity.v, DiscreteGaussBonnet.v)
    and the calibration cross-link files state their theorems for every partition graph and every
    VM state. A graph with shared addresses can be read as a surface: modules
    whose regions meet are neighbors, a module with three addresses is a
    triangle, and two triangles that share two addresses share an edge.

    The machine does not build such graphs. From a state with no modules
    ([init_state] is one), every reachable state has pairwise-disjoint module
    regions and distinct module numbers (VMStep.v, [vm_reachable_regions_disjoint]
    and [vm_step_preserves_partition_in_bounds]). This file proves what that
    leaves of the geometry.

    1. [reachable_no_adjacent_modules]: two different module numbers are never
       adjacent by region. Every module has no neighbors and lies in no
       face-graph triangle; [face_triangle_count] is 0.

    2. [reachable_flat_reading]: every module's mu-Laplacian is 0, its angle
       defect is 2 PI, and its calibration residual is 2 PI. So a reachable
       state is calibrated exactly when it has no modules
       ([reachable_calibrated_iff_no_modules]).

    3. [reachable_triangulated_isolated]: when a reachable graph also meets
       [well_formed_triangulated], it is a set of separate triangles: no
       interior edge, B = E = V = 3F, and Euler characteristic F.

    4. [reachable_triangulated_exists]: one PNEW from [init_state] reaches a
       well-formed triangulated graph (one triangle), so item 3 is not about
       an empty class.

    The theorems of the curvature and calibration cross-link files stay theorems about partition
    graphs in general. On the machine's reachable states their hypotheses of
    shared edges and calibration do not hold, by items 1 to 3. *)

From Coq Require Import List Arith.PeanoNat Lia Reals Lra ZArith Bool.
Import ListNotations.
From Kernel Require Import VMState VMStep SimulationProof MuInitiality.
From Kernel Require Import DiscreteTopology MuGravity CalibrationObstruction.

(** * Disjoint regions and distinct numbers on reachable states *)

(** The two facts this file uses about a graph. *)
Definition regions_separate (g : PartitionGraph) : Prop :=
  regions_disjoint g /\ module_ids_distinct g.

Theorem vm_reachable_regions_separate : forall s s',
  well_formed_graph s.(vm_graph) ->
  s.(vm_graph).(pg_modules) = [] ->
  s.(vm_graph).(pg_next_id) <= NUM_MODULES ->
  vm_reachable s s' ->
  regions_separate s'.(vm_graph).
Proof.
  intros s s' Hwf H0 Hn Hr.
  destruct (vm_reachable_regions_disjoint s s' H0 Hr) as [Hd _].
  split; [exact Hd|].
  assert (Hb0 : partition_in_bounds s.(vm_graph)).
  { split; [exact Hwf|]. split; [apply regions_in_memory_no_modules; exact H0|].
    split; [exact Hn|]. unfold module_ids_distinct. rewrite H0. constructor. }
  clear Hd H0 Hwf Hn.
  induction Hr as [s|s instr s1 s2 Hstep Hr IH].
  - exact (proj2 (proj2 (proj2 Hb0))).
  - apply IH. exact (vm_step_preserves_partition_in_bounds s instr s1 Hstep Hb0).
Qed.

Corollary init_reachable_regions_separate : forall s,
  vm_reachable init_state s -> regions_separate s.(vm_graph).
Proof.
  intros s Hr. apply (vm_reachable_regions_separate init_state s); try reflexivity.
  - repeat split; simpl; auto.
  - unfold NUM_MODULES. simpl. lia.
  - exact Hr.
Qed.

(** Two entries with different numbers sit at different positions, so their
    regions share no address. *)
Lemma separate_entries_disjoint : forall mods a ma b mb,
  modules_regions_disjoint mods -> NoDup (map fst mods) ->
  In (a, ma) mods -> In (b, mb) mods -> a <> b ->
  forall x, In x (module_region ma) -> ~ In x (module_region mb).
Proof.
  induction mods as [|[id m] rest IH];
    intros a ma b mb Hd Hnd Ha Hb Hab x Hxa Hxb; [destruct Ha|].
  simpl in Hd. destruct Hd as [Hf Hd].
  simpl in Hnd. inversion Hnd as [|? ? Hnotin Hnd']. subst.
  rewrite Forall_forall in Hf.
  destruct Ha as [Ha|Ha]; destruct Hb as [Hb|Hb].
  - inversion Ha. inversion Hb. subst. contradiction.
  - inversion Ha. subst. specialize (Hf (b, mb) Hb). simpl in Hf.
    exact (proj1 (nat_list_disjoint_spec _ _) Hf x Hxa Hxb).
  - inversion Hb. subst. specialize (Hf (a, ma) Ha). simpl in Hf.
    exact (proj1 (nat_list_disjoint_spec _ _) Hf x Hxb Hxa).
  - exact (IH a ma b mb Hd Hnd' Ha Hb Hab x Hxa Hxb).
Qed.

(** * 1. No adjacency, no neighbors, no face-graph triangles *)

Lemma separate_not_adjacent : forall s,
  regions_separate s.(vm_graph) ->
  forall a b, a <> b -> modules_adjacent_by_region s a b = false.
Proof.
  intros s [Hd Hnd] a b Hab. unfold modules_adjacent_by_region.
  destruct (graph_lookup (vm_graph s) a) as [ma|] eqn:Ha; [|reflexivity].
  destruct (graph_lookup (vm_graph s) b) as [mb|] eqn:Hb; [|reflexivity].
  unfold graph_lookup in Ha, Hb.
  apply graph_lookup_modules_In in Ha. apply graph_lookup_modules_In in Hb.
  assert (Hdis : nat_list_disjoint (module_region ma) (module_region mb) = true).
  { apply nat_list_disjoint_spec.
    exact (separate_entries_disjoint _ a ma b mb Hd Hnd Ha Hb Hab). }
  rewrite Hdis. reflexivity.
Qed.

Lemma filter_all_false : forall (A : Type) (f : A -> bool) (l : list A),
  (forall x, f x = false) -> filter f l = [].
Proof.
  intros A f l H. induction l as [|x l IH]; [reflexivity|].
  simpl. rewrite H. exact IH.
Qed.

Lemma separate_no_neighbors : forall s m,
  regions_separate s.(vm_graph) -> module_neighbors s m = [].
Proof.
  intros s m Hsep.
  unfold module_neighbors, module_neighbors_physical, module_neighbors_adjacent.
  apply filter_all_false. intro n.
  destruct (Nat.eqb_spec m n) as [Heq|Hne]; [reflexivity|].
  rewrite (separate_not_adjacent s Hsep m n Hne). apply andb_false_r.
Qed.

Lemma separate_no_module_triangles : forall s m,
  regions_separate s.(vm_graph) -> module_triangles s m = [].
Proof.
  intros s m Hsep. unfold module_triangles.
  rewrite (separate_no_neighbors s m Hsep). reflexivity.
Qed.

Lemma separate_face_tri_false : forall s a b c,
  regions_separate s.(vm_graph) -> face_tri s a b c = false.
Proof.
  intros s a b c Hsep. unfold face_tri.
  destruct (Nat.eqb_spec a b) as [Heq|Hne]; [reflexivity|].
  rewrite (separate_not_adjacent s Hsep a b Hne).
  destruct (a =? c), (b =? c); reflexivity.
Qed.

Lemma nsum_zero : forall (A : Type) (l : list A) (f : A -> nat),
  (forall x, f x = 0%nat) -> nsum l f = 0%nat.
Proof.
  intros A l f H. unfold nsum. induction l as [|x l IH]; [reflexivity|].
  simpl. rewrite H. exact IH.
Qed.

Lemma separate_face_triangle_count : forall s,
  regions_separate s.(vm_graph) -> face_triangle_count s = 0%nat.
Proof.
  intros s Hsep. unfold face_triangle_count.
  apply nsum_zero. intro a. apply nsum_zero. intro b. apply nsum_zero. intro c.
  rewrite (separate_face_tri_false s a b c Hsep). reflexivity.
Qed.

(** reachable_no_adjacent_modules. On every state reachable from
    [init_state]: different module numbers are not adjacent, every module
    number has no neighbors and lies in no triangle of [module_triangles],
    and the face graph has no triangle. *)
Theorem reachable_no_adjacent_modules : forall s,
  vm_reachable init_state s ->
  (forall a b, a <> b -> modules_adjacent_by_region s a b = false) /\
  (forall m, module_neighbors s m = [] /\ module_triangles s m = []) /\
  face_triangle_count s = 0%nat.
Proof.
  intros s Hr. pose proof (init_reachable_regions_separate s Hr) as Hsep.
  split; [exact (separate_not_adjacent s Hsep)|]. split.
  - intro m. split.
    + exact (separate_no_neighbors s m Hsep).
    + exact (separate_no_module_triangles s m Hsep).
  - exact (separate_face_triangle_count s Hsep).
Qed.

(** * 2. Laplacian, angle defect and calibration residual *)

Lemma separate_flat_reading : forall s m,
  regions_separate s.(vm_graph) ->
  mu_laplacian s m = 0%R /\
  angle_defect_curvature s m = (2 * PI)%R /\
  calibration_residual s m = (2 * PI)%R.
Proof.
  intros s m Hsep.
  assert (Hlap : mu_laplacian s m = 0%R).
  { unfold mu_laplacian, mu_laplacian_w.
    rewrite (separate_no_neighbors s m Hsep). reflexivity. }
  assert (Hdef : angle_defect_curvature s m = (2 * PI)%R).
  { unfold angle_defect_curvature, geometric_angle_defect.
    rewrite (separate_no_module_triangles s m Hsep). simpl. ring. }
  split; [exact Hlap|]. split; [exact Hdef|].
  unfold calibration_residual. rewrite Hlap, Hdef.
  replace (2 * PI - curvature_coupling * 0)%R with (2 * PI)%R by ring.
  apply Rabs_pos_eq. pose proof PI_RGT_0. lra.
Qed.

(** reachable_flat_reading. On every state reachable from [init_state],
    every module number has mu-Laplacian 0, angle defect 2 PI and
    calibration residual 2 PI. *)
Theorem reachable_flat_reading : forall s m,
  vm_reachable init_state s ->
  mu_laplacian s m = 0%R /\
  angle_defect_curvature s m = (2 * PI)%R /\
  calibration_residual s m = (2 * PI)%R.
Proof.
  intros s m Hr. exact (separate_flat_reading s m (init_reachable_regions_separate s Hr)).
Qed.

(** reachable_calibrated_iff_no_modules. A state reachable from
    [init_state] is calibrated ([calibrated], CalibrationObstruction.v)
    exactly when it has no modules. *)
Theorem reachable_calibrated_iff_no_modules : forall s,
  vm_reachable init_state s ->
  (calibrated s <-> pg_modules (vm_graph s) = []).
Proof.
  intros s Hr. split.
  - intro Hcal.
    destruct (pg_modules (vm_graph s)) as [|[m ms] rest] eqn:Hm; [reflexivity|].
    exfalso. specialize (Hcal m).
    rewrite Hm in Hcal. specialize (Hcal (or_introl eq_refl)).
    destruct (reachable_flat_reading s m Hr) as [_ [_ Hres]].
    rewrite Hres in Hcal. pose proof PI_RGT_0. lra.
  - intros Hnil m Hin. rewrite Hnil in Hin. destruct Hin.
Qed.

(** * 3. Reachable triangulations are separate triangles *)

Lemma edge_in_region_edges : forall e m,
  list_mem edge_eq e (module_edges m) = true -> In (fst e) (module_region m).
Proof.
  intros e m H. apply list_mem_edge_iff in H.
  exact (proj1 (region_edges_inv _ _ H)).
Qed.

Lemma count_edge_absent : forall e rest,
  (forall p, In p rest -> ~ In (fst e) (module_region (snd p))) ->
  count_modules_with_edge e rest = 0%nat.
Proof.
  intros e rest. induction rest as [|[id m] rest IH]; intro H; [reflexivity|].
  simpl. destruct (list_mem edge_eq e (module_edges m)) eqn:Hmem.
  - exfalso. apply (H (id, m) (or_introl eq_refl)). simpl.
    exact (edge_in_region_edges e m Hmem).
  - apply IH. intros p Hp. apply H. right. exact Hp.
Qed.

(** With pairwise-disjoint regions, no edge lies in two modules. *)
Lemma disjoint_count_le_1 : forall mods e,
  modules_regions_disjoint mods -> (count_modules_with_edge e mods <= 1)%nat.
Proof.
  induction mods as [|[id m] rest IH]; intros e Hd; [simpl; lia|].
  simpl in Hd. destruct Hd as [Hf Hd]. simpl.
  destruct (list_mem edge_eq e (module_edges m)) eqn:Hmem.
  - rewrite count_edge_absent; [lia|].
    intros p Hp Hin. rewrite Forall_forall in Hf. specialize (Hf p Hp).
    exact (proj1 (nat_list_disjoint_spec _ _) Hf (fst e)
             (edge_in_region_edges e m Hmem) Hin).
  - exact (IH e Hd).
Qed.

Lemma count_interior_edges_zero : forall l g,
  (forall e, (count_modules_with_edge e (pg_modules g) <= 1)%nat) ->
  count_interior_edges l g = 0%nat.
Proof.
  intros l g H. induction l as [|e l IH]; [reflexivity|].
  simpl. unfold is_interior_edge.
  destruct (Nat.eqb_spec (count_modules_with_edge e (pg_modules g)) 2) as [Heq|_].
  - specialize (H e). lia.
  - exact IH.
Qed.

Lemma separate_triangulated_isolated : forall g,
  regions_disjoint g ->
  well_formed_triangulated g ->
  DiscreteTopology.I g = 0%nat /\
  DiscreteTopology.B g = (3 * DiscreteTopology.F g)%nat /\
  DiscreteTopology.E g = (3 * DiscreteTopology.F g)%nat /\
  DiscreteTopology.V g = (3 * DiscreteTopology.F g)%nat /\
  euler_characteristic g = Z.of_nat (DiscreteTopology.F g).
Proof.
  intros g Hd Hwf.
  assert (HI : DiscreteTopology.I g = 0%nat).
  { unfold DiscreteTopology.I. apply count_interior_edges_zero.
    intro e. exact (disjoint_count_le_1 _ e Hd). }
  pose proof (total_edges_eq_interior_plus_boundary g Hwf) as HEIB.
  pose proof (edge_face_incidence_equation g Hwf) as H3F.
  destruct Hwf as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hge HB]]]]]]]]]].
  assert (HB3 : DiscreteTopology.B g = (3 * DiscreteTopology.F g)%nat) by lia.
  assert (HE3 : DiscreteTopology.E g = (3 * DiscreteTopology.F g)%nat) by lia.
  assert (HV3 : DiscreteTopology.V g = (3 * DiscreteTopology.F g)%nat) by lia.
  split; [exact HI|]. split; [exact HB3|]. split; [exact HE3|].
  split; [exact HV3|].
  unfold euler_characteristic. rewrite HE3, HV3. lia.
Qed.

(** reachable_triangulated_isolated. A state reachable from [init_state]
    whose graph meets [well_formed_triangulated] has no interior edge, and
    B = E = V = 3F with Euler characteristic F: the faces are separate
    triangles. *)
Theorem reachable_triangulated_isolated : forall s,
  vm_reachable init_state s ->
  well_formed_triangulated (vm_graph s) ->
  DiscreteTopology.I (vm_graph s) = 0%nat /\
  DiscreteTopology.B (vm_graph s) = (3 * DiscreteTopology.F (vm_graph s))%nat /\
  DiscreteTopology.E (vm_graph s) = (3 * DiscreteTopology.F (vm_graph s))%nat /\
  DiscreteTopology.V (vm_graph s) = (3 * DiscreteTopology.F (vm_graph s))%nat /\
  euler_characteristic (vm_graph s) = Z.of_nat (DiscreteTopology.F (vm_graph s)).
Proof.
  intros s Hr Hwf.
  exact (separate_triangulated_isolated _
           (proj1 (init_reachable_regions_separate s Hr)) Hwf).
Qed.

(** * 4. A reachable well-formed triangulated state *)

Definition one_triangle_step : vm_instruction := instr_pnew [0; 1; 2] 0.

Definition one_triangle_state : VMState := vm_apply init_state one_triangle_step.

Lemma one_triangle_graph :
  vm_graph one_triangle_state =
  {| pg_next_id := 1;
     pg_modules := [(0, mk_module_state [0; 1; 2] [])];
     pg_next_morph_id := 1;
     pg_morphisms := [] |}.
Proof. vm_compute. reflexivity. Qed.

Theorem reachable_triangulated_exists :
  vm_reachable init_state one_triangle_state /\
  well_formed_triangulated (vm_graph one_triangle_state) /\
  DiscreteTopology.F (vm_graph one_triangle_state) = 1%nat /\
  euler_characteristic (vm_graph one_triangle_state) = 1%Z.
Proof.
  split.
  - apply (vm_reachable_step init_state one_triangle_step one_triangle_state
             one_triangle_state).
    + unfold one_triangle_state, one_triangle_step, vm_apply.
      apply step_pnew. reflexivity.
    + apply vm_reachable_refl.
  - rewrite one_triangle_graph. split; [|split].
    + unfold well_formed_triangulated.
      split; [repeat split; simpl; auto; lia|].
      split; [intros mid m Hin; destruct Hin as [Hin|[]]; inversion Hin; subst;
              reflexivity|].
      split; [intros mid m Hin; destruct Hin as [Hin|[]]; inversion Hin; subst;
              reflexivity|].
      split; [intros e He; vm_compute in He;
              destruct He as [He|[He|[He|[]]]]; subst; left; reflexivity|].
      vm_compute. repeat split; lia.
    + reflexivity.
    + reflexivity.
Qed.

Print Assumptions reachable_no_adjacent_modules.
Print Assumptions reachable_calibrated_iff_no_modules.
Print Assumptions reachable_triangulated_isolated.
Print Assumptions reachable_triangulated_exists.
