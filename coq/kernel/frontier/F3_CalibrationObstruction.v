(** F3_CalibrationObstruction: what calibration at every module forces on a
    well-formed triangulated state, and the cases in which it is impossible.

    Setting (MuGravity.v). calibration_residual s m is
    |angle_defect_curvature s m - PI * mu_laplacian s m|, the angle defect is
    2 PI minus the sum of triangle_angle over module_triangles s m, and
    triangle_angle s a b c = PI * d(b,c) / (1 + d(a,b) + d(a,c) + d(b,c))
    with d = mu_module_distance. well_formed_triangulated is from
    DiscreteTopology.v. Below, "calibrated" means
    forall m, In m (map fst (pg_modules (vm_graph s))) ->
              calibration_residual s m = 0,
    F is the number of modules, B the number of boundary edges, and T the
    number of face-graph triangles (unordered triples of distinct module IDs
    whose regions pairwise meet), face_triangle_count.

    Proved here.

    1. F3_calibration_forces_flat_faces (needs only that regions are
       normalized triangles). Calibrated implies every mu_laplacian is 0 and
       every face is flat (angle sum 2 PI). Each region has 3 nodes and each
       axiom costs 8 bits per character, so every density is 3 plus a
       multiple of 8 and every mu-Laplacian lies in 8Z. Calibration gives
       Laplacian = 2 - (angle sum)/PI <= 2, hence <= 0, and the proved
       identity total_mu_laplacian_zero forces every term to be 0.

    2. F3_calibration_forces_five_triangles. Every angle is below PI/2, so a
       flat face lies in at least 5 face-graph triangles.

    3. total_angle_sum_identity (unconditional). The sum over modules of the
       angle sums equals PI/6 times the sum, over ordered triples of
       distinct pairwise adjacent modules, of P/(1+P), P the perimeter.

    4. F3_calibration_window. Calibrated implies 2F < T and 21 T <= 44 F,
       hence F >= 11. The +1 in the angle denominator makes each triple
       weigh strictly less than 1, and P >= 21 makes it weigh at least 21/22.

    5. F3_vertex_triangle_bound. With distinct module IDs and is_2_manifold,
       sum over vertices of d (d - 1) (d - 2) <= 6 T: three faces through a
       vertex form a face-graph triangle, and three distinct faces cannot
       share two vertices (that edge would lie in three faces).

    6. F3_calibration_consequences, F3_calibration_forces_degree_inequality
       (21 * sum_v d(d-1)(d-2) <= 88 * sum_v d) and
       F3_calibration_forces_large_boundary (61 F <= 140 B).

    7. Closed obstructions, with distinct module IDs:
       F3_calibration_obstruction_closed (no boundary edge, B = 0) and
       F3_calibration_obstruction_min_degree4 (every vertex in at least
       four faces).

    8. F3_degree_route_insufficient and F3_om_not_calibrated. A concrete
       well-formed triangulated state with distinct IDs (an octahedron next
       to a zigzag triangulation of a 9-gon; every vertex link is connected)
       satisfies the degree inequality and the boundary bound of item 6.
       There sum_v C(d_v, 3) = 29 is below (44/21) F = 31.4, so the claim
       that this vertex count exceeds the window for every admissible
       topology is false once a closed component sits next to a disk. The
       state is still excluded, by the full count T = 37 > 31.4.

    9. euler_component. For an edge-connected list of triangles in which
       every edge lies in one or two faces, V + F <= E + 2, and
       V + F <= E + 1 when some edge is a boundary edge. The faces are
       placed one at a time, each attached along an edge to an earlier one
       (euler_inv); the edges other than these F - 1 attaching edges still
       connect all vertices, so they number at least V - 1. With a boundary
       edge b, either they stay connected after deleting b (one more edge),
       or deleting b separates its two ends; then the number of face edges
       crossing that cut is even face by face but odd in total, since b is
       counted once and every attaching edge twice.

    10. F3_calibration_obstruction, the full target:
          forall s, well_formed_triangulated (vm_graph s) ->
            links_connected s -> NoDup (module IDs) -> ~ calibrated s.
       links_connected says the link of every vertex is a connected graph
       (on a 2-manifold, a path or a cycle). Then faces sharing a vertex are
       joined by faces sharing edges (adj_share_closure), so each component
       under vertex adjacency is edge-connected. Calibration restricts to
       each component (residual_restrict), so each component satisfies the
       window of item 4, the vertex bound of item 5 and the Euler bound of
       item 9. Per component, 21 T <= 44 F and 6 T >= sum d(d-1)(d-2)
       >= 54 F - 48 V give 145 F <= 168 V; with 2E = 3F + B
       (edges_faces_boundary) this forces F <= 5 when B = 0, against
       F >= 11, and B >= 6 > 3 chi when B >= 1 (component_inequality).
       V, E, F and B add over components (restrict_union), so B > 3 chi
       for the whole state (components_sum), against B = 3 chi in
       well_formed_triangulated. In the state of item 8 the octahedron is
       a component by itself with F = 8 < 11, so the per-component window
       already excludes it; no count of face-graph triangles without a
       common vertex is needed.
       The hypothesis (exists m, module_triangles s m <> []) of the
       original target is not needed: 1 <= F comes with
       well_formed_triangulated.

    11. F3_obstruction_hypotheses_satisfiable. The state of item 8 meets
       every hypothesis of item 10 (om_links_connected checks its links),
       so the theorem is not vacuous.

    Items 1 to 4 do not use distinct module IDs. No axioms are added; the
    Reals-based statements depend only on the standard axioms of Coq's
    real numbers (see the Print Assumptions block at the end). *)

From Coq Require Import List Arith.PeanoNat Lia Reals Lra ZArith Bool.
From Coq Require String.
Import ListNotations.
From Kernel Require Import VMState VMStep DiscreteTopology MuGravity F3_MuLaplacianSum.

(** * Part 0. Finite sums over lists. *)

Definition lsum {A : Type} (l : list A) (f : A -> R) : R :=
  fold_right Rplus 0%R (map f l).

Lemma lsum_nil : forall (A : Type) (f : A -> R), lsum [] f = 0%R.
Proof. reflexivity. Qed.

Lemma lsum_cons : forall (A : Type) (x : A) (l : list A) (f : A -> R),
  lsum (x :: l) f = (f x + lsum l f)%R.
Proof. reflexivity. Qed.

Lemma lsum_ext_in : forall (A : Type) (l : list A) (f g : A -> R),
  (forall x, In x l -> f x = g x) -> lsum l f = lsum l g.
Proof.
  intros A l f g H. induction l as [|x l IH]; [reflexivity|].
  rewrite !lsum_cons. rewrite (H x (or_introl eq_refl)).
  rewrite IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma lsum_ext : forall (A : Type) (l : list A) (f g : A -> R),
  (forall x, f x = g x) -> lsum l f = lsum l g.
Proof. intros A l f g H. apply lsum_ext_in. intros x _. apply H. Qed.

Lemma lsum_plus : forall (A : Type) (l : list A) (f g : A -> R),
  lsum l (fun x => (f x + g x)%R) = (lsum l f + lsum l g)%R.
Proof.
  intros A l f g. induction l as [|x l IH]; [unfold lsum; simpl; lra|].
  rewrite !lsum_cons, IH. lra.
Qed.

Lemma lsum_scal : forall (A : Type) (l : list A) (c : R) (f : A -> R),
  lsum l (fun x => (c * f x)%R) = (c * lsum l f)%R.
Proof.
  intros A l c f. induction l as [|x l IH]; [unfold lsum; simpl; lra|].
  rewrite !lsum_cons, IH. lra.
Qed.

Lemma lsum_const : forall (A : Type) (l : list A) (c : R),
  lsum l (fun _ => c) = (INR (List.length l) * c)%R.
Proof.
  intros A l c. induction l as [|x l IH]; [unfold lsum; simpl; lra|].
  rewrite lsum_cons, IH. cbn [List.length]. rewrite S_INR. lra.
Qed.

Lemma lsum_le_in : forall (A : Type) (l : list A) (f g : A -> R),
  (forall x, In x l -> f x <= g x)%R -> (lsum l f <= lsum l g)%R.
Proof.
  intros A l f g H. induction l as [|x l IH]; [unfold lsum; simpl; lra|].
  rewrite !lsum_cons.
  assert (Hx := H x (or_introl eq_refl)).
  assert (Hl : (lsum l f <= lsum l g)%R).
  { apply IH. intros y Hy. apply H. right. exact Hy. }
  lra.
Qed.

Lemma lsum_nonneg_in : forall (A : Type) (l : list A) (f : A -> R),
  (forall x, In x l -> 0 <= f x)%R -> (0 <= lsum l f)%R.
Proof.
  intros A l f H.
  replace 0%R with (lsum l (fun _ => 0%R)) by (rewrite lsum_const; lra).
  apply lsum_le_in. exact H.
Qed.

Lemma lsum_pos : forall (A : Type) (l : list A) (f : A -> R) (y : A),
  (forall x, In x l -> 0 <= f x)%R -> In y l -> (0 < f y)%R -> (0 < lsum l f)%R.
Proof.
  intros A l f y H Hy Hpos. induction l as [|x l IH]; [destruct Hy|].
  rewrite lsum_cons. destruct Hy as [Hxy|Hy].
  - subst x.
    assert (0 <= lsum l f)%R.
    { apply lsum_nonneg_in. intros z Hz. apply H. right. exact Hz. }
    lra.
  - assert (0 <= f x)%R by (apply H; left; reflexivity).
    assert (0 < lsum l f)%R.
    { apply IH; [intros z Hz; apply H; right; exact Hz|exact Hy]. }
    lra.
Qed.

Lemma lsum_pos_exists : forall (A : Type) (l : list A) (f : A -> R),
  (0 < lsum l f)%R -> exists x, In x l /\ (0 < f x)%R.
Proof.
  intros A l f H. induction l as [|x l IH].
  - unfold lsum in H. simpl in H. lra.
  - rewrite lsum_cons in H. destruct (Rlt_le_dec 0 (f x)) as [Hx|Hx].
    + exists x. split; [left; reflexivity|exact Hx].
    + destruct IH as [y [Hy Hfy]]; [lra|]. exists y. split; [right; exact Hy|exact Hfy].
Qed.

Lemma lsum_app : forall (A : Type) (l1 l2 : list A) (f : A -> R),
  lsum (l1 ++ l2) f = (lsum l1 f + lsum l2 f)%R.
Proof.
  intros A l1 l2 f. induction l1 as [|x l1 IH]; [unfold lsum; simpl; lra|].
  simpl. rewrite !lsum_cons, IH. lra.
Qed.

Lemma lsum_map : forall (A B : Type) (g : A -> B) (l : list A) (f : B -> R),
  lsum (map g l) f = lsum l (fun x => f (g x)).
Proof. intros A B g l f. unfold lsum. rewrite map_map. reflexivity. Qed.

Lemma lsum_flat_map : forall (A B : Type) (g : A -> list B) (l : list A) (f : B -> R),
  lsum (flat_map g l) f = lsum l (fun x => lsum (g x) f).
Proof.
  intros A B g l f. induction l as [|x l IH]; [reflexivity|].
  simpl. rewrite lsum_app, lsum_cons, IH. reflexivity.
Qed.

Lemma lsum_filter : forall (A : Type) (p : A -> bool) (l : list A) (f : A -> R),
  lsum (filter p l) f = lsum l (fun x => if p x then f x else 0%R).
Proof.
  intros A p l f. induction l as [|x l IH]; [reflexivity|].
  cbn [filter]. rewrite (lsum_cons _ x l). cbv beta.
  destruct (p x); [rewrite lsum_cons|]; rewrite IH; cbv beta iota; lra.
Qed.

Lemma lsum_swap : forall (A B : Type) (l1 : list A) (l2 : list B) (f : A -> B -> R),
  lsum l1 (fun a => lsum l2 (fun b => f a b)) =
  lsum l2 (fun b => lsum l1 (fun a => f a b)).
Proof.
  intros A B l1 l2 f. induction l1 as [|x l1 IH].
  - rewrite lsum_nil. rewrite (lsum_ext _ l2 _ (fun _ => 0%R)) by reflexivity.
    rewrite lsum_const. lra.
  - rewrite lsum_cons, IH.
    rewrite (lsum_ext _ l2 (fun b => lsum (x :: l1) (fun a => f a b))
                       (fun b => (f x b + lsum l1 (fun a => f a b))%R))
      by (intro b; reflexivity).
    rewrite lsum_plus. reflexivity.
Qed.

Lemma if_lsum : forall (A : Type) (bb : bool) (l : list A) (f : A -> R),
  (if bb then lsum l f else 0%R) = lsum l (fun x => if bb then f x else 0%R).
Proof.
  intros A bb l f. destruct bb; [reflexivity|].
  rewrite lsum_const. lra.
Qed.

(** Finite sums of natural numbers, and their cast to the reals. *)

Definition nsum {A : Type} (l : list A) (f : A -> nat) : nat :=
  fold_right Nat.add 0%nat (map f l).

Lemma INR_nsum : forall (A : Type) (l : list A) (f : A -> nat),
  INR (nsum l f) = lsum l (fun x => INR (f x)).
Proof.
  intros A l f. induction l as [|x l IH]; [reflexivity|].
  unfold nsum in *. simpl. rewrite plus_INR, IH. reflexivity.
Qed.

(** Indicator of a boolean, as a real number. *)
Definition ind (b : bool) : R := if b then 1%R else 0%R.

Lemma ind_nonneg : forall b, (0 <= ind b)%R.
Proof. destruct b; simpl; lra. Qed.

(** * Part 1. Regions of three nodes and the mu-Laplacian in 8Z. *)

Definition regions_are_triples (g : PartitionGraph) : Prop :=
  forall mid m, In (mid, m) (pg_modules g) -> List.length (module_region m) = 3%nat.

Lemma triangulated_regions_are_triples : forall g,
  all_modules_are_triangles_list g ->
  all_regions_normalized_list g ->
  regions_are_triples g.
Proof.
  intros g Htri Hnorm mid m Hin.
  specialize (Htri mid m Hin). specialize (Hnorm mid m Hin).
  unfold is_triangle in Htri. apply Nat.eqb_eq in Htri.
  rewrite Hnorm. exact Htri.
Qed.

Lemma graph_lookup_modules_In : forall mods mid ms,
  graph_lookup_modules mods mid = Some ms -> In (mid, ms) mods.
Proof.
  induction mods as [|[id m] rest IH]; simpl; intros mid ms H; [discriminate|].
  destruct (Nat.eqb_spec id mid) as [Heq|Hneq].
  - inversion H. subst. left. reflexivity.
  - right. apply IH. exact H.
Qed.

Lemma graph_lookup_modules_some : forall mods mid,
  In mid (map fst mods) -> exists ms, graph_lookup_modules mods mid = Some ms.
Proof.
  induction mods as [|[id m] rest IH]; simpl; intros mid H; [destruct H|].
  destruct (Nat.eqb_spec id mid) as [Heq|Hneq].
  - exists m. reflexivity.
  - destruct H as [H|H]; [contradiction|]. apply IH. exact H.
Qed.

Lemma graph_lookup_modules_nodup : forall mods mid ms,
  NoDup (map fst mods) -> In (mid, ms) mods -> graph_lookup_modules mods mid = Some ms.
Proof.
  induction mods as [|[id m] rest IH]; simpl; intros mid ms Hnd Hin; [destruct Hin|].
  inversion Hnd as [|x xs Hnotin Hnd' Hxs]. subst.
  destruct (Nat.eqb_spec id mid) as [Heq|Hneq].
  - subst id. destruct Hin as [Hin|Hin].
    + inversion Hin. reflexivity.
    + exfalso. apply Hnotin. change mid with (fst (mid, ms)). apply in_map. exact Hin.
  - destruct Hin as [Hin|Hin].
    + inversion Hin. contradiction.
    + apply IH; assumption.
Qed.

Lemma adjacent_lookup_l : forall s m n,
  modules_adjacent_by_region s m n = true ->
  exists ms, graph_lookup (vm_graph s) m = Some ms.
Proof.
  unfold modules_adjacent_by_region. intros s m n H.
  destruct (graph_lookup (vm_graph s) m) as [ms|]; [eauto|discriminate].
Qed.

Lemma adjacent_lookup_r : forall s m n,
  modules_adjacent_by_region s m n = true ->
  exists ms, graph_lookup (vm_graph s) n = Some ms.
Proof.
  intros s m n H. rewrite modules_adjacent_by_region_sym in H.
  eapply adjacent_lookup_l. exact H.
Qed.

Lemma lookup_region3 : forall s n ms,
  regions_are_triples (vm_graph s) ->
  graph_lookup (vm_graph s) n = Some ms ->
  List.length (module_region ms) = 3%nat.
Proof.
  intros s n ms H3 Hl. apply (H3 n). apply graph_lookup_modules_In. exact Hl.
Qed.

Lemma fold_encoding_mult8 : forall axs acc,
  exists k, fold_left (fun acc ax => (acc + axiom_encoding_length ax)%nat) axs acc
            = (acc + 8 * k)%nat.
Proof.
  induction axs as [|ax axs IH]; intros acc; simpl.
  - exists 0%nat. lia.
  - destruct (IH (acc + axiom_encoding_length ax)%nat) as [k Hk].
    exists (String.length ax + k)%nat. rewrite Hk.
    unfold axiom_encoding_length. rewrite payload_bit_length_ascii. lia.
Qed.

(** Each region has 3 nodes and each axiom has 8 bits per character, so
    every density is 3 more than a multiple of 8. *)
Lemma density_form : forall s n ms,
  graph_lookup (vm_graph s) n = Some ms ->
  List.length (module_region ms) = 3%nat ->
  exists k, mu_cost_density s n = (8 * INR k + 3)%R.
Proof.
  intros s n ms Hl H3.
  unfold mu_cost_density, module_encoding_length, module_region_size.
  rewrite Hl. destruct (fold_encoding_mult8 (module_axioms ms) 0) as [k Hk].
  rewrite Hk, H3. exists k.
  replace (0 + 8 * k + 3)%nat with (8 * k + 3)%nat by lia.
  rewrite plus_INR, mult_INR. simpl. lra.
Qed.

Lemma lap_fold_mult8 : forall s m km,
  regions_are_triples (vm_graph s) ->
  mu_cost_density s m = (8 * INR km + 3)%R ->
  forall l acc, exists z,
    fold_left (fun acc n => (acc + edge_weight s m n * mu_gradient s m n)%R) l acc
    = (acc + 8 * IZR z)%R.
Proof.
  intros s m km H3 Hm l. induction l as [|n l IH]; intros acc; simpl.
  - exists 0%Z. simpl. lra.
  - destruct (IH (acc + edge_weight s m n * mu_gradient s m n)%R) as [z Hz].
    rewrite Hz. unfold edge_weight.
    destruct (modules_adjacent_by_region s m n) eqn:Hadj.
    + destruct (adjacent_lookup_r s m n Hadj) as [ms Hms].
      destruct (density_form s n ms Hms (lookup_region3 s n ms H3 Hms)) as [kn Hkn].
      exists (z + Z.of_nat kn - Z.of_nat km)%Z.
      unfold mu_gradient. rewrite Hkn, Hm.
      rewrite minus_IZR, plus_IZR, <- !INR_IZR_INZ. lra.
    + exists z. lra.
Qed.

Lemma mu_laplacian_mult8 : forall s m,
  regions_are_triples (vm_graph s) ->
  In m (map fst (pg_modules (vm_graph s))) ->
  exists z, mu_laplacian s m = (8 * IZR z)%R.
Proof.
  intros s m H3 Hin.
  destruct (graph_lookup_modules_some _ _ Hin) as [ms Hms].
  assert (Hl : graph_lookup (vm_graph s) m = Some ms) by exact Hms.
  destruct (density_form s m ms Hl (lookup_region3 s m ms H3 Hl)) as [km Hkm].
  destruct (lap_fold_mult8 s m km H3 Hkm (module_neighbors s m) 0%R) as [z Hz].
  exists z. unfold mu_laplacian, mu_laplacian_w. rewrite Hz. lra.
Qed.

(** * Part 2. Angles. *)

Lemma triangle_angle_nonneg : forall s a b c, (0 <= triangle_angle s a b c)%R.
Proof.
  intros s a b c. unfold triangle_angle, dist_to_R.
  destruct (_ || _)%bool; [lra|].
  unfold Rdiv. apply Rmult_le_pos.
  - apply Rmult_le_pos; [left; exact PI_RGT_0|apply pos_INR].
  - left. apply Rinv_0_lt_compat. apply lt_0_INR. lia.
Qed.

Lemma sum_angles_nonneg : forall s m l, (0 <= sum_angles s m l)%R.
Proof.
  intros s m l. induction l as [|[n1 n2] l IH]; simpl; [lra|].
  pose proof (triangle_angle_nonneg s m n1 n2). lra.
Qed.

Lemma triangle_angle_lt_half_pi : forall s a b c, (triangle_angle s a b c < PI / 2)%R.
Proof.
  intros s a b c. pose proof PI_RGT_0 as Hpi.
  unfold triangle_angle, dist_to_R.
  destruct (_ || _)%bool; [lra|].
  pose proof (mu_module_distance_triangle s b a c) as Htri.
  rewrite (mu_module_distance_sym s b a) in Htri.
  set (dab := mu_module_distance s a b) in *.
  set (dac := mu_module_distance s a c) in *.
  set (dbc := mu_module_distance s b c) in *.
  assert (Hy : (0 < INR (S (dab + dac + dbc)))%R) by (apply lt_0_INR; lia).
  assert (H2 : (2 * INR dbc < INR (S (dab + dac + dbc)))%R).
  { replace (2 * INR dbc)%R with (INR (2 * dbc)) by (rewrite mult_INR; simpl; lra).
    apply lt_INR. lia. }
  assert (Hdiff : (PI / 2 - PI * INR dbc / INR (S (dab + dac + dbc)) =
                   PI * (INR (S (dab + dac + dbc)) - 2 * INR dbc)
                     * / (2 * INR (S (dab + dac + dbc))))%R)
    by (field; lra).
  assert (0 < PI * (INR (S (dab + dac + dbc)) - 2 * INR dbc)
                 * / (2 * INR (S (dab + dac + dbc))))%R.
  { apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; lra|].
    apply Rinv_0_lt_compat. lra. }
  lra.
Qed.

Lemma sum_angles_le : forall s m l,
  (sum_angles s m l <= INR (List.length l) * (PI / 2))%R.
Proof.
  intros s m l. induction l as [|[n1 n2] l IH]; simpl sum_angles; [simpl; lra|].
  cbn [List.length]. rewrite S_INR.
  pose proof (triangle_angle_lt_half_pi s m n1 n2). lra.
Qed.

Lemma sum_angles_lt : forall s m l, l <> [] ->
  (sum_angles s m l < INR (List.length l) * (PI / 2))%R.
Proof.
  intros s m l Hne. destruct l as [|[n1 n2] l]; [contradiction|].
  simpl sum_angles. cbn [List.length]. rewrite S_INR.
  pose proof (triangle_angle_lt_half_pi s m n1 n2).
  pose proof (sum_angles_le s m l). lra.
Qed.

(** Calibration at one module, with all regions of three nodes, forces a
    non-positive mu-Laplacian there. *)
Lemma calibrated_lap_nonpos : forall s m,
  regions_are_triples (vm_graph s) ->
  In m (map fst (pg_modules (vm_graph s))) ->
  calibration_residual s m = 0%R ->
  (mu_laplacian s m <= 0)%R.
Proof.
  intros s m H3 Hin Hcal.
  apply calibration_residual_zero_iff in Hcal.
  unfold angle_defect_curvature, geometric_angle_defect, curvature_coupling in Hcal.
  pose proof (sum_angles_nonneg s m (module_triangles s m)) as Hsa.
  pose proof PI_RGT_0 as Hpi.
  destruct (mu_laplacian_mult8 s m H3 Hin) as [z Hz].
  rewrite Hz in Hcal |- *.
  assert (Hle : (PI * (8 * IZR z - 2) <= 0)%R) by lra.
  assert (Hz2 : (8 * IZR z - 2 <= 0)%R).
  { destruct (Rle_dec (8 * IZR z - 2) 0) as [H|H]; [exact H|].
    apply Rnot_le_lt in H.
    assert (0 < PI * (8 * IZR z - 2))%R by (apply Rmult_lt_0_compat; lra).
    lra. }
  assert (Hzle : (z <= 0)%Z).
  { destruct (Z_le_gt_dec z 0) as [H|H]; [exact H|].
    assert (H1 : (1 <= IZR z)%R) by (apply IZR_le; lia). lra. }
  apply IZR_le in Hzle. lra.
Qed.

Lemma fold_sum_nonpos : forall (f : nat -> R) l,
  (forall x, In x l -> f x <= 0)%R -> (fold_right Rplus 0%R (map f l) <= 0)%R.
Proof.
  intros f l H. induction l as [|x l IH]; simpl; [lra|].
  assert (f x <= 0)%R by (apply H; left; reflexivity).
  assert (fold_right Rplus 0%R (map f l) <= 0)%R.
  { apply IH. intros y Hy. apply H. right. exact Hy. }
  lra.
Qed.

Lemma fold_sum_nonpos_zero : forall (f : nat -> R) l,
  fold_right Rplus 0%R (map f l) = 0%R ->
  (forall x, In x l -> f x <= 0)%R ->
  forall x, In x l -> f x = 0%R.
Proof.
  intros f l. induction l as [|y l IH]; simpl; intros Hsum Hle x Hx; [destruct Hx|].
  assert (Hy : (f y <= 0)%R) by (apply Hle; left; reflexivity).
  assert (Hrest : (fold_right Rplus 0%R (map f l) <= 0)%R).
  { apply fold_sum_nonpos. intros z Hz. apply Hle. right. exact Hz. }
  destruct Hx as [Hx|Hx].
  - subst. lra.
  - apply IH; [lra| |exact Hx]. intros z Hz. apply Hle. right. exact Hz.
Qed.

(** Calibration at every module forces every face to be flat. *)
Theorem F3_calibration_forces_flat_faces : forall s,
  all_modules_are_triangles_list (vm_graph s) ->
  all_regions_normalized_list (vm_graph s) ->
  (forall m, In m (map fst (pg_modules (vm_graph s))) ->
             calibration_residual s m = 0%R) ->
  forall m, In m (map fst (pg_modules (vm_graph s))) ->
    mu_laplacian s m = 0%R /\
    angle_defect_curvature s m = 0%R /\
    sum_angles s m (module_triangles s m) = (2 * PI)%R.
Proof.
  intros s Htri Hnorm Hcal m Hin.
  pose proof (triangulated_regions_are_triples _ Htri Hnorm) as H3.
  assert (Hlap : mu_laplacian s m = 0%R).
  { apply (fold_sum_nonpos_zero (mu_laplacian s) (map fst (pg_modules (vm_graph s)))).
    - apply total_mu_laplacian_zero.
    - intros x Hx. apply calibrated_lap_nonpos; auto.
    - exact Hin. }
  pose proof (Hcal m Hin) as Hm.
  apply calibration_residual_zero_iff in Hm.
  rewrite Hlap in Hm.
  split; [exact Hlap|]. split.
  - rewrite Hm. lra.
  - unfold angle_defect_curvature, geometric_angle_defect in Hm. lra.
Qed.

(** A flat face has at least five triangles through it: each angle is
    below pi/2. *)
Theorem F3_calibration_forces_five_triangles : forall s,
  all_modules_are_triangles_list (vm_graph s) ->
  all_regions_normalized_list (vm_graph s) ->
  (forall m, In m (map fst (pg_modules (vm_graph s))) ->
             calibration_residual s m = 0%R) ->
  forall m, In m (map fst (pg_modules (vm_graph s))) ->
    (5 <= List.length (module_triangles s m))%nat.
Proof.
  intros s Htri Hnorm Hcal m Hin.
  destruct (F3_calibration_forces_flat_faces s Htri Hnorm Hcal m Hin) as [_ [_ Hsa]].
  pose proof PI_RGT_0 as Hpi.
  destruct (le_lt_dec 5 (List.length (module_triangles s m))) as [H|H]; [exact H|].
  exfalso.
  destruct (module_triangles s m) as [|p l] eqn:Ht.
  - simpl in Hsa. lra.
  - assert (Hne : p :: l <> []) by discriminate.
    pose proof (sum_angles_lt s m (p :: l) Hne) as Hlt.
    assert (Hlen : (INR (List.length (p :: l)) <= 4)%R).
    { replace 4%R with (INR 4) by (simpl; lra). apply le_INR. lia. }
    assert (INR (List.length (p :: l)) * (PI / 2) <= 4 * (PI / 2))%R.
    { apply Rmult_le_compat_r; lra. }
    lra.
Qed.

(** * Part 3. Triple sums over module identifiers. *)

Definition tsum (l : list nat) (f : nat -> nat -> nat -> R) : R :=
  lsum l (fun a => lsum l (fun b => lsum l (fun c => f a b c))).

Lemma tsum_ext_in : forall l f g,
  (forall a b c, In a l -> In b l -> In c l -> f a b c = g a b c) ->
  tsum l f = tsum l g.
Proof.
  intros l f g H. unfold tsum.
  apply lsum_ext_in. intros a Ha. apply lsum_ext_in. intros b Hb.
  apply lsum_ext_in. intros c Hc. apply H; assumption.
Qed.

Lemma tsum_ext : forall l f g,
  (forall a b c, f a b c = g a b c) -> tsum l f = tsum l g.
Proof. intros l f g H. apply tsum_ext_in. intros. apply H. Qed.

Lemma tsum_plus : forall l f g,
  tsum l (fun a b c => (f a b c + g a b c)%R) = (tsum l f + tsum l g)%R.
Proof.
  intros l f g. unfold tsum. rewrite <- lsum_plus. apply lsum_ext. intro a.
  rewrite <- lsum_plus. apply lsum_ext. intro b. apply lsum_plus.
Qed.

Lemma tsum_scal : forall l k f,
  tsum l (fun a b c => (k * f a b c)%R) = (k * tsum l f)%R.
Proof.
  intros l k f. unfold tsum. rewrite <- lsum_scal. apply lsum_ext. intro a.
  rewrite <- lsum_scal. apply lsum_ext. intro b. apply lsum_scal.
Qed.

Lemma tsum_le_in : forall l f g,
  (forall a b c, In a l -> In b l -> In c l -> f a b c <= g a b c)%R ->
  (tsum l f <= tsum l g)%R.
Proof.
  intros l f g H. unfold tsum.
  apply lsum_le_in. intros a Ha. apply lsum_le_in. intros b Hb.
  apply lsum_le_in. intros c Hc. apply H; assumption.
Qed.

Lemma tsum_swap23 : forall l f, tsum l f = tsum l (fun a b c => f a c b).
Proof.
  intros l f. unfold tsum. apply lsum_ext. intro a.
  apply (lsum_swap _ _ l l (fun b c => f a b c)).
Qed.

Lemma tsum_swap12 : forall l f, tsum l f = tsum l (fun a b c => f b a c).
Proof.
  intros l f. unfold tsum.
  apply (lsum_swap _ _ l l (fun a b => lsum l (fun c => f a b c))).
Qed.

Lemma tsum_rot : forall l f, tsum l f = tsum l (fun a b c => f b c a).
Proof.
  intros l f.
  transitivity (tsum l (fun a b c => f a c b)); [apply tsum_swap23|].
  apply (tsum_swap12 l (fun a b c => f a c b)).
Qed.

Lemma tsum_rot2 : forall l f, tsum l f = tsum l (fun a b c => f c a b).
Proof.
  intros l f. rewrite (tsum_rot l f).
  apply (tsum_rot l (fun a b c => f b c a)).
Qed.

Lemma tsum_swap13 : forall l f, tsum l f = tsum l (fun a b c => f c b a).
Proof.
  intros l f. rewrite (tsum_rot l f).
  apply (tsum_swap23 l (fun a b c => f b c a)).
Qed.

(** Ordered triples of distinct, pairwise adjacent modules. *)
Definition face_tri (s : VMState) (a b c : ModuleID) : bool :=
  negb (a =? b) && negb (a =? c) && negb (b =? c) &&
  modules_adjacent_by_region s a b && modules_adjacent_by_region s a c &&
  modules_adjacent_by_region s b c.

Lemma face_tri_swap23 : forall s a b c, face_tri s a c b = face_tri s a b c.
Proof.
  intros s a b c. unfold face_tri.
  rewrite (Nat.eqb_sym c b), (modules_adjacent_by_region_sym s c b).
  destruct (a =? b), (a =? c), (b =? c), (modules_adjacent_by_region s a b),
    (modules_adjacent_by_region s a c), (modules_adjacent_by_region s b c);
    reflexivity.
Qed.

Lemma face_tri_rot : forall s a b c, face_tri s b c a = face_tri s a b c.
Proof.
  intros s a b c. unfold face_tri.
  rewrite (Nat.eqb_sym b a), (Nat.eqb_sym c a),
    (modules_adjacent_by_region_sym s b a), (modules_adjacent_by_region_sym s c a).
  destruct (a =? b), (a =? c), (b =? c), (modules_adjacent_by_region s a b),
    (modules_adjacent_by_region s a c), (modules_adjacent_by_region s b c);
    reflexivity.
Qed.

Lemma face_tri_rot2 : forall s a b c, face_tri s c a b = face_tri s a b c.
Proof. intros. rewrite face_tri_rot. apply face_tri_rot. Qed.

Lemma face_tri_swap12 : forall s a b c, face_tri s b a c = face_tri s a b c.
Proof. intros. rewrite <- (face_tri_rot s b a c). apply face_tri_swap23. Qed.

Lemma face_tri_swap13 : forall s a b c, face_tri s c b a = face_tri s a b c.
Proof. intros. rewrite (face_tri_swap23 s c a b). apply face_tri_rot2. Qed.

Lemma face_tri_true : forall s a b c, face_tri s a b c = true ->
  a <> b /\ a <> c /\ b <> c /\
  modules_adjacent_by_region s a b = true /\
  modules_adjacent_by_region s a c = true /\
  modules_adjacent_by_region s b c = true.
Proof.
  intros s a b c H. unfold face_tri in H.
  destruct (Nat.eqb_spec a b), (Nat.eqb_spec a c), (Nat.eqb_spec b c);
    simpl in H; try discriminate.
  destruct (modules_adjacent_by_region s a b), (modules_adjacent_by_region s a c),
    (modules_adjacent_by_region s b c); simpl in H; try discriminate.
  repeat split; auto.
Qed.

Definition tri_perim (s : VMState) (a b c : ModuleID) : nat :=
  (mu_module_distance s a b + mu_module_distance s a c + mu_module_distance s b c)%nat.

Lemma tri_perim_rot : forall s a b c, tri_perim s b c a = tri_perim s a b c.
Proof.
  intros. unfold tri_perim.
  rewrite (mu_module_distance_sym s b a), (mu_module_distance_sym s c a). lia.
Qed.

Lemma tri_perim_rot2 : forall s a b c, tri_perim s c a b = tri_perim s a b c.
Proof. intros. rewrite tri_perim_rot. apply tri_perim_rot. Qed.

Lemma dist_nonzero : forall s a b, a <> b -> mu_module_distance s a b <> 0%nat.
Proof.
  intros s a b H. unfold mu_module_distance.
  destruct (Nat.eqb_spec a b); [contradiction|lia].
Qed.

Lemma triangle_angle_swap23 : forall s a b c,
  triangle_angle s a b c = triangle_angle s a c b.
Proof.
  intros s a b c. unfold triangle_angle. cbv zeta.
  rewrite (mu_module_distance_sym s c b).
  rewrite (orb_comm (mu_module_distance s a b =? 0) (mu_module_distance s a c =? 0)).
  rewrite (Nat.add_comm (mu_module_distance s a c) (mu_module_distance s a b)).
  reflexivity.
Qed.

Lemma triangle_angle_face : forall s a b c, a <> b -> a <> c ->
  triangle_angle s a b c =
  (PI * INR (mu_module_distance s b c) / INR (S (tri_perim s a b c)))%R.
Proof.
  intros s a b c Hab Hac. unfold triangle_angle, tri_perim, dist_to_R. cbv zeta.
  destruct (Nat.eqb_spec (mu_module_distance s a b) 0) as [E|_];
    [exfalso; exact (dist_nonzero s a b Hab E)|].
  destruct (Nat.eqb_spec (mu_module_distance s a c) 0) as [E|_];
    [exfalso; exact (dist_nonzero s a c Hac E)|].
  reflexivity.
Qed.

Lemma sum_angles_lsum : forall s m l,
  sum_angles s m l = lsum l (fun p => triangle_angle s m (fst p) (snd p)).
Proof.
  intros s m l. induction l as [|[n1 n2] l IH]; [reflexivity|].
  simpl sum_angles. rewrite lsum_cons, IH. reflexivity.
Qed.

(** The angle sum at m, rewritten as a double sum over all module IDs. *)
Lemma sum_angles_triple : forall s m,
  sum_angles s m (module_triangles s m) =
  lsum (map fst (pg_modules (vm_graph s))) (fun b =>
    lsum (map fst (pg_modules (vm_graph s))) (fun c =>
      if face_tri s m b c && (b <? c) then triangle_angle s m b c else 0%R)).
Proof.
  intros s m.
  rewrite sum_angles_lsum.
  unfold module_triangles, module_neighbors, module_neighbors_physical,
    module_neighbors_adjacent.
  cbv zeta.
  rewrite lsum_flat_map, lsum_filter.
  apply lsum_ext. intro b. cbv beta.
  rewrite lsum_map. cbn [fst snd]. rewrite !lsum_filter.
  rewrite if_lsum. apply lsum_ext. intro c. cbv beta.
  unfold face_tri.
  destruct (m =? b), (m =? c), (b =? c), (b <? c),
    (modules_adjacent_by_region s m b), (modules_adjacent_by_region s m c),
    (modules_adjacent_by_region s b c); reflexivity.
Qed.

(** The per-triangle weight P/(1+P), with P the perimeter. *)
Definition tri_weight (s : VMState) (a b c : ModuleID) : R :=
  if face_tri s a b c
  then (INR (tri_perim s a b c) / INR (S (tri_perim s a b c)))%R
  else 0%R.

(** Unconditional double-counting identity: the total of all angle sums
    is pi/6 times the total triangle weight. *)
Theorem total_angle_sum_identity : forall s,
  lsum (map fst (pg_modules (vm_graph s)))
       (fun m => sum_angles s m (module_triangles s m)) =
  (PI * tsum (map fst (pg_modules (vm_graph s))) (tri_weight s) / 6)%R.
Proof.
  intros s. set (ids := map fst (pg_modules (vm_graph s))).
  rewrite (lsum_ext _ ids _ _ (sum_angles_triple s)). fold ids.
  change (lsum ids (fun a => lsum ids (fun b => lsum ids (fun c =>
            if face_tri s a b c && (b <? c) then triangle_angle s a b c else 0%R))))
    with (tsum ids (fun a b c =>
            if face_tri s a b c && (b <? c) then triangle_angle s a b c else 0%R)).
  set (G := fun a b c =>
        if face_tri s a b c && (b <? c) then triangle_angle s a b c else 0%R).
  set (G' := fun a b c =>
        if face_tri s a b c && (c <? b) then triangle_angle s a b c else 0%R).
  set (H := fun a b c => if face_tri s a b c then triangle_angle s a b c else 0%R).
  assert (HGG : tsum ids G' = tsum ids G).
  { rewrite (tsum_swap23 ids G'). apply tsum_ext. intros a b c. unfold G, G'.
    rewrite face_tri_swap23, triangle_angle_swap23. reflexivity. }
  assert (HGH : (tsum ids G + tsum ids G')%R = tsum ids H).
  { rewrite <- tsum_plus. apply tsum_ext. intros a b c. unfold G, G', H.
    destruct (face_tri s a b c) eqn:Hf; simpl; [|lra].
    destruct (face_tri_true s a b c Hf) as [_ [_ [Hbc _]]].
    destruct (Nat.ltb_spec b c), (Nat.ltb_spec c b); try lia; lra. }
  set (K := fun a b c => if face_tri s a b c
        then (PI * INR (mu_module_distance s b c) / INR (S (tri_perim s a b c)))%R
        else 0%R).
  assert (HHK : tsum ids H = tsum ids K).
  { apply tsum_ext. intros a b c. unfold H, K.
    destruct (face_tri s a b c) eqn:Hf; [|reflexivity].
    destruct (face_tri_true s a b c Hf) as [Hab [Hac _]].
    apply triangle_angle_face; assumption. }
  set (K2 := fun a b c => if face_tri s a b c
        then (PI * INR (mu_module_distance s a c) / INR (S (tri_perim s a b c)))%R
        else 0%R).
  set (K3 := fun a b c => if face_tri s a b c
        then (PI * INR (mu_module_distance s a b) / INR (S (tri_perim s a b c)))%R
        else 0%R).
  assert (HK2 : tsum ids K = tsum ids K2).
  { rewrite (tsum_rot ids K). apply tsum_ext. intros a b c. unfold K, K2.
    rewrite face_tri_rot, tri_perim_rot, (mu_module_distance_sym s c a). reflexivity. }
  assert (HK3 : tsum ids K = tsum ids K3).
  { rewrite (tsum_rot2 ids K). apply tsum_ext. intros a b c. unfold K, K3.
    rewrite face_tri_rot2, tri_perim_rot2. reflexivity. }
  assert (HKsum : (tsum ids K + tsum ids K2 + tsum ids K3)%R =
                  (PI * tsum ids (tri_weight s))%R).
  { rewrite <- tsum_scal, <- !tsum_plus. apply tsum_ext. intros a b c.
    unfold K, K2, K3, tri_weight.
    destruct (face_tri s a b c); [|lra].
    assert (Hpos : (0 < INR (S (tri_perim s a b c)))%R) by (apply lt_0_INR; lia).
    assert (HP : INR (tri_perim s a b c) =
      (INR (mu_module_distance s a b) + INR (mu_module_distance s a c)
       + INR (mu_module_distance s b c))%R)
      by (unfold tri_perim; rewrite !plus_INR; reflexivity).
    rewrite HP. field. lra. }
  change (tsum ids G = PI * tsum ids (tri_weight s) / 6)%R.
  lra.
Qed.

(** * Part 4. The window 2F < T <= (44/21) F. *)

Lemma mass_ge3 : forall s a ms,
  regions_are_triples (vm_graph s) ->
  graph_lookup (vm_graph s) a = Some ms ->
  (3 <= module_structural_mass s a)%nat.
Proof.
  intros s a ms H3 Hl. unfold module_structural_mass.
  rewrite Hl. rewrite (lookup_region3 s a ms H3 Hl). lia.
Qed.

Lemma dist_ge7 : forall s a b,
  regions_are_triples (vm_graph s) ->
  modules_adjacent_by_region s a b = true -> a <> b ->
  (7 <= mu_module_distance s a b)%nat.
Proof.
  intros s a b H3 Hadj Hab.
  destruct (adjacent_lookup_l s a b Hadj) as [ma Ha].
  destruct (adjacent_lookup_r s a b Hadj) as [mb Hb].
  pose proof (mass_ge3 s a ma H3 Ha). pose proof (mass_ge3 s b mb H3 Hb).
  unfold mu_module_distance. destruct (Nat.eqb_spec a b); [contradiction|lia].
Qed.

Lemma perim_ge21 : forall s a b c,
  regions_are_triples (vm_graph s) ->
  face_tri s a b c = true -> (21 <= tri_perim s a b c)%nat.
Proof.
  intros s a b c H3 Hf.
  destruct (face_tri_true s a b c Hf) as [Hab [Hac [Hbc [Aab [Aac Abc]]]]].
  pose proof (dist_ge7 s a b H3 Aab Hab).
  pose proof (dist_ge7 s a c H3 Aac Hac).
  pose proof (dist_ge7 s b c H3 Abc Hbc).
  unfold tri_perim. lia.
Qed.

Definition tri_rem (s : VMState) (a b c : ModuleID) : R :=
  if face_tri s a b c then (/ INR (S (tri_perim s a b c)))%R else 0%R.

Lemma weight_plus_rem : forall s a b c,
  (tri_weight s a b c + tri_rem s a b c)%R = ind (face_tri s a b c).
Proof.
  intros s a b c. unfold tri_weight, tri_rem, ind.
  destruct (face_tri s a b c); [|lra].
  rewrite S_INR. pose proof (pos_INR (tri_perim s a b c)). field. lra.
Qed.

Lemma rem_nonneg : forall s a b c, (0 <= tri_rem s a b c)%R.
Proof.
  intros s a b c. unfold tri_rem. destruct (face_tri s a b c); [|lra].
  left. apply Rinv_0_lt_compat. apply lt_0_INR. lia.
Qed.

Lemma rem_le : forall s a b c,
  regions_are_triples (vm_graph s) ->
  (22 * tri_rem s a b c <= ind (face_tri s a b c))%R.
Proof.
  intros s a b c H3. unfold tri_rem, ind.
  destruct (face_tri s a b c) eqn:Hf; [|lra].
  pose proof (perim_ge21 s a b c H3 Hf) as HP.
  assert (Hx : (22 <= INR (S (tri_perim s a b c)))%R).
  { replace 22%R with (INR 22) by (simpl; lra). apply le_INR. lia. }
  apply (Rmult_le_reg_r (INR (S (tri_perim s a b c)))); [lra|].
  rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

Lemma weight_pos_rem_pos : forall s a b c,
  (0 < tri_weight s a b c)%R -> (0 < tri_rem s a b c)%R.
Proof.
  intros s a b c H. unfold tri_weight, tri_rem in *.
  destruct (face_tri s a b c); [|lra].
  apply Rinv_0_lt_compat. apply lt_0_INR. lia.
Qed.

Lemma tri_weight_nonneg : forall s a b c, (0 <= tri_weight s a b c)%R.
Proof.
  intros s a b c. unfold tri_weight. destruct (face_tri s a b c); [|lra].
  unfold Rdiv. apply Rmult_le_pos; [apply pos_INR|].
  left. apply Rinv_0_lt_compat. apply lt_0_INR. lia.
Qed.

Lemma tsum_pos_of_witness : forall l (f g : nat -> nat -> nat -> R),
  (forall a b c, 0 <= g a b c)%R ->
  (forall a b c, 0 < f a b c -> 0 < g a b c)%R ->
  (0 < tsum l f)%R -> (0 < tsum l g)%R.
Proof.
  intros l f g Hnn Hfg Hf. unfold tsum in *.
  destruct (lsum_pos_exists _ _ _ Hf) as [a [Ha Hfa]].
  destruct (lsum_pos_exists _ _ _ Hfa) as [b [Hb Hfb]].
  destruct (lsum_pos_exists _ _ _ Hfb) as [c [Hc Hfc]].
  apply lsum_pos with a; [|exact Ha|].
  { intros x _. apply lsum_nonneg_in. intros y _. apply lsum_nonneg_in.
    intros z _. apply Hnn. }
  apply lsum_pos with b; [|exact Hb|].
  { intros y _. apply lsum_nonneg_in. intros z _. apply Hnn. }
  apply lsum_pos with c; [|exact Hc|].
  { intros z _. apply Hnn. }
  apply Hfg. exact Hfc.
Qed.

Theorem F3_calibration_window_R : forall s,
  all_modules_are_triangles_list (vm_graph s) ->
  all_regions_normalized_list (vm_graph s) ->
  (1 <= List.length (pg_modules (vm_graph s)))%nat ->
  (forall m, In m (map fst (pg_modules (vm_graph s))) ->
             calibration_residual s m = 0%R) ->
  (12 * INR (List.length (pg_modules (vm_graph s))) <
     tsum (map fst (pg_modules (vm_graph s))) (fun a b c => ind (face_tri s a b c)))%R /\
  (21 * tsum (map fst (pg_modules (vm_graph s))) (fun a b c => ind (face_tri s a b c))
     <= 264 * INR (List.length (pg_modules (vm_graph s))))%R.
Proof.
  intros s Htri Hnorm HF Hcal.
  pose proof (triangulated_regions_are_triples _ Htri Hnorm) as H3.
  set (ids := map fst (pg_modules (vm_graph s))).
  set (nF := INR (List.length (pg_modules (vm_graph s)))).
  pose proof PI_RGT_0 as Hpi.
  assert (Hsum : lsum ids (fun m => sum_angles s m (module_triangles s m)) =
                 (nF * (2 * PI))%R).
  { rewrite (lsum_ext_in _ ids _ (fun _ => (2 * PI)%R)).
    - rewrite lsum_const. unfold ids, nF. rewrite map_length. reflexivity.
    - intros m Hm. apply (F3_calibration_forces_flat_faces s Htri Hnorm Hcal m Hm). }
  unfold ids in Hsum. rewrite total_angle_sum_identity in Hsum. fold ids in Hsum.
  assert (HW : tsum ids (tri_weight s) = (12 * nF)%R).
  { assert (Hz : (PI * (tsum ids (tri_weight s) - 12 * nF) = 0)%R) by lra.
    apply Rmult_integral in Hz. destruct Hz as [Hz|Hz]; lra. }
  assert (Hsplit : tsum ids (fun a b c => ind (face_tri s a b c)) =
                   (tsum ids (tri_weight s) + tsum ids (tri_rem s))%R).
  { rewrite <- tsum_plus. apply tsum_ext. intros a b c.
    symmetry. apply weight_plus_rem. }
  assert (Hle : (22 * tsum ids (tri_rem s) <=
                 tsum ids (fun a b c => ind (face_tri s a b c)))%R).
  { rewrite <- tsum_scal. apply tsum_le_in. intros a b c _ _ _. apply rem_le. exact H3. }
  assert (HnF : (1 <= nF)%R).
  { unfold nF. replace 1%R with (INR 1) by reflexivity. apply le_INR. exact HF. }
  assert (Hpos : (0 < tsum ids (tri_rem s))%R).
  { apply (tsum_pos_of_witness ids (tri_weight s)).
    - apply rem_nonneg.
    - apply weight_pos_rem_pos.
    - lra. }
  split; lra.
Qed.

(** Number of face-graph triangles, each counted once (a < b < c). *)
Definition face_triangle_count (s : VMState) : nat :=
  nsum (map fst (pg_modules (vm_graph s))) (fun a =>
    nsum (map fst (pg_modules (vm_graph s))) (fun b =>
      nsum (map fst (pg_modules (vm_graph s))) (fun c =>
        if face_tri s a b c && (a <? b) && (b <? c) then 1%nat else 0%nat))).

Lemma INR_if : forall bb : bool, INR (if bb then 1%nat else 0%nat) = ind bb.
Proof. destruct bb; reflexivity. Qed.

Lemma INR_face_triangle_count : forall s,
  INR (face_triangle_count s) =
  tsum (map fst (pg_modules (vm_graph s)))
       (fun a b c => ind (face_tri s a b c && (a <? b) && (b <? c))).
Proof.
  intros s. unfold face_triangle_count, tsum.
  rewrite INR_nsum. apply lsum_ext. intro a.
  rewrite INR_nsum. apply lsum_ext. intro b.
  rewrite INR_nsum. apply lsum_ext. intro c.
  apply INR_if.
Qed.

Lemma ind_six : forall s a b c,
  ind (face_tri s a b c) =
  (ind (face_tri s a b c && (a <? b) && (b <? c)) +
   ind (face_tri s a b c && (a <? c) && (c <? b)) +
   ind (face_tri s a b c && (b <? a) && (a <? c)) +
   ind (face_tri s a b c && (b <? c) && (c <? a)) +
   ind (face_tri s a b c && (c <? a) && (a <? b)) +
   ind (face_tri s a b c && (c <? b) && (b <? a)))%R.
Proof.
  intros s a b c. destruct (face_tri s a b c) eqn:Hf.
  - destruct (face_tri_true s a b c Hf) as [Hab [Hac [Hbc _]]].
    unfold ind.
    destruct (Nat.ltb_spec a b), (Nat.ltb_spec b c), (Nat.ltb_spec a c),
      (Nat.ltb_spec c b), (Nat.ltb_spec b a), (Nat.ltb_spec c a);
      simpl; try lra; exfalso; lia.
  - unfold ind. simpl. lra.
Qed.

Lemma ordered_count_six : forall s,
  tsum (map fst (pg_modules (vm_graph s))) (fun a b c => ind (face_tri s a b c)) =
  (6 * tsum (map fst (pg_modules (vm_graph s)))
         (fun a b c => ind (face_tri s a b c && (a <? b) && (b <? c))))%R.
Proof.
  intros s. set (ids := map fst (pg_modules (vm_graph s))).
  set (U := tsum ids (fun a b c => ind (face_tri s a b c && (a <? b) && (b <? c)))).
  rewrite (tsum_ext ids (fun a b c : nat => ind (face_tri s a b c)) _ (ind_six s)).
  rewrite !tsum_plus.
  assert (H2 : tsum ids (fun a b c => ind (face_tri s a b c && (a <? c) && (c <? b))) = U).
  { rewrite tsum_swap23. apply tsum_ext. intros a b c.
    rewrite face_tri_swap23. reflexivity. }
  assert (H3 : tsum ids (fun a b c => ind (face_tri s a b c && (b <? a) && (a <? c))) = U).
  { rewrite tsum_swap12. apply tsum_ext. intros a b c.
    rewrite face_tri_swap12. reflexivity. }
  assert (H4 : tsum ids (fun a b c => ind (face_tri s a b c && (b <? c) && (c <? a))) = U).
  { rewrite tsum_rot2. apply tsum_ext. intros a b c.
    rewrite face_tri_rot2. reflexivity. }
  assert (H5 : tsum ids (fun a b c => ind (face_tri s a b c && (c <? a) && (a <? b))) = U).
  { rewrite tsum_rot. apply tsum_ext. intros a b c.
    rewrite face_tri_rot. reflexivity. }
  assert (H6 : tsum ids (fun a b c => ind (face_tri s a b c && (c <? b) && (b <? a))) = U).
  { rewrite tsum_swap13. apply tsum_ext. intros a b c.
    rewrite face_tri_swap13. reflexivity. }
  rewrite H2, H3, H4, H5, H6. fold U. lra.
Qed.

(** Calibration at every module puts the number T of face-graph triangles
    in the window 2F < T <= (44/21) F, which forces F >= 11. *)
Theorem F3_calibration_window : forall s,
  well_formed_triangulated (vm_graph s) ->
  (forall m, In m (map fst (pg_modules (vm_graph s))) ->
             calibration_residual s m = 0%R) ->
  (2 * DiscreteTopology.F (vm_graph s) < face_triangle_count s)%nat /\
  (21 * face_triangle_count s <= 44 * DiscreteTopology.F (vm_graph s))%nat /\
  (11 <= DiscreteTopology.F (vm_graph s))%nat.
Proof.
  intros s Hwf Hcal.
  destruct Hwf as [_ [Htri [Hnorm [_ [_ [_ [HF _]]]]]]].
  unfold DiscreteTopology.F in *.
  destruct (F3_calibration_window_R s Htri Hnorm HF Hcal) as [Hlo Hhi].
  rewrite ordered_count_six in Hlo, Hhi.
  rewrite <- INR_face_triangle_count in Hlo, Hhi.
  set (T := face_triangle_count s) in *.
  set (nF := List.length (pg_modules (vm_graph s))) in *.
  assert (H1 : (2 * nF < T)%nat).
  { apply INR_lt. rewrite mult_INR. simpl (INR 2). lra. }
  assert (H2 : (21 * T <= 44 * nF)%nat).
  { apply INR_le. rewrite !mult_INR.
    replace (INR 21) with 21%R by (simpl; lra).
    replace (INR 44) with 44%R by (simpl; lra). lra. }
  repeat split; lia.
Qed.

(** * Part 5. Faces through a common vertex form face-graph triangles. *)

Definition cont (s : VMState) (v : nat) (a : ModuleID) : bool :=
  match graph_lookup (vm_graph s) a with
  | Some ms => nat_list_mem v (module_region ms)
  | None => false
  end.

Definition dist3 (a b c : nat) : bool :=
  negb (a =? b) && negb (a =? c) && negb (b =? c).

Lemma share_adjacent : forall s v a b,
  cont s v a = true -> cont s v b = true -> modules_adjacent_by_region s a b = true.
Proof.
  intros s v a b Ha Hb. unfold cont in *. unfold modules_adjacent_by_region.
  destruct (graph_lookup (vm_graph s) a) as [ma|]; [|discriminate].
  destruct (graph_lookup (vm_graph s) b) as [mb|]; [|discriminate].
  destruct (nat_list_disjoint (module_region ma) (module_region mb)) eqn:Hd; [|reflexivity].
  exfalso. unfold nat_list_disjoint in Hd. rewrite forallb_forall in Hd.
  specialize (Hd v (proj1 (nat_list_mem_In v _) Ha)).
  rewrite Hb in Hd. discriminate.
Qed.

Lemma share_face_tri : forall s v a b c,
  dist3 a b c && cont s v a && cont s v b && cont s v c = true ->
  face_tri s a b c = true.
Proof.
  intros s v a b c H.
  destruct (dist3 a b c) eqn:Hd; [|discriminate].
  destruct (cont s v a) eqn:Ha; [|discriminate].
  destruct (cont s v b) eqn:Hb; [|discriminate].
  destruct (cont s v c) eqn:Hc; [|discriminate].
  unfold face_tri. unfold dist3 in Hd. rewrite Hd. simpl.
  rewrite (share_adjacent s v a b Ha Hb), (share_adjacent s v a c Ha Hc),
    (share_adjacent s v b c Hb Hc). reflexivity.
Qed.

Definition norm_edge (v w : nat) : nat * nat :=
  if v <? w then (v, w) else (w, v).

Lemma norm_edge_sym : forall v w, v <> w -> norm_edge v w = norm_edge w v.
Proof.
  intros v w H. unfold norm_edge.
  destruct (Nat.ltb_spec v w), (Nat.ltb_spec w v); try reflexivity; lia.
Qed.

Lemma region_edges_In : forall region v w, v <> w ->
  In v region -> In w region -> In (norm_edge v w) (region_edges_internal region).
Proof.
  induction region as [|n rest IH]; intros v w Hvw Hv Hw; [destruct Hv|].
  simpl. apply in_or_app.
  destruct Hv as [Hv|Hv]; destruct Hw as [Hw|Hw].
  - subst. contradiction.
  - subst v. left. apply in_map_iff. exists w. split; [reflexivity|exact Hw].
  - subst w. left. apply in_map_iff. exists v. split; [|exact Hv].
    rewrite norm_edge_sym by (intro E; apply Hvw; exact E).
    reflexivity.
  - right. apply IH; assumption.
Qed.

Lemma edge_eq_refl : forall e, edge_eq e e = true.
Proof. intros [x y]. unfold edge_eq. simpl. rewrite !Nat.eqb_refl. reflexivity. Qed.

Lemma list_mem_edge_In : forall e l, In e l -> list_mem edge_eq e l = true.
Proof.
  intros e l H. induction l as [|y l IH]; [destruct H|].
  simpl. destruct (edge_eq e y) eqn:Hey; [reflexivity|].
  destruct H as [H|H].
  - subst. rewrite edge_eq_refl in Hey. discriminate.
  - apply IH. exact H.
Qed.

Lemma dedup_In : forall e l, In e l -> In e (deduplicate_edges l).
Proof.
  intros e l. induction l as [|e' rest IH]; intros H; [destruct H|].
  simpl. destruct (existsb _ rest) eqn:Hex.
  - apply IH. destruct H as [H|H]; [|exact H].
    subst e'. apply existsb_exists in Hex. destruct Hex as [x [Hx Heq]].
    apply andb_prop in Heq. destruct Heq as [H1 H2].
    apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2.
    destruct e as [e1 e2], x as [x1 x2]. simpl in *. subst. exact Hx.
  - destruct H as [H|H]; [left; exact H|right; apply IH; exact H].
Qed.

Lemma collect_edges_In : forall mods id m e,
  In (id, m) mods -> In e (module_edges m) -> In e (collect_edges_from_modules mods).
Proof.
  induction mods as [|[id' m'] rest IH]; intros id m e Hin He; [destruct Hin|].
  simpl. apply in_or_app. destruct Hin as [Hin|Hin].
  - inversion Hin. subst. left. exact He.
  - right. eapply IH; eassumption.
Qed.

Lemma count_modules_with_edge_filter : forall e mods,
  count_modules_with_edge e mods =
  List.length (filter (fun p => list_mem edge_eq e (module_edges (snd p))) mods).
Proof.
  intros e mods. induction mods as [|[id m] rest IH]; [reflexivity|].
  simpl. destruct (list_mem edge_eq e (module_edges m)); simpl; rewrite IH; reflexivity.
Qed.

Lemma cont_lookup : forall s v a, cont s v a = true ->
  exists ma, graph_lookup (vm_graph s) a = Some ma /\ In v (module_region ma).
Proof.
  intros s v a H. unfold cont in H.
  destruct (graph_lookup (vm_graph s) a) as [ma|]; [|discriminate].
  exists ma. split; [reflexivity|]. apply nat_list_mem_In. exact H.
Qed.

(** Three distinct faces never share two distinct vertices: the edge
    between them would lie in three faces. *)
Lemma no_three_faces_on_edge : forall s,
  NoDup (map fst (pg_modules (vm_graph s))) ->
  is_2_manifold (vm_graph s) ->
  forall a b c v w,
    dist3 a b c = true -> v <> w ->
    cont s v a = true -> cont s v b = true -> cont s v c = true ->
    cont s w a = true -> cont s w b = true -> cont s w c = true -> False.
Proof.
  intros s Hnd Hman a b c v w Hd Hvw Hva Hvb Hvc Hwa Hwb Hwc.
  unfold dist3 in Hd.
  destruct (Nat.eqb_spec a b) as [|Hab]; [discriminate|].
  destruct (Nat.eqb_spec a c) as [|Hac]; [discriminate|].
  destruct (Nat.eqb_spec b c) as [|Hbc]; [discriminate|].
  destruct (cont_lookup s v a Hva) as [ma [La Va]].
  destruct (cont_lookup s v b Hvb) as [mb [Lb Vb]].
  destruct (cont_lookup s v c Hvc) as [mc [Lc Vc]].
  destruct (cont_lookup s w a Hwa) as [ma' [La' Wa]].
  destruct (cont_lookup s w b Hwb) as [mb' [Lb' Wb]].
  destruct (cont_lookup s w c Hwc) as [mc' [Lc' Wc]].
  rewrite La in La'. inversion La'. subst ma'.
  rewrite Lb in Lb'. inversion Lb'. subst mb'.
  rewrite Lc in Lc'. inversion Lc'. subst mc'.
  pose proof (graph_lookup_modules_In _ _ _ La) as Ia.
  pose proof (graph_lookup_modules_In _ _ _ Lb) as Ib.
  pose proof (graph_lookup_modules_In _ _ _ Lc) as Ic.
  set (e := norm_edge v w).
  set (P := fun p : ModuleID * ModuleState =>
              list_mem edge_eq e (module_edges (snd p))).
  assert (Pa : P (a, ma) = true).
  { unfold P. apply list_mem_edge_In. apply region_edges_In; assumption. }
  assert (Pb : P (b, mb) = true).
  { unfold P. apply list_mem_edge_In. apply region_edges_In; assumption. }
  assert (Pc : P (c, mc) = true).
  { unfold P. apply list_mem_edge_In. apply region_edges_In; assumption. }
  assert (Hnd3 : NoDup [(a, ma); (b, mb); (c, mc)]).
  { constructor; [simpl; intros [E|[E|E]]; [congruence|congruence|contradiction]|].
    constructor; [simpl; intros [E|E]; [congruence|contradiction]|].
    constructor; [simpl; tauto|constructor]. }
  assert (Hincl : incl [(a, ma); (b, mb); (c, mc)] (filter P (pg_modules (vm_graph s)))).
  { intros p Hp. apply filter_In. simpl in Hp.
    destruct Hp as [Hp|[Hp|[Hp|Hp]]]; [subst p; auto|subst p; auto|subst p; auto|destruct Hp]. }
  pose proof (NoDup_incl_length Hnd3 Hincl) as Hlen. simpl in Hlen.
  assert (He : In e (edges (vm_graph s))).
  { unfold edges. apply dedup_In. apply (collect_edges_In _ a ma); [exact Ia|].
    apply region_edges_In; assumption. }
  pose proof (Hman e He) as Hc. cbv zeta in Hc.
  rewrite count_modules_with_edge_filter in Hc. fold P in Hc.
  change (prod nat ModuleState) with (prod ModuleID ModuleState) in Hlen.
  lia.
Qed.

Lemma lsum_ind_at_most_one : forall (l : list nat) (p : nat -> bool),
  NoDup l ->
  (forall x y, In x l -> In y l -> p x = true -> p y = true -> x = y) ->
  (lsum l (fun x => ind (p x)) <= 1)%R.
Proof.
  intros l p Hnd. induction Hnd as [|x l Hx Hnd IH]; intros Huniq.
  - unfold lsum. simpl. lra.
  - rewrite lsum_cons. destruct (p x) eqn:Hpx.
    + rewrite (lsum_ext_in _ l _ (fun _ => 0%R)).
      * rewrite lsum_const. unfold ind. lra.
      * intros y Hy. destruct (p y) eqn:Hpy; [|reflexivity].
        exfalso. apply Hx.
        rewrite (Huniq x y (or_introl eq_refl) (or_intror Hy) Hpx Hpy). exact Hy.
    + unfold ind at 1. assert (lsum l (fun x0 => ind (p x0)) <= 1)%R.
      { apply IH. intros a b Ha Hb. apply Huniq; right; assumption. }
      lra.
Qed.

Lemma vertex_terms_le_face_tri : forall s a b c,
  NoDup (map fst (pg_modules (vm_graph s))) ->
  is_2_manifold (vm_graph s) ->
  (lsum (vertices (vm_graph s))
     (fun v => ind (dist3 a b c && cont s v a && cont s v b && cont s v c))
   <= ind (face_tri s a b c))%R.
Proof.
  intros s a b c Hnd Hman.
  destruct (face_tri s a b c) eqn:Hf.
  - apply (lsum_ind_at_most_one _ (fun v => dist3 a b c && cont s v a && cont s v b && cont s v c)).
    + unfold vertices. apply normalize_region_nodup.
    + intros v w _ _ Hv Hw.
      destruct (Nat.eq_dec v w) as [E|Hvw]; [exact E|exfalso].
      destruct (dist3 a b c) eqn:Hd; [|discriminate].
      destruct (cont s v a) eqn:Va; [|discriminate].
      destruct (cont s v b) eqn:Vb; [|discriminate].
      destruct (cont s v c) eqn:Vc; [|discriminate].
      destruct (cont s w a) eqn:Wa; [|discriminate].
      destruct (cont s w b) eqn:Wb; [|discriminate].
      destruct (cont s w c) eqn:Wc; [|discriminate].
      exact (no_three_faces_on_edge s Hnd Hman a b c v w Hd Hvw Va Vb Vc Wa Wb Wc).
  - rewrite (lsum_ext_in _ _ _ (fun _ => 0%R)).
    + rewrite lsum_const. unfold ind. lra.
    + intros v _. destruct (dist3 a b c && cont s v a && cont s v b && cont s v c) eqn:H.
      * rewrite (share_face_tri s v a b c H) in Hf. discriminate.
      * reflexivity.
Qed.

Lemma tsum_lsum_swap : forall (l L : list nat) (f : nat -> nat -> nat -> nat -> R),
  tsum l (fun a b c => lsum L (fun v => f v a b c)) =
  lsum L (fun v => tsum l (fun a b c => f v a b c)).
Proof.
  intros l L f. unfold tsum.
  transitivity (lsum l (fun a => lsum l (fun b => lsum L (fun v => lsum l (fun c => f v a b c))))).
  { apply lsum_ext. intro a. apply lsum_ext. intro b.
    apply (lsum_swap _ _ l L (fun c v => f v a b c)). }
  transitivity (lsum l (fun a => lsum L (fun v => lsum l (fun b => lsum l (fun c => f v a b c))))).
  { apply lsum_ext. intro a.
    apply (lsum_swap _ _ l L (fun b v => lsum l (fun c => f v a b c))). }
  apply (lsum_swap _ _ l L (fun a v => lsum l (fun b => lsum l (fun c => f v a b c)))).
Qed.

Lemma tsum_filter3 : forall (l : list nat) (p : nat -> bool) (f : nat -> nat -> nat -> R),
  tsum l (fun a b c => if p a && p b && p c then f a b c else 0%R) =
  tsum (filter p l) f.
Proof.
  intros l p f. unfold tsum. rewrite lsum_filter. apply lsum_ext. intro a. cbv beta.
  destruct (p a) eqn:Ha; cbn [andb].
  - rewrite lsum_filter. apply lsum_ext. intro b. cbv beta.
    destruct (p b) eqn:Hb; cbn [andb].
    + rewrite lsum_filter. apply lsum_ext. intro c. cbv beta. destruct (p c); reflexivity.
    + rewrite lsum_const. lra.
  - rewrite (lsum_ext _ l _ (fun _ => 0%R)).
    + rewrite lsum_const. lra.
    + intro b. rewrite lsum_const. lra.
Qed.

Lemma lsum_eqb_one : forall (L : list nat) a,
  NoDup L -> In a L -> lsum L (fun c => ind (a =? c)) = 1%R.
Proof.
  intros L a Hnd. induction Hnd as [|x l Hx Hnd IH]; intros Ha; [destruct Ha|].
  rewrite lsum_cons. destruct Ha as [Ha|Ha].
  - subst x. rewrite Nat.eqb_refl.
    rewrite (lsum_ext_in _ l _ (fun _ => 0%R)).
    + rewrite lsum_const. unfold ind. lra.
    + intros y Hy. destruct (Nat.eqb_spec a y); [subst; contradiction|reflexivity].
  - destruct (Nat.eqb_spec a x); [subst; contradiction|].
    rewrite IH by exact Ha. unfold ind. lra.
Qed.

Lemma count_distinct3 : forall L, NoDup L ->
  tsum L (fun a b c => ind (dist3 a b c)) =
  (INR (List.length L) * (INR (List.length L) - 1) * (INR (List.length L) - 2))%R.
Proof.
  intros L Hnd. set (n := INR (List.length L)).
  unfold tsum.
  rewrite (lsum_ext_in _ L _ (fun _ => ((n - 1) * (n - 2))%R)).
  - rewrite lsum_const. fold n. ring.
  - intros a Ha.
    rewrite (lsum_ext_in _ L _ (fun b => ((1 - ind (a =? b)) * (n - 2))%R)).
    + rewrite (lsum_ext _ L (fun b => ((1 - ind (a =? b)) * (n - 2))%R)
                 (fun b => ((n - 2) + (- (n - 2)) * ind (a =? b))%R))
        by (intro b; ring).
      rewrite lsum_plus, lsum_scal, lsum_const, lsum_eqb_one by assumption.
      fold n. ring.
    + intros b Hb. destruct (Nat.eqb_spec a b) as [Eab|Nab].
      * subst b. unfold dist3. rewrite Nat.eqb_refl. simpl.
        rewrite lsum_const. unfold ind. lra.
      * rewrite (lsum_ext _ L _ (fun c => (1 + (-1) * ind (a =? c) + (-1) * ind (b =? c))%R)).
        -- rewrite !lsum_plus, !lsum_scal, lsum_const, !lsum_eqb_one by assumption.
           fold n. unfold ind. lra.
        -- intro c. unfold dist3, ind.
           destruct (Nat.eqb_spec a b); [contradiction|].
           destruct (Nat.eqb_spec a c), (Nat.eqb_spec b c); simpl; try lra.
           exfalso. apply Nab. congruence.
Qed.

Lemma filter_cont_length : forall s v l,
  (forall p, In p l -> graph_lookup (vm_graph s) (fst p) = Some (snd p)) ->
  List.length (filter (cont s v) (map fst l)) = count_incident_triangles v l.
Proof.
  intros s v l. induction l as [|[id m] rest IH]; intros H; [reflexivity|].
  assert (Hl : graph_lookup (vm_graph s) id = Some m) by exact (H (id, m) (or_introl eq_refl)).
  assert (Hc : cont s v id = nat_list_mem v (module_region m))
    by (unfold cont; rewrite Hl; reflexivity).
  cbn [map filter count_incident_triangles fst]. rewrite Hc.
  destruct (nat_list_mem v (module_region m)); cbn [List.length];
    rewrite IH by (intros p Hp; apply H; right; exact Hp); reflexivity.
Qed.

Lemma INR_falling3 : forall d,
  INR (d * (d - 1) * (d - 2)) = (INR d * (INR d - 1) * (INR d - 2))%R.
Proof.
  intros d. destruct d as [|[|d]].
  - simpl. ring.
  - simpl. ring.
  - rewrite !mult_INR, !minus_INR by lia.
    replace (INR 1) with 1%R by reflexivity.
    replace (INR 2) with 2%R by (simpl; lra). reflexivity.
Qed.

(** Every triple of faces through one vertex is a face-graph triangle, and
    on a 2-manifold with distinct module IDs no triangle is counted twice:
    6 T >= sum over vertices of d (d - 1) (d - 2). *)
Theorem F3_vertex_triangle_bound : forall s,
  NoDup (map fst (pg_modules (vm_graph s))) ->
  is_2_manifold (vm_graph s) ->
  (nsum (vertices (vm_graph s))
     (fun v => vertex_degree (vm_graph s) v * (vertex_degree (vm_graph s) v - 1)
               * (vertex_degree (vm_graph s) v - 2))
   <= 6 * face_triangle_count s)%nat.
Proof.
  intros s Hnd Hman.
  apply INR_le. rewrite mult_INR, INR_face_triangle_count, INR_nsum.
  replace (INR 6) with 6%R by (simpl; lra).
  rewrite <- ordered_count_six.
  set (ids := map fst (pg_modules (vm_graph s))).
  rewrite (lsum_ext _ _ _ (fun v => tsum ids (fun a b c =>
             ind (dist3 a b c && cont s v a && cont s v b && cont s v c)))).
  - rewrite <- (tsum_lsum_swap ids (vertices (vm_graph s))
                  (fun v a b c => ind (dist3 a b c && cont s v a && cont s v b && cont s v c))).
    apply tsum_le_in. intros a b c _ _ _.
    apply vertex_terms_le_face_tri; assumption.
  - intro v. rewrite INR_falling3.
    rewrite (tsum_ext ids _ (fun a b c => if cont s v a && cont s v b && cont s v c
                                         then ind (dist3 a b c) else 0%R)).
    + rewrite tsum_filter3. rewrite count_distinct3 by (apply NoDup_filter; exact Hnd).
      unfold vertex_degree. unfold ids.
      rewrite filter_cont_length; [reflexivity|].
      intros p Hp. apply graph_lookup_modules_nodup; [exact Hnd|].
      destruct p. exact Hp.
    + intros a b c. unfold ind.
      destruct (dist3 a b c), (cont s v a), (cont s v b), (cont s v c); reflexivity.
Qed.

(** * Part 6. Consequences. *)

(** Everything calibration everywhere forces on a well-formed triangulated
    state with distinct module IDs. *)
Theorem F3_calibration_consequences : forall s,
  well_formed_triangulated (vm_graph s) ->
  NoDup (map fst (pg_modules (vm_graph s))) ->
  (forall m, In m (map fst (pg_modules (vm_graph s))) ->
             calibration_residual s m = 0%R) ->
  (forall m, In m (map fst (pg_modules (vm_graph s))) ->
     mu_laplacian s m = 0%R /\ angle_defect_curvature s m = 0%R /\
     (5 <= List.length (module_triangles s m))%nat) /\
  (2 * DiscreteTopology.F (vm_graph s) < face_triangle_count s)%nat /\
  (21 * face_triangle_count s <= 44 * DiscreteTopology.F (vm_graph s))%nat /\
  (11 <= DiscreteTopology.F (vm_graph s))%nat /\
  (nsum (vertices (vm_graph s))
     (fun v => vertex_degree (vm_graph s) v * (vertex_degree (vm_graph s) v - 1)
               * (vertex_degree (vm_graph s) v - 2))
   <= 6 * face_triangle_count s)%nat.
Proof.
  intros s Hwf Hnd Hcal.
  pose proof Hwf as Hwf'.
  destruct Hwf' as [_ [Htri [Hnorm [Hman _]]]].
  destruct (F3_calibration_window s Hwf Hcal) as [H1 [H2 H3]].
  split.
  - intros m Hm.
    destruct (F3_calibration_forces_flat_faces s Htri Hnorm Hcal m Hm) as [A [B _]].
    split; [exact A|]. split; [exact B|].
    exact (F3_calibration_forces_five_triangles s Htri Hnorm Hcal m Hm).
  - split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    apply F3_vertex_triangle_bound; assumption.
Qed.

(** The degree inequality that calibration forces:
    21 * sum_v d_v (d_v - 1) (d_v - 2) <= 264 F = 88 * sum_v d_v. *)
Theorem F3_calibration_forces_degree_inequality : forall s,
  well_formed_triangulated (vm_graph s) ->
  NoDup (map fst (pg_modules (vm_graph s))) ->
  (forall m, In m (map fst (pg_modules (vm_graph s))) ->
             calibration_residual s m = 0%R) ->
  (21 * nsum (vertices (vm_graph s))
          (fun v => vertex_degree (vm_graph s) v * (vertex_degree (vm_graph s) v - 1)
                    * (vertex_degree (vm_graph s) v - 2))
   <= 88 * sum_degrees (vm_graph s) (vertices (vm_graph s)))%nat.
Proof.
  intros s Hwf Hnd Hcal.
  destruct (F3_calibration_consequences s Hwf Hnd Hcal) as [_ [_ [H2 [_ H4]]]].
  destruct Hwf as [_ [_ [_ [_ [_ [_ [_ [_ [Hdeg _]]]]]]]]].
  unfold satisfies_degree_face_relation in Hdeg. rewrite Hdeg. lia.
Qed.

Lemma falling3_ge_6d : forall d, (4 <= d)%nat -> (6 * d <= d * (d - 1) * (d - 2))%nat.
Proof.
  intros d Hd.
  assert (H : (6 <= (d - 1) * (d - 2))%nat).
  { change 6%nat with (3 * 2)%nat. apply Nat.mul_le_mono; lia. }
  rewrite <- Nat.mul_assoc. rewrite (Nat.mul_comm 6 d).
  apply Nat.mul_le_mono_l. exact H.
Qed.

Lemma nsum_falling3_ge : forall g l,
  (forall v, In v l -> (4 <= vertex_degree g v)%nat) ->
  (6 * sum_degrees g l <=
   nsum l (fun v => vertex_degree g v * (vertex_degree g v - 1) * (vertex_degree g v - 2)))%nat.
Proof.
  intros g l H. induction l as [|v l IH]; [simpl; lia|].
  unfold nsum in *. simpl.
  pose proof (falling3_ge_6d (vertex_degree g v) (H v (or_introl eq_refl))).
  assert (6 * sum_degrees g l <=
          fold_right Nat.add 0
            (map (fun v0 => vertex_degree g v0 * (vertex_degree g v0 - 1)
                            * (vertex_degree g v0 - 2)) l))%nat.
  { apply IH. intros w Hw. apply H. right. exact Hw. }
  lia.
Qed.

(** A closed obstruction: if every vertex lies in at least four faces
    (for example any triangulated torus without vertices of degree 3),
    calibration cannot hold at every module. *)
Theorem F3_calibration_obstruction_min_degree4 : forall s,
  well_formed_triangulated (vm_graph s) ->
  NoDup (map fst (pg_modules (vm_graph s))) ->
  (forall v, In v (vertices (vm_graph s)) -> (4 <= vertex_degree (vm_graph s) v)%nat) ->
  ~ (forall m, In m (map fst (pg_modules (vm_graph s))) ->
               calibration_residual s m = 0%R).
Proof.
  intros s Hwf Hnd Hdeg4 Hcal.
  pose proof (F3_calibration_forces_degree_inequality s Hwf Hnd Hcal) as Hineq.
  destruct (F3_calibration_consequences s Hwf Hnd Hcal) as [_ [_ [_ [H3 _]]]].
  pose proof (nsum_falling3_ge (vm_graph s) (vertices (vm_graph s)) Hdeg4) as Hge.
  destruct Hwf as [_ [_ [_ [_ [_ [_ [_ [_ [Hdeg _]]]]]]]]].
  unfold satisfies_degree_face_relation in Hdeg.
  rewrite Hdeg in Hineq, Hge.
  lia.
Qed.

(** * Part 7. The degree inequality alone does not finish the argument. *)

Lemma triangles_check : forall g,
  forallb (fun p => is_triangle (module_region (snd p))) (pg_modules g) = true ->
  all_modules_are_triangles_list g.
Proof.
  intros g H mid m Hin. rewrite forallb_forall in H. exact (H (mid, m) Hin).
Qed.

Lemma normalized_check : forall g,
  forallb (fun p => if list_eq_dec Nat.eq_dec (module_region (snd p))
                         (normalize_region (module_region (snd p)))
                    then true else false) (pg_modules g) = true ->
  all_regions_normalized_list g.
Proof.
  intros g H mid m Hin. rewrite forallb_forall in H.
  specialize (H (mid, m) Hin). simpl in H.
  destruct (list_eq_dec Nat.eq_dec (module_region m) (normalize_region (module_region m)));
    [assumption|discriminate].
Qed.

Lemma manifold_check : forall g,
  forallb (fun e => (count_modules_with_edge e (pg_modules g) =? 1)
                    || (count_modules_with_edge e (pg_modules g) =? 2)) (edges g) = true ->
  is_2_manifold g.
Proof.
  intros g H e Hin. cbv zeta. rewrite forallb_forall in H.
  specialize (H e Hin). apply orb_true_iff in H.
  destruct H as [H|H]; apply Nat.eqb_eq in H; [left|right]; exact H.
Qed.

Lemma nodup_check : forall l : list nat, nodup Nat.eq_dec l = l -> NoDup l.
Proof. intros l H. rewrite <- H. apply NoDup_nodup. Qed.

(** An octahedron (closed, chi = 2) next to a zigzag triangulation of a
    9-gon (a disk with 9 boundary edges, chi = 1). Total chi = 3 and B = 9,
    so B = 3 chi holds. Every vertex link is connected in this complex. *)
Definition om_regions : list (list nat) :=
  [[0;2;4]; [0;2;5]; [0;3;4]; [0;3;5]; [1;2;4]; [1;2;5]; [1;3;4]; [1;3;5];
   [11;12;19]; [12;19;18]; [12;13;18]; [13;18;17]; [13;14;17]; [14;17;16]; [14;15;16]].

Definition om_graph : PartitionGraph :=
  {| pg_next_id := 15;
     pg_modules := combine (seq 0 15) (map (fun r => mk_module_state r []) om_regions);
     pg_next_morph_id := 0;
     pg_morphisms := [] |}.

Definition om_state : VMState :=
  {| vm_graph := om_graph;
     vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0; csr_heap_base := 0 |};
     vm_regs := [];
     vm_mem := [];
     vm_pc := 0;
     vm_mu := 0;
     vm_mu_tensor := [];
     vm_err := false;
     vm_logic_acc := 0;
     vm_mstatus := 0;
     vm_witness := witness_counts_zero;
     vm_certified := false |}.

Lemma om_well_formed : well_formed_triangulated (vm_graph om_state).
Proof.
  unfold well_formed_triangulated.
  split; [|split; [|split; [|split]]].
  - unfold well_formed_graph. simpl. repeat split; lia.
  - apply triangles_check. vm_compute. reflexivity.
  - apply normalized_check. vm_compute. reflexivity.
  - apply manifold_check. vm_compute. reflexivity.
  - unfold satisfies_edge_face_incidence, satisfies_degree_face_relation,
      satisfies_boundary_euler_relation.
    vm_compute. repeat split; lia.
Qed.

Lemma om_nodup : NoDup (map fst (pg_modules (vm_graph om_state))).
Proof. apply nodup_check. vm_compute. reflexivity. Qed.

(** On this state the conclusion of [F3_calibration_forces_degree_inequality]
    holds (21 * 174 <= 88 * 45), so that inequality cannot refute
    calibration by itself; the full count T = 37 of face-graph triangles
    (which includes triangles with no common vertex) already leaves the
    window 2F < T <= (44/21) F, since 21 * 37 > 44 * 15. *)
Theorem F3_degree_route_insufficient :
  well_formed_triangulated (vm_graph om_state) /\
  NoDup (map fst (pg_modules (vm_graph om_state))) /\
  (21 * nsum (vertices (vm_graph om_state))
          (fun v => vertex_degree (vm_graph om_state) v
                    * (vertex_degree (vm_graph om_state) v - 1)
                    * (vertex_degree (vm_graph om_state) v - 2))
   <= 88 * sum_degrees (vm_graph om_state) (vertices (vm_graph om_state)))%nat /\
  (44 * DiscreteTopology.F (vm_graph om_state) < 21 * face_triangle_count om_state)%nat.
Proof.
  split; [exact om_well_formed|]. split; [exact om_nodup|]. split.
  - apply Nat.leb_le. vm_compute. reflexivity.
  - apply Nat.ltb_lt. vm_compute. reflexivity.
Qed.

Corollary F3_om_not_calibrated :
  ~ (forall m, In m (map fst (pg_modules (vm_graph om_state))) ->
               calibration_residual om_state m = 0%R).
Proof.
  intro Hcal.
  destruct (F3_calibration_window om_state om_well_formed Hcal) as [_ [H _]].
  destruct F3_degree_route_insufficient as [_ [_ [_ H']]].
  lia.
Qed.

Lemma falling3_tangent : forall d, (18 * d <= d * (d - 1) * (d - 2) + 48)%nat.
Proof.
  intros d.
  destruct (le_lt_dec 9 d) as [Hd|Hd].
  - assert (H : (18 <= (d - 1) * (d - 2))%nat).
    { change 18%nat with (6 * 3)%nat. apply Nat.mul_le_mono; lia. }
    rewrite <- Nat.mul_assoc. rewrite (Nat.mul_comm 18 d).
    pose proof (Nat.mul_le_mono_l _ _ d H). lia.
  - do 9 (destruct d as [|d]; [simpl; lia|]). lia.
Qed.

Lemma nsum_falling3_tangent : forall g l,
  (18 * sum_degrees g l <=
   nsum l (fun v => vertex_degree g v * (vertex_degree g v - 1) * (vertex_degree g v - 2))
   + 48 * List.length l)%nat.
Proof.
  intros g l. induction l as [|v l IH]; [simpl; lia|].
  unfold nsum in *. simpl.
  pose proof (falling3_tangent (vertex_degree g v)). lia.
Qed.

(** Calibration at every module forces a large boundary:
    61 F <= 140 B. With the well-formedness identities 3F = 2I + B,
    E = I + B and B = 3 chi, the sum of degrees is 6V - 5B, and the bound
    d (d - 1) (d - 2) >= 18 d - 48 turns the degree inequality into this. *)
Theorem F3_calibration_forces_large_boundary : forall s,
  well_formed_triangulated (vm_graph s) ->
  NoDup (map fst (pg_modules (vm_graph s))) ->
  (forall m, In m (map fst (pg_modules (vm_graph s))) ->
             calibration_residual s m = 0%R) ->
  (61 * DiscreteTopology.F (vm_graph s) <= 140 * DiscreteTopology.B (vm_graph s))%nat.
Proof.
  intros s Hwf Hnd Hcal.
  pose proof (F3_calibration_forces_degree_inequality s Hwf Hnd Hcal) as Hineq.
  pose proof (nsum_falling3_tangent (vm_graph s) (vertices (vm_graph s))) as Htan.
  pose proof (total_edges_eq_interior_plus_boundary (vm_graph s) Hwf) as HEIB.
  destruct Hwf as [_ [_ [_ [_ [_ [_ [_ [H3F [Hdeg Hbd]]]]]]]]].
  unfold satisfies_edge_face_incidence in H3F.
  unfold satisfies_degree_face_relation in Hdeg.
  unfold satisfies_boundary_euler_relation in Hbd.
  unfold DiscreteTopology.V in Hbd.
  destruct Hbd as [Hge HBeq].
  lia.
Qed.

(** A closed obstruction: a well-formed triangulated state with no
    boundary edge (a closed surface) cannot be calibrated at every module. *)
Theorem F3_calibration_obstruction_closed : forall s,
  well_formed_triangulated (vm_graph s) ->
  NoDup (map fst (pg_modules (vm_graph s))) ->
  DiscreteTopology.B (vm_graph s) = 0%nat ->
  ~ (forall m, In m (map fst (pg_modules (vm_graph s))) ->
               calibration_residual s m = 0%R).
Proof.
  intros s Hwf Hnd HB Hcal.
  pose proof (F3_calibration_forces_large_boundary s Hwf Hnd Hcal) as H.
  destruct Hwf as [_ [_ [_ [_ [_ [_ [HF _]]]]]]].
  lia.
Qed.

From Coq Require Import Permutation Relations.

(** * Part 8. Finite sums of naturals, breadth-first growth, edge counts. *)

Lemma nsum_cons : forall (A : Type) (x : A) (l : list A) (f : A -> nat),
  nsum (x :: l) f = (f x + nsum l f)%nat.
Proof. reflexivity. Qed.

Lemma nsum_nil : forall (A : Type) (f : A -> nat), nsum [] f = 0%nat.
Proof. reflexivity. Qed.

Lemma nsum_app : forall (A : Type) (l1 l2 : list A) (f : A -> nat),
  nsum (l1 ++ l2) f = (nsum l1 f + nsum l2 f)%nat.
Proof.
  intros A l1 l2 f. induction l1 as [|x l1 IH]; [reflexivity|].
  simpl. rewrite !nsum_cons, IH. lia.
Qed.

Lemma nsum_ext_in : forall (A : Type) (l : list A) (f g : A -> nat),
  (forall x, In x l -> f x = g x) -> nsum l f = nsum l g.
Proof.
  intros A l f g H. induction l as [|x l IH]; [reflexivity|].
  rewrite !nsum_cons. rewrite (H x (or_introl eq_refl)).
  rewrite IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma nsum_plus : forall (A : Type) (l : list A) (f g : A -> nat),
  nsum l (fun x => (f x + g x)%nat) = (nsum l f + nsum l g)%nat.
Proof.
  intros A l f g. induction l as [|x l IH]; [reflexivity|].
  rewrite !nsum_cons, IH. lia.
Qed.

Lemma nsum_scal : forall (A : Type) (l : list A) (c : nat) (f : A -> nat),
  nsum l (fun x => (c * f x)%nat) = (c * nsum l f)%nat.
Proof.
  intros A l c f. induction l as [|x l IH]; [unfold nsum; simpl; lia|].
  rewrite !nsum_cons, IH. lia.
Qed.

Lemma nsum_zero : forall (A : Type) (l : list A), nsum l (fun _ => 0%nat) = 0%nat.
Proof. intros A l. induction l as [|x l IH]; [reflexivity|]. rewrite nsum_cons, IH. reflexivity. Qed.

Lemma nsum_swap : forall (A B : Type) (l1 : list A) (l2 : list B) (f : A -> B -> nat),
  nsum l1 (fun a => nsum l2 (fun b => f a b)) =
  nsum l2 (fun b => nsum l1 (fun a => f a b)).
Proof.
  intros A B l1 l2 f. induction l1 as [|x l1 IH].
  - rewrite nsum_nil. symmetry. apply nsum_zero.
  - rewrite nsum_cons, IH.
    rewrite (nsum_ext_in _ l2 (fun b => nsum (x :: l1) (fun a => f a b))
                       (fun b => (f x b + nsum l1 (fun a => f a b))%nat))
      by (intros b _; reflexivity).
    rewrite nsum_plus. reflexivity.
Qed.

Lemma nsum_perm : forall (A : Type) (l1 l2 : list A) (f : A -> nat),
  Permutation l1 l2 -> nsum l1 f = nsum l2 f.
Proof.
  intros A l1 l2 f H. induction H; simpl; unfold nsum in *; simpl; try lia.
Qed.

Lemma nsum_filter : forall (A : Type) (p : A -> bool) (l : list A) (f : A -> nat),
  nsum (filter p l) f = nsum l (fun x => if p x then f x else 0%nat).
Proof.
  intros A p l f. induction l as [|x l IH]; [reflexivity|].
  cbn [filter]. rewrite (nsum_cons _ x l).
  destruct (p x); [rewrite nsum_cons|]; rewrite IH; reflexivity.
Qed.

Lemma nsum_length : forall (A : Type) (l : list A), nsum l (fun _ => 1%nat) = List.length l.
Proof. intros A l. induction l as [|x l IH]; [reflexivity|]. rewrite nsum_cons, IH. reflexivity. Qed.

Lemma nsum_const : forall (A : Type) (l : list A) (c : nat),
  nsum l (fun _ => c) = (c * List.length l)%nat.
Proof. intros A l c. induction l as [|x l IH]; [unfold nsum; simpl; lia|]. rewrite nsum_cons, IH. simpl. lia. Qed.

(** Sum over a duplicate-free list L of the terms that lie in a
    duplicate-free sublist l. *)
Lemma nsum_indicator_sub : forall (A : Type) (L l : list A) (pm : A -> bool) (f : A -> nat),
  NoDup L -> NoDup l -> incl l L -> (forall x, pm x = true <-> In x l) ->
  nsum L (fun x => if pm x then f x else 0%nat) = nsum l f.
Proof.
  intros A L l pm f HL Hl Hincl Hpm.
  rewrite <- nsum_filter. apply nsum_perm. apply NoDup_Permutation.
  - apply NoDup_filter. exact HL.
  - exact Hl.
  - intros x. rewrite filter_In. rewrite Hpm. split; [tauto|].
    intros Hx. split; [apply Hincl; exact Hx|exact Hx].
Qed.

Lemma length_filter_split : forall (A : Type) (p : A -> bool) (l : list A),
  (List.length (filter p l) + List.length (filter (fun x => negb (p x)) l))%nat = List.length l.
Proof.
  intros A p l. induction l as [|x l IH]; [reflexivity|].
  simpl. destruct (p x); simpl; lia.
Qed.

Lemma length_same_elements : forall (A : Type) (l1 l2 : list A),
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 <-> In x l2) -> List.length l1 = List.length l2.
Proof.
  intros A l1 l2 H1 H2 H. apply Permutation_length. apply NoDup_Permutation; assumption.
Qed.

(** Double counting of incidences between items (vertices or edges) and
    faces. *)
Lemma double_count : forall (A B : Type) (L : list A) (M : list B)
    (items : B -> list A) (mem : B -> A -> bool) (h : A -> nat),
  NoDup L ->
  (forall b, In b M -> NoDup (items b) /\ incl (items b) L /\
                       forall x, mem b x = true <-> In x (items b)) ->
  nsum L (fun x => (h x * nsum M (fun b => if mem b x then 1 else 0))%nat) =
  nsum M (fun b => nsum (items b) h).
Proof.
  intros A B L M items mem h HL HM.
  rewrite (nsum_ext_in _ L _ (fun x => nsum M (fun b => if mem b x then h x else 0%nat))).
  - rewrite nsum_swap. apply nsum_ext_in. intros b Hb.
    destruct (HM b Hb) as [Hnd [Hincl Hmem]].
    apply nsum_indicator_sub; assumption.
  - intros x _. rewrite <- nsum_scal. apply nsum_ext_in. intros b _.
    destruct (mem b x); lia.
Qed.

(** Growth of a list from a root, each new element related to an earlier
    one (newest first). *)
Inductive grown (R : nat -> nat -> bool) (x0 : nat) : list nat -> Prop :=
| grown_one : grown R x0 [x0]
| grown_cons : forall x l, grown R x0 l -> (exists y, In y l /\ R y x = true) ->
    grown R x0 (x :: l).

Lemma grown_root : forall R x0 l, grown R x0 l -> In x0 l.
Proof.
  intros R x0 l H. induction H as [|x l H IH _]; [left; reflexivity|right; exact IH].
Qed.

Lemma grown_reach : forall R x0 l (P : nat -> Prop), grown R x0 l -> P x0 ->
  (forall x y, In x l -> In y l -> P x -> R x y = true -> P y) ->
  forall x, In x l -> P x.
Proof.
  intros R x0 l P H. induction H as [|x l H IH [y [Hy Ryx]]]; intros H0 Hcl z Hz.
  - destruct Hz as [Hz|[]]. subst. exact H0.
  - assert (Hl : forall w, In w l -> P w).
    { apply IH; [exact H0|]. intros a b Ha Hb. apply Hcl; right; assumption. }
    destruct Hz as [Hz|Hz]; [|apply Hl; exact Hz].
    subst z. apply (Hcl y x); [right; exact Hy|left; reflexivity|apply Hl; exact Hy|exact Ryx].
Qed.

Lemma bfs_aux : forall (R : nat -> nat -> bool) (S : list nat) x0 n C,
  grown R x0 C -> NoDup C -> incl C S -> (List.length S - List.length C <= n)%nat ->
  exists C', grown R x0 C' /\ NoDup C' /\ incl C' S /\
    (forall x y, In x C' -> In y S -> R x y = true -> In y C').
Proof.
  intros R S x0 n. induction n as [|n IH]; intros C HC Hnd Hincl Hlen.
  - destruct (find (fun y => negb (nat_list_mem y C) && existsb (fun x => R x y) C) S)
      as [y|] eqn:Hf.
    + exfalso. apply find_some in Hf. destruct Hf as [Hy Hp].
      apply andb_prop in Hp. destruct Hp as [Hm _].
      assert (HyC : ~ In y C).
      { intro HyC. apply nat_list_mem_In in HyC. rewrite HyC in Hm. discriminate. }
      assert (Hnd' : NoDup (y :: C)) by (constructor; assumption).
      assert (Hi : incl (y :: C) S) by (intros z [Hz|Hz]; [subst; exact Hy|apply Hincl; exact Hz]).
      pose proof (NoDup_incl_length Hnd' Hi). simpl in *. lia.
    + exists C. split; [exact HC|]. split; [exact Hnd|]. split; [exact Hincl|].
      intros x y Hx Hy Rxy. pose proof (find_none _ _ Hf y Hy) as Hp. simpl in Hp.
      destruct (nat_list_mem y C) eqn:Hm; [apply nat_list_mem_In; exact Hm|].
      exfalso. simpl in Hp.
      assert (existsb (fun x => R x y) C = true) by (apply existsb_exists; exists x; auto).
      congruence.
  - destruct (find (fun y => negb (nat_list_mem y C) && existsb (fun x => R x y) C) S)
      as [y|] eqn:Hf.
    + apply find_some in Hf. destruct Hf as [Hy Hp].
      apply andb_prop in Hp. destruct Hp as [Hm Hex].
      assert (HyC : ~ In y C).
      { intro HyC. apply nat_list_mem_In in HyC. rewrite HyC in Hm. discriminate. }
      assert (Hnd' : NoDup (y :: C)) by (constructor; assumption).
      assert (Hi : incl (y :: C) S) by (intros z [Hz|Hz]; [subst; exact Hy|apply Hincl; exact Hz]).
      pose proof (NoDup_incl_length Hnd' Hi).
      apply (IH (y :: C)); [|exact Hnd'|exact Hi|simpl in *; lia].
      apply grown_cons; [exact HC|]. apply existsb_exists in Hex.
      destruct Hex as [x [Hx Rx]]. exists x. split; assumption.
    + exists C. split; [exact HC|]. split; [exact Hnd|]. split; [exact Hincl|].
      intros x y Hx Hy Rxy. pose proof (find_none _ _ Hf y Hy) as Hp. simpl in Hp.
      destruct (nat_list_mem y C) eqn:Hm; [apply nat_list_mem_In; exact Hm|].
      exfalso. simpl in Hp.
      assert (existsb (fun x => R x y) C = true) by (apply existsb_exists; exists x; auto).
      congruence.
Qed.

(** Breadth-first search: the part of S reachable from x0, closed under R. *)
Lemma bfs : forall (R : nat -> nat -> bool) (S : list nat) x0, In x0 S ->
  exists C, grown R x0 C /\ NoDup C /\ incl C S /\
    (forall x y, In x C -> In y S -> R x y = true -> In y C).
Proof.
  intros R S x0 H. apply (bfs_aux R S x0 (List.length S) [x0]).
  - apply grown_one.
  - constructor; [intros []|constructor].
  - intros z [Hz|[]]. subst. exact H.
  - lia.
Qed.

Lemma norm_edge_inv : forall a b c d, norm_edge a b = norm_edge c d ->
  (a = c /\ b = d) \/ (a = d /\ b = c).
Proof.
  intros a b c d H. unfold norm_edge in H.
  destruct (a <? b), (c <? d); inversion H; subst; auto.
Qed.

Lemma norm_edge_lt : forall x y, x <> y -> (fst (norm_edge x y) < snd (norm_edge x y))%nat.
Proof.
  intros x y H. unfold norm_edge. destruct (Nat.ltb_spec x y); simpl; lia.
Qed.

Lemma norm_edge_fst_snd : forall e, (fst e < snd e)%nat -> norm_edge (fst e) (snd e) = e.
Proof.
  intros [a b] H. simpl in *. unfold norm_edge. destruct (Nat.ltb_spec a b); [reflexivity|lia].
Qed.

Lemma norm_edge_swap_fst_snd : forall e, (fst e < snd e)%nat -> norm_edge (snd e) (fst e) = e.
Proof.
  intros [a b] H. simpl in *. unfold norm_edge. destruct (Nat.ltb_spec b a); [lia|reflexivity].
Qed.

Lemma norm_edge_ends : forall x y (P : nat -> bool),
  P (fst (norm_edge x y)) = P (snd (norm_edge x y)) -> P x = P y.
Proof.
  intros x y P H. unfold norm_edge in H. destruct (x <? y); simpl in H; congruence.
Qed.

(** A grown list of n vertices carries n - 1 distinct edges of R. *)
Lemma grown_edges : forall R x0 C, grown R x0 C -> NoDup C ->
  exists Es : list (nat * nat), NoDup Es /\ S (List.length Es) = List.length C /\
    forall e, In e Es -> exists x y, In x C /\ In y C /\ R y x = true /\ e = norm_edge y x.
Proof.
  intros R x0 C H. induction H as [|x l H IH [y [Hy Ryx]]]; intros Hnd.
  - exists []. split; [constructor|]. split; [reflexivity|]. intros e [].
  - inversion Hnd as [|? ? Hx Hnd']. subst.
    destruct (IH Hnd') as [Es [HEs [Hlen Hall]]].
    exists (norm_edge y x :: Es). split; [|split].
    + constructor; [|exact HEs]. intro Hin.
      destruct (Hall _ Hin) as [x' [y' [Hx' [Hy' [_ Heq]]]]].
      apply norm_edge_inv in Heq. destruct Heq as [[E1 E2]|[E1 E2]]; subst; contradiction.
    + simpl. rewrite Hlen. reflexivity.
    + intros e [He|He].
      * subst e. exists x, y. split; [left; reflexivity|]. split; [right; exact Hy|].
        split; [exact Ryx|reflexivity].
      * destruct (Hall e He) as [x' [y' [Hx' [Hy' [R' Heq]]]]].
        exists x', y'. split; [right; exact Hx'|]. split; [right; exact Hy'|]. auto.
Qed.

Lemma edge_eq_true : forall e1 e2, edge_eq e1 e2 = true -> e1 = e2.
Proof.
  intros [a b] [c d] H. unfold edge_eq in H. simpl in H.
  apply andb_prop in H. destruct H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma list_mem_edge_iff : forall e l, list_mem edge_eq e l = true <-> In e l.
Proof.
  intros e l. split; [|apply list_mem_edge_In].
  induction l as [|y l IH]; simpl; [discriminate|].
  destruct (edge_eq e y) eqn:Hey.
  - intros _. left. symmetry. apply edge_eq_true. exact Hey.
  - intros H. right. apply IH. exact H.
Qed.

(** A connected edge set on a vertex list has at least |V| - 1 edges. *)
Lemma connected_edge_count : forall (Vs : list nat) (H : list (nat * nat)) (r0 : nat),
  NoDup Vs -> NoDup H -> In r0 Vs ->
  (forall e, In e H -> (fst e < snd e)%nat /\ In (fst e) Vs /\ In (snd e) Vs) ->
  (forall P : nat -> bool, P r0 = true ->
     (forall e, In e H -> P (fst e) = P (snd e)) -> forall v, In v Vs -> P v = true) ->
  (List.length Vs <= S (List.length H))%nat.
Proof.
  intros Vs H r0 HV HH Hr0 Hends Hconn.
  set (R := fun u w => negb (u =? w) && list_mem edge_eq (norm_edge u w) H).
  destruct (bfs R Vs r0 Hr0) as [C [HC [HndC [HinclC HclC]]]].
  assert (Hall : forall v, In v Vs -> nat_list_mem v C = true).
  { apply Hconn.
    - apply nat_list_mem_In. eapply grown_root. exact HC.
    - intros e He. destruct (Hends e He) as [Hlt [Hu Hw]].
      assert (Ruw : R (fst e) (snd e) = true).
      { unfold R. rewrite norm_edge_fst_snd by exact Hlt.
        destruct (Nat.eqb_spec (fst e) (snd e)); [lia|]. simpl.
        apply list_mem_edge_iff. exact He. }
      assert (Rwu : R (snd e) (fst e) = true).
      { unfold R. rewrite norm_edge_swap_fst_snd by exact Hlt.
        destruct (Nat.eqb_spec (snd e) (fst e)); [lia|]. simpl.
        apply list_mem_edge_iff. exact He. }
      destruct (nat_list_mem (fst e) C) eqn:H1, (nat_list_mem (snd e) C) eqn:H2;
        try reflexivity.
      + apply nat_list_mem_In in H1.
        pose proof (HclC _ _ H1 Hw Ruw) as H3. apply nat_list_mem_In in H3. congruence.
      + apply nat_list_mem_In in H2.
        pose proof (HclC _ _ H2 Hu Rwu) as H3. apply nat_list_mem_In in H3. congruence. }
  destruct (grown_edges R r0 C HC HndC) as [Es [HEs [Hlen HEsR]]].
  assert (Hincl : incl Es H).
  { intros e He. destruct (HEsR e He) as [x [y [_ [_ [Ryx Heq]]]]].
    unfold R in Ryx. apply andb_prop in Ryx. destruct Ryx as [_ Hm].
    apply list_mem_edge_iff in Hm. subst. exact Hm. }
  pose proof (NoDup_incl_length HEs Hincl).
  assert (HVC : incl Vs C) by (intros v Hv; apply nat_list_mem_In; apply Hall; exact Hv).
  pose proof (NoDup_incl_length HV HVC). lia.
Qed.

(** Either the edge set stays connected after deleting b (then it has at
    least |V| edges), or deleting b separates its two ends. *)
Lemma cut_or_count : forall (Vs : list nat) (H : list (nat * nat)) (r0 : nat) (b : nat * nat),
  NoDup Vs -> NoDup H -> In r0 Vs -> In b H ->
  (forall e, In e H -> (fst e < snd e)%nat /\ In (fst e) Vs /\ In (snd e) Vs) ->
  (forall P : nat -> bool, P r0 = true ->
     (forall e, In e H -> P (fst e) = P (snd e)) -> forall v, In v Vs -> P v = true) ->
  (List.length Vs <= List.length H)%nat \/
  exists P : nat -> bool, P (fst b) = true /\ P (snd b) = false /\
    forall e, In e H -> e <> b -> P (fst e) = P (snd e).
Proof.
  intros Vs H r0 b HV HH Hr0 Hb Hends Hconn.
  set (H' := filter (fun e => negb (edge_eq e b)) H).
  assert (HinH' : forall e, In e H' <-> In e H /\ e <> b).
  { intros e. unfold H'. rewrite filter_In. split.
    - intros [He Hne]. split; [exact He|]. intro E. subst. rewrite edge_eq_refl in Hne. discriminate.
    - intros [He Hne]. split; [exact He|]. destruct (edge_eq e b) eqn:Eb; [|reflexivity].
      exfalso. apply Hne. apply edge_eq_true. exact Eb. }
  assert (HlenH' : S (List.length H') = List.length H).
  { assert (Hsplit := length_filter_split _ (fun e => negb (edge_eq e b)) H).
    fold H' in Hsplit.
    assert (Hone : List.length (filter (fun x => negb (negb (edge_eq x b))) H) = 1%nat).
    { apply (length_same_elements _ _ [b]).
      - apply NoDup_filter. exact HH.
      - constructor; [intros []|constructor].
      - intros x. rewrite filter_In. rewrite negb_involutive. split.
        + intros [Hx Ex]. left. symmetry. apply edge_eq_true. exact Ex.
        + intros [Hx|[]]. subst. split; [exact Hb|apply edge_eq_refl]. }
    lia. }
  assert (HbV : In (fst b) Vs) by (apply (Hends b Hb)).
  set (R := fun u w => negb (u =? w) && list_mem edge_eq (norm_edge u w) H').
  destruct (bfs R Vs (fst b) HbV) as [C [HC [HndC [HinclC HclC]]]].
  assert (Hcl' : forall e, In e H -> e <> b ->
            nat_list_mem (fst e) C = nat_list_mem (snd e) C).
  { intros e He Hne. destruct (Hends e He) as [Hlt [Hu Hw]].
    assert (He' : In e H') by (apply HinH'; split; assumption).
    assert (Ruw : R (fst e) (snd e) = true).
    { unfold R. rewrite norm_edge_fst_snd by exact Hlt.
      destruct (Nat.eqb_spec (fst e) (snd e)); [lia|]. simpl.
      apply list_mem_edge_iff. exact He'. }
    assert (Rwu : R (snd e) (fst e) = true).
    { unfold R. rewrite norm_edge_swap_fst_snd by exact Hlt.
      destruct (Nat.eqb_spec (snd e) (fst e)); [lia|]. simpl.
      apply list_mem_edge_iff. exact He'. }
    destruct (nat_list_mem (fst e) C) eqn:H1, (nat_list_mem (snd e) C) eqn:H2;
      try reflexivity.
    + apply nat_list_mem_In in H1.
      pose proof (HclC _ _ H1 Hw Ruw) as H3. apply nat_list_mem_In in H3. congruence.
    + apply nat_list_mem_In in H2.
      pose proof (HclC _ _ H2 Hu Rwu) as H3. apply nat_list_mem_In in H3. congruence. }
  assert (Hfb : nat_list_mem (fst b) C = true).
  { apply nat_list_mem_In. eapply grown_root. exact HC. }
  destruct (nat_list_mem (snd b) C) eqn:Hsb.
  - left.
    assert (Hclosed : forall e, In e H -> nat_list_mem (fst e) C = nat_list_mem (snd e) C).
    { intros e He. destruct (pair_eq_dec Nat.eq_dec Nat.eq_dec e b) as [E|Ne].
      - subst. rewrite Hfb, Hsb. reflexivity.
      - apply Hcl'; assumption. }
    assert (Hall : forall v, In v Vs -> nat_list_mem v C = true).
    { destruct (nat_list_mem r0 C) eqn:Hr.
      - apply Hconn; assumption.
      - exfalso.
        assert (Hneg := Hconn (fun v => negb (nat_list_mem v C))).
        simpl in Hneg. rewrite Hr in Hneg.
        assert (Hx := Hneg eq_refl).
        assert (Hc : forall e, In e H ->
                  negb (nat_list_mem (fst e) C) = negb (nat_list_mem (snd e) C)).
        { intros e He. rewrite (Hclosed e He). reflexivity. }
        specialize (Hx Hc (fst b) HbV). rewrite Hfb in Hx. discriminate. }
    destruct (grown_edges R (fst b) C HC HndC) as [Es [HEs [Hlen HEsR]]].
    assert (Hincl : incl Es H').
    { intros e He. destruct (HEsR e He) as [x [y [_ [_ [Ryx Heq]]]]].
      unfold R in Ryx. apply andb_prop in Ryx. destruct Ryx as [_ Hm].
      apply list_mem_edge_iff in Hm. subst. exact Hm. }
    pose proof (NoDup_incl_length HEs Hincl).
    assert (HVC : incl Vs C) by (intros v Hv; apply nat_list_mem_In; apply Hall; exact Hv).
    pose proof (NoDup_incl_length HV HVC). lia.
  - right. exists (fun v => nat_list_mem v C). split; [exact Hfb|]. split; [exact Hsb|].
    exact Hcl'.
Qed.

(** * Part 9. Vertex, edge and face incidences of a module list. *)

(** Every region is a duplicate-free list of three nodes. *)
Definition tri_ok (g : PartitionGraph) : Prop :=
  forall mid m, In (mid, m) (pg_modules g) ->
    NoDup (module_region m) /\ List.length (module_region m) = 3%nat.

Lemma tri_ok_of_wf : forall g,
  all_modules_are_triangles_list g -> all_regions_normalized_list g -> tri_ok g.
Proof.
  intros g Ht Hn mid m Hin. split.
  - rewrite (Hn mid m Hin). apply normalize_region_nodup.
  - exact (triangulated_regions_are_triples g Ht Hn mid m Hin).
Qed.

Lemma NoDup_app_disj : forall (A : Type) (l1 l2 : list A),
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1. induction H1 as [|x l1 Hx H1 IH]; intros H2 Hd; [exact H2|].
  simpl. constructor.
  - rewrite in_app_iff. intros [H|H]; [contradiction|].
    exact (Hd x (or_introl eq_refl) H).
  - apply IH; [exact H2|]. intros y Hy. apply Hd. right. exact Hy.
Qed.

Lemma collect_nodes_In : forall mods v,
  In v (collect_nodes_from_modules mods) <->
  exists p, In p mods /\ In v (module_region (snd p)).
Proof.
  induction mods as [|[id m] rest IH]; intros v; simpl.
  - split; [intros []|intros [p [[] _]]].
  - rewrite in_app_iff, IH. split.
    + intros [H|[p [Hp Hv]]]; [exists (id, m); auto|exists p; auto].
    + intros [p [[Hp|Hp] Hv]]; [subst; left; exact Hv|right; exists p; auto].
Qed.

Lemma vertices_In : forall g v,
  In v (vertices g) <-> exists p, In p (pg_modules g) /\ In v (module_region (snd p)).
Proof.
  intros g v. unfold vertices, normalize_region. rewrite nodup_In. apply collect_nodes_In.
Qed.

Lemma vertices_NoDup : forall g, NoDup (vertices g).
Proof. intros g. apply normalize_region_nodup. Qed.

Lemma region_edges_inv : forall r e, In e (region_edges_internal r) ->
  In (fst e) r /\ In (snd e) r.
Proof.
  induction r as [|n rest IH]; intros e H; simpl in H; [destruct H|].
  apply in_app_iff in H. destruct H as [H|H].
  - apply in_map_iff in H. destruct H as [m [He Hm]]. subst e.
    change (if n <? m then (n, m) else (m, n)) with (norm_edge n m).
    unfold norm_edge. destruct (n <? m); simpl; auto.
  - destruct (IH e H). simpl. auto.
Qed.

Lemma region_edges_inv_nodup : forall r e, NoDup r -> In e (region_edges_internal r) ->
  exists x y, In x r /\ In y r /\ x <> y /\ e = norm_edge x y.
Proof.
  induction r as [|n rest IH]; intros e Hnd H; simpl in H; [destruct H|].
  inversion Hnd as [|? ? Hn Hnd']. subst.
  apply in_app_iff in H. destruct H as [H|H].
  - apply in_map_iff in H. destruct H as [m [He Hm]].
    exists n, m. split; [left; reflexivity|]. split; [right; exact Hm|].
    split; [intro E; subst; contradiction|]. symmetry. exact He.
  - destruct (IH e Hnd' H) as [x [y [Hx [Hy [Hxy He]]]]].
    exists x, y. split; [right; exact Hx|]. split; [right; exact Hy|]. auto.
Qed.

Lemma norm_edge_In_fst : forall x y, fst (norm_edge x y) = x \/ fst (norm_edge x y) = y.
Proof. intros x y. unfold norm_edge. destruct (x <? y); simpl; auto. Qed.

Lemma norm_edge_In_snd : forall x y, snd (norm_edge x y) = x \/ snd (norm_edge x y) = y.
Proof. intros x y. unfold norm_edge. destruct (x <? y); simpl; auto. Qed.

Lemma region_edges_iff : forall r e, NoDup r ->
  (In e (region_edges_internal r) <->
   (fst e < snd e)%nat /\ In (fst e) r /\ In (snd e) r).
Proof.
  intros r e Hnd. split.
  - intros H. destruct (region_edges_inv_nodup r e Hnd H) as [x [y [Hx [Hy [Hxy He]]]]].
    subst e. split; [apply norm_edge_lt; exact Hxy|].
    split; [destruct (norm_edge_In_fst x y) as [E|E]|destruct (norm_edge_In_snd x y) as [E|E]];
      rewrite E; assumption.
  - intros [Hlt [H1 H2]]. rewrite <- (norm_edge_fst_snd e Hlt).
    apply region_edges_In; [lia|exact H1|exact H2].
Qed.

Lemma map_norm_nodup : forall n rest, ~ In n rest -> NoDup rest ->
  NoDup (map (fun m => if n <? m then (n, m) else (m, n)) rest).
Proof.
  intros n rest Hn Hnd. induction Hnd as [|m rest Hm Hnd IH]; simpl; [constructor|].
  constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [m' [He Hm']].
    change (norm_edge n m' = norm_edge n m) in He.
    apply norm_edge_inv in He. destruct He as [[_ E]|[E1 E2]].
    + subst. contradiction.
    + subst. apply Hn. left. reflexivity.
  - apply IH. intro H. apply Hn. right. exact H.
Qed.

Lemma region_edges_nodup : forall r, NoDup r -> NoDup (region_edges_internal r).
Proof.
  induction r as [|n rest IH]; intros Hnd; simpl; [constructor|].
  inversion Hnd as [|? ? Hn Hnd']. subst.
  apply NoDup_app_disj.
  - apply map_norm_nodup; assumption.
  - apply IH. exact Hnd'.
  - intros e He1 He2. apply in_map_iff in He1. destruct He1 as [m [He Hm]].
    destruct (region_edges_inv rest e He2) as [Hf Hs]. subst e.
    change (if n <? m then (n, m) else (m, n)) with (norm_edge n m) in Hf, Hs.
    unfold norm_edge in Hf, Hs. destruct (n <? m); simpl in Hf, Hs; contradiction.
Qed.

Lemma region_edges_length3 : forall r, List.length r = 3%nat ->
  List.length (region_edges_internal r) = 3%nat.
Proof.
  intros r H. destruct r as [|a [|b [|c [|d r]]]]; simpl in H; try discriminate.
  reflexivity.
Qed.

Lemma collect_edges_iff : forall mods e,
  In e (collect_edges_from_modules mods) <->
  exists p, In p mods /\ In e (module_edges (snd p)).
Proof.
  induction mods as [|[id m] rest IH]; intros e; simpl.
  - split; [intros []|intros [p [[] _]]].
  - rewrite in_app_iff, IH. split.
    + intros [H|[p [Hp He]]]; [exists (id, m); auto|exists p; auto].
    + intros [p [[Hp|Hp] He]]; [subst; left; exact He|right; exists p; auto].
Qed.

Lemma dedup_In_iff : forall e l, In e (deduplicate_edges l) <-> In e l.
Proof.
  intros e l. split; [|apply dedup_In].
  induction l as [|e' rest IH]; simpl; [intros []|].
  destruct (existsb _ rest); [intros H; right; apply IH; exact H|].
  intros [H|H]; [left; exact H|right; apply IH; exact H].
Qed.

Lemma dedup_NoDup : forall l, NoDup (deduplicate_edges l).
Proof.
  induction l as [|e rest IH]; simpl; [constructor|].
  destruct (existsb _ rest) eqn:Hex; [exact IH|].
  constructor; [|exact IH].
  rewrite dedup_In_iff. intro Hin.
  assert (existsb (fun e' => (fst e =? fst e') && (snd e =? snd e')) rest = true).
  { apply existsb_exists. exists e. split; [exact Hin|]. rewrite !Nat.eqb_refl. reflexivity. }
  congruence.
Qed.

Lemma edges_In : forall g e,
  In e (edges g) <-> exists p, In p (pg_modules g) /\ In e (module_edges (snd p)).
Proof. intros g e. unfold edges. rewrite dedup_In_iff. apply collect_edges_iff. Qed.

Lemma edges_NoDup : forall g, NoDup (edges g).
Proof. intros g. apply dedup_NoDup. Qed.

Lemma count_modules_with_edge_nsum : forall e mods,
  count_modules_with_edge e mods =
  nsum mods (fun p => if list_mem edge_eq e (module_edges (snd p)) then 1%nat else 0%nat).
Proof.
  intros e mods. induction mods as [|[id m] rest IH]; [reflexivity|].
  simpl. rewrite nsum_cons. simpl. destruct (list_mem edge_eq e (module_edges m)); rewrite IH; reflexivity.
Qed.

Lemma count_incident_nsum : forall v mods,
  count_incident_triangles v mods =
  nsum mods (fun p => if nat_list_mem v (module_region (snd p)) then 1%nat else 0%nat).
Proof.
  intros v mods. induction mods as [|[id m] rest IH]; [reflexivity|].
  simpl. rewrite nsum_cons. simpl. destruct (nat_list_mem v (module_region m)); rewrite IH; reflexivity.
Qed.

Lemma sum_degrees_nsum : forall g l, sum_degrees g l = nsum l (vertex_degree g).
Proof.
  intros g l. induction l as [|v l IH]; [reflexivity|]. simpl. rewrite nsum_cons, IH. reflexivity.
Qed.

Lemma count_boundary_filter : forall l g,
  count_boundary_edges l g =
  List.length (filter (fun e => count_modules_with_edge e (pg_modules g) =? 1) l).
Proof.
  intros l g. induction l as [|e l IH]; [reflexivity|].
  simpl. unfold is_boundary_edge. destruct (count_modules_with_edge e (pg_modules g) =? 1);
    simpl; rewrite IH; reflexivity.
Qed.

Lemma module_edges_props : forall g p, tri_ok g -> In p (pg_modules g) ->
  NoDup (module_edges (snd p)) /\ incl (module_edges (snd p)) (edges g) /\
  List.length (module_edges (snd p)) = 3%nat.
Proof.
  intros g [mid m] Htri Hp. destruct (Htri mid m Hp) as [Hnd H3]. simpl.
  split; [apply region_edges_nodup; exact Hnd|]. split.
  - intros e He. apply edges_In. exists (mid, m). split; assumption.
  - apply region_edges_length3. exact H3.
Qed.

(** The sum of vertex degrees is three times the number of faces, for any
    module list of triangles. *)
Theorem degree_sum_general : forall g, tri_ok g ->
  sum_degrees g (vertices g) = (3 * DiscreteTopology.F g)%nat.
Proof.
  intros g Htri. rewrite sum_degrees_nsum. unfold vertex_degree, DiscreteTopology.F.
  rewrite (nsum_ext_in _ _ _ (fun v => (1 * nsum (pg_modules g)
              (fun p => if nat_list_mem v (module_region (snd p)) then 1%nat else 0%nat))%nat))
    by (intros v _; rewrite count_incident_nsum; lia).
  rewrite (double_count _ _ (vertices g) (pg_modules g) (fun p => module_region (snd p))
             (fun p v => nat_list_mem v (module_region (snd p))) (fun _ => 1%nat)).
  - rewrite (nsum_ext_in _ _ _ (fun _ => 3%nat)).
    + rewrite nsum_const. reflexivity.
    + intros [mid m] Hp. rewrite nsum_length. apply (Htri mid m Hp).
  - apply vertices_NoDup.
  - intros [mid m] Hp. destruct (Htri mid m Hp) as [Hnd _]. split; [exact Hnd|]. split.
    + intros v Hv. apply vertices_In. exists (mid, m). split; assumption.
    + intros v. apply nat_list_mem_In.
Qed.

Theorem edge_sum_general : forall g, tri_ok g ->
  nsum (edges g) (fun e => count_modules_with_edge e (pg_modules g)) =
  (3 * DiscreteTopology.F g)%nat.
Proof.
  intros g Htri. unfold DiscreteTopology.F.
  rewrite (nsum_ext_in _ _ _ (fun e => (1 * nsum (pg_modules g)
              (fun p => if list_mem edge_eq e (module_edges (snd p)) then 1%nat else 0%nat))%nat))
    by (intros e _; rewrite count_modules_with_edge_nsum; lia).
  rewrite (double_count _ _ (edges g) (pg_modules g) (fun p => module_edges (snd p))
             (fun p e => list_mem edge_eq e (module_edges (snd p))) (fun _ => 1%nat)).
  - rewrite (nsum_ext_in _ _ _ (fun _ => 3%nat)).
    + rewrite nsum_const. reflexivity.
    + intros p Hp. rewrite nsum_length. apply (module_edges_props g p Htri Hp).
  - apply edges_NoDup.
  - intros p Hp. destruct (module_edges_props g p Htri Hp) as [Hnd [Hincl _]].
    split; [exact Hnd|]. split; [exact Hincl|].
    intros e. apply list_mem_edge_iff.
Qed.

Lemma nsum_one_two : forall (A : Type) (l : list A) (c : A -> nat),
  (forall e, In e l -> c e = 1%nat \/ c e = 2%nat) ->
  (nsum l c + List.length (filter (fun e => c e =? 1) l))%nat = (2 * List.length l)%nat.
Proof.
  intros A l c H. induction l as [|e l IH]; [reflexivity|].
  rewrite nsum_cons. simpl.
  assert (IH' := IH (fun x Hx => H x (or_intror Hx))).
  destruct (H e (or_introl eq_refl)) as [E|E]; rewrite E; simpl; lia.
Qed.

(** On a 2-manifold of triangles, 2E = 3F + B. *)
Theorem edges_faces_boundary : forall g, tri_ok g -> is_2_manifold g ->
  (2 * DiscreteTopology.E g = 3 * DiscreteTopology.F g + DiscreteTopology.B g)%nat.
Proof.
  intros g Htri Hman.
  rewrite <- edge_sum_general by exact Htri.
  unfold DiscreteTopology.E, DiscreteTopology.B. rewrite count_boundary_filter.
  rewrite <- (nsum_one_two _ (edges g) (fun e => count_modules_with_edge e (pg_modules g))).
  - reflexivity.
  - intros e He. exact (Hman e He).
Qed.

(** * Part 10. Euler characteristic of an edge-connected component. *)

(** The normalized edge e lies in the face with ID a. *)
Definition ein (s : VMState) (e : nat * nat) (a : ModuleID) : bool :=
  (fst e <? snd e) && cont s (fst e) a && cont s (snd e) a.

(** Two faces share an edge (two distinct nodes). *)
Definition share_edge (s : VMState) (a b : ModuleID) : bool :=
  match graph_lookup (vm_graph s) a with
  | Some ma => existsb (fun e => ein s e b) (module_edges ma)
  | None => false
  end.

Lemma cont_entry : forall s v a m,
  NoDup (map fst (pg_modules (vm_graph s))) ->
  In (a, m) (pg_modules (vm_graph s)) ->
  cont s v a = nat_list_mem v (module_region m).
Proof.
  intros s v a m Hnd Hin. unfold cont, graph_lookup.
  rewrite (graph_lookup_modules_nodup _ _ _ Hnd Hin). reflexivity.
Qed.

Lemma cont_true_entry : forall s v a, cont s v a = true ->
  exists m, graph_lookup (vm_graph s) a = Some m /\
            In (a, m) (pg_modules (vm_graph s)) /\ In v (module_region m).
Proof.
  intros s v a H. destruct (cont_lookup s v a H) as [m [Hl Hv]].
  exists m. split; [exact Hl|]. split; [|exact Hv].
  apply graph_lookup_modules_In. exact Hl.
Qed.

Lemma ein_norm : forall s x y a, x <> y ->
  ein s (norm_edge x y) a = cont s x a && cont s y a.
Proof.
  intros s x y a H. unfold ein, norm_edge.
  destruct (Nat.ltb_spec x y); simpl.
  - destruct (Nat.ltb_spec x y); [|lia]. reflexivity.
  - destruct (Nat.ltb_spec y x); [|lia]. simpl. apply andb_comm.
Qed.

Lemma ein_entry : forall s e a, ein s e a = true ->
  exists m, graph_lookup (vm_graph s) a = Some m /\
            In (a, m) (pg_modules (vm_graph s)) /\
            In e (module_edges m) /\ (fst e < snd e)%nat.
Proof.
  intros s e a H. unfold ein in H.
  destruct (Nat.ltb_spec (fst e) (snd e)) as [Hlt|]; [|discriminate].
  destruct (cont s (fst e) a) eqn:H1; [|discriminate].
  destruct (cont s (snd e) a) eqn:H2; [|discriminate].
  destruct (cont_true_entry s _ _ H1) as [m [Hl [Hin Hv1]]].
  destruct (cont_true_entry s _ _ H2) as [m' [Hl' [_ Hv2]]].
  rewrite Hl in Hl'. inversion Hl'. subst m'.
  exists m. split; [exact Hl|]. split; [exact Hin|]. split; [|exact Hlt].
  unfold module_edges. rewrite <- (norm_edge_fst_snd e Hlt).
  apply region_edges_In; [lia|exact Hv1|exact Hv2].
Qed.

Lemma ein_edges : forall s e a, ein s e a = true -> In e (edges (vm_graph s)).
Proof.
  intros s e a H. destruct (ein_entry s e a H) as [m [_ [Hin [He _]]]].
  apply edges_In. exists (a, m). split; assumption.
Qed.

Lemma edges_ein : forall s e,
  NoDup (map fst (pg_modules (vm_graph s))) -> tri_ok (vm_graph s) ->
  In e (edges (vm_graph s)) ->
  exists a, In a (map fst (pg_modules (vm_graph s))) /\ ein s e a = true.
Proof.
  intros s e Hnd Htri He. apply edges_In in He. destruct He as [[a m] [Hin He]].
  simpl in He. destruct (Htri a m Hin) as [Hr _].
  apply region_edges_iff in He; [|exact Hr]. destruct He as [Hlt [H1 H2]].
  exists a. split; [apply in_map_iff; exists (a, m); auto|].
  unfold ein. rewrite !(cont_entry s _ a m Hnd Hin).
  apply nat_list_mem_In in H1. apply nat_list_mem_In in H2. rewrite H1, H2.
  destruct (Nat.ltb_spec (fst e) (snd e)); [reflexivity|lia].
Qed.

Lemma ein_count2 : forall s e a b, a <> b -> ein s e a = true -> ein s e b = true ->
  (2 <= count_modules_with_edge e (pg_modules (vm_graph s)))%nat.
Proof.
  intros s e a b Hab Ha Hb.
  destruct (ein_entry s e a Ha) as [ma [_ [Ia [Ea _]]]].
  destruct (ein_entry s e b Hb) as [mb [_ [Ib [Eb _]]]].
  rewrite count_modules_with_edge_filter.
  set (P := fun p : ModuleID * ModuleState => list_mem edge_eq e (module_edges (snd p))).
  assert (Hnd2 : NoDup [(a, ma); (b, mb)]).
  { constructor; [simpl; intros [E|[]]; congruence|]. constructor; [intros []|constructor]. }
  assert (Hincl : incl [(a, ma); (b, mb)] (filter P (pg_modules (vm_graph s)))).
  { intros p Hp. apply filter_In. unfold P.
    destruct Hp as [Hp|[Hp|[]]]; subst p; simpl; split; auto; apply list_mem_edge_iff; assumption. }
  pose proof (NoDup_incl_length Hnd2 Hincl) as H. simpl in H. exact H.
Qed.

Lemma three_faces_ein : forall s e a b c,
  NoDup (map fst (pg_modules (vm_graph s))) -> is_2_manifold (vm_graph s) ->
  a <> b -> a <> c -> b <> c ->
  ein s e a = true -> ein s e b = true -> ein s e c = true -> False.
Proof.
  intros s e a b c Hnd Hman Hab Hac Hbc Ha Hb Hc. unfold ein in Ha, Hb, Hc.
  destruct (Nat.ltb_spec (fst e) (snd e)) as [Hlt|]; [|discriminate].
  apply andb_prop in Ha. destruct Ha as [Ha2 Ha1]. apply andb_prop in Ha2. destruct Ha2 as [_ Ha0].
  apply andb_prop in Hb. destruct Hb as [Hb2 Hb1]. apply andb_prop in Hb2. destruct Hb2 as [_ Hb0].
  apply andb_prop in Hc. destruct Hc as [Hc2 Hc1]. apply andb_prop in Hc2. destruct Hc2 as [_ Hc0].
  apply (no_three_faces_on_edge s Hnd Hman a b c (fst e) (snd e)); try assumption; [|lia].
  unfold dist3. destruct (Nat.eqb_spec a b), (Nat.eqb_spec a c), (Nat.eqb_spec b c);
    try contradiction; reflexivity.
Qed.

Lemma share_edge_spec : forall s a b, share_edge s a b = true ->
  exists x y, x <> y /\ cont s x a = true /\ cont s y a = true /\
              cont s x b = true /\ cont s y b = true.
Proof.
  intros s a b H. unfold share_edge in H.
  destruct (graph_lookup (vm_graph s) a) as [ma|] eqn:Hl; [|discriminate].
  apply existsb_exists in H. destruct H as [e [He Heb]].
  destruct (region_edges_inv _ e He) as [H1 H2].
  unfold ein in Heb.
  destruct (Nat.ltb_spec (fst e) (snd e)) as [Hlt|]; [|discriminate].
  apply andb_prop in Heb. destruct Heb as [Heb Hs]. apply andb_prop in Heb. destruct Heb as [_ Hf].
  exists (fst e), (snd e). split; [lia|].
  unfold cont at 1 2. rewrite Hl.
  split; [apply nat_list_mem_In; exact H1|]. split; [apply nat_list_mem_In; exact H2|].
  split; assumption.
Qed.

Lemma share_edge_intro : forall s a b x y, x <> y ->
  cont s x a = true -> cont s y a = true -> cont s x b = true -> cont s y b = true ->
  share_edge s a b = true.
Proof.
  intros s a b x y Hxy Hxa Hya Hxb Hyb.
  destruct (cont_lookup s x a Hxa) as [ma [Hl Hx]].
  destruct (cont_lookup s y a Hya) as [ma' [Hl' Hy]].
  rewrite Hl in Hl'. inversion Hl'. subst ma'.
  unfold share_edge. rewrite Hl. apply existsb_exists. exists (norm_edge x y). split.
  - apply region_edges_In; assumption.
  - rewrite ein_norm by exact Hxy. rewrite Hxb, Hyb. reflexivity.
Qed.

Lemma third_vertex : forall (r : list nat) (x y : nat), NoDup r -> List.length r = 3%nat ->
  In x r -> In y r -> x <> y ->
  exists w, In w r /\ w <> x /\ w <> y /\ forall v, In v r -> v = x \/ v = y \/ v = w.
Proof.
  intros r x y Hnd H3 Hx Hy Hxy.
  destruct r as [|p [|q [|t [|z r]]]]; simpl in H3; try discriminate.
  assert (Hpq : p <> q) by (intro E; subst; inversion Hnd as [|? ? Hn _]; apply Hn; left; reflexivity).
  assert (Hpt : p <> t) by (intro E; subst; inversion Hnd as [|? ? Hn _]; apply Hn; right; left; reflexivity).
  assert (Hqt : q <> t).
  { intro E; subst. inversion Hnd as [|? ? _ Hnd']. inversion Hnd' as [|? ? Hn _].
    apply Hn. left. reflexivity. }
  destruct Hx as [<-|[<-|[<-|[]]]]; destruct Hy as [<-|[<-|[<-|[]]]];
    try (exfalso; apply Hxy; reflexivity).
  - exists t. split; [simpl; auto|]. split; [auto|]. split; [auto|].
    intros v [<-|[<-|[<-|[]]]]; auto.
  - exists q. split; [simpl; auto|]. split; [auto|]. split; [auto|].
    intros v [<-|[<-|[<-|[]]]]; auto.
  - exists t. split; [simpl; auto|]. split; [auto|]. split; [auto|].
    intros v [<-|[<-|[<-|[]]]]; auto.
  - exists p. split; [simpl; auto|]. split; [auto|]. split; [auto|].
    intros v [<-|[<-|[<-|[]]]]; auto.
  - exists q. split; [simpl; auto|]. split; [auto|]. split; [auto|].
    intros v [<-|[<-|[<-|[]]]]; auto.
  - exists p. split; [simpl; auto|]. split; [auto|]. split; [auto|].
    intros v [<-|[<-|[<-|[]]]]; auto.
Qed.

(** Invariant of the face-by-face construction: L the faces placed so far,
    T one tree edge for each face after the first (the edge by which it was
    attached), and the remaining edges connect all vertices placed so far. *)
Definition VL (s : VMState) (L : list nat) (v : nat) : Prop :=
  exists a, In a L /\ cont s v a = true.

Definition Hedge (s : VMState) (L : list nat) (T : list (nat * nat)) (e : nat * nat) : Prop :=
  (exists a, In a L /\ ein s e a = true) /\ ~ In e T.

Definition Conn (s : VMState) (L : list nat) (T : list (nat * nat)) (r0 : nat) : Prop :=
  forall P : nat -> bool, P r0 = true ->
    (forall e, Hedge s L T e -> P (fst e) = P (snd e)) ->
    forall v, VL s L v -> P v = true.

Definition TreeOK (s : VMState) (L : list nat) (T : list (nat * nat)) : Prop :=
  NoDup T /\ S (List.length T) = List.length L /\
  forall t, In t T -> exists a b, In a L /\ In b L /\ a <> b /\
                                  ein s t a = true /\ ein s t b = true.

Lemma euler_inv : forall s a0 L,
  NoDup (map fst (pg_modules (vm_graph s))) -> tri_ok (vm_graph s) ->
  is_2_manifold (vm_graph s) -> In a0 (map fst (pg_modules (vm_graph s))) ->
  grown (share_edge s) a0 L -> NoDup L ->
  exists T r0, VL s L r0 /\ TreeOK s L T /\ Conn s L T r0.
Proof.
  intros s a0 L Hnd Htri Hman Ha0 HL.
  induction HL as [|f L HL IH [g0 [Hg0 Rgf]]]; intros HndL.
  - apply in_map_iff in Ha0. destruct Ha0 as [[a m0] [Ea Hin]]. simpl in Ea. subst a.
    destruct (Htri a0 m0 Hin) as [Hr H3].
    destruct (module_region m0) as [|p [|q [|t [|z rr]]]] eqn:Hreg; simpl in H3; try discriminate.
    assert (Hc : forall v, cont s v a0 = nat_list_mem v [p; q; t]).
    { intros v. rewrite (cont_entry s v a0 m0 Hnd Hin), Hreg. reflexivity. }
    assert (Hpq : p <> q) by (intro E; subst; inversion Hr as [|? ? Hn _]; apply Hn; left; reflexivity).
    assert (Hpt : p <> t) by (intro E; subst; inversion Hr as [|? ? Hn _]; apply Hn; right; left; reflexivity).
    assert (Hcp : cont s p a0 = true) by (rewrite Hc; apply nat_list_mem_In; simpl; auto).
    assert (Hcq : cont s q a0 = true) by (rewrite Hc; apply nat_list_mem_In; simpl; auto).
    assert (Hct : cont s t a0 = true) by (rewrite Hc; apply nat_list_mem_In; simpl; auto).
    exists [], p. split; [exists a0; split; [left; reflexivity|exact Hcp]|]. split.
    + split; [constructor|]. split; [reflexivity|]. intros t' [].
    + intros P HP Hcl v [a [Ha Hv]]. destruct Ha as [Ha|[]]. subst a.
      rewrite Hc in Hv. apply nat_list_mem_In in Hv.
      assert (Eq : P p = P q).
      { apply norm_edge_ends. apply Hcl. split; [|intros []].
        exists a0. split; [left; reflexivity|]. rewrite ein_norm by exact Hpq.
        rewrite Hcp, Hcq. reflexivity. }
      assert (Et : P p = P t).
      { apply norm_edge_ends. apply Hcl. split; [|intros []].
        exists a0. split; [left; reflexivity|]. rewrite ein_norm by exact Hpt.
        rewrite Hcp, Hct. reflexivity. }
      destruct Hv as [<-|[<-|[<-|[]]]]; congruence.
  - inversion HndL as [|? ? HfL HndL']. subst.
    destruct (IH HndL') as [T [r0 [Hr0 [[HTnd [HTlen HTin]] HC]]]].
    destruct (share_edge_spec s g0 f Rgf) as [x [y [Hxy [Hxg [Hyg [Hxf Hyf]]]]]].
    destruct (cont_true_entry s x f Hxf) as [mf [Hlf [Hinf Hxr]]].
    assert (Hcf : forall v, cont s v f = nat_list_mem v (module_region mf))
      by (intros v; apply (cont_entry s v f mf Hnd Hinf)).
    destruct (Htri f mf Hinf) as [Hrf H3f].
    assert (Hyr : In y (module_region mf)) by (apply nat_list_mem_In; rewrite <- Hcf; exact Hyf).
    destruct (third_vertex _ x y Hrf H3f Hxr Hyr Hxy) as [w [Hwr [Hwx [Hwy Hall]]]].
    assert (Hwf : cont s w f = true) by (rewrite Hcf; apply nat_list_mem_In; exact Hwr).
    assert (Hnot3 : forall t, In t T -> ein s t f = true -> False).
    { intros t Ht Htf. destruct (HTin t Ht) as [a [b [Ha [Hb [Hab [Hta Htb]]]]]].
      apply (three_faces_ein s t f a b Hnd Hman); try assumption;
        intro E; subst; contradiction. }
    set (ef := norm_edge x y).
    assert (Hef : ein s ef f = true) by (unfold ef; rewrite ein_norm by exact Hxy; rewrite Hxf, Hyf; reflexivity).
    assert (HefT : ~ In ef T) by (intro H; exact (Hnot3 ef H Hef)).
    assert (Hxw : ein s (norm_edge x w) f = true)
      by (rewrite ein_norm by congruence; rewrite Hxf, Hwf; reflexivity).
    assert (Hyw : ein s (norm_edge y w) f = true)
      by (rewrite ein_norm by congruence; rewrite Hyf, Hwf; reflexivity).
    assert (Hxw' : ~ In (norm_edge x w) (ef :: T)).
    { intros [E|E].
      - unfold ef in E. apply norm_edge_inv in E. destruct E as [[_ E]|[E _]]; congruence.
      - exact (Hnot3 _ E Hxw). }
    assert (Hyw' : ~ In (norm_edge y w) (ef :: T)).
    { intros [E|E].
      - unfold ef in E. apply norm_edge_inv in E. destruct E as [[E _]|[E _]]; congruence.
      - exact (Hnot3 _ E Hyw). }
    exists (ef :: T), r0. split.
    { destruct Hr0 as [a [Ha Hra]]. exists a. split; [right; exact Ha|exact Hra]. }
    split.
    + split; [constructor; assumption|]. split; [simpl; rewrite HTlen; reflexivity|].
      intros t [Ht|Ht].
      * subst t. exists f, g0. split; [left; reflexivity|]. split; [right; exact Hg0|].
        split; [intro E; subst; contradiction|]. split; [exact Hef|].
        unfold ef. rewrite ein_norm by exact Hxy. rewrite Hxg, Hyg. reflexivity.
      * destruct (HTin t Ht) as [a [b [Ha [Hb [Hab [Hta Htb]]]]]].
        exists a, b. split; [right; exact Ha|]. split; [right; exact Hb|]. auto.
    + intros P HP Hcl v Hv.
      assert (Pxw : P x = P w).
      { apply norm_edge_ends. apply Hcl. split; [|exact Hxw'].
        exists f. split; [left; reflexivity|exact Hxw]. }
      assert (Pyw : P y = P w).
      { apply norm_edge_ends. apply Hcl. split; [|exact Hyw'].
        exists f. split; [left; reflexivity|exact Hyw]. }
      assert (HL' : forall u, VL s L u -> P u = true).
      { apply HC; [exact HP|]. intros e [[a [Ha Hea]] HeT].
        destruct (pair_eq_dec Nat.eq_dec Nat.eq_dec e ef) as [E|Ne].
        - subst e. unfold ef, norm_edge. destruct (x <? y); simpl; congruence.
        - apply Hcl. split.
          + exists a. split; [right; exact Ha|exact Hea].
          + intros [E|E]; [apply Ne; symmetry; exact E|contradiction]. }
      assert (Px : P x = true) by (apply HL'; exists g0; split; assumption).
      destruct Hv as [a [[Ha|Ha] Hva]].
      * subst a. rewrite Hcf in Hva. apply nat_list_mem_In in Hva.
        destruct (Hall v Hva) as [E|[E|E]]; subst v.
        -- exact Px.
        -- apply HL'. exists g0. split; assumption.
        -- congruence.
      * apply HL'. exists a. split; assumption.
Qed.

Lemma nsum_even : forall (A : Type) (l : list A) (f : A -> nat),
  (forall x, In x l -> Nat.even (f x) = true) -> Nat.even (nsum l f) = true.
Proof.
  intros A l f H. induction l as [|x l IH]; [reflexivity|].
  rewrite nsum_cons, Nat.even_add, (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy. apply H. right. exact Hy.
Qed.

Lemma nsum_odd_one : forall (A : Type) (l : list A) (f : A -> nat) (b : A),
  NoDup l -> In b l -> Nat.even (f b) = false ->
  (forall x, In x l -> x <> b -> Nat.even (f x) = true) ->
  Nat.even (nsum l f) = false.
Proof.
  intros A l f b Hnd. induction Hnd as [|x l Hx Hnd IH]; intros Hb Hfb Hrest; [destruct Hb|].
  rewrite nsum_cons, Nat.even_add. destruct Hb as [Hb|Hb].
  - subst x. rewrite Hfb.
    rewrite nsum_even; [reflexivity|]. intros y Hy. apply Hrest; [right; exact Hy|].
    intro E. subst. contradiction.
  - assert (Hxb : x <> b) by (intro E; subst; contradiction).
    rewrite (Hrest x (or_introl eq_refl) Hxb), IH; try assumption; [reflexivity|].
    intros y Hy. apply Hrest. right. exact Hy.
Qed.

Lemma cross_three : forall (P : nat -> bool) x y z,
  Nat.even (nsum (region_edges_internal [x; y; z])
     (fun e => if xorb (P (fst e)) (P (snd e)) then 1%nat else 0%nat)) = true.
Proof.
  intros P x y z. unfold nsum. simpl.
  destruct (x <? y), (x <? z), (y <? z); simpl;
    destruct (P x), (P y), (P z); reflexivity.
Qed.

(** Euler characteristic bound for an edge-connected list of triangles in
    which every edge lies in one or two faces: chi <= 2, and chi <= 1 when
    some edge is a boundary edge. *)
Theorem euler_component : forall s a0 L,
  NoDup (map fst (pg_modules (vm_graph s))) -> tri_ok (vm_graph s) ->
  is_2_manifold (vm_graph s) -> In a0 (map fst (pg_modules (vm_graph s))) ->
  grown (share_edge s) a0 L -> NoDup L ->
  (forall a, In a (map fst (pg_modules (vm_graph s))) <-> In a L) ->
  (DiscreteTopology.V (vm_graph s) + DiscreteTopology.F (vm_graph s)
     <= DiscreteTopology.E (vm_graph s) + 2)%nat /\
  (1 <= DiscreteTopology.B (vm_graph s) ->
   DiscreteTopology.V (vm_graph s) + DiscreteTopology.F (vm_graph s)
     <= DiscreteTopology.E (vm_graph s) + 1)%nat.
Proof.
  intros s a0 L Hnd Htri Hman Ha0 HL HndL HidsL.
  destruct (euler_inv s a0 L Hnd Htri Hman Ha0 HL HndL)
    as [T [r0 [Hr0 [[HTnd [HTlen HTin]] HC]]]].
  set (g := vm_graph s) in *.
  set (Eg := edges g).
  assert (HTsub : incl T Eg).
  { intros t Ht. destruct (HTin t Ht) as [a [_ [_ [_ [_ [Hta _]]]]]].
    exact (ein_edges s t a Hta). }
  assert (HTcnt : forall t, In t T -> count_modules_with_edge t (pg_modules g) = 2%nat).
  { intros t Ht. destruct (HTin t Ht) as [a [b [_ [_ [Hab [Hta Htb]]]]]].
    pose proof (ein_count2 s t a b Hab Hta Htb) as H2. fold g in H2.
    destruct (Hman t (HTsub t Ht)) as [E|E]; fold g in E; lia. }
  set (H := filter (fun e => negb (list_mem edge_eq e T)) Eg).
  assert (HinH : forall e, In e H <-> In e Eg /\ ~ In e T).
  { intros e. unfold H. rewrite filter_In. split.
    - intros [He Hn]. split; [exact He|]. intro Ht. apply list_mem_edge_iff in Ht.
      rewrite Ht in Hn. discriminate.
    - intros [He Hn]. split; [exact He|].
      destruct (list_mem edge_eq e T) eqn:Hm; [|reflexivity].
      exfalso. apply Hn. apply list_mem_edge_iff. exact Hm. }
  assert (HndE : NoDup Eg) by apply edges_NoDup.
  assert (HndH : NoDup H) by (apply NoDup_filter; exact HndE).
  assert (HlenH : (List.length H + List.length T)%nat = List.length Eg).
  { rewrite <- (length_filter_split _ (fun e => negb (list_mem edge_eq e T)) Eg).
    fold H. f_equal. symmetry. apply length_same_elements.
    - apply NoDup_filter. exact HndE.
    - exact HTnd.
    - intros e. rewrite filter_In, negb_involutive, list_mem_edge_iff.
      split; [tauto|]. intros Ht. split; [apply HTsub; exact Ht|exact Ht]. }
  assert (HlenL : List.length L = DiscreteTopology.F g).
  { unfold DiscreteTopology.F. rewrite <- (map_length fst).
    symmetry. apply length_same_elements; [exact Hnd|exact HndL|exact HidsL]. }
  set (Vs := vertices g).
  assert (HndV : NoDup Vs) by apply vertices_NoDup.
  assert (Hcont_V : forall v a, cont s v a = true -> In v Vs).
  { intros v a Hv. destruct (cont_true_entry s v a Hv) as [m [_ [Hin Hvm]]].
    apply vertices_In. exists (a, m). split; assumption. }
  assert (Hr0V : In r0 Vs) by (destruct Hr0 as [a [_ Ha]]; exact (Hcont_V r0 a Ha)).
  assert (Hends : forall e, In e H -> (fst e < snd e)%nat /\ In (fst e) Vs /\ In (snd e) Vs).
  { intros e He. apply HinH in He. destruct He as [He _].
    destruct (edges_ein s e Hnd Htri He) as [a [_ Hea]].
    unfold ein in Hea. destruct (Nat.ltb_spec (fst e) (snd e)) as [Hlt|]; [|discriminate].
    apply andb_prop in Hea. destruct Hea as [Hea H2]. apply andb_prop in Hea. destruct Hea as [_ H1].
    split; [exact Hlt|]. split; [exact (Hcont_V _ _ H1)|exact (Hcont_V _ _ H2)]. }
  assert (HconnV : forall P : nat -> bool, P r0 = true ->
            (forall e, In e H -> P (fst e) = P (snd e)) -> forall v, In v Vs -> P v = true).
  { intros P HP Hcl v Hv. apply (HC P HP).
    - intros e [[a [Ha Hea]] HeT]. apply Hcl. apply HinH. split; [|exact HeT].
      exact (ein_edges s e a Hea).
    - apply vertices_In in Hv. destruct Hv as [[a m] [Hin Hvm]]. exists a. split.
      + apply HidsL. apply in_map_iff. exists (a, m). auto.
      + rewrite (cont_entry s v a m Hnd Hin). apply nat_list_mem_In. exact Hvm. }
  pose proof (connected_edge_count Vs H r0 HndV HndH Hr0V Hends HconnV) as Hcount.
  unfold DiscreteTopology.V, DiscreteTopology.E. fold g Eg Vs.
  split; [lia|].
  intros HB. unfold DiscreteTopology.B in HB. fold g Eg in HB.
  rewrite count_boundary_filter in HB.
  destruct (filter (fun e => count_modules_with_edge e (pg_modules g) =? 1) Eg) as [|b rest] eqn:Hf;
    [simpl in HB; lia|].
  assert (Hb : In b (filter (fun e => count_modules_with_edge e (pg_modules g) =? 1) Eg))
    by (rewrite Hf; left; reflexivity).
  apply filter_In in Hb. destruct Hb as [HbE Hb1]. apply Nat.eqb_eq in Hb1.
  assert (HbT : ~ In b T) by (intro Ht; rewrite (HTcnt b Ht) in Hb1; discriminate).
  assert (HbH : In b H) by (apply HinH; split; assumption).
  destruct (cut_or_count Vs H r0 b HndV HndH Hr0V HbH Hends HconnV) as [Hle|[P [P1 [P2 Pcl]]]];
    [lia|].
  exfalso.
  set (cr := fun e : nat * nat => if xorb (P (fst e)) (P (snd e)) then 1%nat else 0%nat).
  assert (HDC := double_count _ _ Eg (pg_modules g) (fun p => module_edges (snd p))
                   (fun p e => list_mem edge_eq e (module_edges (snd p))) cr HndE).
  assert (HDC' : nsum Eg (fun e => (cr e * count_modules_with_edge e (pg_modules g))%nat) =
                 nsum (pg_modules g) (fun p => nsum (module_edges (snd p)) cr)).
  { rewrite <- HDC.
    - apply nsum_ext_in. intros e _. rewrite count_modules_with_edge_nsum. reflexivity.
    - intros p Hp. destruct (module_edges_props g p Htri Hp) as [Hn [Hi _]].
      split; [exact Hn|]. split; [exact Hi|]. intros e. apply list_mem_edge_iff. }
  assert (Heven : Nat.even (nsum (pg_modules g) (fun p => nsum (module_edges (snd p)) cr)) = true).
  { apply nsum_even. intros [mid m] Hp. destruct (Htri mid m Hp) as [_ H3].
    simpl. unfold module_edges.
    destruct (module_region m) as [|x [|y [|z [|w rr]]]]; simpl in H3; try discriminate.
    apply cross_three. }
  assert (Hodd : Nat.even (nsum Eg (fun e => (cr e * count_modules_with_edge e (pg_modules g))%nat)) = false).
  { apply (nsum_odd_one _ Eg _ b HndE HbE).
    - rewrite Hb1. unfold cr. rewrite P1, P2. reflexivity.
    - intros e He Hne. destruct (in_dec (pair_eq_dec Nat.eq_dec Nat.eq_dec) e T) as [Ht|Ht].
      + rewrite (HTcnt e Ht). rewrite Nat.even_mul. simpl. apply orb_true_r.
      + assert (HeH : In e H) by (apply HinH; split; assumption).
        unfold cr. rewrite (Pcl e HeH Hne). rewrite xorb_nilpotent. reflexivity. }
  rewrite HDC' in Hodd. congruence.
Qed.

(** * Part 11. Restriction of a state to a set of modules. *)

Definition restrict_graph (g : PartitionGraph) (p : ModuleID -> bool) : PartitionGraph :=
  {| pg_next_id := pg_next_id g;
     pg_modules := filter (fun x => p (fst x)) (pg_modules g);
     pg_next_morph_id := pg_next_morph_id g;
     pg_morphisms := pg_morphisms g |}.

Definition restrict_state (s : VMState) (p : ModuleID -> bool) : VMState :=
  {| vm_graph := restrict_graph (vm_graph s) p;
     vm_csrs := vm_csrs s;
     vm_regs := vm_regs s;
     vm_mem := vm_mem s;
     vm_pc := vm_pc s;
     vm_mu := vm_mu s;
     vm_mu_tensor := vm_mu_tensor s;
     vm_err := vm_err s;
     vm_logic_acc := vm_logic_acc s;
     vm_mstatus := vm_mstatus s;
     vm_witness := vm_witness s;
     vm_certified := vm_certified s |}.

Lemma lookup_restrict : forall s p x,
  graph_lookup (vm_graph (restrict_state s p)) x =
  if p x then graph_lookup (vm_graph s) x else None.
Proof.
  intros s p x. unfold graph_lookup. simpl.
  induction (pg_modules (vm_graph s)) as [|[id m] rest IH]; simpl.
  - destruct (p x); reflexivity.
  - destruct (p id) eqn:Hp; simpl.
    + destruct (Nat.eqb_spec id x) as [E|N].
      * subst. rewrite Hp. reflexivity.
      * exact IH.
    + destruct (Nat.eqb_spec id x) as [E|N].
      * subst. rewrite Hp in IH |- *. exact IH.
      * exact IH.
Qed.

Lemma ids_restrict : forall s p,
  map fst (pg_modules (vm_graph (restrict_state s p))) =
  filter p (map fst (pg_modules (vm_graph s))).
Proof.
  intros s p. simpl. induction (pg_modules (vm_graph s)) as [|[id m] rest IH]; [reflexivity|].
  simpl. destruct (p id); simpl; rewrite IH; reflexivity.
Qed.

Lemma restrict_entry : forall s p a m,
  In (a, m) (pg_modules (vm_graph (restrict_state s p))) <->
  In (a, m) (pg_modules (vm_graph s)) /\ p a = true.
Proof. intros s p a m. simpl. rewrite filter_In. simpl. tauto. Qed.

Lemma cont_restrict : forall s p v a, p a = true -> cont (restrict_state s p) v a = cont s v a.
Proof. intros s p v a H. unfold cont. rewrite lookup_restrict, H. reflexivity. Qed.

Lemma share_edge_restrict : forall s p a b, p a = true -> p b = true ->
  share_edge (restrict_state s p) a b = share_edge s a b.
Proof.
  intros s p a b Ha Hb. unfold share_edge. rewrite lookup_restrict, Ha.
  destruct (graph_lookup (vm_graph s) a) as [ma|]; [|reflexivity].
  induction (module_edges ma) as [|e l IH]; [reflexivity|].
  simpl. rewrite IH. f_equal. unfold ein. rewrite !cont_restrict by exact Hb. reflexivity.
Qed.

Lemma tri_ok_restrict : forall s p, tri_ok (vm_graph s) -> tri_ok (vm_graph (restrict_state s p)).
Proof. intros s p H mid m Hin. apply restrict_entry in Hin. apply (H mid m). tauto. Qed.

Lemma triangles_restrict : forall s p,
  all_modules_are_triangles_list (vm_graph s) ->
  all_modules_are_triangles_list (vm_graph (restrict_state s p)).
Proof. intros s p H mid m Hin. apply restrict_entry in Hin. apply (H mid m). tauto. Qed.

Lemma normalized_restrict : forall s p,
  all_regions_normalized_list (vm_graph s) ->
  all_regions_normalized_list (vm_graph (restrict_state s p)).
Proof. intros s p H mid m Hin. apply restrict_entry in Hin. apply (H mid m). tauto. Qed.

Lemma nodup_restrict : forall s p,
  NoDup (map fst (pg_modules (vm_graph s))) ->
  NoDup (map fst (pg_modules (vm_graph (restrict_state s p)))).
Proof. intros s p H. rewrite ids_restrict. apply NoDup_filter. exact H. Qed.

Lemma count_edge_filter_le : forall e (f : ModuleID * ModuleState -> bool) mods,
  (count_modules_with_edge e (filter f mods) <= count_modules_with_edge e mods)%nat.
Proof.
  intros e f mods. induction mods as [|[id m] rest IH]; [simpl; lia|].
  simpl. destruct (f (id, m)); simpl;
    destruct (list_mem edge_eq e (module_edges m)); lia.
Qed.

Lemma count_edge_pos : forall e mods p,
  In p mods -> In e (module_edges (snd p)) -> (1 <= count_modules_with_edge e mods)%nat.
Proof.
  intros e mods p Hp He. rewrite count_modules_with_edge_filter.
  destruct (filter (fun q => list_mem edge_eq e (module_edges (snd q))) mods) eqn:Hf.
  - exfalso. assert (Hin : In p (filter (fun q => list_mem edge_eq e (module_edges (snd q))) mods)).
    { apply filter_In. split; [exact Hp|]. apply list_mem_edge_iff. exact He. }
    rewrite Hf in Hin. destruct Hin.
  - simpl. lia.
Qed.

Lemma manifold_restrict : forall s p, is_2_manifold (vm_graph s) ->
  is_2_manifold (vm_graph (restrict_state s p)).
Proof.
  intros s p Hman e He. cbv zeta.
  assert (He' := He). apply edges_In in He'. destruct He' as [q [Hq Heq]].
  assert (Hs : In e (edges (vm_graph s))).
  { apply edges_In. exists q. split; [|exact Heq]. simpl in Hq. apply filter_In in Hq. tauto. }
  pose proof (Hman e Hs) as Hc. cbv zeta in Hc.
  pose proof (count_edge_filter_le e (fun x => p (fst x)) (pg_modules (vm_graph s))).
  pose proof (count_edge_pos e _ q Hq Heq).
  simpl in *. lia.
Qed.

(** * Part 12. Calibration is local to a set of modules closed under
    adjacency. *)

Section Closed.
Variable s : VMState.
Variable C : list ModuleID.
Variable HclC : forall x y, In x C -> In y (map fst (pg_modules (vm_graph s))) ->
  modules_adjacent_by_region s x y = true -> In y C.

Let q := fun a => nat_list_mem a C.
Let sc := restrict_state s q.

Lemma q_In : forall a, q a = true <-> In a C.
Proof. intros a. unfold q. apply nat_list_mem_In. Qed.

Lemma adj_closed : forall a b, q a = true ->
  modules_adjacent_by_region s a b = true -> q b = true.
Proof.
  intros a b Ha Hab. apply q_In. apply q_In in Ha. apply (HclC a b Ha); [|exact Hab].
  destruct (adjacent_lookup_r s a b Hab) as [mb Hmb].
  apply in_map_iff. exists (b, mb). split; [reflexivity|].
  apply graph_lookup_modules_In. exact Hmb.
Qed.

Lemma adj_restrict : forall a b, q a = true ->
  modules_adjacent_by_region sc a b = modules_adjacent_by_region s a b.
Proof.
  intros a b Ha. destruct (q b) eqn:Hb.
  - unfold modules_adjacent_by_region, sc. rewrite !lookup_restrict, Ha, Hb. reflexivity.
  - destruct (modules_adjacent_by_region s a b) eqn:Hab.
    + rewrite (adj_closed a b Ha Hab) in Hb. discriminate.
    + unfold modules_adjacent_by_region, sc. rewrite !lookup_restrict, Ha, Hb.
      destruct (graph_lookup (vm_graph s) a); reflexivity.
Qed.

Lemma filter_filter_drop : forall (f g : nat -> bool) (l : list nat),
  (forall x, In x l -> g x = false -> f x = false) -> filter f (filter g l) = filter f l.
Proof.
  intros f g l H. induction l as [|x l IH]; [reflexivity|].
  simpl. destruct (g x) eqn:Hg; simpl.
  - destruct (f x); rewrite IH by (intros y Hy; apply H; right; exact Hy); reflexivity.
  - rewrite (H x (or_introl eq_refl) Hg). apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma neighbors_restrict : forall m, q m = true ->
  module_neighbors sc m = module_neighbors s m.
Proof.
  intros m Hm. unfold module_neighbors, module_neighbors_physical, module_neighbors_adjacent.
  cbv zeta. unfold sc. rewrite ids_restrict. fold sc.
  rewrite (filter_ext (fun n => negb (m =? n) && modules_adjacent_by_region sc m n)
                      (fun n => negb (m =? n) && modules_adjacent_by_region s m n))
    by (intros n; rewrite adj_restrict by exact Hm; reflexivity).
  apply filter_filter_drop. intros x _ Hx.
  destruct (modules_adjacent_by_region s m x) eqn:Hadj; [|apply andb_false_r].
  rewrite (adj_closed m x Hm Hadj) in Hx. discriminate.
Qed.

Lemma neighbors_in : forall m n, q m = true -> In n (module_neighbors s m) -> q n = true.
Proof.
  intros m n Hm Hn. unfold module_neighbors, module_neighbors_physical, module_neighbors_adjacent in Hn.
  apply filter_In in Hn. destruct Hn as [_ Hn]. apply andb_prop in Hn. destruct Hn as [_ Hn].
  exact (adj_closed m n Hm Hn).
Qed.

Lemma flat_map_ext_in : forall (A B : Type) (f g : A -> list B) (l : list A),
  (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof.
  intros A B f g l H. induction l as [|x l IH]; [reflexivity|].
  simpl. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy. apply H. right. exact Hy.
Qed.

Lemma triangles_restrict_eq : forall m, q m = true ->
  module_triangles sc m = module_triangles s m.
Proof.
  intros m Hm. unfold module_triangles. cbv zeta. rewrite neighbors_restrict by exact Hm.
  apply flat_map_ext_in. intros n1 Hn1. f_equal. apply filter_ext. intros n2.
  rewrite adj_restrict by exact (neighbors_in m n1 Hm Hn1). reflexivity.
Qed.

Lemma triangles_in : forall m p, q m = true -> In p (module_triangles s m) ->
  q (fst p) = true /\ q (snd p) = true.
Proof.
  intros m p Hm Hp. unfold module_triangles in Hp. cbv zeta in Hp.
  apply in_flat_map in Hp. destruct Hp as [n1 [Hn1 Hp]].
  apply in_map_iff in Hp. destruct Hp as [n2 [Hp Hn2]]. subst p.
  apply filter_In in Hn2. destruct Hn2 as [Hn2 _]. simpl.
  split; apply (neighbors_in m); assumption.
Qed.

Lemma mass_restrict : forall n, q n = true ->
  module_structural_mass sc n = module_structural_mass s n.
Proof. intros n Hn. unfold module_structural_mass, sc. rewrite lookup_restrict, Hn. reflexivity. Qed.

Lemma dist_restrict : forall a b, q a = true -> q b = true ->
  mu_module_distance sc a b = mu_module_distance s a b.
Proof.
  intros a b Ha Hb. unfold mu_module_distance. rewrite !mass_restrict by assumption. reflexivity.
Qed.

Lemma angle_restrict : forall a b c, q a = true -> q b = true -> q c = true ->
  triangle_angle sc a b c = triangle_angle s a b c.
Proof.
  intros a b c Ha Hb Hc. unfold triangle_angle. rewrite !dist_restrict by assumption. reflexivity.
Qed.

Lemma sum_angles_restrict : forall m l, q m = true ->
  (forall p, In p l -> q (fst p) = true /\ q (snd p) = true) ->
  sum_angles sc m l = sum_angles s m l.
Proof.
  intros m l Hm Hl. induction l as [|[n1 n2] l IH]; [reflexivity|].
  simpl. destruct (Hl (n1, n2) (or_introl eq_refl)) as [H1 H2]. simpl in H1, H2.
  rewrite angle_restrict by assumption.
  rewrite IH; [reflexivity|]. intros p Hp. apply Hl. right. exact Hp.
Qed.

Lemma density_restrict : forall n, q n = true -> mu_cost_density sc n = mu_cost_density s n.
Proof.
  intros n Hn. unfold mu_cost_density, module_encoding_length, module_region_size, sc.
  rewrite lookup_restrict, Hn. reflexivity.
Qed.

Lemma fold_left_ext_in : forall (A B : Type) (f g : A -> B -> A) (l : list B) (a : A),
  (forall acc x, In x l -> f acc x = g acc x) -> fold_left f l a = fold_left g l a.
Proof.
  intros A B f g l. induction l as [|x l IH]; intros a H; [reflexivity|].
  simpl. rewrite (H a x (or_introl eq_refl)). apply IH.
  intros acc y Hy. apply H. right. exact Hy.
Qed.

Lemma laplacian_restrict : forall m, q m = true -> mu_laplacian sc m = mu_laplacian s m.
Proof.
  intros m Hm. unfold mu_laplacian, mu_laplacian_w. cbv zeta.
  rewrite neighbors_restrict by exact Hm.
  apply fold_left_ext_in. intros acc n Hn.
  unfold edge_weight, mu_gradient. rewrite adj_restrict by exact Hm.
  rewrite !density_restrict by (exact Hm || exact (neighbors_in m n Hm Hn)).
  reflexivity.
Qed.

Lemma residual_restrict : forall m, q m = true ->
  calibration_residual sc m = calibration_residual s m.
Proof.
  intros m Hm. unfold calibration_residual, angle_defect_curvature, geometric_angle_defect.
  rewrite triangles_restrict_eq by exact Hm.
  rewrite sum_angles_restrict; [|exact Hm|intros p Hp; exact (triangles_in m p Hm Hp)].
  rewrite laplacian_restrict by exact Hm. reflexivity.
Qed.

End Closed.

(** * Part 13. Connected vertex links. *)

(** w is a vertex of the link of v: some face contains both. *)
Definition link_vertex (g : PartitionGraph) (v w : nat) : Prop :=
  exists mid m, In (mid, m) (pg_modules g) /\
    In v (module_region m) /\ In w (module_region m) /\ v <> w.

(** w1 w2 is an edge of the link of v: some face is {v, w1, w2}. *)
Definition link_edge (g : PartitionGraph) (v w1 w2 : nat) : Prop :=
  exists mid m, In (mid, m) (pg_modules g) /\
    In v (module_region m) /\ In w1 (module_region m) /\ In w2 (module_region m) /\
    v <> w1 /\ v <> w2 /\ w1 <> w2.

(** The link of every vertex is a connected graph. With is_2_manifold a
    link vertex w lies on at most two link edges (the faces containing the
    edge v w, see no_three_faces_on_edge), so a connected link is a path
    (v on the boundary) or a cycle (v in the interior): the standard
    condition for a combinatorial surface with boundary. *)
Definition links_connected (s : VMState) : Prop :=
  forall v w1 w2, link_vertex (vm_graph s) v w1 -> link_vertex (vm_graph s) v w2 ->
    clos_refl_trans_1n nat (link_edge (vm_graph s) v) w1 w2.

(** Calibration at every module. *)
Definition calibrated (s : VMState) : Prop :=
  forall m, In m (map fst (pg_modules (vm_graph s))) -> calibration_residual s m = 0%R.

(** Faces through v whose links are joined by a link path are joined by a
    chain of faces through v, consecutive faces sharing an edge. *)
Lemma link_chain : forall s v u u',
  NoDup (map fst (pg_modules (vm_graph s))) ->
  clos_refl_trans_1n nat (link_edge (vm_graph s) v) u u' ->
  forall (Q : ModuleID -> Prop) a b,
    In a (map fst (pg_modules (vm_graph s))) -> In b (map fst (pg_modules (vm_graph s))) ->
    cont s v a = true -> cont s u a = true -> u <> v ->
    cont s v b = true -> cont s u' b = true -> Q a ->
    (forall a' b', In a' (map fst (pg_modules (vm_graph s))) ->
       In b' (map fst (pg_modules (vm_graph s))) ->
       cont s v a' = true -> cont s v b' = true -> Q a' -> share_edge s a' b' = true -> Q b') ->
    Q b.
Proof.
  intros s v u u' Hnd Hrt.
  induction Hrt as [u|u u1 u' Hstep Hrest IH];
    intros Q a b Ha Hb Hva Hua Huv Hvb Hub HQa Hcl.
  - apply (Hcl a b Ha Hb Hva Hvb HQa).
    apply (share_edge_intro s a b v u); auto.
  - destruct Hstep as [mid [m [Hin [Hv [Hu [Hu1 [Hvu [Hvu1 Huu1]]]]]]]].
    assert (Hmid : In mid (map fst (pg_modules (vm_graph s))))
      by (apply in_map_iff; exists (mid, m); auto).
    assert (Hc : forall x, In x (module_region m) -> cont s x mid = true).
    { intros x Hx. rewrite (cont_entry s x mid m Hnd Hin). apply nat_list_mem_In. exact Hx. }
    apply (IH Q mid b Hmid Hb (Hc v Hv) (Hc u1 Hu1)); auto.
    apply (Hcl a mid Ha Hmid Hva (Hc v Hv) HQa).
    apply (share_edge_intro s a mid v u); auto.
Qed.

Lemma nat_list_disjoint_false : forall xs ys,
  nat_list_disjoint xs ys = false -> exists v, In v xs /\ In v ys.
Proof.
  unfold nat_list_disjoint. induction xs as [|x xs IH]; intros ys H; simpl in H; [discriminate|].
  destruct (nat_list_mem x ys) eqn:Hx; simpl in H.
  - exists x. split; [left; reflexivity|apply nat_list_mem_In; exact Hx].
  - destruct (IH ys H) as [v [Hv1 Hv2]]. exists v. split; [right; exact Hv1|exact Hv2].
Qed.

Lemma adj_common_vertex : forall s a b, modules_adjacent_by_region s a b = true ->
  exists v, cont s v a = true /\ cont s v b = true.
Proof.
  intros s a b H. unfold modules_adjacent_by_region in H. unfold cont.
  destruct (graph_lookup (vm_graph s) a) as [ma|]; [|discriminate].
  destruct (graph_lookup (vm_graph s) b) as [mb|]; [|discriminate].
  apply negb_true_iff in H. destruct (nat_list_disjoint_false _ _ H) as [v [H1 H2]].
  exists v. split; apply nat_list_mem_In; assumption.
Qed.

Lemma other_vertex : forall (r : list nat) v, NoDup r -> List.length r = 3%nat ->
  exists u, In u r /\ u <> v.
Proof.
  intros r v Hnd H3. destruct r as [|p [|q [|t [|z r]]]]; simpl in H3; try discriminate.
  assert (Hpq : p <> q) by (intro E; subst; inversion Hnd as [|? ? Hn _]; apply Hn; left; reflexivity).
  destruct (Nat.eq_dec p v) as [E|N].
  - exists q. split; [simpl; auto|congruence].
  - exists p. split; [simpl; auto|exact N].
Qed.

(** With connected links, faces that share a vertex are joined by a chain
    of faces sharing edges. *)
Lemma adj_share_closure : forall s,
  NoDup (map fst (pg_modules (vm_graph s))) -> tri_ok (vm_graph s) -> links_connected s ->
  forall (Q : ModuleID -> Prop) a b,
    In a (map fst (pg_modules (vm_graph s))) -> In b (map fst (pg_modules (vm_graph s))) ->
    modules_adjacent_by_region s a b = true -> Q a ->
    (forall v a' b', In a' (map fst (pg_modules (vm_graph s))) ->
       In b' (map fst (pg_modules (vm_graph s))) ->
       cont s v a' = true -> cont s v b' = true -> Q a' -> share_edge s a' b' = true -> Q b') ->
    Q b.
Proof.
  intros s Hnd Htri Hlinks Q a b Ha Hb Hab HQa Hcl.
  destruct (adj_common_vertex s a b Hab) as [v [Hva Hvb]].
  destruct (cont_true_entry s v a Hva) as [ma [_ [Ia Va]]].
  destruct (cont_true_entry s v b Hvb) as [mb [_ [Ib Vb]]].
  destruct (Htri a ma Ia) as [Nda La]. destruct (Htri b mb Ib) as [Ndb Lb].
  destruct (other_vertex _ v Nda La) as [u [Hu Huv]].
  destruct (other_vertex _ v Ndb Lb) as [u' [Hu' Hu'v]].
  assert (Hrt : clos_refl_trans_1n nat (link_edge (vm_graph s) v) u u').
  { apply Hlinks.
    - exists a, ma. split; [exact Ia|]. split; [exact Va|]. split; [exact Hu|]. auto.
    - exists b, mb. split; [exact Ib|]. split; [exact Vb|]. split; [exact Hu'|]. auto. }
  apply (link_chain s v u u' Hnd Hrt Q a b Ha Hb Hva); auto.
  - rewrite (cont_entry s u a ma Hnd Ia). apply nat_list_mem_In. exact Hu.
  - rewrite (cont_entry s u' b mb Hnd Ib). apply nat_list_mem_In. exact Hu'.
  - intros a' b' Ha' Hb' Hva' Hvb'. apply (Hcl v a' b'); assumption.
Qed.

(** * Part 14. Each calibrated component pays more boundary than 3 chi. *)

Lemma window_nat : forall s,
  all_modules_are_triangles_list (vm_graph s) ->
  all_regions_normalized_list (vm_graph s) ->
  (1 <= List.length (pg_modules (vm_graph s)))%nat ->
  calibrated s ->
  (2 * DiscreteTopology.F (vm_graph s) < face_triangle_count s)%nat /\
  (21 * face_triangle_count s <= 44 * DiscreteTopology.F (vm_graph s))%nat.
Proof.
  intros s Htri Hnorm HF Hcal.
  unfold DiscreteTopology.F.
  destruct (F3_calibration_window_R s Htri Hnorm HF Hcal) as [Hlo Hhi].
  rewrite ordered_count_six in Hlo, Hhi.
  rewrite <- INR_face_triangle_count in Hlo, Hhi.
  set (T := face_triangle_count s) in *.
  set (nF := List.length (pg_modules (vm_graph s))) in *.
  split.
  - apply INR_lt. rewrite mult_INR. simpl (INR 2). lra.
  - apply INR_le. rewrite !mult_INR.
    replace (INR 21) with 21%R by (simpl; lra).
    replace (INR 44) with 44%R by (simpl; lra). lra.
Qed.

Theorem component_inequality : forall s a0 C,
  NoDup (map fst (pg_modules (vm_graph s))) ->
  all_modules_are_triangles_list (vm_graph s) ->
  all_regions_normalized_list (vm_graph s) ->
  is_2_manifold (vm_graph s) -> links_connected s -> calibrated s ->
  In a0 (map fst (pg_modules (vm_graph s))) ->
  grown (modules_adjacent_by_region s) a0 C -> incl C (map fst (pg_modules (vm_graph s))) ->
  (forall x y, In x C -> In y (map fst (pg_modules (vm_graph s))) ->
     modules_adjacent_by_region s x y = true -> In y C) ->
  (3 * DiscreteTopology.V (vm_graph (restrict_state s (fun a => nat_list_mem a C)))
   + 3 * DiscreteTopology.F (vm_graph (restrict_state s (fun a => nat_list_mem a C)))
   < DiscreteTopology.B (vm_graph (restrict_state s (fun a => nat_list_mem a C)))
   + 3 * DiscreteTopology.E (vm_graph (restrict_state s (fun a => nat_list_mem a C))))%nat.
Proof.
  intros s a0 C Hnd Htri Hnorm Hman Hlinks Hcal Ha0 HgC HinclC HclC.
  set (q := fun a => nat_list_mem a C).
  set (sc := restrict_state s q).
  assert (Hok : tri_ok (vm_graph s)) by (apply tri_ok_of_wf; assumption).
  assert (Hnd_c : NoDup (map fst (pg_modules (vm_graph sc)))) by (apply nodup_restrict; exact Hnd).
  assert (Hok_c : tri_ok (vm_graph sc)) by (apply tri_ok_restrict; exact Hok).
  assert (Hman_c : is_2_manifold (vm_graph sc)) by (apply manifold_restrict; exact Hman).
  assert (Htri_c : all_modules_are_triangles_list (vm_graph sc)) by (apply triangles_restrict; exact Htri).
  assert (Hnorm_c : all_regions_normalized_list (vm_graph sc)) by (apply normalized_restrict; exact Hnorm).
  assert (Hids_c : forall a, In a (map fst (pg_modules (vm_graph sc))) <->
                             In a (map fst (pg_modules (vm_graph s))) /\ In a C).
  { intros a. unfold sc. rewrite ids_restrict, filter_In. unfold q. rewrite nat_list_mem_In. tauto. }
  assert (Hcal_c : calibrated sc).
  { intros m Hm. apply Hids_c in Hm. destruct Hm as [Hm HmC].
    unfold sc, q. rewrite (residual_restrict s C HclC m) by (apply nat_list_mem_In; exact HmC).
    apply Hcal. exact Hm. }
  assert (Ha0C : In a0 C) by (eapply grown_root; exact HgC).
  assert (Ha0c : In a0 (map fst (pg_modules (vm_graph sc)))) by (apply Hids_c; auto).
  assert (HF_c : (1 <= List.length (pg_modules (vm_graph sc)))%nat).
  { destruct (pg_modules (vm_graph sc)) as [|x l]; [destruct Ha0c|simpl; lia]. }
  destruct (window_nat sc Htri_c Hnorm_c HF_c Hcal_c) as [Hw1 Hw2].
  pose proof (F3_vertex_triangle_bound sc Hnd_c Hman_c) as Hvtb.
  pose proof (degree_sum_general (vm_graph sc) Hok_c) as Hdeg.
  pose proof (nsum_falling3_tangent (vm_graph sc) (vertices (vm_graph sc))) as Htan.
  pose proof (edges_faces_boundary (vm_graph sc) Hok_c Hman_c) as Hefb.
  destruct (bfs (share_edge sc) (map fst (pg_modules (vm_graph sc))) a0 Ha0c)
    as [C2 [HgC2 [HndC2 [HinclC2 HclC2]]]].
  assert (Hall : forall x, In x C -> In x C2).
  { apply (grown_reach (modules_adjacent_by_region s) a0 C (fun a => In a C2) HgC).
    - eapply grown_root. exact HgC2.
    - intros x y Hx Hy Hx2 Hxy.
      apply (adj_share_closure s Hnd Hok Hlinks (fun a => In a C2) x y
               (HinclC x Hx) (HinclC y Hy) Hxy Hx2).
      intros v a' b' Ha' Hb' Hva' Hvb' Ha'2 Hsh.
      assert (Ha'C : In a' C) by (apply (Hids_c a'); apply HinclC2; exact Ha'2).
      assert (Hb'C : In b' C).
      { apply (HclC a' b' Ha'C Hb'). exact (share_adjacent s v a' b' Hva' Hvb'). }
      apply (HclC2 a' b' Ha'2); [apply Hids_c; auto|].
      unfold sc. rewrite share_edge_restrict; [exact Hsh| |];
        unfold q; apply nat_list_mem_In; assumption. }
  assert (Hiff : forall a, In a (map fst (pg_modules (vm_graph sc))) <-> In a C2).
  { intros a. split; [intros Ha; apply Hall; apply Hids_c; exact Ha|apply HinclC2]. }
  destruct (euler_component sc a0 C2 Hnd_c Hok_c Hman_c Ha0c HgC2 HndC2 Hiff) as [Heu1 Heu2].
  change (restrict_state s (fun a : ModuleID => nat_list_mem a C)) with sc.
  unfold DiscreteTopology.V in *.
  set (Vc := List.length (vertices (vm_graph sc))) in *.
  set (Fc := DiscreteTopology.F (vm_graph sc)) in *.
  set (Ec := DiscreteTopology.E (vm_graph sc)) in *.
  set (Bc := DiscreteTopology.B (vm_graph sc)) in *.
  set (Tc := face_triangle_count sc) in *.
  set (S3 := nsum (vertices (vm_graph sc))
               (fun v => vertex_degree (vm_graph sc) v * (vertex_degree (vm_graph sc) v - 1)
                         * (vertex_degree (vm_graph sc) v - 2))) in *.
  destruct (Nat.eq_dec Bc 0) as [HB0|HB0].
  - exfalso. lia.
  - specialize (Heu2 ltac:(lia)). lia.
Qed.

(** * Part 15. Summing over the components. *)

Lemma restrict_graph_ext_in : forall g p p',
  (forall x, In x (pg_modules g) -> p (fst x) = p' (fst x)) ->
  restrict_graph g p = restrict_graph g p'.
Proof.
  intros g p p' H. unfold restrict_graph. f_equal. apply filter_ext_in. exact H.
Qed.

Lemma restrict_graph_true : forall g, restrict_graph g (fun _ => true) = g.
Proof.
  intros [nid mods nmid morphs]. unfold restrict_graph. simpl. f_equal.
  induction mods as [|x l IH]; [reflexivity|]. simpl. rewrite IH. reflexivity.
Qed.

Lemma restrict_empty : forall g p, (forall x, In x (pg_modules g) -> p (fst x) = false) ->
  DiscreteTopology.V (restrict_graph g p) = 0%nat /\
  DiscreteTopology.E (restrict_graph g p) = 0%nat /\
  DiscreteTopology.F (restrict_graph g p) = 0%nat /\
  DiscreteTopology.B (restrict_graph g p) = 0%nat.
Proof.
  intros g p H.
  assert (H0 : pg_modules (restrict_graph g p) = []).
  { simpl. induction (pg_modules g) as [|x l IH]; [reflexivity|].
    simpl. rewrite (H x (or_introl eq_refl)). apply IH. intros y Hy. apply H. right. exact Hy. }
  unfold DiscreteTopology.V, DiscreteTopology.E, DiscreteTopology.F, DiscreteTopology.B,
    vertices, edges.
  rewrite H0. repeat split; reflexivity.
Qed.

Lemma count_edge_union : forall e (q r : ModuleID -> bool) mods,
  (forall x, In x mods -> q (fst x) = true -> r (fst x) = false) ->
  count_modules_with_edge e (filter (fun x => q (fst x) || r (fst x)) mods) =
  (count_modules_with_edge e (filter (fun x => q (fst x)) mods) +
   count_modules_with_edge e (filter (fun x => r (fst x)) mods))%nat.
Proof.
  intros e q r mods H. induction mods as [|[id m] rest IH]; [reflexivity|].
  assert (IH' := IH (fun x Hx => H x (or_intror Hx))).
  pose proof (H (id, m) (or_introl eq_refl)) as Hid. simpl in Hid.
  simpl. destruct (q id) eqn:Hq, (r id) eqn:Hr; simpl; rewrite ?IH'.
  - specialize (Hid eq_refl). discriminate.
  - destruct (list_mem edge_eq e (module_edges m)); reflexivity.
  - destruct (list_mem edge_eq e (module_edges m)); lia.
  - reflexivity.
Qed.

Lemma count_edge_zero : forall e mods,
  (forall x, In x mods -> ~ In e (module_edges (snd x))) ->
  count_modules_with_edge e mods = 0%nat.
Proof.
  intros e mods H. induction mods as [|[id m] rest IH]; [reflexivity|].
  simpl. destruct (list_mem edge_eq e (module_edges m)) eqn:He.
  - exfalso. apply (H (id, m) (or_introl eq_refl)). apply list_mem_edge_iff. exact He.
  - apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma length_filter_union : forall (A : Type) (q r : A -> bool) (l : list A),
  (forall x, In x l -> q x = true -> r x = false) ->
  List.length (filter (fun x => q x || r x) l) =
  (List.length (filter q l) + List.length (filter r l))%nat.
Proof.
  intros A q r l H. induction l as [|x l IH]; [reflexivity|].
  assert (IH' := IH (fun y Hy => H y (or_intror Hy))).
  pose proof (H x (or_introl eq_refl)) as Hx.
  simpl. destruct (q x) eqn:Hq, (r x) eqn:Hr; simpl; rewrite IH'; try lia.
Qed.

(** V, E, F and B add over two vertex-disjoint sets of faces. *)
Lemma restrict_union : forall g (q r : ModuleID -> bool),
  (forall x, In x (pg_modules g) -> q (fst x) = true -> r (fst x) = false) ->
  (forall x y v, In x (pg_modules g) -> In y (pg_modules g) -> q (fst x) = true ->
     r (fst y) = true -> In v (module_region (snd x)) -> In v (module_region (snd y)) -> False) ->
  DiscreteTopology.V (restrict_graph g (fun a => q a || r a)) =
    (DiscreteTopology.V (restrict_graph g q) + DiscreteTopology.V (restrict_graph g r))%nat /\
  DiscreteTopology.E (restrict_graph g (fun a => q a || r a)) =
    (DiscreteTopology.E (restrict_graph g q) + DiscreteTopology.E (restrict_graph g r))%nat /\
  DiscreteTopology.F (restrict_graph g (fun a => q a || r a)) =
    (DiscreteTopology.F (restrict_graph g q) + DiscreteTopology.F (restrict_graph g r))%nat /\
  DiscreteTopology.B (restrict_graph g (fun a => q a || r a)) =
    (DiscreteTopology.B (restrict_graph g q) + DiscreteTopology.B (restrict_graph g r))%nat.
Proof.
  intros g q r Hqr Hdisj.
  set (gu := restrict_graph g (fun a => q a || r a)).
  set (gq := restrict_graph g q). set (gr := restrict_graph g r).
  assert (Hmu : forall x, In x (pg_modules gu) <->
                  In x (pg_modules gq) \/ In x (pg_modules gr)).
  { intros x. unfold gu, gq, gr, restrict_graph. simpl. rewrite !filter_In.
    destruct (q (fst x)), (r (fst x)); simpl; intuition discriminate. }
  assert (Hq_in : forall x, In x (pg_modules gq) -> In x (pg_modules g) /\ q (fst x) = true)
    by (intros x Hx; unfold gq, restrict_graph in Hx; simpl in Hx; apply filter_In in Hx; exact Hx).
  assert (Hr_in : forall x, In x (pg_modules gr) -> In x (pg_modules g) /\ r (fst x) = true)
    by (intros x Hx; unfold gr, restrict_graph in Hx; simpl in Hx; apply filter_In in Hx; exact Hx).
  split; [|split; [|split]].
  - unfold DiscreteTopology.V. rewrite <- app_length. apply length_same_elements.
    + apply vertices_NoDup.
    + apply NoDup_app_disj; [apply vertices_NoDup|apply vertices_NoDup|].
      intros v H1 H2. apply vertices_In in H1. apply vertices_In in H2.
      destruct H1 as [x [Hx Hvx]]. destruct H2 as [y [Hy Hvy]].
      destruct (Hq_in x Hx) as [Hx' Hqx]. destruct (Hr_in y Hy) as [Hy' Hry].
      exact (Hdisj x y v Hx' Hy' Hqx Hry Hvx Hvy).
    + intros v. rewrite in_app_iff, !vertices_In. split.
      * intros [x [Hx Hvx]]. apply Hmu in Hx. destruct Hx as [Hx|Hx]; [left|right]; exists x; auto.
      * intros [[x [Hx Hvx]]|[x [Hx Hvx]]]; exists x; split; auto; apply Hmu; auto.
  - unfold DiscreteTopology.E. rewrite <- app_length. apply length_same_elements.
    + apply edges_NoDup.
    + apply NoDup_app_disj; [apply edges_NoDup|apply edges_NoDup|].
      intros e H1 H2. apply edges_In in H1. apply edges_In in H2.
      destruct H1 as [x [Hx Hex]]. destruct H2 as [y [Hy Hey]].
      destruct (Hq_in x Hx) as [Hx' Hqx]. destruct (Hr_in y Hy) as [Hy' Hry].
      destruct (region_edges_inv _ e Hex) as [Hfx _]. destruct (region_edges_inv _ e Hey) as [Hfy _].
      exact (Hdisj x y (fst e) Hx' Hy' Hqx Hry Hfx Hfy).
    + intros e. rewrite in_app_iff, !edges_In. split.
      * intros [x [Hx Hex]]. apply Hmu in Hx. destruct Hx as [Hx|Hx]; [left|right]; exists x; auto.
      * intros [[x [Hx Hex]]|[x [Hx Hex]]]; exists x; split; auto; apply Hmu; auto.
  - unfold DiscreteTopology.F, gu, gq, gr, restrict_graph. simpl.
    apply (length_filter_union _ (fun x => q (fst x)) (fun x => r (fst x))). exact Hqr.
  - unfold DiscreteTopology.B. rewrite !count_boundary_filter.
    assert (Hcnt : forall e, count_modules_with_edge e (pg_modules gu) =
                    (count_modules_with_edge e (pg_modules gq) +
                     count_modules_with_edge e (pg_modules gr))%nat).
    { intros e. unfold gu, gq, gr, restrict_graph. simpl. apply count_edge_union. exact Hqr. }
    assert (Hzr : forall e, In e (edges gq) -> count_modules_with_edge e (pg_modules gr) = 0%nat).
    { intros e He. apply edges_In in He. destruct He as [x [Hx Hex]].
      apply count_edge_zero. intros y Hy Hey.
      destruct (Hq_in x Hx) as [Hx' Hqx]. destruct (Hr_in y Hy) as [Hy' Hry].
      destruct (region_edges_inv _ e Hex) as [Hfx _]. destruct (region_edges_inv _ e Hey) as [Hfy _].
      exact (Hdisj x y (fst e) Hx' Hy' Hqx Hry Hfx Hfy). }
    assert (Hzq : forall e, In e (edges gr) -> count_modules_with_edge e (pg_modules gq) = 0%nat).
    { intros e He. apply edges_In in He. destruct He as [y [Hy Hey]].
      apply count_edge_zero. intros x Hx Hex.
      destruct (Hq_in x Hx) as [Hx' Hqx]. destruct (Hr_in y Hy) as [Hy' Hry].
      destruct (region_edges_inv _ e Hex) as [Hfx _]. destruct (region_edges_inv _ e Hey) as [Hfy _].
      exact (Hdisj x y (fst e) Hx' Hy' Hqx Hry Hfx Hfy). }
    set (bu := fun e => count_modules_with_edge e (pg_modules gu) =? 1).
    assert (Hperm : List.length (filter bu (edges gu)) =
                    List.length (filter bu (edges gq ++ edges gr))).
    { apply length_same_elements; [apply NoDup_filter; apply edges_NoDup|
                                   apply NoDup_filter|].
      - apply NoDup_app_disj; [apply edges_NoDup|apply edges_NoDup|].
        intros e H1 H2. pose proof (Hzr e H1) as Z.
        apply edges_In in H2. destruct H2 as [y [Hy Hey]].
        pose proof (count_edge_pos e (pg_modules gr) y Hy Hey). lia.
      - intros e. rewrite !filter_In, in_app_iff, !edges_In. split.
        + intros [[x [Hx Hex]] Hb]. split; [|exact Hb].
          apply Hmu in Hx. destruct Hx as [Hx|Hx]; [left|right]; exists x; auto.
        + intros [[[x [Hx Hex]]|[x [Hx Hex]]] Hb]; split; auto; exists x; split; auto;
            apply Hmu; auto. }
    rewrite Hperm, filter_app, app_length. f_equal.
    + apply f_equal. apply filter_ext_in. intros e He. unfold bu.
      rewrite Hcnt, (Hzr e He). rewrite Nat.add_0_r. reflexivity.
    + apply f_equal. apply filter_ext_in. intros e He. unfold bu.
      rewrite Hcnt, (Hzq e He). reflexivity.
Qed.

Lemma length_filter_and : forall (A : Type) (p q : A -> bool) (l : list A),
  List.length (filter p l) =
  (List.length (filter (fun x => p x && q x) l) +
   List.length (filter (fun x => p x && negb (q x)) l))%nat.
Proof.
  intros A p q l. induction l as [|x l IH]; [reflexivity|].
  simpl. destruct (p x), (q x); simpl; lia.
Qed.

Theorem components_sum : forall s,
  NoDup (map fst (pg_modules (vm_graph s))) ->
  all_modules_are_triangles_list (vm_graph s) ->
  all_regions_normalized_list (vm_graph s) ->
  is_2_manifold (vm_graph s) -> links_connected s -> calibrated s ->
  forall n (p : ModuleID -> bool),
    (List.length (filter p (map fst (pg_modules (vm_graph s)))) <= n)%nat ->
    (forall x y, In x (map fst (pg_modules (vm_graph s))) ->
       In y (map fst (pg_modules (vm_graph s))) -> p x = true ->
       modules_adjacent_by_region s x y = true -> p y = true) ->
    (exists a, In a (map fst (pg_modules (vm_graph s))) /\ p a = true) ->
    (3 * DiscreteTopology.V (restrict_graph (vm_graph s) p)
     + 3 * DiscreteTopology.F (restrict_graph (vm_graph s) p)
     < DiscreteTopology.B (restrict_graph (vm_graph s) p)
     + 3 * DiscreteTopology.E (restrict_graph (vm_graph s) p))%nat.
Proof.
  intros s Hnd Htri Hnorm Hman Hlinks Hcal n.
  set (ids := map fst (pg_modules (vm_graph s))).
  induction n as [|n IH]; intros p Hlen Hcl [a0 [Ha0 Hpa0]].
  - exfalso. assert (Hin : In a0 (filter p ids)) by (apply filter_In; auto).
    destruct (filter p ids); [destruct Hin|simpl in Hlen; lia].
  - destruct (bfs (modules_adjacent_by_region s) ids a0 Ha0) as [C [HgC [HndC [HinclC HclC]]]].
    set (q := fun a => nat_list_mem a C).
    assert (HCp : forall a, In a C -> p a = true).
    { apply (grown_reach (modules_adjacent_by_region s) a0 C (fun a => p a = true) HgC Hpa0).
      intros x y Hx Hy Hpx Hxy. exact (Hcl x y (HinclC x Hx) (HinclC y Hy) Hpx Hxy). }
    pose proof (component_inequality s a0 C Hnd Htri Hnorm Hman Hlinks Hcal Ha0 HgC HinclC HclC)
      as Hcomp.
    set (r := fun a => p a && negb (q a)).
    assert (Hr_cl : forall x y, In x ids -> In y ids -> r x = true ->
              modules_adjacent_by_region s x y = true -> r y = true).
    { intros x y Hx Hy Hrx Hxy. unfold r in *. apply andb_prop in Hrx. destruct Hrx as [Hpx Hqx].
      rewrite (Hcl x y Hx Hy Hpx Hxy). simpl.
      destruct (q y) eqn:Hqy; [|reflexivity]. exfalso.
      unfold q in Hqy. apply nat_list_mem_In in Hqy.
      rewrite modules_adjacent_by_region_sym in Hxy.
      pose proof (HclC y x Hqy Hx Hxy) as HxC. apply nat_list_mem_In in HxC.
      unfold q in Hqx. rewrite HxC in Hqx. discriminate. }
    assert (Hlen_r : (List.length (filter r ids) <= n)%nat).
    { pose proof (length_filter_and _ p q ids) as Hsplit. fold r in Hsplit.
      assert (Hin : In a0 (filter (fun x => p x && q x) ids)).
      { apply filter_In. split; [exact Ha0|]. rewrite Hpa0. simpl. unfold q.
        apply nat_list_mem_In. eapply grown_root. exact HgC. }
      destruct (filter (fun x => p x && q x) ids); [destruct Hin|simpl in Hsplit; lia]. }
    assert (Hrest : (3 * DiscreteTopology.V (restrict_graph (vm_graph s) r)
                     + 3 * DiscreteTopology.F (restrict_graph (vm_graph s) r)
                     <= DiscreteTopology.B (restrict_graph (vm_graph s) r)
                     + 3 * DiscreteTopology.E (restrict_graph (vm_graph s) r))%nat).
    { destruct (existsb r ids) eqn:Hex.
      - apply existsb_exists in Hex. destruct Hex as [a [Ha Hra]].
        pose proof (IH r Hlen_r Hr_cl (ex_intro _ a (conj Ha Hra))). lia.
      - destruct (restrict_empty (vm_graph s) r) as [E1 [E2 [E3 E4]]].
        + intros x Hx. destruct (r (fst x)) eqn:Hrx; [|reflexivity].
          assert (existsb r ids = true).
          { apply existsb_exists. exists (fst x). split; [|exact Hrx].
            apply in_map. exact Hx. }
          congruence.
        + rewrite E1, E2, E3, E4. lia. }
    assert (Hqr : forall x, In x (pg_modules (vm_graph s)) -> q (fst x) = true -> r (fst x) = false).
    { intros x _ Hq. unfold r. rewrite Hq. apply andb_false_r. }
    assert (Hdisj : forall x y v, In x (pg_modules (vm_graph s)) -> In y (pg_modules (vm_graph s)) ->
              q (fst x) = true -> r (fst y) = true ->
              In v (module_region (snd x)) -> In v (module_region (snd y)) -> False).
    { intros [a ma] [b mb] v Hx Hy Hqa Hrb Hva Hvb. simpl in *.
      assert (Hca : cont s v a = true).
      { rewrite (cont_entry s v a ma Hnd Hx). apply nat_list_mem_In. exact Hva. }
      assert (Hcb : cont s v b = true).
      { rewrite (cont_entry s v b mb Hnd Hy). apply nat_list_mem_In. exact Hvb. }
      pose proof (share_adjacent s v a b Hca Hcb) as Hab.
      unfold q in Hqa. apply nat_list_mem_In in Hqa.
      assert (Hb : In b ids) by (apply in_map_iff; exists (b, mb); auto).
      pose proof (HclC a b Hqa Hb Hab) as HbC.
      unfold r, q in Hrb. apply nat_list_mem_In in HbC. rewrite HbC in Hrb.
      rewrite andb_false_r in Hrb. discriminate. }
    destruct (restrict_union (vm_graph s) q r Hqr Hdisj) as [U1 [U2 [U3 U4]]].
    rewrite (restrict_graph_ext_in (vm_graph s) p (fun a => q a || r a)).
    + rewrite U1, U2, U3, U4.
      change (vm_graph (restrict_state s (fun a : ModuleID => nat_list_mem a C)))
        with (restrict_graph (vm_graph s) q) in Hcomp.
      lia.
    + intros [a ma] Hx. simpl. unfold r. destruct (q a) eqn:Hq; simpl.
      * apply HCp. unfold q in Hq. apply nat_list_mem_In. exact Hq.
      * rewrite andb_true_r. reflexivity.
Qed.

(** * Part 16. The full obstruction. *)

(** A well-formed triangulated state with distinct module IDs and
    connected vertex links cannot be calibrated at every module. *)
Theorem F3_calibration_obstruction : forall s,
  well_formed_triangulated (vm_graph s) ->
  links_connected s ->
  NoDup (map fst (pg_modules (vm_graph s))) ->
  ~ calibrated s.
Proof.
  intros s Hwf Hlinks Hnd Hcal.
  destruct Hwf as [_ [Htri [Hnorm [Hman [_ [_ [HF [_ [_ [Hge HBeq]]]]]]]]]].
  assert (Hne : exists a, In a (map fst (pg_modules (vm_graph s))) /\ (fun _ : ModuleID => true) a = true).
  { unfold DiscreteTopology.F in HF.
    destruct (pg_modules (vm_graph s)) as [|[a m] l] eqn:Hm; [simpl in HF; lia|].
    exists a. split; [left; reflexivity|reflexivity]. }
  pose proof (components_sum s Hnd Htri Hnorm Hman Hlinks Hcal
                (List.length (filter (fun _ => true) (map fst (pg_modules (vm_graph s)))))
                (fun _ => true) (le_n _) (fun _ _ _ _ _ _ => eq_refl) Hne) as H.
  rewrite restrict_graph_true in H.
  unfold DiscreteTopology.V in *. lia.
Qed.

(** * Part 17. The hypotheses of the full obstruction are satisfiable. *)

(** A boolean check of connected links, sound for links_connected. *)
Definition link_edge_b (g : PartitionGraph) (v w1 w2 : nat) : bool :=
  existsb (fun p => nat_list_mem v (module_region (snd p)) &&
                    nat_list_mem w1 (module_region (snd p)) &&
                    nat_list_mem w2 (module_region (snd p)) &&
                    negb (v =? w1) && negb (v =? w2) && negb (w1 =? w2)) (pg_modules g).

Definition link_vertex_b (g : PartitionGraph) (v w : nat) : bool :=
  existsb (fun p => nat_list_mem v (module_region (snd p)) &&
                    nat_list_mem w (module_region (snd p)) && negb (v =? w)) (pg_modules g).

Fixpoint link_reach (g : PartitionGraph) (v : nat) (nodes : list nat) (n w1 w2 : nat) : bool :=
  if w1 =? w2 then true
  else match n with
       | 0 => false
       | S n' => existsb (fun u => if link_edge_b g v w1 u
                                   then link_reach g v nodes n' u w2 else false) nodes
       end.

Lemma link_edge_b_sound : forall g v w1 w2, link_edge_b g v w1 w2 = true -> link_edge g v w1 w2.
Proof.
  intros g v w1 w2 H. apply existsb_exists in H. destruct H as [[mid m] [Hin H]].
  simpl in H. repeat rewrite andb_true_iff in H.
  destruct H as [[[[[H1 H2] H3] H4] H5] H6].
  apply nat_list_mem_In in H1. apply nat_list_mem_In in H2. apply nat_list_mem_In in H3.
  apply negb_true_iff, Nat.eqb_neq in H4. apply negb_true_iff, Nat.eqb_neq in H5.
  apply negb_true_iff, Nat.eqb_neq in H6.
  exists mid, m. repeat split; assumption.
Qed.

Lemma link_vertex_b_complete : forall g v w, link_vertex g v w -> link_vertex_b g v w = true.
Proof.
  intros g v w [mid [m [Hin [Hv [Hw Hvw]]]]]. apply existsb_exists.
  exists (mid, m). split; [exact Hin|]. simpl.
  apply nat_list_mem_In in Hv. apply nat_list_mem_In in Hw. rewrite Hv, Hw.
  destruct (Nat.eqb_spec v w); [contradiction|reflexivity].
Qed.

Lemma link_reach_sound : forall g v nodes n w1 w2,
  link_reach g v nodes n w1 w2 = true -> clos_refl_trans_1n nat (link_edge g v) w1 w2.
Proof.
  intros g v nodes n. induction n as [|n IH]; intros w1 w2 H; simpl in H.
  - destruct (Nat.eqb_spec w1 w2); [subst; constructor|discriminate].
  - destruct (Nat.eqb_spec w1 w2); [subst; constructor|].
    apply existsb_exists in H. destruct H as [u [_ Hu]].
    destruct (link_edge_b g v w1 u) eqn:He; [|discriminate].
    eapply Relation_Operators.rt1n_trans; [apply link_edge_b_sound; exact He|apply IH; exact Hu].
Qed.

Lemma links_connected_check : forall s n,
  forallb (fun v => forallb (fun w1 => forallb (fun w2 =>
      negb (link_vertex_b (vm_graph s) v w1 && link_vertex_b (vm_graph s) v w2) ||
      link_reach (vm_graph s) v (vertices (vm_graph s)) n w1 w2)
    (vertices (vm_graph s))) (vertices (vm_graph s))) (vertices (vm_graph s)) = true ->
  links_connected s.
Proof.
  intros s n H v w1 w2 H1 H2.
  assert (Hv : In v (vertices (vm_graph s))).
  { destruct H1 as [mid [m [Hin [Hv _]]]]. apply vertices_In. exists (mid, m). auto. }
  assert (Hw1 : In w1 (vertices (vm_graph s))).
  { destruct H1 as [mid [m [Hin [_ [Hw _]]]]]. apply vertices_In. exists (mid, m). auto. }
  assert (Hw2 : In w2 (vertices (vm_graph s))).
  { destruct H2 as [mid [m [Hin [_ [Hw _]]]]]. apply vertices_In. exists (mid, m). auto. }
  rewrite forallb_forall in H. specialize (H v Hv).
  rewrite forallb_forall in H. specialize (H w1 Hw1).
  rewrite forallb_forall in H. specialize (H w2 Hw2).
  rewrite (link_vertex_b_complete _ _ _ H1), (link_vertex_b_complete _ _ _ H2) in H.
  simpl in H. eapply link_reach_sound. exact H.
Qed.

Lemma om_links_connected : links_connected om_state.
Proof. apply (links_connected_check om_state 4). vm_compute. reflexivity. Qed.

(** The octahedron next to the 9-gon of Part 7 meets every hypothesis of
    F3_calibration_obstruction, so those hypotheses are consistent. *)
Corollary F3_obstruction_hypotheses_satisfiable :
  well_formed_triangulated (vm_graph om_state) /\ links_connected om_state /\
  NoDup (map fst (pg_modules (vm_graph om_state))) /\ ~ calibrated om_state.
Proof.
  split; [exact om_well_formed|]. split; [exact om_links_connected|].
  split; [exact om_nodup|].
  apply F3_calibration_obstruction; [exact om_well_formed|exact om_links_connected|exact om_nodup].
Qed.

(** * Assumption audit. *)

Print Assumptions F3_calibration_forces_flat_faces.
Print Assumptions F3_calibration_forces_five_triangles.
Print Assumptions total_angle_sum_identity.
Print Assumptions F3_calibration_window_R.
Print Assumptions F3_calibration_window.
Print Assumptions F3_vertex_triangle_bound.
Print Assumptions F3_calibration_consequences.
Print Assumptions F3_calibration_forces_degree_inequality.
Print Assumptions F3_calibration_obstruction_min_degree4.
Print Assumptions F3_calibration_forces_large_boundary.
Print Assumptions F3_calibration_obstruction_closed.
Print Assumptions F3_degree_route_insufficient.
Print Assumptions F3_om_not_calibrated.
Print Assumptions degree_sum_general.
Print Assumptions edges_faces_boundary.
Print Assumptions euler_component.
Print Assumptions component_inequality.
Print Assumptions components_sum.
Print Assumptions F3_calibration_obstruction.
Print Assumptions om_links_connected.
Print Assumptions F3_obstruction_hypotheses_satisfiable.
