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

    Not proved: the full target
      forall s, well_formed_triangulated (vm_graph s) ->
        (vertex links connected) -> NoDup (module IDs) ->
        ~ calibrated.
    By items 4, 6 and 7 the open case is a state with boundary, with
    61 F <= 140 B, F >= 11 and every vertex-degree pattern allowed by the
    degree inequality (some vertex of degree at most 3). Closing it needs
    (a) a formal definition of connected vertex links, (b) Euler
    characteristic bounds per connected component (chi <= 2, and chi <= 1
    with boundary), because B = 3 chi is a global identity that lets a
    closed component pay for extra boundary on another component, and
    (c) a count of the face-graph triangles that have no common vertex,
    because by item 8 the vertex count alone does not reach the window.
    The hypothesis (exists m, module_triangles s m <> []) of the target is
    not needed anywhere: 1 <= F comes with well_formed_triangulated.

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
