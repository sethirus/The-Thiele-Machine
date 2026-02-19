From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

From Kernel Require Import VMState MuGravity.
From ModularProofs Require Import EncodingBounds.

(** * Finite triangular lattice encoding for partition graphs.

    This provides a concrete, bounded graph class that we can use as the
    first testbed for geometric calibration proofs.
*)

Definition lattice_size (n : nat) : nat := n * n.

Definition lattice_id (n x y : nat) : nat := x + n * y.

Definition coord_of_id (n id : nat) : nat * nat :=
  if n =? 0 then (0, 0) else (id mod n, id / n).

Definition in_bounds (n x y : nat) : bool := (x <? n) && (y <? n).

Definition neighbor_coords (x y : nat) : list (nat * nat) :=
  [(x + 1, y);
   (x, y + 1);
   (x + 1, y + 1);
   (x, y - 1);
   (x - 1, y);
   (x - 1, y - 1)].

Definition neighbors_of (n id : nat) : list nat :=
  let '(x, y) := coord_of_id n id in
  map (fun '(x', y') => lattice_id n x' y')
      (filter (fun '(x', y') => in_bounds n x' y') (neighbor_coords x y)).

Definition edge_id (n u v : nat) : nat :=
  let max := lattice_size n in
  if u <? v then u * max + v else v * max + u.

Definition module_region_for (n id : nat) : list nat :=
  map (edge_id n id) (neighbors_of n id).

Definition module_state_for (n id : nat) : ModuleState :=
  {| module_region := module_region_for n id;
     module_axioms := [] |}.

Definition lattice_ids (n : nat) : list nat := seq 0 (lattice_size n).

Definition lattice_modules (n : nat) : list (ModuleID * ModuleState) :=
  map (fun id => (id, module_state_for n id)) (lattice_ids n).

Definition lattice_graph (n : nat) : PartitionGraph :=
  {| pg_next_id := lattice_size n;
     pg_modules := lattice_modules n |}.

Definition lattice_vm_state (n : nat) : VMState :=
  {| vm_graph := lattice_graph n;
     vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0 |};
     vm_regs := repeat 0 32;
     vm_mem := repeat 0 256;
     vm_pc := 0;
     vm_mu := 0;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err := false |}.

Lemma lattice_id_coord_of_id : forall n u,
  n <> 0 ->
  lattice_id n (fst (coord_of_id n u)) (snd (coord_of_id n u)) = u.
Proof.
  intros n u Hn.
  unfold lattice_id, coord_of_id.
  destruct (n =? 0) eqn:H0.
  - apply Nat.eqb_eq in H0. contradiction.
  - simpl.
    pose proof (Nat.div_mod u n Hn) as Hdivmod.
    replace (u / n * n) with (n * (u / n)) in Hdivmod by (rewrite Nat.mul_comm; reflexivity).
    rewrite Nat.add_comm in Hdivmod.
    symmetry.
    exact Hdivmod.
Qed.

Lemma coord_of_id_lattice_id : forall n x y,
  n <> 0 ->
  x < n ->
  coord_of_id n (lattice_id n x y) = (x, y).
Proof.
  intros n x y Hn Hx.
  unfold coord_of_id, lattice_id.
  destruct (n =? 0) eqn:H0.
  - apply Nat.eqb_eq in H0. contradiction.
  - simpl.
    assert (Hn' : 0 < n) by lia.
    pose proof (div_mul_add_small n y x Hn' Hx) as [Hdiv Hmod].
    rewrite Nat.add_comm.
    rewrite Nat.mul_comm.
    rewrite Hmod.
    rewrite Hdiv.
    reflexivity.
Qed.

Lemma coord_of_id_in_bounds : forall n u,
  n <> 0 ->
  u < lattice_size n ->
  in_bounds n (fst (coord_of_id n u)) (snd (coord_of_id n u)) = true.
Proof.
  intros n u Hn Hu.
  unfold in_bounds, coord_of_id.
  destruct (n =? 0) eqn:H0.
  - apply Nat.eqb_eq in H0. contradiction.
  - simpl.
    apply andb_true_intro.
    split.
    + apply Nat.ltb_lt.
      apply Nat.mod_upper_bound.
      exact Hn.
    + apply Nat.ltb_lt.
      unfold lattice_size in Hu.
      apply (Nat.div_lt_upper_bound u n n) in Hu.
      * exact Hu.
      * exact Hn.
Qed.

Lemma edge_id_sym : forall n u v,
  edge_id n u v = edge_id n v u.
Proof.
  intros n u v.
  unfold edge_id.
  destruct (u <? v) eqn:Huv;
  destruct (v <? u) eqn:Hvu.
  - apply Nat.ltb_lt in Huv.
    apply Nat.ltb_lt in Hvu.
    lia.
  - reflexivity.
  - reflexivity.
  - apply Nat.ltb_ge in Huv.
    apply Nat.ltb_ge in Hvu.
    assert (u = v) by (apply Nat.le_antisymm; [exact Hvu | exact Huv]).
    subst.
    reflexivity.
Qed.

Lemma module_region_for_has_edge : forall n u v,
  In v (neighbors_of n u) ->
  In (edge_id n u v) (module_region_for n u).
Proof.
  intros n u v Hin.
  unfold module_region_for.
  apply in_map_iff.
  exists v.
  split; [reflexivity|assumption].
Qed.

Lemma nat_list_disjoint_false_of_mem : forall xs ys x,
  In x xs ->
  nat_list_mem x ys = true ->
  nat_list_disjoint xs ys = false.
Proof.
  intros xs ys x Hin Hmem.
  unfold nat_list_disjoint.
  apply Bool.not_true_is_false.
  intro Hall.
  pose proof (proj1 (forallb_forall (fun y => negb (nat_list_mem y ys)) xs) Hall) as Hall'.
  specialize (Hall' x Hin).
  apply Bool.negb_true_iff in Hall'.
  rewrite Hmem in Hall'.
  discriminate.
Qed.

Lemma nat_list_mem_true_of_in : forall x xs,
  In x xs ->
  nat_list_mem x xs = true.
Proof.
  intros x xs Hin.
  induction xs as [|y ys IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst. rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.eqb x y) eqn:Heq.
      * reflexivity.
      * apply IH. exact Hin.
Qed.

Lemma module_regions_share_edge_if_neighbors : forall n u v,
  In v (neighbors_of n u) ->
  In u (neighbors_of n v) ->
  nat_list_disjoint (module_region_for n u) (module_region_for n v) = false.
Proof.
  intros n u v Huv Hvu.
  apply nat_list_disjoint_false_of_mem with (x := edge_id n u v).
  - apply module_region_for_has_edge.
    exact Huv.
  - unfold module_region_for.
    rewrite edge_id_sym.
    apply nat_list_mem_true_of_in.
    apply module_region_for_has_edge.
    exact Hvu.
Qed.

Lemma neighbor_coords_sym : forall x y x' y',
  In (x', y') (neighbor_coords x y) ->
  In (x, y) (neighbor_coords x' y').
Proof.
  intros x y x' y' Hin.
  unfold neighbor_coords in Hin.
  simpl in Hin.
  destruct Hin as [Heq|Hin];
  [inversion Heq; subst; simpl; right; right; right; right; left;
   replace (x + 1 - 1) with x by lia; reflexivity|
   destruct Hin as [Heq|Hin];
   [inversion Heq; subst; simpl; right; right; right; left;
    replace (y + 1 - 1) with y by lia; reflexivity|
    destruct Hin as [Heq|Hin];
    [inversion Heq; subst; simpl; right; right; right; right; right; left;
     replace (x + 1 - 1) with x by lia;
     replace (y + 1 - 1) with y by lia; reflexivity|
     destruct Hin as [Heq|Hin];
       [inversion Heq; subst;
        destruct y as [|y1]; simpl;
       [right; right; right; left; reflexivity|
         right; left; rewrite Nat.sub_0_r; rewrite Nat.add_comm; simpl; reflexivity]|
      destruct Hin as [Heq|Hin];
       [inversion Heq; subst;
          destruct x as [|x1]; simpl;
        [right; right; right; right; left; reflexivity|
        left; rewrite Nat.sub_0_r; rewrite Nat.add_comm; simpl; reflexivity]|
       destruct Hin as [Heq|Hin];
        [inversion Heq; subst;
           destruct x as [|x1]; destruct y as [|y1]; simpl;
         [right; right; right; left; reflexivity|
           right; left; rewrite Nat.sub_0_r; rewrite Nat.add_comm; simpl; reflexivity|
         left; rewrite Nat.sub_0_r; rewrite Nat.add_comm; simpl; reflexivity|
         right; right; left;
         repeat rewrite Nat.sub_0_r;
         rewrite (Nat.add_comm x1 1);
         rewrite (Nat.add_comm y1 1);
         simpl; reflexivity]|
        inversion Hin]]]]]].
Qed.

Lemma neighbors_of_symmetric : forall n u v,
  n <> 0 ->
  u < lattice_size n ->
  v < lattice_size n ->
  In v (neighbors_of n u) ->
  In u (neighbors_of n v).
Proof.
  intros n u v Hn Hu Hv Huv.
  unfold neighbors_of in Huv.
  remember (coord_of_id n u) as cu.
  destruct cu as [x y].
  apply in_map_iff in Huv.
  destruct Huv as [[x' y'] [Hv_eq Hfilter]].
  simpl in Hv_eq.
  subst v.
  apply filter_In in Hfilter.
  destruct Hfilter as [Hcoords Hbounds].
  unfold neighbors_of.
  remember (coord_of_id n (lattice_id n x' y')) as cv.
  destruct cv as [xv yv].
  assert (Hcv : (xv, yv) = (x', y')).
  {
    rewrite Heqcv.
    apply coord_of_id_lattice_id; try assumption.
    apply andb_true_iff in Hbounds.
    destruct Hbounds as [Hx Hy].
    apply Nat.ltb_lt in Hx.
    apply Nat.ltb_lt in Hy.
    exact Hx.
  }
  inversion Hcv. subst xv yv.
  apply in_map_iff.
  exists (x, y).
  split.
  - pose proof (f_equal fst Heqcu) as Hx.
    pose proof (f_equal snd Heqcu) as Hy.
    simpl in Hx.
    simpl in Hy.
    rewrite Hx, Hy.
    apply lattice_id_coord_of_id. exact Hn.
  - apply filter_In.
    split.
    + apply neighbor_coords_sym. exact Hcoords.
    + pose proof (f_equal fst Heqcu) as Hx.
      pose proof (f_equal snd Heqcu) as Hy.
      simpl in Hx.
      simpl in Hy.
      rewrite Hx, Hy.
      apply coord_of_id_in_bounds; assumption.
Qed.


Lemma all_ids_below_map : forall ids bound f,
  (forall id, In id ids -> id < bound) ->
  all_ids_below (map (fun id => (id, f id)) ids) bound.
Proof.
  induction ids as [|id rest IH]; intros bound f Hlt; simpl.
  - exact I.
  - split.
    + apply Hlt. simpl. left. reflexivity.
    + apply IH. intros id' Hin. apply Hlt. simpl. right. exact Hin.
Qed.

Lemma lattice_graph_well_formed : forall n,
  well_formed_graph (lattice_graph n).
Proof.
  intro n.
  unfold well_formed_graph, lattice_graph, lattice_modules, lattice_ids.
  apply all_ids_below_map.
  intros id Hin.
  apply in_seq in Hin.
  destruct Hin as [_ Hlt].
  exact Hlt.
Qed.

Lemma graph_lookup_modules_map : forall ids f mid,
  In mid ids ->
  graph_lookup_modules (map (fun id => (id, f id)) ids) mid = Some (f mid).
Proof.
  induction ids as [|id rest IH]; intros f mid Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst. rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.eqb id mid) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst. reflexivity.
      * apply IH. exact Hin.
Qed.

Lemma graph_lookup_lattice : forall n id,
  id < lattice_size n ->
  graph_lookup (lattice_graph n) id = Some (module_state_for n id).
Proof.
  intros n id Hid.
  unfold graph_lookup, lattice_graph, lattice_modules, lattice_ids.
  apply graph_lookup_modules_map.
  apply in_seq.
  split; [lia|].
  rewrite Nat.add_0_l. exact Hid.
Qed.

Lemma nat_list_mem_true_in : forall x xs,
  nat_list_mem x xs = true ->
  In x xs.
Proof.
  induction xs as [|y ys IH]; intros Hmem; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:Heq.
    + left. apply Nat.eqb_eq in Heq. symmetry. exact Heq.
    + right. apply IH. exact Hmem.
Qed.

Lemma nat_list_disjoint_false_exists : forall xs ys,
  nat_list_disjoint xs ys = false ->
  exists x, In x xs /\ nat_list_mem x ys = true.
Proof.
  induction xs as [|x xs IH]; intros ys Hdisjoint; simpl in *.
  - discriminate.
  - apply Bool.andb_false_iff in Hdisjoint.
    destruct Hdisjoint as [Hmem|Hrest].
    + exists x. split.
      * left. reflexivity.
      * apply Bool.negb_false_iff in Hmem. exact Hmem.
    + destruct (IH _ Hrest) as [y [Hin Hmem]].
      exists y. split.
      * right. exact Hin.
      * exact Hmem.
Qed.

Lemma in_bounds_true_lt : forall n x y,
  in_bounds n x y = true ->
  x < n /\
  y < n.
Proof.
  intros n x y Hb.
  unfold in_bounds in Hb.
  apply andb_true_iff in Hb.
  destruct Hb as [Hx Hy].
  split; apply Nat.ltb_lt; assumption.
Qed.

Lemma lattice_id_lt : forall n x y,
  x < n ->
  y < n ->
  lattice_id n x y < lattice_size n.
Proof.
  intros n x y Hx Hy.
  unfold lattice_id, lattice_size.
  destruct n as [|n']; simpl in *.
  - lia.
  - assert (Hmul : S n' * y < S n' * S n') by
      (apply Nat.mul_lt_mono_pos_l; lia).
    nia.
Qed.

Lemma neighbors_of_lt : forall n id v,
  In v (neighbors_of n id) ->
  v < lattice_size n.
Proof.
  intros n id v Hin.
  unfold neighbors_of in Hin.
  destruct (coord_of_id n id) as [x0 y0] eqn:Hc.
  set (coords := neighbor_coords x0 y0).
  set (bounded := filter (fun '(x', y') => in_bounds n x' y') coords).
  change (In v (map (fun '(x', y') => lattice_id n x' y') bounded)) in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [[x y] [Hv Hfilter]].
  subst v.
  unfold bounded in Hfilter.
  apply filter_In in Hfilter.
  destruct Hfilter as [_ Hbounds].
  apply in_bounds_true_lt in Hbounds.
  destruct Hbounds as [Hx Hy].
  apply lattice_id_lt; assumption.
Qed.

Lemma edge_id_min_max : forall n u v,
  edge_id n u v = Nat.min u v * lattice_size n + Nat.max u v.
Proof.
  intros n u v.
  unfold edge_id.
  destruct (u <? v) eqn:Huv.
  - apply Nat.ltb_lt in Huv.
    rewrite Nat.min_l by lia.
    rewrite Nat.max_r by lia.
    reflexivity.
  - apply Nat.ltb_ge in Huv.
    rewrite Nat.min_r by lia.
    rewrite Nat.max_l by lia.
    reflexivity.
Qed.

Lemma edge_id_eq_unordered : forall n u v c d,
  n <> 0 ->
  u < lattice_size n ->
  v < lattice_size n ->
  c < lattice_size n ->
  d < lattice_size n ->
  edge_id n u v = edge_id n c d ->
  (u = c /\ v = d) \/ (u = d /\ v = c).
Proof.
  intros n u v c d Hn Hu Hv Hc Hd Heq.
  set (max := lattice_size n).
  assert (Hmax : 0 < max) by (unfold max; destruct n; simpl in *; lia).
  assert (Huvmax : Nat.max u v < max) by (subst max; lia).
  assert (Hcdmax : Nat.max c d < max) by (subst max; lia).
  pose proof (div_mul_add_small max (Nat.min u v) (Nat.max u v) Hmax Huvmax) as [Hdiv1 Hmod1].
  pose proof (div_mul_add_small max (Nat.min c d) (Nat.max c d) Hmax Hcdmax) as [Hdiv2 Hmod2].
  assert (Hdiv1' : edge_id n u v / max = Nat.min u v) by (rewrite edge_id_min_max; exact Hdiv1).
  assert (Hmod1' : edge_id n u v mod max = Nat.max u v) by (rewrite edge_id_min_max; exact Hmod1).
  assert (Hdiv2' : edge_id n c d / max = Nat.min c d) by (rewrite edge_id_min_max; exact Hdiv2).
  assert (Hmod2' : edge_id n c d mod max = Nat.max c d) by (rewrite edge_id_min_max; exact Hmod2).
  rewrite Heq in Hdiv1', Hmod1'.
  rewrite Hdiv2' in Hdiv1'.
  rewrite Hmod2' in Hmod1'.
  assert (Hmin : Nat.min u v = Nat.min c d) by (symmetry; exact Hdiv1').
  assert (Hmaxeq : Nat.max u v = Nat.max c d) by (symmetry; exact Hmod1').
  destruct (Nat.le_gt_cases u v) as [Huv|Huv];
  destruct (Nat.le_gt_cases c d) as [Hcd|Hcd].
  - left.
    rewrite Nat.min_l in Hmin by lia.
    rewrite Nat.max_r in Hmaxeq by lia.
    rewrite Nat.min_l in Hmin by lia.
    rewrite Nat.max_r in Hmaxeq by lia.
    split; [exact Hmin|exact Hmaxeq].
  - right.
    rewrite Nat.min_l in Hmin by lia.
    rewrite Nat.max_r in Hmaxeq by lia.
    rewrite Nat.min_r in Hmin by lia.
    rewrite Nat.max_l in Hmaxeq by lia.
    split; [exact Hmin|exact Hmaxeq].
  - right.
    rewrite Nat.min_r in Hmin by lia.
    rewrite Nat.max_l in Hmaxeq by lia.
    rewrite Nat.min_l in Hmin by lia.
    rewrite Nat.max_r in Hmaxeq by lia.
    split; [exact Hmaxeq|exact Hmin].
  - left.
    rewrite Nat.min_r in Hmin by lia.
    rewrite Nat.max_l in Hmaxeq by lia.
    rewrite Nat.min_r in Hmin by lia.
    rewrite Nat.max_l in Hmaxeq by lia.
    split; [exact Hmaxeq|exact Hmin].
Qed.

Lemma modules_adjacent_by_region_lattice : forall n u v,
  u < lattice_size n ->
  v < lattice_size n ->
  modules_adjacent_by_region (lattice_vm_state n) u v =
  negb (nat_list_disjoint (module_region_for n u) (module_region_for n v)).
Proof.
  intros n u v Hu Hv.
  unfold modules_adjacent_by_region, lattice_vm_state.
  simpl.
  rewrite (graph_lookup_lattice n u Hu).
  rewrite (graph_lookup_lattice n v Hv).
  simpl. reflexivity.
Qed.

Lemma modules_adjacent_by_region_neighbors : forall n u v,
  n <> 0 ->
  u < lattice_size n ->
  v < lattice_size n ->
  u <> v ->
  modules_adjacent_by_region (lattice_vm_state n) u v = true <->
  In v (neighbors_of n u) /\ In u (neighbors_of n v).
Proof.
  intros n u v Hn Hu Hv Huvneq.
  rewrite (modules_adjacent_by_region_lattice n u v Hu Hv).
  split.
  - intro Hadj.
    apply Bool.negb_true_iff in Hadj.
    destruct (nat_list_disjoint_false_exists _ _ Hadj) as [x [Hin Hmem]].
    apply nat_list_mem_true_in in Hmem.
    unfold module_region_for in Hin, Hmem.
    apply in_map_iff in Hin.
    apply in_map_iff in Hmem.
    destruct Hin as [w1 [Hx1 Hw1]].
    destruct Hmem as [w2 [Hx2 Hw2]].
    subst x.
    assert (Hw1lt : w1 < lattice_size n) by (apply (neighbors_of_lt n u w1); exact Hw1).
    assert (Hw2lt : w2 < lattice_size n) by (apply (neighbors_of_lt n v w2); exact Hw2).
        pose proof (edge_id_eq_unordered n u w1 v w2 Hn Hu Hw1lt Hv Hw2lt (eq_sym Hx2)) as Hpair.
        refine (match Hpair with
                | or_introl Hpair' => _
                | or_intror Hpair' => _
                end).
        + destruct Hpair' as [Huv1 _].
          exfalso. apply Huvneq. exact Huv1.
        + destruct Hpair' as [Huv2 Hw2'].
          subst u. subst w1.
          split; [exact Hw1 | exact Hw2].
  - intros [Huv Hvu].
    apply Bool.negb_true_iff.
    apply module_regions_share_edge_if_neighbors; assumption.
Qed.

Lemma lattice_modules_ids : forall n,
  map fst (lattice_modules n) = lattice_ids n.
Proof.
  intro n.
  unfold lattice_modules, lattice_ids.
  rewrite map_map. simpl.
  rewrite map_id. reflexivity.
Qed.

Lemma module_neighbors_lattice_iff_mutual : forall n u v,
  n <> 0 ->
  u < lattice_size n ->
  v < lattice_size n ->
  In v (module_neighbors (lattice_vm_state n) u) <->
  v <> u /\ In v (neighbors_of n u) /\ In u (neighbors_of n v).
Proof.
  intros n u v Hn Hu Hv.
  unfold module_neighbors, module_neighbors_physical, module_neighbors_adjacent.
  unfold lattice_vm_state, lattice_graph.
  simpl.
  rewrite lattice_modules_ids.
  split.
  - intro Hin.
    apply filter_In in Hin.
    destruct Hin as [Hin Hpred].
    apply andb_true_iff in Hpred.
    destruct Hpred as [Hneq Hadj].
    apply Bool.negb_true_iff in Hneq.
    apply Nat.eqb_neq in Hneq.
    assert (Hneq' : v <> u) by (intro Heq; apply Hneq; symmetry; exact Heq).
    pose proof (proj1 (modules_adjacent_by_region_neighbors n u v Hn Hu Hv Hneq) Hadj) as Hneighbors.
    destruct Hneighbors as [Huv Hvu].
    split; [exact Hneq'|].
    split; assumption.
  - intros [Hneq [Huv Hvu]].
    apply filter_In.
    split.
    + apply in_seq. split; [lia|].
      rewrite Nat.add_0_l. exact Hv.
    + apply andb_true_iff. split.
      * apply Bool.negb_true_iff. apply Nat.eqb_neq. intro Heq. apply Hneq. symmetry. exact Heq.
      * assert (Hneq' : u <> v) by (intro Heq; apply Hneq; symmetry; exact Heq).
        apply (proj2 (modules_adjacent_by_region_neighbors n u v Hn Hu Hv Hneq')).
        split; assumption.
Qed.

Lemma module_neighbors_lattice_iff : forall n u v,
  n <> 0 ->
  u < lattice_size n ->
  v < lattice_size n ->
  In v (module_neighbors (lattice_vm_state n) u) <->
  v <> u /\ In v (neighbors_of n u).
Proof.
  intros n u v Hn Hu Hv.
  split.
  - intro Hin.
    apply (proj1 (module_neighbors_lattice_iff_mutual n u v Hn Hu Hv)) in Hin.
    destruct Hin as [Hneq [Huv _]].
    split; assumption.
  - intros [Hneq Huv].
    apply (proj2 (module_neighbors_lattice_iff_mutual n u v Hn Hu Hv)).
    split; [exact Hneq|].
    split; [exact Huv|].
    apply neighbors_of_symmetric; assumption.
Qed.

Lemma module_neighbors_lattice_eq : forall n u,
  n <> 0 ->
  u < lattice_size n ->
  module_neighbors (lattice_vm_state n) u =
  filter (fun v => andb (negb (Nat.eqb u v)) (nat_list_mem v (neighbors_of n u)))
         (lattice_ids n).
Proof.
  intros n u Hn Hu.
  unfold module_neighbors, module_neighbors_physical, module_neighbors_adjacent.
  unfold lattice_vm_state, lattice_graph.
  simpl.
  rewrite lattice_modules_ids.
  apply filter_ext_in.
  intros v Hin.
  apply in_seq in Hin.
  destruct Hin as [_ Hv].
  destruct (Nat.eqb u v) eqn:Heq; simpl.
  - reflexivity.
  - apply Nat.eqb_neq in Heq.
    apply eq_true_iff_eq.
    split.
    + intro Hadj.
      pose proof (proj1 (modules_adjacent_by_region_neighbors n u v Hn Hu Hv Heq) Hadj) as Hneighbors.
      apply nat_list_mem_true_of_in. exact (proj1 Hneighbors).
    + intro Hmem.
      apply nat_list_mem_true_in in Hmem as Huv.
      pose proof (neighbors_of_symmetric n u v Hn Hu Hv Huv) as Hvu.
      pose proof (proj2 (modules_adjacent_by_region_neighbors n u v Hn Hu Hv Heq)) as Hadj'.
      apply Hadj'. exact (conj Huv Hvu).
Qed.

