(** MorphTensorGap.v: the kernel's tensor product never succeeds on a graph
    reconstructed from a hardware snapshot whose ranges are pairwise disjoint.
    Every reconstructed module region is a nonempty range, so a module that
    owns the union of two disjoint regions would have to share an address with
    one of them without being it, which disjointness forbids. *)
From Coq Require Import List Arith Lia String Bool.
Import ListNotations.
Require Import Kernel.VMState.
From KamiHW Require Import Abstraction.
Local Open Scope nat_scope.

Definition ranged_region (m : ModuleState) : Prop :=
  exists b n, module_region m = seq b (S n).

Lemma lookup_modules_ranged : forall l mid m,
  Forall (fun p => ranged_region (snd p)) l ->
  graph_lookup_modules l mid = Some m -> ranged_region m.
Proof.
  induction l as [|[id m'] l IH]; intros mid m HF H; cbn in H; [discriminate|].
  inversion HF as [|? ? Hh Ht]; subst.
  destruct (Nat.eqb id mid); [inversion H; subst; exact Hh|].
  exact (IH mid m Ht H).
Qed.

Lemma filtermap_ranged : forall (sizes bases : nat -> nat) l,
  Forall (fun p => ranged_region (snd p))
    (filtermap (fun i => if Nat.eqb (sizes i) 0 then None
       else Some (i, {| module_region := seq (bases i) (sizes i);
                        module_axioms := [];
                        module_mu_tensor := module_mu_tensor_default |})) l).
Proof.
  intros sizes bases l. induction l as [|i l IH]; cbn [filtermap]; [constructor|].
  destruct (Nat.eqb (sizes i) 0) eqn:E; [exact IH|].
  constructor; [|exact IH].
  cbn [snd module_region]. exists (bases i), (pred (sizes i)).
  apply Nat.eqb_neq in E. rewrite Nat.succ_pred by exact E. reflexivity.
Qed.

Lemma snap_full_graph_ranged : forall s mid m,
  graph_lookup (snap_full_graph s) mid = Some m -> ranged_region m.
Proof.
  intros s mid m H. unfold graph_lookup, snap_full_graph in H. cbn [pg_modules] in H.
  eapply lookup_modules_ranged; [|exact H].
  apply Forall_map.
  unfold snap_pt_to_graph. cbn [pg_modules].
  eapply Forall_impl;
    [|exact (filtermap_ranged (snap_pt_sizes s) (snap_pt_bases s) (rev (seq 0 (snap_pt_next_id s))))].
  intros [id m'] Hm. exact Hm.
Qed.

Lemma graph_lookup_modules_pair : forall l mid m,
  graph_lookup_modules l mid = Some m -> In (mid, m) l.
Proof.
  induction l as [|[id ms] rest IH]; intros mid m H; cbn in H; [discriminate|].
  destruct (Nat.eqb id mid) eqn:E.
  - apply Nat.eqb_eq in E. subst. inversion H; subst. left. reflexivity.
  - right. exact (IH _ _ H).
Qed.

Lemma find_region_modules_pair : forall l r id,
  graph_find_region_modules l r = Some id ->
  exists m, In (id, m) l /\ nat_list_eq (module_region m) r = true.
Proof.
  induction l as [|[id' ms] rest IH]; intros r id H; cbn in H; [discriminate|].
  destruct (nat_list_eq (module_region ms) r) eqn:E.
  - inversion H; subst. exists ms. split; [left; reflexivity | exact E].
  - destruct (IH r id H) as [m [Hin He]]. exists m. split; [right; exact Hin | exact He].
Qed.

Lemma nat_list_eq_incl_r : forall xs ys, nat_list_eq xs ys = true ->
  forall x, In x ys -> In x xs.
Proof.
  intros xs ys H x Hx. unfold nat_list_eq in H. apply andb_true_iff in H as [_ H].
  unfold nat_list_subset in H. rewrite forallb_forall in H.
  apply nat_list_mem_In. exact (H x Hx).
Qed.

(** Under [regions_disjoint], no module owns the union of two disjoint,
    nonempty regions of modules of the graph. *)
Lemma find_union_none : forall g ia ic a c,
  regions_disjoint g ->
  graph_lookup g ia = Some a -> graph_lookup g ic = Some c ->
  module_region a <> [] -> module_region c <> [] ->
  nat_list_disjoint (module_region a) (module_region c) = true ->
  graph_find_region g (nat_list_union (module_region a) (module_region c)) = None.
Proof.
  intros g ia ic a c Hd Ha Hc Hna Hnc Hdis.
  destruct (graph_find_region g _) as [id|] eqn:Hf; [|reflexivity]. exfalso.
  unfold graph_find_region in Hf.
  destruct (find_region_modules_pair _ _ _ Hf) as [m [Hin Heq]].
  assert (Hxa : exists x, In x (module_region a)).
  { destruct (module_region a) as [|x xs]; [exfalso; exact (Hna eq_refl)|].
    exists x. left. reflexivity. }
  assert (Hxc : exists x, In x (module_region c)).
  { destruct (module_region c) as [|x xs]; [exfalso; exact (Hnc eq_refl)|].
    exists x. left. reflexivity. }
  destruct Hxa as [xa Hxa]. destruct Hxc as [xc Hxc].
  assert (Hma : In xa (module_region m)).
  { apply (nat_list_eq_incl_r _ _ Heq).
    unfold nat_list_union, normalize_region.
    apply (proj2 (nodup_In _ _ _)). apply (proj2 (nodup_In _ _ _)).
    apply in_or_app. left. exact Hxa. }
  assert (Hmc : In xc (module_region m)).
  { apply (nat_list_eq_incl_r _ _ Heq).
    unfold nat_list_union, normalize_region.
    apply (proj2 (nodup_In _ _ _)). apply (proj2 (nodup_In _ _ _)).
    apply in_or_app. right. exact Hxc. }
  assert (Hia : id = ia).
  { destruct (Nat.eq_dec id ia) as [E|E]; [exact E|]. exfalso.
    pose proof (regions_disjoint_distinct_modules g id m ia a Hd Hin
                  (graph_lookup_modules_pair _ _ _ Ha) E) as Hdm.
    exact (proj1 (nat_list_disjoint_spec _ _) Hdm xa Hma Hxa). }
  assert (Hic : id = ic).
  { destruct (Nat.eq_dec id ic) as [E|E]; [exact E|]. exfalso.
    pose proof (regions_disjoint_distinct_modules g id m ic c Hd Hin
                  (graph_lookup_modules_pair _ _ _ Hc) E) as Hdm.
    exact (proj1 (nat_list_disjoint_spec _ _) Hdm xc Hmc Hxc). }
  assert (Hiac : ia = ic) by congruence.
  rewrite <- Hiac in Hc. rewrite Ha in Hc. inversion Hc; subst c.
  exact (proj1 (nat_list_disjoint_spec _ _) Hdis xa Hxa Hxa).
Qed.

(** On a reconstructed graph with pairwise disjoint ranges the tensor
    product finds no union module, so it is [None]. *)
Theorem snap_graph_tensor_none : forall s f g,
  regions_disjoint (snap_full_graph s) ->
  graph_tensor_morphisms (snap_full_graph s) f g = None.
Proof.
  intros s f g Hd. unfold graph_tensor_morphisms.
  destruct (graph_lookup_morphism _ f) as [mf|]; [|reflexivity].
  destruct (graph_lookup_morphism _ g) as [mg|]; [|reflexivity].
  destruct (graph_lookup _ (morph_source mf)) as [a|] eqn:Ea; [|reflexivity].
  destruct (graph_lookup _ (morph_target mf)) as [bm|] eqn:Eb; [|reflexivity].
  destruct (graph_lookup _ (morph_source mg)) as [c|] eqn:Ec; [|reflexivity].
  destruct (graph_lookup _ (morph_target mg)) as [dm|] eqn:Ed; [|reflexivity].
  destruct (nat_list_disjoint (module_region a) (module_region c) &&
            nat_list_disjoint (module_region bm) (module_region dm)) eqn:Edis;
    [|reflexivity].
  apply andb_true_iff in Edis as [E1 E2].
  destruct (snap_full_graph_ranged s _ _ Ea) as [ba [na Ha]].
  destruct (snap_full_graph_ranged s _ _ Ec) as [bc [nc Hc]].
  assert (N1 : module_region a <> []) by (rewrite Ha; discriminate).
  assert (N2 : module_region c <> []) by (rewrite Hc; discriminate).
  rewrite (find_union_none _ _ _ _ _ Hd Ea Ec N1 N2 E1). reflexivity.
Qed.
