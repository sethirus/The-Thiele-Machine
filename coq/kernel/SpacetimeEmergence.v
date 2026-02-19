From Coq Require Import List Arith.PeanoNat Lia.
From Coq Require Import Classes.RelationClasses.

From Kernel Require Import VMState VMStep KernelPhysics.

Import ListNotations.

Definition Event : Type := VMState.
Definition event_equiv : Event -> Event -> Prop := obs_equiv.

Instance event_equiv_equivalence : Equivalence event_equiv.
Proof.
  split.
  - exact obs_equiv_refl.
  - exact obs_equiv_sym.
  - exact obs_equiv_trans.
Qed.

Definition step_rel (s s' : VMState) : Prop := exists instr, vm_step s instr s'.

Inductive reaches : VMState -> VMState -> Prop :=
| reaches_refl : forall s, reaches s s
| reaches_cons : forall s1 s2 s3, step_rel s1 s2 -> reaches s2 s3 -> reaches s1 s3.

(** [reaches_one]: formal specification. *)
Lemma reaches_one : forall s s', step_rel s s' -> reaches s s'.
Proof.
  intros s s' H.
  eapply reaches_cons.
  - exact H.
  - constructor.
Qed.

(** [reaches_trans]: formal specification. *)
Lemma reaches_trans : forall s1 s2 s3, reaches s1 s2 -> reaches s2 s3 -> reaches s1 s3.
Proof.
  intros s1 s2 s3 H12 H23.
  induction H12.
  - exact H23.
  - eapply reaches_cons; eauto.
Qed.

(** [step_rel_no_signaling]: formal specification. *)
Lemma step_rel_no_signaling :
  forall s instr s' mid,
    well_formed_graph s.(vm_graph) ->
    mid < pg_next_id s.(vm_graph) ->
    vm_step s instr s' ->
    ~ In mid (instr_targets instr) ->
    ObservableRegion s mid = ObservableRegion s' mid.
Proof.
  intros s instr s' mid Hwf Hmid Hstep Hnot.
  eapply observational_no_signaling; eauto.
Qed.

(** [all_ids_below_graph_insert_modules]: formal specification. *)
Lemma all_ids_below_graph_insert_modules :
  forall modules bound mid m,
    all_ids_below modules bound ->
    mid < bound ->
    all_ids_below (graph_insert_modules modules mid m) bound.
Proof.
  induction modules as [|[id ms] rest IH]; intros bound mid m Hall Hlt.
  - simpl. split; [exact Hlt| exact I].
  - simpl in Hall. destruct Hall as [Hid Hrest].
    simpl. destruct (Nat.eqb id mid) eqn:Heq.
    + split; [exact Hlt| exact Hrest].
    + split.
      * exact Hid.
      * apply IH; assumption.
Qed.

(** [graph_update_preserves_wf]: formal specification. *)
Lemma graph_update_preserves_wf : forall g mid m,
  well_formed_graph g ->
  mid < pg_next_id g ->
  well_formed_graph (graph_update g mid m).
Proof.
  intros g mid m Hwf Hlt.
  unfold graph_update, well_formed_graph. simpl.
  apply all_ids_below_graph_insert_modules; assumption.
Qed.

(** [graph_add_axiom_preserves_wf]: formal specification. *)
Lemma graph_add_axiom_preserves_wf : forall g mid ax,
  well_formed_graph g ->
  well_formed_graph (graph_add_axiom g mid ax).
Proof.
  intros g mid ax Hwf.
  unfold graph_add_axiom.
  destruct (graph_lookup g mid) eqn:Hlookup.
  - apply graph_update_preserves_wf; [exact Hwf|].
    assert (mid < pg_next_id g) as Hlt.
    { destruct (Nat.lt_ge_cases mid (pg_next_id g)) as [Hlt|Hge]; [exact Hlt|].
      pose proof (wf_graph_lookup_beyond_next_id g mid Hwf Hge) as Hnone.
      rewrite Hlookup in Hnone. discriminate. }
    exact Hlt.
  - exact Hwf.
Qed.

(** [graph_add_axioms_preserves_wf]: formal specification. *)
Lemma graph_add_axioms_preserves_wf : forall axs g mid,
  well_formed_graph g ->
  well_formed_graph (graph_add_axioms g mid axs).
Proof.
  induction axs as [|ax rest IH]; intros g mid Hwf.
  - simpl. exact Hwf.
  - simpl.
    apply IH.
    apply graph_add_axiom_preserves_wf.
    exact Hwf.
Qed.

(** [graph_record_discovery_preserves_wf]: formal specification. *)
Lemma graph_record_discovery_preserves_wf : forall g mid ev,
  well_formed_graph g ->
  well_formed_graph (graph_record_discovery g mid ev).
Proof.
  intros g mid ev Hwf.
  unfold graph_record_discovery.
  apply graph_add_axioms_preserves_wf.
  exact Hwf.
Qed.

(** [graph_pnew_preserves_wf]: formal specification. *)
Lemma graph_pnew_preserves_wf : forall g region,
  well_formed_graph g ->
  well_formed_graph (fst (graph_pnew g region)).
Proof.
  intros g region Hwf.
  unfold graph_pnew.
  destruct (graph_find_region g (normalize_region region)) eqn:Hfind.
  - simpl. exact Hwf.
  - simpl. apply graph_add_module_preserves_wf. exact Hwf.
Qed.

(** [graph_psplit_preserves_wf]: formal specification. *)
Lemma graph_psplit_preserves_wf : forall g mid left right g' l_id r_id,
  well_formed_graph g ->
  graph_psplit g mid left right = Some (g', l_id, r_id) ->
  well_formed_graph g'.
Proof.
  intros g mid left right g' l_id r_id Hwf Hps.
  unfold graph_psplit in Hps.
  destruct (graph_lookup g mid) eqn:Hlookup; try discriminate.
  set (left_norm := normalize_region left) in *.
  set (right_norm := normalize_region right) in *.
  destruct (orb (Nat.eqb (length left_norm) 0) (Nat.eqb (length right_norm) 0)) eqn:Hempty.
  - destruct (graph_add_module g [] []) as [g1 empty_id] eqn:Hadd.
    inversion Hps; subst.
    pose proof (graph_add_module_preserves_wf g [] [] Hwf) as Hwf_fst.
    rewrite Hadd in Hwf_fst. simpl in Hwf_fst.
    exact Hwf_fst.
  - destruct (partition_valid (module_region m) left_norm right_norm) eqn:Hvalid; try discriminate.
    destruct (graph_remove g mid) as [[g_removed removed]|] eqn:Hrem; try discriminate.
    destruct (graph_add_module g_removed left_norm (module_axioms m)) as [g_left left_id] eqn:HaddL.
    destruct (graph_add_module g_left right_norm (module_axioms m)) as [g_right right_id] eqn:HaddR.
    inversion Hps; subst.
    pose proof (graph_remove_preserves_wf g mid g_removed removed Hwf Hrem) as Hwf_removed.
    pose proof (graph_add_module_preserves_wf g_removed left_norm (module_axioms m) Hwf_removed) as Hwf_left_fst.
    rewrite HaddL in Hwf_left_fst. simpl in Hwf_left_fst.
    pose proof (graph_add_module_preserves_wf g_left right_norm (module_axioms m) Hwf_left_fst) as Hwf_right_fst.
    rewrite HaddR in Hwf_right_fst. simpl in Hwf_right_fst.
    exact Hwf_right_fst.
Qed.

(** [graph_pmerge_preserves_wf]: formal specification. *)
Lemma graph_pmerge_preserves_wf : forall g m1 m2 g' merged_id,
  well_formed_graph g ->
  graph_pmerge g m1 m2 = Some (g', merged_id) ->
  well_formed_graph g'.
Proof.
  intros g m1 m2 g' merged_id Hwf Hp.
  unfold graph_pmerge in Hp.
  destruct (Nat.eqb m1 m2) eqn:Heq; try discriminate.
  destruct (graph_remove g m1) as [[g_without_m1 mod1]|] eqn:Hrm1; try discriminate.
  pose proof (graph_remove_preserves_wf g m1 g_without_m1 mod1 Hwf Hrm1) as Hwf1.
  destruct (graph_remove g_without_m1 m2) as [[g_without_both mod2]|] eqn:Hrm2; try discriminate.
  pose proof (graph_remove_preserves_wf g_without_m1 m2 g_without_both mod2 Hwf1 Hrm2) as Hwf2.
  destruct (negb (nat_list_disjoint (module_region mod1) (module_region mod2))) eqn:Hdisj; try discriminate.
  set (union := nat_list_union (module_region mod1) (module_region mod2)) in *.
  set (combined_axioms := module_axioms mod1 ++ module_axioms mod2) in *.
  destruct (graph_find_region g_without_both union) as [existing_id|] eqn:Hfind.
  {
    destruct (graph_lookup g_without_both existing_id) eqn:Hlookup; try discriminate.
    assert (existing_id < pg_next_id g_without_both) as Hlt.
    { destruct (Nat.lt_ge_cases existing_id (pg_next_id g_without_both)) as [Hlt|Hge]; [exact Hlt|].
      pose proof (wf_graph_lookup_beyond_next_id g_without_both existing_id Hwf2 Hge) as Hnone.
      rewrite Hlookup in Hnone. discriminate. }
    inversion Hp; subst.
    apply graph_update_preserves_wf; [exact Hwf2|].
    exact Hlt.
  }
  {
    destruct (graph_add_module g_without_both union combined_axioms) as [g_added new_id] eqn:Hadd.
    inversion Hp; subst.
    pose proof (graph_add_module_preserves_wf g_without_both union combined_axioms Hwf2) as Hwf_added_fst.
    rewrite Hadd in Hwf_added_fst. simpl in Hwf_added_fst.
    exact Hwf_added_fst.
  }
Qed.

(** [vm_step_preserves_wf]: formal specification. *)
Lemma vm_step_preserves_wf : forall s instr s',
  well_formed_graph s.(vm_graph) ->
  vm_step s instr s' ->
  well_formed_graph s'.(vm_graph).
Proof.
  intros s instr s' Hwf Hstep.
  inversion Hstep; subst; simpl;
    try exact Hwf.
  - (* pnew *)
    pose proof (graph_pnew_preserves_wf s.(vm_graph) region Hwf) as Hwf_fst.
    rewrite H in Hwf_fst. simpl in Hwf_fst.
    exact Hwf_fst.
  - (* psplit *)
    eapply graph_psplit_preserves_wf; eauto.
  - (* pmerge *)
    eapply graph_pmerge_preserves_wf; eauto.
  - (* lassert_sat *)
    subst. apply graph_add_axiom_preserves_wf. exact Hwf.
  - (* pdiscover *)
    subst. apply graph_record_discovery_preserves_wf. exact Hwf.
Qed.

(** [graph_pnew_next_id_monotone]: formal specification. *)
Lemma graph_pnew_next_id_monotone : forall g region,
  pg_next_id g <= pg_next_id (fst (graph_pnew g region)).
Proof.
  intros g region.
  unfold graph_pnew.
  destruct (graph_find_region g (normalize_region region)) eqn:Hfind; simpl; lia.
Qed.

(** [graph_update_next_id_same]: formal specification. *)
Lemma graph_update_next_id_same : forall g mid m,
  pg_next_id (graph_update g mid m) = pg_next_id g.
Proof.
  intros g mid m.
  unfold graph_update. simpl. reflexivity.
Qed.

(** [graph_add_axiom_next_id_same]: formal specification. *)
Lemma graph_add_axiom_next_id_same : forall g mid ax,
  pg_next_id (graph_add_axiom g mid ax) = pg_next_id g.
Proof.
  intros g mid ax.
  unfold graph_add_axiom.
  destruct (graph_lookup g mid) eqn:Hlookup.
  - unfold graph_update. simpl. reflexivity.
  - reflexivity.
Qed.

(** [graph_add_axioms_next_id_same]: formal specification. *)
Lemma graph_add_axioms_next_id_same : forall axs g mid,
  pg_next_id (graph_add_axioms g mid axs) = pg_next_id g.
Proof.
  induction axs as [|ax rest IH]; intros g mid.
  - simpl. reflexivity.
  - simpl.
    rewrite IH.
    rewrite graph_add_axiom_next_id_same.
    reflexivity.
Qed.

(** [graph_record_discovery_next_id_same]: formal specification. *)
Lemma graph_record_discovery_next_id_same : forall g mid ev,
  pg_next_id (graph_record_discovery g mid ev) = pg_next_id g.
Proof.
  intros g mid ev.
  unfold graph_record_discovery.
  apply graph_add_axioms_next_id_same.
Qed.

(** [graph_psplit_next_id_monotone]: formal specification. *)
Lemma graph_psplit_next_id_monotone : forall g mid left right g' l_id r_id,
  graph_psplit g mid left right = Some (g', l_id, r_id) ->
  pg_next_id g <= pg_next_id g'.
Proof.
  intros g mid left right g' l_id r_id Hps.
  unfold graph_psplit in Hps.
  destruct (graph_lookup g mid) eqn:Hlookup; try discriminate.
  set (left_norm := normalize_region left) in *.
  set (right_norm := normalize_region right) in *.
  destruct (orb (Nat.eqb (length left_norm) 0) (Nat.eqb (length right_norm) 0)) eqn:Hempty.
  - destruct (graph_add_module g [] []) as [g1 empty_id] eqn:Hadd.
    inversion Hps; subst; clear Hps.
    unfold graph_add_module in Hadd.
    inversion Hadd; subst; simpl; lia.
  - destruct (partition_valid (module_region m) left_norm right_norm) eqn:Hvalid; try discriminate.
    destruct (graph_remove g mid) as [[g_removed removed]|] eqn:Hrem; try discriminate.
    destruct (graph_add_module g_removed left_norm (module_axioms m)) as [g_left left_id] eqn:HaddL.
    destruct (graph_add_module g_left right_norm (module_axioms m)) as [g_right right_id] eqn:HaddR.
    inversion Hps; subst.
    unfold graph_remove in Hrem.
    destruct (graph_remove_modules (pg_modules g) mid) eqn:Hrmmods; try discriminate.
    destruct p as [mods' rem]. inversion Hrem; subst; simpl.
    unfold graph_add_module in HaddL. inversion HaddL; subst; simpl.
    unfold graph_add_module in HaddR. inversion HaddR; subst; simpl.
    lia.
Qed.

(** [graph_remove_next_id_same]: formal specification. *)
Lemma graph_remove_next_id_same : forall g mid g' m,
  graph_remove g mid = Some (g', m) ->
  pg_next_id g' = pg_next_id g.
Proof.
  intros g mid g' m Hrem.
  unfold graph_remove in Hrem.
  destruct (graph_remove_modules (pg_modules g) mid) eqn:Hmods; try discriminate.
  destruct p as [modules' removed].
  inversion Hrem; subst; simpl.
  reflexivity.
Qed.

(** [graph_pmerge_next_id_monotone]: formal specification. *)
Lemma graph_pmerge_next_id_monotone : forall g m1 m2 g' merged_id,
  graph_pmerge g m1 m2 = Some (g', merged_id) ->
  pg_next_id g <= pg_next_id g'.
Proof.
  intros g m1 m2 g' merged_id Hp.
  unfold graph_pmerge in Hp.
  destruct (Nat.eqb m1 m2) eqn:Heq; try discriminate.
  destruct (graph_remove g m1) as [[g_without_m1 mod1]|] eqn:Hrm1; try discriminate.
  assert (pg_next_id g_without_m1 = pg_next_id g) as Hnid1.
  { eapply graph_remove_next_id_same; eauto. }
  destruct (graph_remove g_without_m1 m2) as [[g_without_both mod2]|] eqn:Hrm2; try discriminate.
  assert (pg_next_id g_without_both = pg_next_id g_without_m1) as Hnid2.
  { eapply graph_remove_next_id_same; eauto. }
  destruct (negb (nat_list_disjoint (module_region mod1) (module_region mod2))) eqn:Hdisj; try discriminate.
  set (union := nat_list_union (module_region mod1) (module_region mod2)) in *.
  set (combined_axioms := module_axioms mod1 ++ module_axioms mod2) in *.
  destruct (graph_find_region g_without_both union) eqn:Hfind.
  - destruct (graph_lookup g_without_both m) eqn:Hlookup; try discriminate.
    inversion Hp; subst.
    unfold graph_update. simpl.
    rewrite Hnid2, Hnid1.
    lia.
  - destruct (graph_add_module g_without_both union combined_axioms) as [g_added new_id] eqn:Hadd.
    inversion Hp; subst.
    unfold graph_add_module in Hadd. inversion Hadd; subst; simpl.
    rewrite Hnid2, Hnid1.
    lia.
Qed.

(** [vm_step_next_id_monotone]: formal specification. *)
Lemma vm_step_next_id_monotone : forall s instr s',
  vm_step s instr s' ->
  pg_next_id s.(vm_graph) <= pg_next_id s'.(vm_graph).
Proof.
  intros s instr s' Hstep.
  inversion Hstep; subst; simpl;
    try lia.
  - (* pnew *)
    pose proof (graph_pnew_next_id_monotone s.(vm_graph) region) as Hmono.
    rewrite H in Hmono. simpl in Hmono.
    exact Hmono.
  - (* psplit *)
    eapply graph_psplit_next_id_monotone; eauto.
  - (* pmerge *)
    eapply graph_pmerge_next_id_monotone; eauto.
  - (* lassert_sat *)
    subst. rewrite graph_add_axiom_next_id_same. lia.
  - (* pdiscover *)
    subst. rewrite graph_record_discovery_next_id_same. lia.
Qed.

(** [vm_step_preserves_mid_lt_next_id]: formal specification. *)
Lemma vm_step_preserves_mid_lt_next_id : forall s instr s' mid,
  mid < pg_next_id s.(vm_graph) ->
  vm_step s instr s' ->
  mid < pg_next_id s'.(vm_graph).
Proof.
  intros s instr s' mid Hlt Hstep.
  pose proof (vm_step_next_id_monotone s instr s' Hstep) as Hmono.
  lia.
Qed.

Inductive exec_trace : VMState -> list vm_instruction -> VMState -> Prop :=
| exec_trace_nil : forall s, exec_trace s [] s
| exec_trace_cons : forall s1 instr s2 rest s3,
    vm_step s1 instr s2 ->
    exec_trace s2 rest s3 ->
    exec_trace s1 (instr :: rest) s3.

(** [exec_trace_no_signaling_outside_cone]: formal specification. *)
Lemma exec_trace_no_signaling_outside_cone :
  forall s trace s' mid,
    exec_trace s trace s' ->
    well_formed_graph s.(vm_graph) ->
    mid < pg_next_id s.(vm_graph) ->
    ~ In mid (causal_cone trace) ->
    ObservableRegion s mid = ObservableRegion s' mid.
Proof.
  intros s trace s' mid Hexec.
  induction Hexec as [s0|s1 instr s2 rest s3 Hstep Hrest IH];
    intros Hwf Hmid Hnot.
  - reflexivity.
  - simpl in Hnot.
    assert (~ In mid (instr_targets instr)) as Hnot_instr.
    { intro Hin. apply Hnot. apply in_or_app. left. exact Hin. }
    assert (~ In mid (causal_cone rest)) as Hnot_rest.
    { intro Hin. apply Hnot. apply in_or_app. right. exact Hin. }
    pose proof (step_rel_no_signaling s1 instr s2 mid Hwf Hmid Hstep Hnot_instr) as Heq12.
    rewrite Heq12.
    apply IH.
    + eapply vm_step_preserves_wf; eauto.
    + eapply vm_step_preserves_mid_lt_next_id; eauto.
    + exact Hnot_rest.
Qed.
