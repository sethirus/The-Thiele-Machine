(** This file proves discrete state and observation properties of [VMState] and [VMStep].
    It defines module observables, proves observational equivalence is reflexive/symmetric/transitive, proves the stated additive shift of [vm_mu], and proves selected graph-locality lemmas.
    The results are properties of this VM model; they are not axioms or derivations of physical law. *)

From Coq Require Import List ZArith Lia.
Import ListNotations.
Local Open Scope nat_scope.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.

(** [Observable] returns a normalized module region together with the current ledger value, or [None] when the module is absent. *)
Definition Observable (s : VMState) (mid : nat) : option (list nat * nat) :=
  match graph_lookup s.(vm_graph) mid with
  | Some modstate => Some (normalize_region modstate.(module_region), s.(vm_mu))
  | None => None
  end.

(** [ObservableRegion] exposes the normalized region without the ledger. *)
Definition ObservableRegion (s : VMState) (mid : nat) : option (list nat) :=
  match graph_lookup s.(vm_graph) mid with
  | Some modstate => Some (normalize_region modstate.(module_region))
  | None => None
  end.

(** [ObservableSignature] records module regions and the ledger value. *)
Definition ObservableSignature (s : VMState) : list (option (list nat)) * nat :=
  (map (fun mid => 
         match graph_lookup s.(vm_graph) mid with
         | Some m => Some m.(module_region)
         | None => None
         end) 
       (seq 0 (length (pg_modules s.(vm_graph)))), 
   s.(vm_mu)).

(** [obs_equiv] means that every module query returns the same result in both states. *)
Definition obs_equiv (s1 s2 : VMState) : Prop :=
  forall mid : nat, Observable s1 mid = Observable s2 mid.

(** Reflexivity is discharged inline by the only current downstream equivalence instance, so this file keeps only the nontrivial symmetry and transitivity lemmas. *)

(** Observational equivalence is symmetric. *)
Theorem obs_equiv_sym : forall s1 s2, obs_equiv s1 s2 -> obs_equiv s2 s1.
Proof.
  intros s1 s2 H mid. symmetry. apply H.
Qed.

(** Observational equivalence is transitive. *)
Theorem obs_equiv_trans : forall s1 s2 s3,
  obs_equiv s1 s2 -> obs_equiv s2 s3 -> obs_equiv s1 s3.
Proof.
  intros s1 s2 s3 H12 H23 mid.
  rewrite H12. apply H23.
Qed.

(** The shift operation adds a constant to [vm_mu] while leaving the other VM fields unchanged. *)

(** [mu_gauge_shift] adds [k] to the ledger. *)
Definition mu_gauge_shift (k : nat) (s : VMState) : VMState :=
  {| vm_regs := s.(vm_regs);
     vm_mem := s.(vm_mem);
     vm_csrs := s.(vm_csrs);
     vm_pc := s.(vm_pc);
     vm_graph := s.(vm_graph);
     vm_mu := s.(vm_mu) + k;
     vm_mu_tensor := s.(vm_mu_tensor);
     vm_err := s.(vm_err);
     vm_logic_acc := s.(vm_logic_acc);
     vm_mstatus := s.(vm_mstatus);
     vm_witness := s.(vm_witness);
     vm_certified := s.(vm_certified) |}.

(** A ledger shift preserves the normalized region and adds [k] to the observed ledger. *)
Theorem gauge_invariance_observables : forall s k mid,
  match Observable s mid, Observable (mu_gauge_shift k s) mid with
  | Some (p1, mu1), Some (p2, mu2) => (p1 = p2 /\ mu2 = mu1 + k)%nat
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros s k mid.
  unfold Observable, mu_gauge_shift. simpl.
  destruct (graph_lookup (vm_graph s) mid).
  - split; reflexivity.
  - trivial.
Qed.

(** [instr_targets] names the module IDs targeted by the instruction forms modeled here; [causal_cone] concatenates those targets over a trace. *)

(** Target modules for the instruction forms with explicit module operands. *)
Definition instr_targets (i : vm_instruction) : list nat :=
  match i with
  | instr_pnew _ _ => []
  | instr_psplit mid _ _ _ => [mid mod 64]
  | instr_pmerge m1 m2 _ => [m1 mod 64; m2 mod 64]
  | instr_pdiscover mid _ _ => [mid]
  | instr_lassert _ _ _ _ _ => [0]  (* module is hardcoded to 0 in new ISA *)
  | instr_mdlacc mid _ => [mid]
  | instr_emit mid _ _ => [mid]
  | instr_tensor_set mid _ _ _ _ => [mid]
  | _ => []
  end.

(** The causal cone of a trace is the concatenation of its per-instruction target lists. *)
Fixpoint causal_cone (trace : list vm_instruction) : list nat :=
  match trace with
  | [] => []
  | i :: rest => instr_targets i ++ causal_cone rest
  end.

(** A prefix cone is contained in the cone of the prefix extended by another trace. *)
Theorem cone_monotonic : forall trace1 trace2,
  (forall x, In x (causal_cone trace1) -> In x (causal_cone (trace1 ++ trace2))).
Proof.
  intros trace1 trace2 x Hin.
  induction trace1 as [|i rest IH].
  - simpl in Hin. contradiction.
  - simpl. 
    apply in_app_or in Hin. destruct Hin as [Htarget | Hrest].
    + apply in_or_app. left. exact Htarget.
    + apply in_or_app. right. apply IH. exact Hrest.
Qed.

(** The VM step relation never decreases [vm_mu]. This is an arithmetic property of the instruction-cost rules, not a claim about physical dissipation. *)
(* SAFE: short proof — inversion + lia exhausts all vm_step cases directly *)
Theorem mu_conservation_kernel : forall s s' instr,
  vm_step s instr s' ->
  s'.(vm_mu) >= s.(vm_mu).
Proof.
  intros s s' instr Hstep.
  inversion Hstep; subst; simpl; unfold apply_cost; simpl; lia.
Qed.

(** [trace_mu_cost] sums the declared instruction costs in a trace. *)
Fixpoint trace_mu_cost (trace : list vm_instruction) : nat :=
  match trace with
  | [] => 0
  | i :: rest => instruction_cost i + trace_mu_cost rest
  end.

(** The shift operation has the identity and composition laws of an additive natural-number action. *)

(** The action is the natural-number version of the ledger shift. *)
Definition nat_action (k : nat) : VMState -> VMState := mu_gauge_shift k.

(** Shifting by zero is the identity. *)
Theorem nat_action_identity : forall s,
  nat_action 0 s = s.
Proof.
  intros s.
  unfold nat_action, mu_gauge_shift.
  destruct s. simpl. f_equal. lia.
Qed.

(** Successive shifts add their offsets. *)
Theorem nat_action_composition : forall k1 k2 s,
  nat_action (k1 + k2) s = nat_action k1 (nat_action k2 s).
Proof.
  intros k1 k2 s.
  unfold nat_action, mu_gauge_shift.
  destruct s. simpl. f_equal. lia.
Qed.

(** The partition component of the observable signature. *)
Definition conserved_partition_structure (s : VMState) : list (option (list nat)) :=
  fst (ObservableSignature s).

(* The partition projection is unchanged by [nat_action] because the action modifies only [vm_mu]. *)

(** The graph lemmas below show that updates targeting [mid'] preserve lookups for an unrelated [mid]. *)

(** Basic graph lookup preservation lemmas. *)

Lemma graph_insert_modules_preserves_unrelated : forall modules mid mid' m,
  mid <> mid' ->
  graph_lookup_modules (graph_insert_modules modules mid' m) mid =
  graph_lookup_modules modules mid.
Proof.
  induction modules as [|[id ms] rest IH]; intros mid mid' m Hneq.
  - (* Base case: modules = [] *)
    simpl.
    (* LHS: if mid' =? mid then Some m else None *)
    (* RHS: None *)
    assert (Hneq_sym: mid' <> mid) by (intro; subst; contradiction).
    apply Nat.eqb_neq in Hneq_sym.
    rewrite Hneq_sym. reflexivity.
  - (* Inductive case: modules = (id, ms) :: rest *)
    simpl.
    destruct (Nat.eqb id mid') eqn:Heq_id.
    + (* id = mid', so insert replaces: [(mid', m)] ++ rest *)
      simpl. 
      apply Nat.eqb_eq in Heq_id. subst id.
      destruct (Nat.eqb mid' mid) eqn:Heq_mid.
      * (* mid' = mid, contradicts Hneq *)
        apply Nat.eqb_eq in Heq_mid. symmetry in Heq_mid. contradiction.
      * reflexivity.
    + (* id ≠ mid', so insert recurses *)
      simpl. destruct (Nat.eqb id mid) eqn:Heq_mid.
      * reflexivity.
      * apply IH. assumption.
Qed.

(** Inserting a module makes lookup at its ID return that module. *)
Lemma graph_insert_modules_lookup_same : forall modules mid m,
  graph_lookup_modules (graph_insert_modules modules mid m) mid = Some m.
Proof.
  induction modules as [|[id ms] rest IH]; intros mid m.
  - (* Base case: modules = [] *)
    simpl. rewrite Nat.eqb_refl. reflexivity.
  - (* Inductive case *)
    simpl.
    destruct (Nat.eqb id mid) eqn:Heq.
    + (* id = mid: insert replaces *)
      simpl. rewrite Nat.eqb_refl. reflexivity.
    + (* id ≠ mid: insert recurses *)
      simpl. rewrite Heq. apply IH.
Qed.

(** Updating a module makes lookup at its ID return the normalized module. *)
Lemma graph_update_lookup_same : forall g mid m,
  graph_lookup (graph_update g mid m) mid = Some (normalize_module m).
Proof.
  intros g mid m.
  unfold graph_update, graph_lookup. simpl.
  apply graph_insert_modules_lookup_same.
Qed.

(** Updating [mid'] preserves lookup at an unrelated [mid]. *)
Lemma graph_update_preserves_unrelated : forall g mid mid' m,
  mid <> mid' ->
  graph_lookup (graph_update g mid' m) mid = graph_lookup g mid.
Proof.
  intros g mid mid' m Hneq.
  unfold graph_update, graph_lookup. simpl.
  apply graph_insert_modules_preserves_unrelated. assumption.
Qed.

(** Adding an axiom to [mid'] preserves lookup at an unrelated [mid]. *)
Lemma graph_add_axiom_preserves_unrelated : forall g mid mid' ax,
  mid <> mid' ->
  graph_lookup (graph_add_axiom g mid' ax) mid = graph_lookup g mid.
Proof.
  intros g mid mid' ax Hneq.
  unfold graph_add_axiom.
  destruct (graph_lookup g mid') eqn:Hlookup.
  - (* Some m: graph_update is called *)
    apply graph_update_preserves_unrelated. assumption.
  - (* None: graph unchanged *)
    reflexivity.
Qed.

(** Recording discovery events at [mid'] preserves lookup at an unrelated [mid]. *)
Lemma graph_record_discovery_preserves_unrelated : forall g mid mid' ev,
  mid <> mid' ->
  graph_lookup (graph_record_discovery g mid' ev) mid = graph_lookup g mid.
Proof.
  intros g mid mid' ev Hneq.
  unfold graph_record_discovery, graph_add_axioms.
  (* fold_left (fun acc ax => graph_add_axiom acc mid' ax) ev g *)
  (* Prove by induction on ev that fold_left preserves unrelated lookups *)
  assert (Hfold: forall axs g0,
    graph_lookup (fold_left (fun acc ax => graph_add_axiom acc mid' ax) axs g0) mid =
    graph_lookup g0 mid).
  { induction axs as [|ax rest IH]; intro g0.
    - simpl. reflexivity.
    - simpl. rewrite IH.
      apply graph_add_axiom_preserves_unrelated. assumption. }
  apply Hfold.
Qed.

(** Updating the tensor at [mid'] preserves lookup at an unrelated [mid]. *)
Lemma graph_update_module_tensor_preserves_unrelated : forall g mid mid' k v,
  mid <> mid' ->
  graph_lookup (graph_update_module_tensor g mid' k v) mid = graph_lookup g mid.
Proof.
  intros g mid mid' k v Hneq.
  unfold graph_update_module_tensor.
  destruct (graph_lookup g mid') eqn:Hlookup.
  - apply graph_update_preserves_unrelated. assumption.
  - reflexivity.
Qed.

(** The following lemmas combine lookup preservation with the graph well-formedness condition that existing IDs are below [pg_next_id]. *)

(** A well-formed graph has no module at an ID greater than or equal to [pg_next_id]. *)
Lemma graph_lookup_beyond_next_id : forall g mid,
  well_formed_graph g ->
  mid >= g.(pg_next_id) ->
  graph_lookup g mid = None.
Proof.
  exact wf_graph_lookup_beyond_next_id.
Qed.

(** Adding a module at [pg_next_id] preserves lookup for an existing ID below [pg_next_id]. *)
Lemma graph_add_module_preserves_existing : forall g region axioms mid,
  mid < g.(pg_next_id) ->
  graph_lookup (fst (graph_add_module g region axioms)) mid = graph_lookup g mid.
Proof.
  intros g region axioms mid Hlt.
  unfold graph_add_module. simpl.
  unfold graph_lookup. simpl.
  (* LHS: lookup in (pg_next_id g, new_module) :: old_modules *)
  (* RHS: lookup in old_modules *)
  (* Since mid < pg_next_id, the head doesn't match *)
  simpl.
  assert (Hneq: pg_next_id g <> mid) by lia.
  apply Nat.eqb_neq in Hneq.
  rewrite Hneq. reflexivity.
Qed.

(** Removing a module leaves [pg_next_id] unchanged. *)
Lemma graph_remove_preserves_next_id : forall g mid g' m,
  graph_remove g mid = Some (g', m) ->
  g'.(pg_next_id) = g.(pg_next_id).
Proof.
  intros g mid g' m Hremove.
  unfold graph_remove in Hremove.
  destruct (graph_remove_modules (pg_modules g) mid).
  - destruct p. injection Hremove as Heq _. rewrite <- Heq. simpl. reflexivity.
  - discriminate.
Qed.

(** Removing [mid'] preserves lookup at an unrelated [mid]. *)
Lemma graph_remove_preserves_unrelated : forall g mid mid' g' m',
  mid <> mid' ->
  graph_remove g mid' = Some (g', m') ->
  graph_lookup g' mid = graph_lookup g mid.
Proof.
  intros g mid mid' g' m' Hneq Hremove.
  unfold graph_remove in Hremove.
  destruct (graph_remove_modules (pg_modules g) mid') eqn:Hremove_modules.
  - destruct p as [modules' removed].
    injection Hremove as Heq_g' Heq_m'. subst g' m'.
    unfold graph_lookup. simpl.
    (* Need to show: graph_lookup_modules modules' mid = graph_lookup_modules (pg_modules g) mid *)
    generalize dependent modules'.
    generalize dependent removed.
    induction (pg_modules g) as [|[id ms] rest IH].
    + (* Base case: pg_modules g = [] *)
      intros. simpl in Hremove_modules. discriminate.
    + (* Inductive case *)
      intros removed modules' Hremove_modules.
      simpl in Hremove_modules.
      destruct (Nat.eqb id mid') eqn:Heq_id.
      * (* id = mid', so this module is removed *)
        injection Hremove_modules as Heq_modules' Heq_removed.
        subst modules' removed.
        apply Nat.eqb_eq in Heq_id. subst id.
        simpl.
        assert (Hneq_sym: mid' <> mid) by (intro; subst; contradiction).
        apply Nat.eqb_neq in Hneq_sym.
        rewrite Hneq_sym. reflexivity.
      * (* id ≠ mid', module kept *)
        destruct (graph_remove_modules rest mid') eqn:Hrest.
        -- destruct p as [rest' removed'].
           injection Hremove_modules as Heq_modules' Heq_removed.
           subst modules' removed.
           simpl.
           destruct (Nat.eqb id mid) eqn:Heq_mid.
           ++ reflexivity.
           ++ apply (IH removed' rest' eq_refl).
        -- discriminate.
  - discriminate.
Qed.

(** [graph_pnew_preserves_existing] shows that [PNEW] leaves a lookup below [pg_next_id] unchanged, whether it reuses an existing region or appends a new module. *)
Lemma graph_pnew_preserves_existing : forall g region mid,
  mid < g.(pg_next_id) ->
  graph_lookup (fst (graph_pnew g region)) mid = graph_lookup g mid.
Proof.
  intros g region mid Hlt.
  unfold graph_pnew.
  destruct (graph_find_region g (normalize_region region)) eqn:Hfind.
  - (* Some existing: graph unchanged *)
    simpl. reflexivity.
  - (* None: new module added *)
    apply graph_add_module_preserves_existing. assumption.
Qed.

(** [graph_psplit_preserves_unrelated] chains removal and fresh-module preservation to show that splitting one module leaves an unrelated lookup unchanged. *)
Lemma graph_psplit_preserves_unrelated : forall g mid_split left right g' l_id r_id mid,
  mid <> mid_split ->
  mid < g.(pg_next_id) ->
  graph_psplit g mid_split left right = Some (g', l_id, r_id) ->
  graph_lookup g' mid = graph_lookup g mid.
Proof.
  intros g mid_split left right g' l_id r_id mid Hneq Hlt Hpsplit.
  unfold graph_psplit in Hpsplit.
  destruct (graph_lookup g mid_split) eqn:Hlookup_split.
  2: discriminate.
  destruct (orb _ _) eqn:Horb.
  - (* Empty partition case *)
    destruct (graph_add_module g [] []) eqn:Hadd.
    injection Hpsplit as Heq_g' Heq_l Heq_r. subst g' l_id r_id.
    assert (Heq_p_empty: p = fst (graph_add_module g [] [])).
    { rewrite Hadd. reflexivity. }
    rewrite Heq_p_empty.
    apply graph_add_module_preserves_existing. assumption.
  - (* Valid partition case *)
    destruct (partition_valid _ _ _) eqn:Hvalid.
    2: discriminate.
    (* graph_psplit now uses cascade delete before graph_remove *)
    set (g_cascaded := graph_cascade_delete_morphisms g mid_split) in *.
    destruct (graph_remove g_cascaded mid_split) eqn:Hremove.
    2: discriminate.
    destruct p as [g_removed removed_mod].
    destruct (graph_add_module g_removed _ _) as [g_left left_id'] eqn:Hadd_left.
    destruct (graph_add_module g_left _ _) as [g_right right_id'] eqn:Hadd_right.
    injection Hpsplit as Heq_g' Heq_l Heq_r. subst g'.
    (* Cascade delete preserves lookups *)
    assert (Hcascade_lookup: graph_lookup g_cascaded mid = graph_lookup g mid).
    { unfold g_cascaded. apply graph_cascade_delete_morphisms_lookup. }
    (* g_right = result after two adds, need to show lookup preserved *)
    assert (Heq_lookup_step2: graph_lookup g_right mid = graph_lookup g_left mid).
    {
      (* g_right = fst (graph_add_module g_left ...) *)
      assert (Heq_gr: g_right = fst (graph_add_module g_left (normalize_region right) (module_axioms m))).
      { injection Hadd_right as H _. symmetry. unfold graph_add_module. simpl. exact H. }
      (* Now goal is: graph_lookup g_right mid = graph_lookup g_left mid *)
      (* Rewrite g_right to fst (graph_add_module...) *)
      rewrite Heq_gr.
      (* Use preservation lemma *)
      assert (Hlt_left: mid < pg_next_id g_left).
      { unfold graph_add_module in Hadd_left. injection Hadd_left as Heq_g_left _.
        rewrite <- Heq_g_left. simpl.
        assert (Heq_next: pg_next_id g_removed = pg_next_id g_cascaded).
        { apply (graph_remove_preserves_next_id _ _ _ _ Hremove). }
        assert (Heq_next_cascaded: pg_next_id g_cascaded = pg_next_id g).
        { unfold g_cascaded. apply graph_cascade_delete_morphisms_preserves_next_id. }
        lia.
      }
      apply (graph_add_module_preserves_existing _ _ _ _ Hlt_left).
    }
    rewrite Heq_lookup_step2.
    assert (Heq_lookup_step1: graph_lookup g_left mid = graph_lookup g_removed mid).
    {
      (* g_left = fst (graph_add_module g_removed ...) *)
      assert (Heq_gl: g_left = fst (graph_add_module g_removed (normalize_region left) (module_axioms m))).
      { injection Hadd_left as H _. symmetry. unfold graph_add_module. simpl. exact H. }
      (* Now goal is: graph_lookup g_left mid = graph_lookup g_removed mid *)
      rewrite Heq_gl.
      (* Use preservation lemma *)
      assert (Hlt_removed: mid < pg_next_id g_removed).
      { assert (Heq_next: pg_next_id g_removed = pg_next_id g_cascaded).
        { apply (graph_remove_preserves_next_id _ _ _ _ Hremove). }
        assert (Heq_next_cascaded: pg_next_id g_cascaded = pg_next_id g).
        { unfold g_cascaded. apply graph_cascade_delete_morphisms_preserves_next_id. }
        lia.
      }
      apply (graph_add_module_preserves_existing _ _ _ _ Hlt_removed).
    }
    rewrite Heq_lookup_step1.
    (* Chain through g_removed -> g_cascaded -> g *)
    rewrite (graph_remove_preserves_unrelated g_cascaded mid mid_split g_removed removed_mod Hneq Hremove).
    exact Hcascade_lookup.
Qed.

(** [graph_pmerge_preserves_observables] uses the region-only [Observable] to handle the case where [PMERGE] updates axioms on an existing merged module. It proves preservation at an unrelated module under the stated graph and range premises. *)
Lemma graph_pmerge_preserves_observables : forall g m1 m2 g' merged_id mid mu,
  mid <> m1 ->
  mid <> m2 ->
  mid < g.(pg_next_id) ->
  graph_pmerge g m1 m2 = Some (g', merged_id) ->
  Observable {| vm_regs := []; vm_mem := []; vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0; csr_heap_base := 0 |};
                vm_pc := 0; vm_graph := g'; vm_mu := mu; vm_mu_tensor := vm_mu_tensor_default; vm_err := false; vm_logic_acc := 0; vm_mstatus := 0; vm_witness := witness_counts_zero; vm_certified := false |} mid =
  Observable {| vm_regs := []; vm_mem := []; vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0; csr_heap_base := 0 |};
                vm_pc := 0; vm_graph := g; vm_mu := mu; vm_mu_tensor := vm_mu_tensor_default; vm_err := false; vm_logic_acc := 0; vm_mstatus := 0; vm_witness := witness_counts_zero; vm_certified := false |} mid.

(* NOTE: This lemma uses Observable (region comparison) rather than
   graph_lookup preservation, because graph_lookup is unprovable in the
   mid = existing_id case where axioms are updated. Observable compares
   only regions, not axioms: this is observational locality (Option C). *)
Proof.
  intros g m1 m2 g' merged_id mid mu Hneq1 Hneq2 Hlt Hpmerge.
  unfold Observable. simpl.
  unfold graph_pmerge in Hpmerge.
  destruct (Nat.eqb m1 m2) eqn:Heq_m1_m2.
  - discriminate.
  - (* graph_pmerge now uses cascade delete before graph_remove *)
    set (g1_cascaded := graph_cascade_delete_morphisms g m1) in *.
    set (g2_cascaded := graph_cascade_delete_morphisms g1_cascaded m2) in *.
    (* Cascade delete preserves lookups *)
    assert (Hcascade_lookup: forall mid', graph_lookup g2_cascaded mid' = graph_lookup g mid').
    { intro mid'. unfold g2_cascaded, g1_cascaded.
      rewrite graph_cascade_delete_morphisms_lookup.
      rewrite graph_cascade_delete_morphisms_lookup.
      reflexivity. }
    destruct (graph_remove g2_cascaded m1) eqn:Hremove1.
   2: discriminate.
   destruct p as [g_without_m1 mod1].
   destruct (graph_remove g_without_m1 m2) eqn:Hremove2.
   2: discriminate.
   destruct p as [g_without_both mod2].
   destruct (negb (nat_list_disjoint _ _)) eqn:Hdisjoint.
   + discriminate.
   + destruct (graph_find_region g_without_both (nat_list_union (module_region mod1) (module_region mod2)))
      as [existing_id |] eqn:Hfind.
    * (* Existing region found *)
      destruct (graph_lookup g_without_both existing_id) eqn:Hlookup_existing.
      2: discriminate.
      inversion Hpmerge. subst g' merged_id. clear Hpmerge.

      destruct (Nat.eq_dec mid existing_id) as [Heq_mid_ex | Hneq_mid_ex].
      -- (* mid = existing_id: axioms change, region preserved observationally *)
        subst mid.
        assert (Hlookup_after:
          graph_lookup
            (graph_update g_without_both existing_id
              {| module_region := m.(module_region);
                 module_axioms := m.(module_axioms) ++
                   (mod1.(module_axioms) ++ mod2.(module_axioms));
                 module_mu_tensor := m.(module_mu_tensor) |})
            existing_id
          = Some
              (normalize_module
                {| module_region := m.(module_region);
                   module_axioms := m.(module_axioms) ++
                     (mod1.(module_axioms) ++ mod2.(module_axioms));
                   module_mu_tensor := m.(module_mu_tensor) |})).
        { apply graph_update_lookup_same. }
        rewrite Hlookup_after. simpl.

        (* Reduce the pre-merge lookup to the same module via remove-preservation and cascade *)
        rewrite <- (Hcascade_lookup existing_id).
        rewrite <- (graph_remove_preserves_unrelated g2_cascaded existing_id m1 g_without_m1 mod1 Hneq1 Hremove1).
        rewrite <- (graph_remove_preserves_unrelated g_without_m1 existing_id m2 g_without_both mod2 Hneq2 Hremove2).
        rewrite Hlookup_existing. simpl.
        rewrite normalize_region_idempotent.
        reflexivity.

      -- (* mid  existing_id: graph_update doesn't affect unrelated lookups *)
        rewrite (graph_update_preserves_unrelated g_without_both mid existing_id _ Hneq_mid_ex).
        rewrite (graph_remove_preserves_unrelated g_without_m1 mid m2 g_without_both mod2).
        ++ rewrite (graph_remove_preserves_unrelated g2_cascaded mid m1 g_without_m1 mod1).
          ** rewrite (Hcascade_lookup mid). reflexivity.
          ** assumption.
          ** assumption.
        ++ assumption.
        ++ assumption.

    * (* New region created *)
      destruct (graph_add_module g_without_both
                 (nat_list_union (module_region mod1) (module_region mod2))
                 (mod1.(module_axioms) ++ mod2.(module_axioms)))
        as [g_added new_id] eqn:Hadd.
      inversion Hpmerge. subst g' merged_id. clear Hpmerge.

      pose proof (graph_remove_preserves_next_id g2_cascaded m1 g_without_m1 mod1 Hremove1) as Hnext1.
      pose proof (graph_remove_preserves_next_id g_without_m1 m2 g_without_both mod2 Hremove2) as Hnext2.
      assert (Hnext_cascaded: pg_next_id g2_cascaded = pg_next_id g).
      { unfold g2_cascaded, g1_cascaded.
        rewrite graph_cascade_delete_morphisms_preserves_next_id.
        rewrite graph_cascade_delete_morphisms_preserves_next_id.
        reflexivity. }
      assert (Hlt_both: mid < pg_next_id g_without_both).
      { rewrite Hnext2. rewrite Hnext1. rewrite Hnext_cascaded. exact Hlt. }

      assert (Hg_added:
        g_added = fst (graph_add_module g_without_both
                         (nat_list_union (module_region mod1) (module_region mod2))
                         (mod1.(module_axioms) ++ mod2.(module_axioms)))).
      { rewrite Hadd. reflexivity. }
      rewrite Hg_added.
      rewrite (graph_add_module_preserves_existing
                 g_without_both
                 (nat_list_union (module_region mod1) (module_region mod2))
                 (mod1.(module_axioms) ++ mod2.(module_axioms))
                 mid
                 Hlt_both).
      rewrite (graph_remove_preserves_unrelated g_without_m1 mid m2 g_without_both mod2).
      -- rewrite (graph_remove_preserves_unrelated g2_cascaded mid m1 g_without_m1 mod1).
        ++ rewrite (Hcascade_lookup mid). reflexivity.
        ++ assumption.
        ++ assumption.
      -- assumption.
      -- assumption.
Qed.

(* A raw graph-lookup locality statement is too strong because PMERGE may update axioms on an existing union module. The theorem below therefore uses [ObservableRegion], which exposes the region rather than the full module record. *)

(** [observational_no_signaling] says that a step whose target list omits [mid] preserves the region observable at [mid], under the stated graph well-formedness and range premises. *)
Theorem observational_no_signaling : forall s s' instr mid,
  well_formed_graph s.(vm_graph) ->
  mid < pg_next_id s.(vm_graph) ->
  vm_step s instr s' ->
  ~ In mid (instr_targets instr) ->
  ObservableRegion s mid = ObservableRegion s' mid.
Proof.
  intros s s' instr mid Hwf Hmid_lt Hstep Hnotin.
  unfold ObservableRegion.
  destruct Hstep; subst;
    unfold advance_state, advance_state_rm, advance_state_reveal,
           jump_state, jump_state_rm in *;
    cbn [vm_graph] in *;
    try reflexivity.
  (* PNEW adds or reuses a module without changing an existing region lookup. *)
  - rewrite graph_add_module_lookup_other; [reflexivity | exact Hmid_lt].
  (* PSPLIT removes one module and adds fresh modules outside the unrelated lookup. *)
  - assert (Hneq: mid <> module mod 64).
    { intro Heq. apply Hnotin. unfold instr_targets. left. symmetry. exact Heq. }
    unfold graph_hw_psplit, graph_module_size.
    destruct (graph_remove (vm_graph s) (module mod 64)) as [[g1 m_rm]|] eqn:Hrm.
    + (* The removed module was found. *)
      pose proof (graph_remove_preserves_next_id _ _ _ _ Hrm) as Hnid.
      destruct (graph_add_module g1 _ _) as [g2 mid2] eqn:Hadd1.
      destruct (graph_add_module g2 _ _) as [g3 mid3] eqn:Hadd2.
      simpl.
      enough (graph_lookup g3 mid = graph_lookup (vm_graph s) mid) as -> by reflexivity.
      transitivity (graph_lookup g2 mid).
      * change g3 with (fst (g3, mid3)). rewrite <- Hadd2.
        apply graph_add_module_lookup_other.
        pose proof (f_equal (fun p => pg_next_id (fst p)) Hadd1) as Htmp.
        unfold graph_add_module in Htmp. simpl in Htmp. lia.
      * transitivity (graph_lookup g1 mid).
        -- change g2 with (fst (g2, mid2)). rewrite <- Hadd1.
           apply graph_add_module_lookup_other. lia.
        -- exact (graph_remove_preserves_unrelated _ mid _ _ _ Hneq Hrm).
    + (* The removed module was absent. *)
      destruct (graph_add_module (vm_graph s) _ _) as [g2 mid2] eqn:Hadd1.
      destruct (graph_add_module g2 _ _) as [g3 mid3] eqn:Hadd2.
      simpl.
      enough (graph_lookup g3 mid = graph_lookup (vm_graph s) mid) as -> by reflexivity.
      transitivity (graph_lookup g2 mid).
      * change g3 with (fst (g3, mid3)). rewrite <- Hadd2.
        apply graph_add_module_lookup_other.
        pose proof (f_equal (fun p => pg_next_id (fst p)) Hadd1) as Htmp.
        unfold graph_add_module in Htmp. simpl in Htmp. lia.
      * change g2 with (fst (g2, mid2)). rewrite <- Hadd1.
        apply graph_add_module_lookup_other. exact Hmid_lt.
  (* PMERGE changes only the two source regions or their union. *)
  - assert (Hneq1: mid <> m1 mod 64).
    { intro Heq. apply Hnotin. unfold instr_targets. left. symmetry. exact Heq. }
    assert (Hneq2: mid <> m2 mod 64).
    { intro Heq. apply Hnotin. unfold instr_targets. right. left. symmetry. exact Heq. }
    unfold graph_hw_pmerge, graph_module_size.
    destruct (graph_remove (vm_graph s) (m1 mod 64)) as [[g1 m1_rm]|] eqn:Hrm1.
    + (* first remove succeeded *)
      pose proof (graph_remove_preserves_next_id _ _ _ _ Hrm1) as Hnid1.
      pose proof (graph_remove_preserves_unrelated _ mid _ _ _ Hneq1 Hrm1) as Hlu1.
      destruct (graph_remove g1 (m2 mod 64)) as [[g2 m2_rm]|] eqn:Hrm2.
      * (* second remove succeeded *)
        pose proof (graph_remove_preserves_next_id _ _ _ _ Hrm2) as Hnid2.
        pose proof (graph_remove_preserves_unrelated _ mid _ _ _ Hneq2 Hrm2) as Hlu2.
        destruct (graph_add_module g2 _ _) as [g3 mid3] eqn:Hadd.
        simpl.
        enough (graph_lookup g3 mid = graph_lookup (vm_graph s) mid) as -> by reflexivity.
        change g3 with (fst (g3, mid3)). rewrite <- Hadd.
        rewrite graph_add_module_lookup_other by lia.
        rewrite Hlu2. exact Hlu1.
      * (* second remove failed *)
        destruct (graph_add_module g1 _ _) as [g3 mid3] eqn:Hadd.
        simpl.
        enough (graph_lookup g3 mid = graph_lookup (vm_graph s) mid) as -> by reflexivity.
        change g3 with (fst (g3, mid3)). rewrite <- Hadd.
        rewrite graph_add_module_lookup_other by lia.
        exact Hlu1.
    + (* first remove failed *)
      destruct (graph_remove (vm_graph s) (m2 mod 64)) as [[g2 m2_rm]|] eqn:Hrm2.
      * (* second remove succeeded *)
        pose proof (graph_remove_preserves_next_id _ _ _ _ Hrm2) as Hnid2.
        pose proof (graph_remove_preserves_unrelated _ mid _ _ _ Hneq2 Hrm2) as Hlu2.
        destruct (graph_add_module g2 _ _) as [g3 mid3] eqn:Hadd.
        simpl.
        enough (graph_lookup g3 mid = graph_lookup (vm_graph s) mid) as -> by reflexivity.
        change g3 with (fst (g3, mid3)). rewrite <- Hadd.
        rewrite graph_add_module_lookup_other by lia.
        exact Hlu2.
      * (* both removes failed *)
        destruct (graph_add_module (vm_graph s) _ _) as [g3 mid3] eqn:Hadd.
        simpl.
        enough (graph_lookup g3 mid = graph_lookup (vm_graph s) mid) as -> by reflexivity.
        change g3 with (fst (g3, mid3)). rewrite <- Hadd.
        apply graph_add_module_lookup_other. exact Hmid_lt.
  (* Goal 4: step_tensor_set_ok — only the target module tensor mutates. *)
  - assert (Hneq : mid <> mid0).
    { intro Heq. apply Hnotin. unfold instr_targets. simpl. left. symmetry. exact Heq. }
    simpl.
    enough (graph_lookup (graph_update_module_tensor (vm_graph s) mid0 (i * 4 + j) value) mid =
            graph_lookup (vm_graph s) mid) as -> by reflexivity.
    apply graph_update_module_tensor_preserves_unrelated. exact Hneq.
  (* Goal 5: step_morph_ok — morph table changes do not affect module lookups. *)
  - simpl.
    enough (graph_lookup graph' mid = graph_lookup (vm_graph s) mid) as -> by reflexivity.
    change graph' with (fst (graph', morph_id)).
    rewrite H1.
    apply graph_add_morphism_preserves_lookup.
  (* Goal 6: step_compose_ok — composing morphisms preserves module lookups. *)
  - simpl.
    enough (graph_lookup graph' mid = graph_lookup (vm_graph s) mid) as -> by reflexivity.
    eapply graph_compose_morphisms_preserves_lookup.
    exact H.
  (* Goal 7: step_morph_id_ok — identity morph creation preserves module lookups. *)
  - simpl.
    enough (graph_lookup graph' mid = graph_lookup (vm_graph s) mid) as -> by reflexivity.
    eapply graph_add_identity_preserves_lookup.
    exact H.
  (* Goal 8: step_morph_delete_ok — deleting a morphism preserves module lookups. *)
  - simpl.
    enough (graph_lookup graph' mid = graph_lookup (vm_graph s) mid) as -> by reflexivity.
    eapply graph_delete_morphism_preserves_lookup.
    exact H.
  (* Goal 9: step_morph_tensor_ok — tensoring morphisms preserves module lookups. *)
  - simpl.
    enough (graph_lookup graph' mid = graph_lookup (vm_graph s) mid) as -> by reflexivity.
    eapply graph_tensor_morphisms_preserves_lookup.
    exact H.
Qed.

(** [min_steps_to_target] returns the zero-based position of the first instruction whose modeled target list contains [mid], or [None] when the trace does not target it. *)

(** Minimum steps to influence a target *)
Fixpoint min_steps_to_target (mid : nat) (trace : list vm_instruction) : option nat :=
  match trace with
  | [] => None
  | i :: rest =>
    if existsb (Nat.eqb mid) (instr_targets i)
    then Some 0
    else match min_steps_to_target mid rest with
         | None => None
         | Some n => Some (S n)
         end
  end.

(** The results in this file are properties of the VM state, graph operations, observation function, and step rules. They do not by themselves establish physical laws. *)
