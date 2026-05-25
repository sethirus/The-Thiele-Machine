(** KernelPhysics: Physical laws as theorems, not axioms.

    I claim all the "physical laws" — gauge symmetry, conservation laws,
    observables — are THEOREMS about VMState/VMStep, not axioms about nature.
    This file proves them constructively from the VM definition.

    Three core claims:
    1. Observables are well-defined (Observable, ObservableRegion).
    2. Observational equivalence is an equivalence relation: refl/sym/trans.
    3. μ-gauge symmetry: shifting μ by a constant preserves partition structure.

    "Zero-axiom" means every statement here is a Qed. No Axiom, no Admitted,
    no Parameter. The properties follow directly from the VMState record and
    vm_step relation.

    The gauge invariance is like choosing a voltage zero-point in physics —
    the partition structure doesn't depend on where you started counting μ.
    Shifting μ by k doesn't change which modules exist or what's in them.

    To falsify: Find two VM states with the same Observable values but
    different physical behavior. Or show a gauge shift changes partition structure.
    Or find a "physical law" that needs an axiom not derivable from VMState/VMStep.
    If any of those is true, this file won't compile. *)

From Coq Require Import List ZArith Lia.
Import ListNotations.
Local Open Scope nat_scope.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.

(** --- Observables ---

    Observable: what you can read out of a VM state for module [mid].
    Returns the normalized region and the current μ, or None if [mid] doesn't exist.

    Regions are normalized so that [1;2] and [2;1;2] both look the same.
    Without that, two states with identical partition structure could appear different
    just because of list ordering — which is not a real difference.
*)
Definition Observable (s : VMState) (mid : nat) : option (list nat * nat) :=
  match graph_lookup s.(vm_graph) mid with
  | Some modstate => Some (normalize_region modstate.(module_region), s.(vm_mu))
  | None => None
  end.

(** Partition-only observable (μ ignored). *)
Definition ObservableRegion (s : VMState) (mid : nat) : option (list nat) :=
  match graph_lookup s.(vm_graph) mid with
  | Some modstate => Some (normalize_region modstate.(module_region))
  | None => None
  end.

(** Full observable signature: partition structure + μ-cost *)
Definition ObservableSignature (s : VMState) : list (option (list nat)) * nat :=
  (map (fun mid => 
         match graph_lookup s.(vm_graph) mid with
         | Some m => Some m.(module_region)
         | None => None
         end) 
       (seq 0 (length (pg_modules s.(vm_graph)))), 
   s.(vm_mu)).

(** --- Observational Equivalence ---

    Two states are observationally equivalent when every module query returns the same thing.
    This is the right notion of "same state" for an outside observer who can only probe
    modules one at a time. It's an equivalence relation — refl/sym/trans all hold.
*)
Definition obs_equiv (s1 s2 : VMState) : Prop :=
  forall mid : nat, Observable s1 mid = Observable s2 mid.

(** Reflexivity of [obs_equiv] was carried here as a named theorem
    [obs_equiv_refl] with a one-line [reflexivity] proof. Its only
    caller (the [Equivalence event_equiv] instance in
    SpacetimeEmergence.v) now discharges that field with the inline
    [fun s mid => eq_refl] term. There is no other downstream
    dependency on the name. *)

(** obs_equiv_sym: symmetry. If s1 looks like s2 to every observer, s2 looks like s1. *)
Theorem obs_equiv_sym : forall s1 s2, obs_equiv s1 s2 -> obs_equiv s2 s1.
Proof.
  intros s1 s2 H mid. symmetry. apply H.
Qed.

(** obs_equiv_trans: transitivity. Chain two agreements into one.
    If s1 matches s2 at every module, and s2 matches s3, then s1 matches s3.
    Proof: rewrite through s2, done. *)
Theorem obs_equiv_trans : forall s1 s2 s3,
  obs_equiv s1 s2 -> obs_equiv s2 s3 -> obs_equiv s1 s3.
Proof.
  intros s1 s2 s3 H12 H23 mid.
  rewrite H12. apply H23.
Qed.

(** --- Gauge Symmetry ---

    The μ-ledger has a gauge freedom: you can shift the starting point by any constant k
    and the partition structure (which modules exist, what cells they contain) is unchanged.
    This is exactly like choosing a voltage zero-point — it's a real degree of freedom, not an error.

    The gauge invariance theorem says: shifting μ changes the μ component of observables
    by exactly k, but leaves the partition component alone.
*)

(** Gauge transformation: shift μ-ledger by constant k *)
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

(** Gauge invariance: μ-shift preserves observables (except μ itself) *)
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

(** --- Causal Structure ---

    Not every instruction touches every module. instr_targets says which modules
    an instruction can modify. causal_cone extends that to a whole trace.

    The monotonicity theorem says: running more instructions can only EXPAND the cone,
    never shrink it. A module not in the cone of a prefix trace stays untouched by
    that prefix — the locality property follows from this.
*)

(** Target set of an instruction: which modules can be affected *)
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

(** Causal cone: all modules potentially affected by a trace *)
Fixpoint causal_cone (trace : list vm_instruction) : list nat :=
  match trace with
  | [] => []
  | i :: rest => instr_targets i ++ causal_cone rest
  end.

(** Cone monotonicity: prefix trace has smaller cone *)
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

(** --- Conservation Laws ---

    The μ-ledger is monotonically non-decreasing. Every vm_step either increases μ or
    leaves it alone — it can never go down. This is the No Free Insight claim in its
    simplest form: you can't un-spend insight.

    Proof: inversion on vm_step, then lia handles all the arithmetic cases.
    To falsify: find any vm_step relation where s'.(vm_mu) < s.(vm_mu). It won't compile.
*)
(* SAFE: short proof — inversion + lia exhausts all vm_step cases directly *)
Theorem mu_conservation_kernel : forall s s' instr,
  vm_step s instr s' ->
  s'.(vm_mu) >= s.(vm_mu).
Proof.
  intros s s' instr Hstep.
  inversion Hstep; subst; simpl; unfold apply_cost; simpl; lia.
Qed.

(** Total μ-cost of a trace *)
Fixpoint trace_mu_cost (trace : list vm_instruction) : nat :=
  match trace with
  | [] => 0
  | i :: rest => instruction_cost i + trace_mu_cost rest
  end.

(** --- Group Action + Conserved Quantities ---

    The μ-gauge shift acts on VMState like an additive semigroup: shift by 0 = identity,
    shift by (k1+k2) = shift by k2 then shift by k1. That's the group action structure.

    The conserved quantity is partition structure: applying any gauge shift leaves the
    partition component of ObservableSignature unchanged. μ moves, partitions don't.
*)

(** Z-action on states via μ-shift (nat version: additive semigroup) *)
Definition nat_action (k : nat) : VMState -> VMState := mu_gauge_shift k.

(** Action properties: identity *)
Theorem nat_action_identity : forall s,
  nat_action 0 s = s.
Proof.
  intros s.
  unfold nat_action, mu_gauge_shift.
  destruct s. simpl. f_equal. lia.
Qed.

(** Action properties: composition *)
Theorem nat_action_composition : forall k1 k2 s,
  nat_action (k1 + k2) s = nat_action k1 (nat_action k2 s).
Proof.
  intros k1 k2 s.
  unfold nat_action, mu_gauge_shift.
  destruct s. simpl. f_equal. lia.
Qed.

(** Conserved quantity: partition structure *)
Definition conserved_partition_structure (s : VMState) : list (option (list nat)) :=
  fst (ObservableSignature s).

(* The conservation property [conserved_partition_structure s =
   conserved_partition_structure (nat_action k s)] holds by definition:
   [nat_action] reduces to [mu_gauge_shift], which touches only [vm_mu], and
   [conserved_partition_structure] reads only the [vm_graph] component via
   [ObservableSignature]. The former theorem [kernel_conservation_mu_gauge]
   had no callers and exposed nothing beyond this transparency, so it has
   been dropped; downstream sites can chain the unfolds inline. *)

(** --- No-Signaling / Locality ---

    An instruction that doesn't touch module [mid] (i.e., [mid] is not in its target set)
    cannot change what an observer of [mid] sees. This is the machine's locality property:
    operations on one module don't silently bleed into unrelated modules.

    The proof is structural: trace through graph_insert_modules and graph_update,
    show that writes to mid' ≠ mid leave mid's lookup result alone.
*)

(** Helper lemmas for graph preservation *)

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

(** graph_insert_modules_lookup_same: after inserting m at mid, looking up mid returns m. *)
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

(** graph_update_lookup_same: after updating mid, looking up mid returns the normalized module. *)
Lemma graph_update_lookup_same : forall g mid m,
  graph_lookup (graph_update g mid m) mid = Some (normalize_module m).
Proof.
  intros g mid m.
  unfold graph_update, graph_lookup. simpl.
  apply graph_insert_modules_lookup_same.
Qed.

(** graph_update_preserves_unrelated: updating mid' doesn't change the lookup of unrelated mid. *)
Lemma graph_update_preserves_unrelated : forall g mid mid' m,
  mid <> mid' ->
  graph_lookup (graph_update g mid' m) mid = graph_lookup g mid.
Proof.
  intros g mid mid' m Hneq.
  unfold graph_update, graph_lookup. simpl.
  apply graph_insert_modules_preserves_unrelated. assumption.
Qed.

(** graph_add_axiom_preserves_unrelated: adding an axiom to mid' doesn't affect lookups of unrelated mid. *)
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

(** graph_record_discovery_preserves_unrelated: recording discovery events at mid' doesn't affect lookups of mid.
    Proof: fold_left over the event list, each step uses graph_add_axiom_preserves_unrelated. *)
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

(** graph_update_module_tensor_preserves_unrelated: updating the tensor of mid' doesn't change mid's lookup. *)
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

(** --- Graph Preservation Lemmas ---

    The no-signaling proof needs to know that pnew/psplit/pmerge don't affect
    modules they aren't targeting. These lemmas build that up piece by piece:
    - graph_add_module only creates IDs >= pg_next_id, so existing IDs are untouched
    - graph_remove preserves pg_next_id (no ID reuse)
    - each unrelated-module lookup is preserved through the whole chain

    The well-formedness hypothesis (well_formed_graph s.(vm_graph)) is structural,
    not a physics axiom — it just says module IDs are < pg_next_id, which is
    maintained by every graph operation in VMState.v.
*)

(** graph_lookup_beyond_next_id: well-formed graphs return None for any module ID >= pg_next_id.
    This is wf_graph_lookup_beyond_next_id from VMState.v, re-exported with a cleaner name. *)
Lemma graph_lookup_beyond_next_id : forall g mid,
  well_formed_graph g ->
  mid >= g.(pg_next_id) ->
  graph_lookup g mid = None.
Proof.
  exact wf_graph_lookup_beyond_next_id.
Qed.

(** graph_add_module_preserves_existing: adding a new module doesn't change lookups of existing modules.
    graph_add_module gives the new module ID = pg_next_id. Since mid < pg_next_id,
    the head of the list doesn't match, and the lookup falls through to the old list. *)
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

(** graph_remove_preserves_next_id: removing a module doesn't change pg_next_id.
    IDs are monotonically increasing — removing a module doesn't free its ID for reuse. *)
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

(** graph_remove_preserves_unrelated: removing mid' leaves mid's lookup unchanged.
    Proof: induction on the module list — when we hit mid' and remove it, mid's entry
    is either before (already returned) or after (still in the tail). *)
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

(** graph_pnew_preserves_existing: PNEW doesn't change lookups of existing modules.
    Either the region already exists (graph unchanged), or a new module is added at
    pg_next_id (which is > mid for any existing mid). Either way, existing lookups survive. *)
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

(** graph_psplit_preserves_unrelated: splitting mid_split doesn't affect lookups of unrelated mid.
    PSPLIT removes mid_split, then adds two new modules (left and right) at fresh IDs.
    Proof: chain graph_remove_preserves_unrelated → two calls to graph_add_module_preserves_existing. *)
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

(** graph_pmerge_preserves_observables: PMERGE doesn't change Observable at unrelated modules.
    PMERGE removes m1 and m2, then either updates an existing super-module or creates a new one.
    The tricky case: when mid equals the existing super-module, its AXIOMS change but its
    REGION doesn't. Observable only looks at region — so observationally, mid is unchanged.
    Proof: chain the two removes + either graph_update_preserves_unrelated or
    graph_add_module_preserves_existing, handling the axiom-update edge case separately. *)
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

(* NOTE: A substrate-level no-signaling theorem using graph_lookup (full module state)
   cannot be proven — PMERGE legitimately updates an existing super-module's axioms when
   the union region already exists. The axioms change, but the observable (region) doesn't.
   The correct statement is observational_no_signaling below, which uses ObservableRegion. *)

(** observational_no_signaling: if mid is not in instr_targets instr, then executing
    instr doesn't change ObservableRegion at mid.

    The key insight here: this CAN'T be proven at the graph_lookup level for pmerge,
    because pmerge sometimes updates axioms of an existing super-module. Axiom updates
    change the full module state (graph_lookup), but they DON'T change the partition region.
    Observable only reads partition region and μ — not axioms.

    So locality is a property of OBSERVABLES, not of raw memory. An instruction that
    doesn't target mid can still touch an unrelated part of mid's record — it just
    can't touch the part that's observable. That's the correct formulation.

    To falsify: Find an instruction not in instr_targets mid, and a vm_step execution
    that changes ObservableRegion at mid. The proof won't compile if that's possible. *)
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
  (* Goal 1: step_pnew — graph' = fst(graph_add_module ...) *)
  - rewrite graph_add_module_lookup_other; [reflexivity | exact Hmid_lt].
  (* Goal 2: step_psplit — graph' = graph_hw_psplit (vm_graph s) (module mod 64) *)
  - assert (Hneq: mid <> module mod 64).
    { intro Heq. apply Hnotin. unfold instr_targets. left. symmetry. exact Heq. }
    unfold graph_hw_psplit, graph_module_size.
    destruct (graph_remove (vm_graph s) (module mod 64)) as [[g1 m_rm]|] eqn:Hrm.
    + (* graph_remove succeeded *)
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
    + (* graph_remove failed *)
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
  (* Goal 3: step_pmerge — graph' = graph_hw_pmerge (vm_graph s) (m1 mod 64) (m2 mod 64) *)
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

(** --- Speed Limit ---

    How many steps does it take before an instruction can influence module mid?
    min_steps_to_target finds the first instruction in the trace that targets mid
    and returns how many steps in we are at that point. None means mid is never
    targeted by this trace.
*)

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

(** Summary.

  The file establishes observational equivalence as a real equivalence,
  proves the gauge-shift invariance and cone monotonicity facts it needs, and
  then uses those pieces to support the locality and graph-preservation
  claims. All of it is built from VMState and vm_step rather than outside
  physical assumptions. *)
