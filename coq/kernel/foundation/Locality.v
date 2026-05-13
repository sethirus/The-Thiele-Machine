(**
    Locality: existing module regions are preserved outside instruction targets.

    This file proves a VM-locality theorem for the observable used here:
    normalized module regions. For each instruction type, if an existing module
    mid is not explicitly targeted, then module_region_obs(s, mid) =
    module_region_obs(s', mid).

    Proof structure: use the well_formed_graph invariant throughout. New modules
    are added at pg_next_id (beyond existing IDs), so lookup at mid < pg_next_id
    is unaffected by additions at ≥ pg_next_id. For ops that remove modules
    (psplit, pmerge), explicitly check untargeted modules remain unchanged.

    To falsify: find an instruction where executing it on module A changes
    the normalized region observation of an existing, untargeted module B. Or
    show the well_formed_graph invariant is not strong enough for the lookup
    preservation arguments.
    *)

(* INQUISITOR NOTE: proof-connectivity - bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

From Coq Require Import List Arith.PeanoNat Lia Bool.
From Coq Require Import Strings.String.
Import ListNotations.

From Kernel Require Import VMState VMStep KernelPhysics.


(** Key contrapositive: If lookup succeeds, then mid < pg_next_id *)
Lemma wf_graph_lookup_implies_below : forall g mid m,
  well_formed_graph g ->
  graph_lookup g mid = Some m ->
  mid < g.(pg_next_id).
Proof.
  intros g mid m Hwf Hlookup.
  destruct (Nat.ltb mid (pg_next_id g)) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt. exact Hlt.
  - apply Nat.ltb_ge in Hlt.
    (* mid >= pg_next_id but lookup succeeded - contradiction *)
    pose proof (wf_graph_lookup_beyond_next_id g mid Hwf Hlt) as Hnone.
    rewrite Hlookup in Hnone. discriminate.
Qed.

(** Same but for module lists directly *)
Lemma all_ids_below_lookup_implies_below : forall modules mid m bound,
  all_ids_below modules bound ->
  graph_lookup_modules modules mid = Some m ->
  mid < bound.
Proof.
  induction modules as [|[id ms] rest IH]; intros mid m bound Hall Hlookup.
  - simpl in Hlookup. discriminate.
  - simpl in Hall. destruct Hall as [Hid Hrest].
    simpl in Hlookup. destruct (Nat.eqb id mid) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. exact Hid.
    + apply (IH mid m bound Hrest Hlookup).
Qed.


(** Lookup is unchanged for modules not in the modified set *)

Lemma graph_pnew_preserves_lookup :
  forall g region g' new_id mid,
    graph_pnew g region = (g', new_id) ->
    mid < g.(pg_next_id) ->
    graph_lookup g' mid = graph_lookup g mid.
Proof.
  intros g region g' new_id mid Hpnew Hlt.
  unfold graph_pnew in Hpnew.
  destruct (graph_find_region g (normalize_region region)) eqn:Hfind.
  - injection Hpnew as Hg' Hid. subst g'. reflexivity.
  - unfold graph_add_module in Hpnew.
    injection Hpnew as Hg' Hid. subst g' new_id.
    unfold graph_lookup. simpl.
    destruct (Nat.eqb (pg_next_id g) mid) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + reflexivity.
Qed.

Lemma graph_update_preserves_lookup_other :
  forall g mid_target m mid,
    mid <> mid_target ->
    graph_lookup (graph_update g mid_target m) mid = graph_lookup g mid.
Proof.
  intros g mid_target m mid Hneq.
  unfold graph_lookup, graph_update. simpl.
  remember (pg_modules g) as modules eqn:Hmodules. clear Hmodules g.
  induction modules as [| [id ms] rest IH].
  - simpl. destruct (Nat.eqb mid_target mid) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst mid_target. exfalso. apply Hneq. reflexivity.
    + reflexivity.
  - simpl. destruct (Nat.eqb id mid_target) eqn:Htarget.
    + apply Nat.eqb_eq in Htarget. subst id. simpl.
      destruct (Nat.eqb mid_target mid) eqn:Hmid.
      * apply Nat.eqb_eq in Hmid. subst mid_target. exfalso. apply Hneq. reflexivity.
      * reflexivity.
    + simpl. destruct (Nat.eqb id mid) eqn:Hmid.
      * reflexivity.
      * apply IH.
Qed.

Lemma graph_add_axiom_preserves_lookup_other :
  forall g mid_target ax mid,
    mid <> mid_target ->
    graph_lookup (graph_add_axiom g mid_target ax) mid = graph_lookup g mid.
Proof.
  intros g mid_target ax mid Hneq.
  unfold graph_add_axiom.
  destruct (graph_lookup g mid_target) eqn:Hlookup.
  - apply graph_update_preserves_lookup_other. exact Hneq.
  - reflexivity.
Qed.

Lemma graph_add_axioms_preserves_lookup_other :
  forall axs g mid_target mid,
    mid <> mid_target ->
    graph_lookup (graph_add_axioms g mid_target axs) mid = graph_lookup g mid.
Proof.
  intros axs. induction axs as [| ax rest IH]; intros g mid_target mid Hneq.
  - simpl. reflexivity.
  - unfold graph_add_axioms. simpl. unfold graph_add_axioms in IH.
    rewrite IH by exact Hneq.
    apply graph_add_axiom_preserves_lookup_other. exact Hneq.
Qed.


(** Define observation of a module in a state as just the region (not axioms).
    We use the NORMALIZED region because graph operations may normalize regions
    during storage, so comparing normalized forms gives semantic equality. *)
Definition module_region_obs (s : VMState) (mid : ModuleID) : option (list nat) :=
  match graph_lookup s.(vm_graph) mid with
  | Some m => Some (normalize_region (m.(module_region)))
  | None => None
  end.

(** A module exists in a state if it has an observation *)
Definition module_exists (s : VMState) (mid : ModuleID) : Prop :=
  module_region_obs s mid <> None.

(** Two states agree on a module if they have the same region observation *)
Definition states_agree_on_module (s s' : VMState) (mid : ModuleID) : Prop :=
  module_region_obs s mid = module_region_obs s' mid.

(** Two states agree on EXISTING modules except on target modules.
    This is the correct locality definition: we only require agreement on
    modules that already existed, not on newly created modules.
 We compare REGIONS only, not axioms. This is because pmerge
    can update axioms of an existing module with the union region, but
    that module is not in the targets [m1; m2]. Observable locality
    only guarantees region preservation, not axiom preservation. *)
Definition states_agree_except (s s' : VMState) (targets : list ModuleID) : Prop :=
  forall mid, 
    module_exists s mid ->
    ~ In mid targets -> 
    states_agree_on_module s s' mid.


Lemma advance_state_graph :
  forall s i g csrs err,
    (advance_state s i g csrs err).(vm_graph) = g.
Proof. intros. reflexivity. Qed.

Lemma advance_state_reveal_graph :
  forall s i flat_idx delta g csrs err,
    (advance_state_reveal s i flat_idx delta g csrs err).(vm_graph) = g.
Proof. intros. reflexivity. Qed.

Lemma advance_state_rm_graph :
  forall s i g csrs regs mem err,
    (advance_state_rm s i g csrs regs mem err).(vm_graph) = g.
Proof. intros. reflexivity. Qed.

Lemma jump_state_graph :
  forall s i target,
    (jump_state s i target).(vm_graph) = s.(vm_graph).
Proof. intros. reflexivity. Qed.

Lemma jump_state_rm_graph :
  forall s i target regs mem,
    (jump_state_rm s i target regs mem).(vm_graph) = s.(vm_graph).
Proof. intros. reflexivity. Qed.


Definition instr_targets (i : vm_instruction) : list ModuleID :=
  match i with
  | instr_pnew _ _ => []
  | instr_psplit mid _ _ _ => [mid mod 64]
  | instr_pmerge m1 m2 _ => [m1 mod 64; m2 mod 64]
  | instr_lassert _ _ _ _ _ => []
  | instr_ljoin _ _ _ => []
  | instr_mdlacc mid _ => [mid]
  | instr_pdiscover mid _ _ => [mid]
  | instr_xfer _ _ _ => []
  | instr_load_imm _ _ _ => []
  | instr_load _ _ _ => []
  | instr_store _ _ _ => []
  | instr_add _ _ _ _ => []
  | instr_sub _ _ _ _ => []
  | instr_jump _ _ => []
  | instr_jnez _ _ _ => []
  | instr_call _ _ => []
  | instr_ret _ => []
  | instr_chsh_trial _ _ _ _ _ => []
  | instr_xor_load _ _ _ => []
  | instr_xor_add _ _ _ => []
  | instr_xor_swap _ _ _ => []
  | instr_xor_rank _ _ _ => []
  | instr_emit mid _ _ => [mid]
  | instr_reveal mid _ _ _ => [mid]
  | instr_checkpoint _ _ => []
  | instr_read_port _ _ _ _ _ => []
  | instr_write_port _ _ _ => []
  | instr_heap_load _ _ _ => []
  | instr_heap_store _ _ _ => []
  | instr_certify _ => []
  | instr_and _ _ _ _ => []
  | instr_or _ _ _ _ => []
  | instr_shl _ _ _ _ => []
  | instr_shr _ _ _ _ => []
  | instr_mul _ _ _ _ => []
  | instr_lui _ _ _ => []
  | instr_halt _ => []
  | instr_tensor_set _ _ _ _ _ => []
  | instr_tensor_get _ _ _ _ _ => []
  (* Categorical / morphism instructions: morphisms do not target modules directly. *)
  | instr_morph _ _ _ _ _ => []
  | instr_compose _ _ _ _ => []
  | instr_morph_id _ _ _ => []
  | instr_morph_delete _ _ => []
  | instr_morph_assert _ _ _ _ => []
  | instr_morph_tensor _ _ _ _ => []
  | instr_morph_get _ _ _ _ => []
  | instr_chsh_lassert _ => []  (* CHSH-aware certification: reads witness counters, no module targets *)
  end.


(** Helper: Define well-formed VM state *)
Definition well_formed_state (s : VMState) : Prop :=
  well_formed_graph s.(vm_graph).

(** Helper: module_exists implies mid < pg_next_id for well-formed states *)
Lemma module_exists_implies_below : forall s mid,
  well_formed_state s ->
  module_exists s mid ->
  mid < s.(vm_graph).(pg_next_id).
Proof.
  intros s mid Hwf Hexists.
  unfold module_exists, module_region_obs in Hexists.
  destruct (graph_lookup (vm_graph s) mid) eqn:Hlookup.
  - apply (wf_graph_lookup_implies_below _ _ _ Hwf Hlookup).
  - exfalso. apply Hexists. reflexivity.
Qed.

(** Helper: region observation is preserved when graph_lookup is preserved.
    Updated to use normalized regions matching module_region_obs definition. *)
Lemma region_obs_lookup_eq : forall g g' mid,
  graph_lookup g' mid = graph_lookup g mid ->
  match graph_lookup g' mid with
  | Some m' => Some (normalize_region (module_region m'))
  | None => None
  end =
  match graph_lookup g mid with
  | Some m => Some (normalize_region (module_region m))
  | None => None
  end.
Proof.
  intros g g' mid Heq. rewrite Heq. reflexivity.
Qed.

(** Helper: targets is [m] and mid not in targets means mid <> m *)
Lemma not_in_singleton : forall mid m : ModuleID,
  ~ In mid [m] -> mid <> m.
Proof.
  intros mid m H. intros Heq. subst.
  apply H. left. reflexivity.
Qed.

(** Helper: targets is [m1; m2] and mid not in targets means mid <> m1 and mid <> m2 *)
Lemma not_in_pair : forall mid m1 m2 : ModuleID,
  ~ In mid [m1; m2] -> mid <> m1 /\ mid <> m2.
Proof.
  intros mid m1 m2 H. split.
  - intros Heq. subst. apply H. left. reflexivity.
  - intros Heq. subst. apply H. right. left. reflexivity.
Qed.

(** Helper: graph_update_module_tensor preserves module_region_obs for ALL modules.
    TENSOR instructions update only module_mu_tensor, not module_region, so
    the observable region (which normalize_region computes from module_region)
    is unchanged for every module ID. *)
Lemma graph_update_module_tensor_preserves_region_obs :
  forall g mid k v mid',
  match graph_lookup g mid' with
  | Some m => Some (normalize_region m.(module_region))
  | None => None
  end =
  match graph_lookup (graph_update_module_tensor g mid k v) mid' with
  | Some m => Some (normalize_region m.(module_region))
  | None => None
  end.
Proof.
  intros g mid k v mid'.
  destruct (graph_lookup g mid) as [ms|] eqn:Hlu.
  - (* Module mid exists: graph_update is called *)
    destruct (Nat.eq_dec mid' mid) as [Heq | Hneq].
    + (* mid' = mid: lookup returns updated module, but module_region preserved *)
      subst.
      rewrite (graph_update_module_tensor_lookup_same g mid k v ms Hlu).
      rewrite Hlu. simpl.
      f_equal. symmetry. apply normalize_region_idempotent.
    + (* mid' <> mid: lookup in updated graph is unchanged *)
      unfold graph_update_module_tensor. rewrite Hlu.
      rewrite graph_update_preserves_unrelated by assumption.
      reflexivity.
  - (* Module mid doesn't exist: graph_update_module_tensor is identity *)
    unfold graph_update_module_tensor. rewrite Hlu. reflexivity.
Qed.

(** graph_add_axiom only changes module_axioms, not module_region.
    So module_region_obs is preserved for ALL modules (not just mid ≠ target). *)
Lemma graph_add_axiom_preserves_region_obs_all :
  forall g mid_target ax mid',
    match graph_lookup (graph_add_axiom g mid_target ax) mid' with
    | Some m' => Some (normalize_region m'.(module_region))
    | None => None
    end =
    match graph_lookup g mid' with
    | Some m => Some (normalize_region m.(module_region))
    | None => None
    end.
Proof.
  intros g mid_target ax mid'.
  unfold graph_add_axiom.
  destruct (graph_lookup g mid_target) eqn:Hlu.
  - (* mid_target has a module: axiom added to it *)
    destruct (Nat.eq_dec mid' mid_target) as [Heq | Hneq].
    + (* mid' = mid_target: updated module has same region as original *)
      subst.
      assert (Hne : graph_lookup g mid_target <> None) by (rewrite Hlu; discriminate).
      erewrite graph_update_lookup_same by exact Hne.
      rewrite Hlu. unfold normalize_module. simpl.
      rewrite normalize_region_idempotent. reflexivity.
    + (* mid' ≠ mid_target: lookup unchanged *)
      rewrite graph_update_preserves_lookup_other by assumption.
      reflexivity.
  - (* mid_target has no module: graph unchanged *)
    reflexivity.
Qed.

(** THE MASTER LOCALITY vm_step only changes target module observations
    Requires well-formed initial state for pnew/psplit/pmerge cases *)
Theorem vm_step_is_local :
  forall s i s',
    well_formed_state s ->
    vm_step s i s' ->
    states_agree_except s s' (instr_targets i).
Proof.
  intros s i s' Hwf Hstep.
  destruct i; simpl; intros mid Hexists Hnot_target.
  - (* pnew - creates new module, preserves existing *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_graph.
    apply region_obs_lookup_eq.
    symmetry.
    apply graph_add_module_preserves_existing.
    apply (module_exists_implies_below s mid Hwf Hexists).
  - (* psplit - restructures graph via graph_hw_psplit *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_graph.
    apply region_obs_lookup_eq. symmetry.
    pose proof (not_in_singleton mid _ Hnot_target) as Hneq.
    pose proof (module_exists_implies_below s mid Hwf Hexists) as Hmid_lt.
    unfold graph_hw_psplit, graph_module_size.
    destruct (graph_remove (vm_graph s) (module mod 64)) as [[g1 m_rm]|] eqn:Hrm.
    + pose proof (graph_remove_preserves_next_id _ _ _ _ Hrm) as Hnid.
      destruct (graph_add_module g1 _ _) as [g2 mid2] eqn:Hadd1.
      destruct (graph_add_module g2 _ _) as [g3 mid3] eqn:Hadd2. simpl.
      transitivity (graph_lookup g2 mid).
      * change g3 with (fst (g3, mid3)). rewrite <- Hadd2.
        apply graph_add_module_preserves_existing.
        pose proof (f_equal (fun p => pg_next_id (fst p)) Hadd1) as Htmp.
        unfold graph_add_module in Htmp. simpl in Htmp. lia.
      * transitivity (graph_lookup g1 mid).
        -- change g2 with (fst (g2, mid2)). rewrite <- Hadd1.
           apply graph_add_module_preserves_existing. lia.
        -- exact (graph_remove_preserves_unrelated _ mid _ _ _ Hneq Hrm).
    + destruct (graph_add_module (vm_graph s) _ _) as [g2 mid2] eqn:Hadd1.
      destruct (graph_add_module g2 _ _) as [g3 mid3] eqn:Hadd2. simpl.
      transitivity (graph_lookup g2 mid).
      * change g3 with (fst (g3, mid3)). rewrite <- Hadd2.
        apply graph_add_module_preserves_existing.
        pose proof (f_equal (fun p => pg_next_id (fst p)) Hadd1) as Htmp.
        unfold graph_add_module in Htmp. simpl in Htmp. lia.
      * change g2 with (fst (g2, mid2)). rewrite <- Hadd1.
        apply graph_add_module_preserves_existing. exact Hmid_lt.
  - (* pmerge - restructures graph via graph_hw_pmerge *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_graph.
    apply region_obs_lookup_eq. symmetry.
    destruct (not_in_pair mid _ _ Hnot_target) as [Hneq1 Hneq2].
    pose proof (module_exists_implies_below s mid Hwf Hexists) as Hmid_lt.
    unfold graph_hw_pmerge, graph_module_size.
    destruct (graph_remove (vm_graph s) (m1 mod 64)) as [[g1 m1_rm]|] eqn:Hrm1.
    + (* first remove succeeded *)
      pose proof (graph_remove_preserves_next_id _ _ _ _ Hrm1) as Hnid1.
      pose proof (graph_remove_preserves_unrelated _ mid _ _ _ Hneq1 Hrm1) as Hlu1.
      destruct (graph_remove g1 (m2 mod 64)) as [[g2 m2_rm]|] eqn:Hrm2.
      * (* second remove succeeded *)
        pose proof (graph_remove_preserves_next_id _ _ _ _ Hrm2) as Hnid2.
        pose proof (graph_remove_preserves_unrelated _ mid _ _ _ Hneq2 Hrm2) as Hlu2.
        destruct (graph_add_module g2 _ _) as [g3 mid3] eqn:Hadd. simpl.
        change g3 with (fst (g3, mid3)). rewrite <- Hadd.
        rewrite graph_add_module_preserves_existing by lia.
        rewrite Hlu2. exact Hlu1.
      * (* second remove failed *)
        destruct (graph_add_module g1 _ _) as [g3 mid3] eqn:Hadd. simpl.
        change g3 with (fst (g3, mid3)). rewrite <- Hadd.
        rewrite graph_add_module_preserves_existing by lia.
        exact Hlu1.
    + (* first remove failed *)
      destruct (graph_remove (vm_graph s) (m2 mod 64)) as [[g2 m2_rm]|] eqn:Hrm2.
      * (* second remove succeeded *)
        pose proof (graph_remove_preserves_next_id _ _ _ _ Hrm2) as Hnid2.
        pose proof (graph_remove_preserves_unrelated _ mid _ _ _ Hneq2 Hrm2) as Hlu2.
        destruct (graph_add_module g2 _ _) as [g3 mid3] eqn:Hadd. simpl.
        change g3 with (fst (g3, mid3)). rewrite <- Hadd.
        rewrite graph_add_module_preserves_existing by lia.
        exact Hlu2.
      * (* both removes failed *)
        destruct (graph_add_module (vm_graph s) _ _) as [g3 mid3] eqn:Hadd. simpl.
        change g3 with (fst (g3, mid3)). rewrite <- Hadd.
        apply graph_add_module_preserves_existing. exact Hmid_lt.
  - (* lassert: single constructor, graph unchanged (record literal) *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    simpl. reflexivity.
  - (* ljoin *)
    inversion Hstep; subst;
    unfold states_agree_on_module, module_region_obs;
    rewrite advance_state_graph; reflexivity.
  - (* mdlacc *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_graph. reflexivity.
  - (* pdiscover: graph unchanged *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_graph. reflexivity.
  - (* xfer *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_rm_graph. reflexivity.
  - (* load_imm *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_rm_graph. reflexivity.
  - (* load *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_rm_graph. reflexivity.
  - (* store *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_rm_graph. reflexivity.
  - (* add *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_rm_graph. reflexivity.
  - (* sub *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_rm_graph. reflexivity.
  - (* jump *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite jump_state_graph. reflexivity.
  - (* jnez *)
    inversion Hstep; subst;
    unfold states_agree_on_module, module_region_obs;
    [rewrite jump_state_graph | rewrite advance_state_graph]; reflexivity.
  - (* call *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite jump_state_rm_graph. reflexivity.
  - (* ret *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite jump_state_rm_graph. reflexivity.
  - (* chsh_trial *)
    inversion Hstep; subst;
    unfold states_agree_on_module, module_region_obs;
    try (rewrite advance_state_graph; reflexivity);
    simpl; reflexivity.
  - (* xor_load *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_rm_graph. reflexivity.
  - (* xor_add *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_rm_graph. reflexivity.
  - (* xor_swap *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_rm_graph. reflexivity.
  - (* xor_rank *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_rm_graph. reflexivity.
  - (* emit *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_graph. reflexivity.
  - (* reveal *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_reveal_graph. reflexivity.
  - (* checkpoint *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    reflexivity.
  - (* read_port *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    reflexivity.
  - (* write_port *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    reflexivity.
  - (* heap_load *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    reflexivity.
  - (* heap_store *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    reflexivity.
  - (* certify *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    reflexivity.
  - (* and *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    reflexivity.
  - (* or *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    reflexivity.
  - (* shl *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    reflexivity.
  - (* shr *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    reflexivity.
  - (* mul *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    reflexivity.
  - (* lui *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    reflexivity.
  - (* halt *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    reflexivity.
  - (* tensor_set: graph may update tensor entries, but regions stay the same *)
    inversion Hstep; subst;
      unfold states_agree_on_module, module_region_obs.
    + rewrite advance_state_graph.
      rewrite <- (graph_update_module_tensor_preserves_region_obs
                    (vm_graph s) module (i * 4 + j) value mid).
      reflexivity.
    + rewrite advance_state_graph. reflexivity.
  - (* tensor_get: graph unchanged *)
    inversion Hstep; subst;
      unfold states_agree_on_module, module_region_obs.
    + rewrite advance_state_rm_graph. reflexivity.
    + rewrite advance_state_graph. reflexivity.
  - (* instr_morph: morph table updates preserve module observations *)
    inversion Hstep; subst;
      unfold states_agree_on_module, module_region_obs.
    + rewrite advance_state_rm_graph.
      apply region_obs_lookup_eq. symmetry.
      change graph' with (fst (graph', morph_id)).
      match goal with
      | Hmorph : (graph', morph_id) =
                 graph_add_morphism (vm_graph s) src_mod dst_mod empty_coupling_data false |- _ =>
          rewrite Hmorph
      end.
      apply graph_add_morphism_preserves_lookup.
    + rewrite advance_state_graph. reflexivity.
    + rewrite advance_state_graph. reflexivity.
  - (* instr_compose: morph composition preserves module observations *)
    inversion Hstep; subst;
      unfold states_agree_on_module, module_region_obs.
    + rewrite advance_state_rm_graph.
      apply region_obs_lookup_eq. symmetry.
      match goal with
      | Hcomp : graph_compose_morphisms (vm_graph s) m1_id m2_id = Some (graph', morph_id) |- _ =>
          eapply graph_compose_morphisms_preserves_lookup; exact Hcomp
      end.
    + rewrite advance_state_graph. reflexivity.
  - (* instr_morph_id: identity morph creation preserves module observations *)
    inversion Hstep; subst;
      unfold states_agree_on_module, module_region_obs.
    + rewrite advance_state_rm_graph.
      apply region_obs_lookup_eq. symmetry.
      match goal with
      | Hid : graph_add_identity (vm_graph s) module = Some (graph', morph_id) |- _ =>
          eapply graph_add_identity_preserves_lookup; exact Hid
      end.
    + rewrite advance_state_graph. reflexivity.
  - (* instr_morph_delete: morph deletion preserves module observations *)
    inversion Hstep; subst;
      unfold states_agree_on_module, module_region_obs.
    + rewrite advance_state_graph.
      apply region_obs_lookup_eq. symmetry.
      match goal with
      | Hdel : graph_delete_morphism (vm_graph s) morph_id = Some graph' |- _ =>
          eapply graph_delete_morphism_preserves_lookup; exact Hdel
      end.
    + rewrite advance_state_graph. reflexivity.
  - (* instr_morph_assert: only changes CSRs, graph unchanged *)
    inversion Hstep; subst;
    unfold states_agree_on_module, module_region_obs;
    rewrite advance_state_graph; reflexivity.
  - (* instr_morph_tensor: tensoring morphisms preserves module observations *)
    inversion Hstep; subst;
      unfold states_agree_on_module, module_region_obs.
    + rewrite advance_state_rm_graph.
      apply region_obs_lookup_eq. symmetry.
      match goal with
      | Htensor : graph_tensor_morphisms (vm_graph s) f_id g_id = Some (graph', morph_id) |- _ =>
          eapply graph_tensor_morphisms_preserves_lookup; exact Htensor
      end.
    + rewrite advance_state_graph. reflexivity.
  - (* instr_morph_get: module observations are unchanged on success or failure *)
    inversion Hstep; subst;
      unfold states_agree_on_module, module_region_obs.
    + rewrite advance_state_rm_graph. reflexivity.
    + rewrite advance_state_graph. reflexivity.
  - (* instr_chsh_lassert: graph and module observations unchanged on both
       success (csr update only) and failure (err latch only). *)
    inversion Hstep; subst;
      unfold states_agree_on_module, module_region_obs; reflexivity.
Qed.

(**
    
    PROVEN over the current vm_step constructor cases:
    - pnew: Uses well_formed_graph invariant + region_obs_lookup_eq
    - psplit: Uses graph_psplit_preserves_unrelated + region_obs_lookup_eq
    - pmerge: Uses graph_pmerge_preserves_region_obs with normalized regions
    - lassert, ljoin, mdlacc, pdiscover, xfer
    - chsh_trial, xor_load, xor_add, xor_swap, xor_rank
    - emit, reveal, halt
    
    KEY INSIGHT: locality here means existing module regions unchanged except targets
    - Axioms may change (e.g., pmerge updates axioms of existing module)
    - Region is the observable part - axioms are internal state
    - New modules (pnew, psplit, pmerge) don't violate this
    - Requires well_formed_graph invariant to prove id < pg_next_id
    - module_region_obs uses normalize_region for semantic equality
    
    REQUIREMENTS:
    - Well-formed initial state (all module IDs < pg_next_id)
    - This is preserved by all graph operations
    
    *)
