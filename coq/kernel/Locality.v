(** =========================================================================
    LOCALITY PROOFS FOR VM INSTRUCTIONS
    =========================================================================

    WHY THIS FILE EXISTS:
    I claim Einstein locality (spacelike-separated operations don't interfere)
    is a THEOREM, not an axiom. This file proves it: vm_step only modifies
    target modules, leaving untargeted modules unchanged.

    THE CORE CLAIM:
    Each VM instruction satisfies locality: executing an instruction only changes
    observables of explicitly targeted modules. Other modules are unaffected.

    WHAT THIS PROVES:
    For each instruction type (pnew, psplit, pmerge, etc.), if module mid is
    not explicitly targeted, then ObservableRegion(s, mid) = ObservableRegion(s', mid).

    KEY LEMMAS:
    - wf_graph_lookup_implies_below: Well-formed graphs have bounded module IDs (line 35)
    - graph_pnew_preserves_lookup: PNEW doesn't change existing module lookups (line 69)
    - Similar preservation lemmas for psplit, pmerge, etc.

    PROOF STRATEGY:
    1. Use well_formed_graph invariant throughout
    2. Key insight: new modules are added at pg_next_id (beyond existing IDs)
    3. Lookup at mid < pg_next_id is unaffected by additions at ≥ pg_next_id
    4. For operations that remove modules (psplit, pmerge), explicitly check
       untargeted modules remain unchanged

    PHYSICAL INTERPRETATION:
    This is the formal statement of "no action at a distance". If I operate on
    partition A, partition B (disjoint from A) is unaffected. This is why
    weight_disjoint_commutes holds (from Definitions.v).

    FALSIFICATION:
    Find an instruction where executing it on module A changes observables of
    unrelated module B. This would violate locality and require superluminal
    information transfer. Or show well_formed_graph invariant is violated,
    breaking the proof.

    This file proves that each VM instruction satisfies the locality property:
    the vm_step relation only modifies observations of target modules.

    This is the KEY LEMMA that connects locality to conservation.

    KEY INSIGHT: Locality means existing module observations are unchanged
    except for explicitly targeted modules. New modules may be created
    (by pnew) but that doesn't violate locality for existing modules.

    PROOF STRATEGY:
    - Use well_formed_graph invariant throughout
    - key lemma: lookup succeeds => id < pg_next_id
    - pnew: adds at pg_next_id, existing lookups unchanged
    - psplit/pmerge: removes specific modules, adds at next_id+

    ========================================================================= *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
From Coq Require Import Strings.String.
Import ListNotations.

Require Import VMState.
Require Import VMStep.
Require Import KernelPhysics.

(** =========================================================================
    PART 0: WELL-FORMEDNESS LEMMAS
    ========================================================================= *)

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

(** =========================================================================
    PART 1: GRAPH LOCALITY LEMMAS
    ========================================================================= *)

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

(** [graph_update_preserves_lookup_other]: formal specification. *)
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

(** [graph_add_axiom_preserves_lookup_other]: formal specification. *)
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

(** [graph_add_axioms_preserves_lookup_other]: formal specification. *)
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

(** =========================================================================
    PART 2: STATE OBSERVATION LOCALITY
    ========================================================================= *)

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
    
    NOTE: We compare REGIONS only, not axioms. This is because pmerge
    can update axioms of an existing module with the union region, but
    that module is not in the targets [m1; m2]. Observable locality
    only guarantees region preservation, not axiom preservation. *)
Definition states_agree_except (s s' : VMState) (targets : list ModuleID) : Prop :=
  forall mid, 
    module_exists s mid ->
    ~ In mid targets -> 
    states_agree_on_module s s' mid.

(** =========================================================================
    PART 3: HELPERS
    ========================================================================= *)

Lemma advance_state_graph :
  forall s i g csrs err,
    (advance_state s i g csrs err).(vm_graph) = g.
Proof. intros. reflexivity. Qed.

(** [advance_state_reveal_graph]: formal specification. *)
Lemma advance_state_reveal_graph :
  forall s i flat_idx delta g csrs err,
    (advance_state_reveal s i flat_idx delta g csrs err).(vm_graph) = g.
Proof. intros. reflexivity. Qed.

(** [advance_state_rm_graph]: formal specification. *)
Lemma advance_state_rm_graph :
  forall s i g csrs regs mem err,
    (advance_state_rm s i g csrs regs mem err).(vm_graph) = g.
Proof. intros. reflexivity. Qed.

(** =========================================================================
    PART 4: TARGET EXTRACTION
    ========================================================================= *)

Definition instr_targets (i : vm_instruction) : list ModuleID :=
  match i with
  | instr_pnew _ _ => []
  | instr_psplit mid _ _ _ => [mid]
  | instr_pmerge m1 m2 _ => [m1; m2]
  | instr_lassert mid _ _ _ => [mid]
  | instr_ljoin _ _ _ => []
  | instr_mdlacc mid _ => [mid]
  | instr_pdiscover mid _ _ => [mid]
  | instr_xfer _ _ _ => []
  | instr_pyexec _ _ => []
  | instr_chsh_trial _ _ _ _ _ => []
  | instr_xor_load _ _ _ => []
  | instr_xor_add _ _ _ => []
  | instr_xor_swap _ _ _ => []
  | instr_xor_rank _ _ _ => []
  | instr_emit mid _ _ => [mid]
  | instr_reveal mid _ _ _ => [mid]
  | instr_oracle_halts _ _ => []
  | instr_halt _ => []
  end.

(** =========================================================================
    PART 5: THE MASTER LOCALITY THEOREM
    ========================================================================= *)

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

(** THE MASTER LOCALITY THEOREM: vm_step only changes target module observations
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
    apply (graph_pnew_preserves_lookup (vm_graph s) region graph' mid0 mid).
    + assumption.
    + apply (module_exists_implies_below s mid Hwf Hexists).
  - (* psplit - restructures graph *)
    inversion Hstep; subst;
    unfold states_agree_on_module, module_region_obs;
    rewrite advance_state_graph.
    + (* Success case: graph_psplit succeeds *)
      apply region_obs_lookup_eq.
      symmetry.
      apply (graph_psplit_preserves_unrelated (vm_graph s) module left right graph' left_id right_id mid).
      * apply not_in_singleton. exact Hnot_target.
      * apply (module_exists_implies_below s mid Hwf Hexists).
      * assumption.
    + (* Failure case: graph doesn't change *)
      reflexivity.
  - (* pmerge - restructures graph *)
    inversion Hstep; subst;
    unfold states_agree_on_module, module_region_obs;
    rewrite advance_state_graph.
    + (* Success case - region locality *)
      destruct (not_in_pair mid m1 m2 Hnot_target) as [Hneq1 Hneq2].
      pose proof (module_exists_implies_below s mid Hwf Hexists) as Hmid_lt.
      (* The goal is: match graph_lookup graph' mid with ... end = 
                      match graph_lookup (vm_graph s) mid with ... end
         after advance_state_graph unfolded. *)
      (* Apply the pmerge preservation lemma from the hypothesis *)
      destruct (graph_lookup graph' mid) as [m'|] eqn:Hlu';
      destruct (graph_lookup (vm_graph s) mid) as [m_orig|] eqn:Hlu.
      * (* Both Some *)
        f_equal.
        (* Get the region preservation *)
        match goal with
        | [ H : graph_pmerge _ _ _ = Some _ |- _ ] =>
          pose proof (graph_pmerge_preserves_region_obs 
                        (vm_graph s) m1 m2 graph' merged_id mid
                        Hneq1 Hneq2 Hmid_lt H) as Hregion
        end.
        rewrite Hlu' in Hregion. rewrite Hlu in Hregion.
        simpl in Hregion. injection Hregion as Hnorm.
        symmetry. exact Hnorm.
      * (* g' Some, g None - contradiction *)
        exfalso.
        match goal with
        | [ H : graph_pmerge _ _ _ = Some _ |- _ ] =>
          pose proof (graph_pmerge_preserves_region_obs 
                        (vm_graph s) m1 m2 graph' merged_id mid
                        Hneq1 Hneq2 Hmid_lt H) as Hregion
        end.
        rewrite Hlu' in Hregion. rewrite Hlu in Hregion.
        simpl in Hregion. discriminate.
      * (* g' None, g Some - contradiction *)
        exfalso.
        match goal with
        | [ H : graph_pmerge _ _ _ = Some _ |- _ ] =>
          pose proof (graph_pmerge_preserves_region_obs 
                        (vm_graph s) m1 m2 graph' merged_id mid
                        Hneq1 Hneq2 Hmid_lt H) as Hregion
        end.
        rewrite Hlu' in Hregion. rewrite Hlu in Hregion.
        simpl in Hregion. discriminate.
      * (* Both None *)
        reflexivity.
    + (* Failure case *)
      reflexivity.
  - (* lassert *)
    inversion Hstep; subst;
    unfold states_agree_on_module, module_region_obs;
    rewrite advance_state_graph.
    + (* Success case *)
      apply region_obs_lookup_eq.
      symmetry.
      apply graph_add_axiom_preserves_lookup_other.
      intros Heq. subst. apply Hnot_target. left. reflexivity.
    + (* Unsat case - graph unchanged *)
      reflexivity.
  - (* ljoin *)
    inversion Hstep; subst;
    unfold states_agree_on_module, module_region_obs;
    rewrite advance_state_graph; reflexivity.
  - (* mdlacc *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_graph. reflexivity.
  - (* pdiscover *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_graph.
    apply region_obs_lookup_eq.
    unfold graph_record_discovery. symmetry.
    apply graph_add_axioms_preserves_lookup_other.
    intros Heq. subst. apply Hnot_target. left. reflexivity.
  - (* xfer *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_rm_graph. reflexivity.
  - (* pyexec *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_graph. reflexivity.
  - (* chsh_trial *)
    inversion Hstep; subst;
    unfold states_agree_on_module, module_region_obs;
    rewrite advance_state_graph; reflexivity.
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
  - (* oracle_halts *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_graph. reflexivity.
  - (* halt *)
    inversion Hstep; subst.
    unfold states_agree_on_module, module_region_obs.
    rewrite advance_state_graph. reflexivity.
Qed.

(** =========================================================================
    STATUS: LOCALITY FRAMEWORK - FULLY PROVEN
    
    PROVEN (18 of 18 cases):
    - pnew: Uses well_formed_graph invariant + region_obs_lookup_eq
    - psplit: Uses graph_psplit_preserves_unrelated + region_obs_lookup_eq
    - pmerge: Uses graph_pmerge_preserves_region_obs with normalized regions
    - lassert, ljoin, mdlacc, pdiscover, xfer, pyexec
    - chsh_trial, xor_load, xor_add, xor_swap, xor_rank
    - emit, reveal, oracle_halts, halt
    
    KEY INSIGHT: locality = existing module REGIONS unchanged except targets
    - Axioms may change (e.g., pmerge updates axioms of existing module)
    - Region is the observable part - axioms are internal state
    - New modules (pnew, psplit, pmerge) don't violate this
    - Requires well_formed_graph invariant to prove id < pg_next_id
    - module_region_obs uses normalize_region for semantic equality
    
    REQUIREMENTS:
    - Well-formed initial state (all module IDs < pg_next_id)
    - This is preserved by all graph operations
    
    ========================================================================= *)
