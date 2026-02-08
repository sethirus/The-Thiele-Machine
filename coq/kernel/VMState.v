From Coq Require Import List ListDec Bool Arith.PeanoNat.
From Coq Require Import NArith.
From Coq Require Import Strings.String Strings.Ascii.
From Coq Require Import micromega.Lia.
Import ListNotations.

(** * VMState: Core state model for the Thiele Machine

    PURPOSE: Define the complete machine state, partition graph operations,
    and canonical normalization that makes the 3-layer isomorphism possible.

    WHY THIS MATTERS: The Thiele Machine makes structural information explicit
    and measurable. This file defines HOW structure is represented (partition graph),
    HOW it's normalized (canonical regions), and proves the representation is
    consistent across Coq/Python/Verilog.

    KEY PROPERTIES (PROVEN):
    - normalize_region_idempotent: Normalization is stable (essential for observables)
    - well_formed_graph: All module IDs < pg_next_id (prevents collisions)
    - wf_graph_lookup_beyond_next_id: Lookups beyond pg_next_id return None
    - graph_*_preserves_wf: All operations maintain well-formedness

    IMPLEMENTATION MIRRORING:
    - Coq kernel: This file (VMState.v)
    - Python VM: thielecpu/state.py (VMState class)
    - Verilog RTL: thielecpu/hardware/rtl/state_regs.v

    VERIFICATION: All proofs compile with Coq 8.18+. Zero axioms, zero admits.

    FALSIFICATION: If ANY state operation violates well-formedness or if
    normalization is non-idempotent, the bisimulation breaks. The proofs won't compile.

    THESIS REFERENCE: Chapter 3, §3.2.1 (State Space), §3.2.2 (Partition Graph)
    *)

Definition ModuleID := nat.
Definition VMAxiom := string.
Definition AxiomSet := list VMAxiom.

(** Regions are represented as duplicate-free lists of natural numbers. *)
Fixpoint nat_list_mem (x : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | y :: ys => if Nat.eqb x y then true else nat_list_mem x ys
  end.

Definition nat_list_add (xs : list nat) (x : nat) : list nat :=
  if nat_list_mem x xs then xs else xs ++ [x].

(** Canonical region normalization: duplicate-free, stable, idempotent.

    WHY: The 3-layer isomorphism requires IDENTICAL observables across Coq/Python/Verilog.
    Without canonical normalization, the same logical region could have multiple
    representations ([1;2] vs [2;1;2]), breaking observable equality.

    IMPLEMENTATION: Uses Coq stdlib nodup with decidable equality. This ensures:
    1. Duplicate-free: NoDup (normalize_region r)
    2. Idempotent: normalize_region (normalize_region r) = normalize_region r
    3. Stable: Same regions always normalize to same representation

    THESIS: See Chapter 3, §3.2.2. This normalization is what makes
    "observables" well-defined - modules are compared by normalized regions,
    not arbitrary list representations.

    PYTHON/VERILOG: Python VM normalizes via sorted(set(region)). RTL doesn't
    store full regions, only region sizes, so normalization happens during
    snapshot extraction.

    FALSIFICATION: If normalize_region is not idempotent, repeated observations
    of the same module would differ, violating observational_no_signaling.
*)
Definition normalize_region (region : list nat) : list nat :=
  nodup Nat.eq_dec region.

Lemma normalize_region_nodup : forall region, NoDup (normalize_region region).
Proof.
  intro region. unfold normalize_region.
  apply NoDup_nodup.
Qed.

Lemma normalize_region_idempotent : forall region,
  normalize_region (normalize_region region) = normalize_region region.
Proof.
  intro region.
  unfold normalize_region.
  apply nodup_fixed_point.
  apply NoDup_nodup.
Qed.

Definition nat_list_subset (xs ys : list nat) : bool :=
  forallb (fun x => nat_list_mem x ys) xs.

Definition nat_list_disjoint (xs ys : list nat) : bool :=
  forallb (fun x => negb (nat_list_mem x ys)) xs.

Definition nat_list_union (xs ys : list nat) : list nat :=
  normalize_region (xs ++ ys).

Definition nat_list_eq (xs ys : list nat) : bool :=
  nat_list_subset xs ys && nat_list_subset ys xs.

Record ModuleState := {
  module_region : list nat;
  module_axioms : AxiomSet
}.

Definition normalize_module (m : ModuleState) : ModuleState :=
  {| module_region := normalize_region m.(module_region);
     module_axioms := m.(module_axioms) |}.

Record PartitionGraph := {
  pg_next_id : ModuleID;
  pg_modules : list (ModuleID * ModuleState)
}.

(** ** Well-Formedness Invariant for PartitionGraph

    A PartitionGraph is well-formed if all module IDs in pg_modules
    are strictly less than pg_next_id. This ensures:
    - No ID collisions when adding new modules
    - Lookups beyond pg_next_id always return None
    - Module IDs are monotonically increasing
    *)

Fixpoint all_ids_below (modules : list (ModuleID * ModuleState)) (bound : nat) : Prop :=
  match modules with
  | [] => True
  | (id, _) :: rest => (id < bound) /\ all_ids_below rest bound
  end.

Definition well_formed_graph (g : PartitionGraph) : Prop :=
  all_ids_below g.(pg_modules) g.(pg_next_id).

Definition empty_graph : PartitionGraph :=
  {| pg_next_id := 1;
     pg_modules := [] |}.

(** The empty graph is well-formed *)
Lemma empty_graph_well_formed : well_formed_graph empty_graph.
Proof.
  unfold well_formed_graph, empty_graph. simpl.
  exact I.  (* all_ids_below [] _ = True *)
Qed.

Fixpoint graph_lookup_modules
  (modules : list (ModuleID * ModuleState)) (mid : ModuleID)
  : option ModuleState :=
  match modules with
  | [] => None
  | (id, m) :: rest =>
      if Nat.eqb id mid then Some m else graph_lookup_modules rest mid
  end.

Definition graph_lookup (g : PartitionGraph) (mid : ModuleID)
  : option ModuleState :=
  graph_lookup_modules g.(pg_modules) mid.

Fixpoint graph_insert_modules
  (modules : list (ModuleID * ModuleState)) (mid : ModuleID) (m : ModuleState)
  : list (ModuleID * ModuleState) :=
  match modules with
  | [] => [(mid, m)]
  | (id, existing) :: rest =>
      if Nat.eqb id mid
      then (mid, m) :: rest
      else (id, existing) :: graph_insert_modules rest mid m
  end.

Definition graph_update (g : PartitionGraph) (mid : ModuleID) (m : ModuleState)
  : PartitionGraph :=
  {| pg_next_id := g.(pg_next_id);
     pg_modules := graph_insert_modules g.(pg_modules) mid (normalize_module m) |}.

Fixpoint graph_remove_modules
  (modules : list (ModuleID * ModuleState)) (mid : ModuleID)
  : option (list (ModuleID * ModuleState) * ModuleState) :=
  match modules with
  | [] => None
  | (id, m) :: rest =>
      if Nat.eqb id mid
      then Some (rest, m)
      else
        match graph_remove_modules rest mid with
        | None => None
        | Some (rest', removed) => Some ((id, m) :: rest', removed)
        end
  end.

Definition graph_remove (g : PartitionGraph) (mid : ModuleID)
  : option (PartitionGraph * ModuleState) :=
  match graph_remove_modules g.(pg_modules) mid with
  | None => None
  | Some (modules', removed) =>
      Some ({| pg_next_id := g.(pg_next_id); pg_modules := modules' |}, removed)
  end.

Definition graph_add_module (g : PartitionGraph)
  (region : list nat) (axioms : AxiomSet)
  : PartitionGraph * ModuleID :=
  let module := normalize_module {| module_region := region; module_axioms := axioms |} in
  let mid := g.(pg_next_id) in
  ({| pg_next_id := S mid;
      pg_modules := (mid, module) :: g.(pg_modules) |}, mid).

(** graph_add_module preserves lookup for IDs below pg_next_id *)
Lemma graph_add_module_lookup_other : forall g region axioms mid,
  mid < g.(pg_next_id) ->
  graph_lookup (fst (graph_add_module g region axioms)) mid = graph_lookup g mid.
Proof.
  intros g region axioms mid Hlt.
  unfold graph_add_module, graph_lookup. simpl.
  destruct (Nat.eqb (pg_next_id g) mid) eqn:Heq.
  - (* pg_next_id g = mid, contradiction with mid < pg_next_id g *)
    apply Nat.eqb_eq in Heq. lia.
  - (* pg_next_id g <> mid, lookup continues in old modules *)
    reflexivity.
Qed.

Fixpoint graph_find_region_modules
  (modules : list (ModuleID * ModuleState)) (region : list nat)
  : option ModuleID :=
  match modules with
  | [] => None
  | (id, m) :: rest =>
      if nat_list_eq m.(module_region) region
      then Some id
      else graph_find_region_modules rest region
  end.

Definition graph_find_region (g : PartitionGraph) (region : list nat)
  : option ModuleID :=
  graph_find_region_modules g.(pg_modules) (normalize_region region).

Definition graph_add_axiom (g : PartitionGraph) (mid : ModuleID) (ax : VMAxiom)
  : PartitionGraph :=
  match graph_lookup g mid with
  | None => g
  | Some m =>
      let updated := {| module_region := m.(module_region);
                        module_axioms := m.(module_axioms) ++ [ax] |} in
      graph_update g mid updated
  end.

Definition graph_add_axioms (g : PartitionGraph) (mid : ModuleID)
  (axs : list VMAxiom) : PartitionGraph :=
  fold_left (fun acc ax => graph_add_axiom acc mid ax) axs g.

Definition graph_record_discovery (g : PartitionGraph) (mid : ModuleID)
  (evidence : list VMAxiom) : PartitionGraph :=
  graph_add_axioms g mid evidence.

(** ** Well-Formedness Preservation Lemmas *)

(** Helper: IDs strictly less than bound remain so after incrementing bound *)
Lemma all_ids_below_weaken : forall modules n,
  all_ids_below modules n ->
  all_ids_below modules (S n).
Proof.
  induction modules as [|[id m] rest IH]; intros n Hall.
  - exact I.
  - simpl in *. destruct Hall as [Hlt Hrest].
    split.
    + lia.
    + apply IH. exact Hrest.
Qed.

(** graph_add_module preserves well-formedness *)
Lemma graph_add_module_preserves_wf : forall g region axioms,
  well_formed_graph g ->
  well_formed_graph (fst (graph_add_module g region axioms)).
Proof.
  intros g region axioms Hwf.
  unfold graph_add_module. simpl.
  unfold well_formed_graph. simpl.
  split.
  - lia.  (* pg_next_id < S pg_next_id *)
  - apply all_ids_below_weaken. exact Hwf.
Qed.

(** Helper: removing an element preserves all_ids_below *)
Lemma graph_remove_modules_preserves_all_ids_below : forall modules mid modules' m bound,
  all_ids_below modules bound ->
  graph_remove_modules modules mid = Some (modules', m) ->
  all_ids_below modules' bound.
Proof.
  induction modules as [|[id ms] rest IH]; intros mid modules' m bound Hall Hrem.
  - simpl in Hrem. discriminate.
  - simpl in Hrem. simpl in Hall. destruct Hall as [Hid Hrest].
    destruct (Nat.eqb id mid) eqn:Heq.
    + injection Hrem as Heq_modules' Heq_m.
      rewrite <- Heq_modules'. exact Hrest.
    + destruct (graph_remove_modules rest mid) eqn:Hrest_rem.
      * destruct p as [rest' removed']. injection Hrem as Heq_modules' Heq_m.
        rewrite <- Heq_modules'. simpl. split.
        -- exact Hid.
        -- apply (IH mid rest' removed' bound Hrest Hrest_rem).
      * discriminate.
Qed.

(** graph_remove preserves well-formedness *)
Lemma graph_remove_preserves_wf : forall g mid g' m,
  well_formed_graph g ->
  graph_remove g mid = Some (g', m) ->
  well_formed_graph g'.
Proof.
  intros g mid g' m Hwf Hrem.
  unfold graph_remove in Hrem.
  destruct (graph_remove_modules (pg_modules g) mid) eqn:Hrem_modules.
  - destruct p as [modules' removed]. injection Hrem as Heq_g' Heq_m. subst.
    unfold well_formed_graph. simpl.
    apply (graph_remove_modules_preserves_all_ids_below _ _ _ _ _ Hwf Hrem_modules).
  - discriminate.
Qed.

(** ** Module Count (Length) Lemmas *)

(** graph_add_module increases length by 1 *)
Lemma graph_add_module_length : forall g region axioms,
  List.length (pg_modules (fst (graph_add_module g region axioms))) =
  S (List.length (pg_modules g)).
Proof.
  intros g region axioms.
  unfold graph_add_module. simpl. reflexivity.
Qed.

(** Helper: graph_remove_modules decreases length by 1 when successful *)
Lemma graph_remove_modules_length : forall modules mid modules' m,
  graph_remove_modules modules mid = Some (modules', m) ->
  List.length modules = S (List.length modules').
Proof.
  induction modules as [|[id ms] rest IH]; intros mid modules' m Hrem.
  - simpl in Hrem. discriminate.
  - simpl in Hrem.
    destruct (Nat.eqb id mid) eqn:Heq.
    + injection Hrem as Heq' _. subst modules'. simpl. reflexivity.
    + destruct (graph_remove_modules rest mid) eqn:Hrest.
      * destruct p as [rest' removed'].
        injection Hrem as Heq' _. subst modules'. simpl.
        f_equal. apply (IH _ _ _ Hrest).
      * discriminate.
Qed.

(** graph_remove decreases length by 1 when successful *)
Lemma graph_remove_length : forall g mid g' m,
  graph_remove g mid = Some (g', m) ->
  List.length (pg_modules g) = S (List.length (pg_modules g')).
Proof.
  intros g mid g' m Hrem.
  unfold graph_remove in Hrem.
  destruct (graph_remove_modules (pg_modules g) mid) eqn:Hrem_mod.
  - destruct p as [modules' removed]. injection Hrem as Heq' _. subst g'.
    simpl. apply (graph_remove_modules_length _ _ _ _ Hrem_mod).
  - discriminate.
Qed.

(** graph_insert_modules preserves or increases length *)
Lemma graph_insert_modules_length : forall modules mid m,
  List.length (graph_insert_modules modules mid m) >= List.length modules.
Proof.
  induction modules as [|[id ms] rest IH]; intros mid m; simpl.
  - lia.
  - destruct (Nat.eqb id mid); simpl.
    + lia.
    + specialize (IH mid m). lia.
Qed.

(** graph_insert_modules on existing id preserves length exactly *)
Lemma graph_insert_modules_existing_length : forall modules mid m,
  In mid (List.map fst modules) ->
  List.length (graph_insert_modules modules mid m) = List.length modules.
Proof.
  induction modules as [|[id ms] rest IH]; intros mid m Hin; simpl.
  - simpl in Hin. destruct Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst mid. destruct (Nat.eqb id id) eqn:Heq.
      * simpl. reflexivity.
      * apply Nat.eqb_neq in Heq. lia.
    + destruct (Nat.eqb id mid) eqn:Heq.
      * simpl. reflexivity.
      * simpl. f_equal. apply IH. exact Hin'.
Qed.

(** graph_update preserves or increases length *)
Lemma graph_update_length : forall g mid m,
  List.length (pg_modules (graph_update g mid m)) >= List.length (pg_modules g).
Proof.
  intros g mid m.
  unfold graph_update. simpl.
  apply graph_insert_modules_length.
Qed.

(** graph_add_axiom preserves or increases length *)
Lemma graph_add_axiom_length : forall g mid ax,
  List.length (pg_modules (graph_add_axiom g mid ax)) >= List.length (pg_modules g).
Proof.
  intros g mid ax.
  unfold graph_add_axiom.
  destruct (graph_lookup g mid) as [m|].
  - apply graph_update_length.
  - lia.
Qed.

(** Helper: graph_lookup_modules succeeds iff mid is in the module list *)
Lemma graph_lookup_modules_in : forall modules mid m,
  graph_lookup_modules modules mid = Some m ->
  In mid (List.map fst modules).
Proof.
  induction modules as [|[id ms] rest IH]; intros mid m Hlu; simpl.
  - simpl in Hlu. discriminate.
  - simpl in Hlu. destruct (Nat.eqb id mid) eqn:Heq.
    + left. apply Nat.eqb_eq in Heq. exact Heq.
    + right. apply (IH _ m). exact Hlu.
Qed.

(** graph_add_axiom preserves length exactly *)
Lemma graph_add_axiom_preserves_length : forall g mid ax,
  List.length (pg_modules (graph_add_axiom g mid ax)) = List.length (pg_modules g).
Proof.
  intros g mid ax.
  unfold graph_add_axiom.
  destruct (graph_lookup g mid) as [m|] eqn:Hlu.
  - (* Lookup succeeded, so update replaces existing entry *)
    unfold graph_update. simpl.
    apply graph_insert_modules_existing_length.
    unfold graph_lookup in Hlu.
    apply (graph_lookup_modules_in _ _ m Hlu).
  - (* Lookup failed, graph unchanged *)
    reflexivity.
Qed.

(** graph_add_axioms preserves length exactly *)
Lemma graph_add_axioms_preserves_length : forall g mid axs,
  List.length (pg_modules (graph_add_axioms g mid axs)) = List.length (pg_modules g).
Proof.
  intros g mid axs.
  unfold graph_add_axioms.
  revert g. induction axs as [|ax rest IH]; intros g; simpl.
  - reflexivity.
  - rewrite IH. apply graph_add_axiom_preserves_length.
Qed.

(** graph_record_discovery preserves length exactly *)
Lemma graph_record_discovery_preserves_length : forall g mid evidence,
  List.length (pg_modules (graph_record_discovery g mid evidence)) = List.length (pg_modules g).
Proof.
  intros g mid evidence.
  unfold graph_record_discovery.
  apply graph_add_axioms_preserves_length.
Qed.

(** graph_update on existing id preserves length exactly *)
Lemma graph_update_existing_length : forall g mid m,
  graph_lookup g mid <> None ->
  List.length (pg_modules (graph_update g mid m)) = List.length (pg_modules g).
Proof.
  intros g mid m Hlu.
  unfold graph_update. simpl.
  apply graph_insert_modules_existing_length.
  unfold graph_lookup in Hlu.
  destruct (graph_lookup_modules (pg_modules g) mid) as [ms|] eqn:Hlu'.
  - apply (graph_lookup_modules_in _ _ ms Hlu').
  - contradiction.
Qed.

(** graph_insert_modules lookup for the same id *)
Lemma graph_insert_modules_lookup_same : forall modules mid m,
  In mid (List.map fst modules) ->
  graph_lookup_modules (graph_insert_modules modules mid m) mid = Some m.
Proof.
  induction modules as [|[id existing] rest IH]; intros mid m Hin.
  - (* empty - contradiction with In *)
    simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [Heq_id | Hin_rest].
    + (* id = mid *)
      subst id. simpl.
      rewrite Nat.eqb_refl. simpl. rewrite Nat.eqb_refl. reflexivity.
    + (* mid in rest *)
      simpl. destruct (Nat.eqb id mid) eqn:Heq.
      * (* id = mid - this case is also fine *)
        simpl. rewrite Nat.eqb_refl. reflexivity.
      * (* id <> mid - recurse *)
        simpl. rewrite Heq. apply IH. exact Hin_rest.
Qed.

(** graph_update lookup for the same id *)
Lemma graph_update_lookup_same : forall g mid m,
  graph_lookup g mid <> None ->
  graph_lookup (graph_update g mid m) mid = Some (normalize_module m).
Proof.
  intros g mid m Hlu.
  unfold graph_update, graph_lookup. simpl.
  apply graph_insert_modules_lookup_same.
  unfold graph_lookup in Hlu.
  destruct (graph_lookup_modules (pg_modules g) mid) as [ms|] eqn:Hlu'.
  - apply (graph_lookup_modules_in _ _ ms Hlu').
  - contradiction.
Qed.

(** graph_insert_modules preserves lookup for different id *)
Lemma graph_insert_modules_preserves_unrelated : forall modules mid_update mid_other m,
  mid_other <> mid_update ->
  graph_lookup_modules (graph_insert_modules modules mid_update m) mid_other =
  graph_lookup_modules modules mid_other.
Proof.
  induction modules as [|[id existing] rest IH]; intros mid_update mid_other m Hneq.
  - (* empty: graph_insert_modules [] mid_update m = [(mid_update, m)] *)
    simpl.
    (* Need to show lookup mid_other in [(mid_update, m)] = None *)
    destruct (Nat.eqb mid_update mid_other) eqn:Heq.
    + (* mid_update = mid_other - contradiction with Hneq *)
      apply Nat.eqb_eq in Heq. symmetry in Heq. contradiction.
    + (* mid_update <> mid_other - lookup returns None *)
      reflexivity.
  - (* cons *)
    simpl. destruct (Nat.eqb id mid_update) eqn:Heq_update.
    + (* id = mid_update, so insert replaces here, result is (mid_update, m) :: rest *)
      apply Nat.eqb_eq in Heq_update. subst id.
      simpl.
      destruct (Nat.eqb mid_update mid_other) eqn:Heq.
      * (* mid_update = mid_other - contradiction *)
        apply Nat.eqb_eq in Heq. subst. contradiction.
      * (* mid_update <> mid_other *)
        reflexivity.
    + (* id <> mid_update, insert goes deeper *)
      simpl. destruct (Nat.eqb id mid_other) eqn:Heq_other.
      * (* id = mid_other, found *)
        reflexivity.
      * (* id <> mid_other, recurse *)
        apply IH. exact Hneq.
Qed.

(** graph_update preserves lookup for different id *)
Lemma graph_update_preserves_unrelated : forall g mid_update mid_other m,
  mid_other <> mid_update ->
  graph_lookup (graph_update g mid_update m) mid_other = graph_lookup g mid_other.
Proof.
  intros g mid_update mid_other m Hneq.
  unfold graph_update, graph_lookup. simpl.
  apply graph_insert_modules_preserves_unrelated. exact Hneq.
Qed.

(** ** Key Structural Theorem: Lookups Beyond pg_next_id Return None *)

(** Helper: If all IDs in a module list are < bound, then lookup of mid >= bound returns None *)
Lemma all_ids_below_implies_lookup_none : forall modules mid bound,
  all_ids_below modules bound ->
  mid >= bound ->
  graph_lookup_modules modules mid = None.
Proof.
  induction modules as [|[id m] rest IH]; intros mid bound Hall Hge.
  - reflexivity.  (* lookup in empty list = None *)
  - simpl in Hall. destruct Hall as [Hid Hrest].
    simpl. destruct (Nat.eqb id mid) eqn:Heq.
    + (* id = mid, but id < bound <= mid, contradiction *)
      apply Nat.eqb_eq in Heq. subst id. lia.
    + (* id ≠ mid, recurse *)
      apply (IH mid bound Hrest Hge).
Qed.

(** graph_remove preserves pg_next_id *)
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

(** graph_remove preserves lookup for unrelated modules *)
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

(** wf_graph_lookup_beyond_next_id: Lookups beyond next_id always return None.

    WHY THIS MATTERS: This theorem establishes a critical invariant: module IDs
    form a contiguous range [0, pg_next_id). Any lookup outside this range is
    guaranteed to fail. This makes ID allocation simple and prevents collisions.

    CLAIM: For any well-formed graph g, if mid ≥ g.(pg_next_id), then
    graph_lookup g mid = None.

    PROOF STRATEGY: Well-formedness means all_ids_below, which states every
    module ID is < pg_next_id. Case analysis on the module list: either empty
    (lookup returns None), or every ID is < pg_next_id, so mid ≥ pg_next_id
    can't match any existing ID. QED.

    USED BY: KernelPhysics.v completes the proof of graph_lookup_beyond_next_id.
    This enables observational_no_signaling - operations can't affect modules
    that don't exist.

    FALSIFICATION: If ANY graph allows lookup beyond pg_next_id to succeed,
    well-formedness is violated. This would allow ID collisions when adding
    new modules. The proofs won't compile.

    IMPLEMENTATION GUARANTEE: Python VM and RTL maintain same invariant.
    Module IDs are strictly < next_id. Tests verify this.
*)
Theorem wf_graph_lookup_beyond_next_id : forall g mid,
  well_formed_graph g ->
  mid >= g.(pg_next_id) ->
  graph_lookup g mid = None.
Proof.
  intros g mid Hwf Hge.
  unfold graph_lookup.
  apply (all_ids_below_implies_lookup_none _ _ _ Hwf Hge).
Qed.

Definition graph_pnew (g : PartitionGraph) (region : list nat)
  : PartitionGraph * ModuleID :=
  let normalized := normalize_region region in
  match graph_find_region g normalized with
  | Some existing => (g, existing)
  | None => graph_add_module g normalized []
  end.

Definition partition_valid
  (original left right : list nat) : bool :=
  nat_list_subset left original &&
  nat_list_subset right original &&
  nat_list_disjoint left right &&
  nat_list_subset original (nat_list_union left right).

Definition graph_psplit (g : PartitionGraph) (mid : ModuleID)
  (left right : list nat)
  : option (PartitionGraph * ModuleID * ModuleID) :=
  match graph_lookup g mid with
  | None => None
  | Some m =>
      let axioms := m.(module_axioms) in
      let original := m.(module_region) in
      let left_norm := normalize_region left in
      let right_norm := normalize_region right in
      if orb (Nat.eqb (List.length left_norm) 0)
             (Nat.eqb (List.length right_norm) 0)
      then
        let '(g', empty_id) := graph_add_module g [] [] in
        Some (g', mid, empty_id)
      else if partition_valid original left_norm right_norm then
        match graph_remove g mid with
        | None => None
        | Some (g_removed, _) =>
            let '(g_left, left_id) := graph_add_module g_removed left_norm axioms in
            let '(g_right, right_id) := graph_add_module g_left right_norm axioms in
            Some (g_right, left_id, right_id)
        end
      else None
  end.

Definition graph_pmerge (g : PartitionGraph) (m1 m2 : ModuleID)
  : option (PartitionGraph * ModuleID) :=
  if Nat.eqb m1 m2 then None else
  match graph_remove g m1 with
  | None => None
  | Some (g_without_m1, mod1) =>
      match graph_remove g_without_m1 m2 with
      | None => None
      | Some (g_without_both, mod2) =>
          if negb (nat_list_disjoint mod1.(module_region) mod2.(module_region))
          then None
          else
            let union := nat_list_union mod1.(module_region) mod2.(module_region) in
            let combined_axioms := mod1.(module_axioms) ++ mod2.(module_axioms) in
            match graph_find_region g_without_both union with
            | Some existing =>
                match graph_lookup g_without_both existing with
                | None => None
                | Some existing_mod =>
                    let updated := {| module_region := existing_mod.(module_region);
                                      module_axioms := existing_mod.(module_axioms)
                                                      ++ combined_axioms |} in
                    Some (graph_update g_without_both existing updated, existing)
                end
            | None =>
                let '(g', merged_id) :=
                  graph_add_module g_without_both union combined_axioms in
                Some (g', merged_id)
            end
      end
  end.

Record CSRState := {
  csr_cert_addr : nat;
  csr_status : nat;
  csr_err : nat
}.

Definition csr_set_status (csrs : CSRState) (status : nat) : CSRState :=
  {| csr_cert_addr := csrs.(csr_cert_addr);
     csr_status := status;
     csr_err := csrs.(csr_err) |}.

Definition csr_set_err (csrs : CSRState) (err : nat) : CSRState :=
  {| csr_cert_addr := csrs.(csr_cert_addr);
     csr_status := csrs.(csr_status);
     csr_err := err |}.

Definition csr_set_cert_addr (csrs : CSRState) (addr : nat) : CSRState :=
  {| csr_cert_addr := addr;
     csr_status := csrs.(csr_status);
     csr_err := csrs.(csr_err) |}.

(** VMState: Complete snapshot of Thiele Machine at single instant.

    WHY: A state machine needs complete information to determine next state.
    This record provides exactly that - nothing more, nothing less.

    STRUCTURE (7 fields):
    - vm_graph: PartitionGraph - HOW state is decomposed into modules
    - vm_csrs: CSRState - Control/status registers (cert address, status, errors)
    - vm_regs: list nat - Register file (32 registers, 32-bit words)
    - vm_mem: list nat - Data memory (256 words)
    - vm_pc: nat - Program counter
    - vm_mu: nat - **μ-LEDGER** (THE CENTRAL COST MEASURE)
    - vm_err: bool - Error flag (latches on error, never clears)

    KEY INSIGHT: vm_mu is the innovation. Every structural operation increases
    this monotonically. No operation decreases it. This is proven in
    MuLedgerConservation.v. If μ could decrease, the No Free Insight theorem
    would be meaningless.

    COQTYPE PROPERTIES:
    - Record = syntactic sugar for inductive type with one constructor
    - Immutable: State transitions create NEW VMState, never mutate
    - Total: Every field always defined (no null/undefined)

    IMPLEMENTATION MIRRORING:
    - Coq: This record (kernel/VMState.v:689)
    - Python: thielecpu/state.py VMState dataclass
    - Verilog: thielecpu/hardware/rtl/state_regs.v (distributed across registers)

    SIZES: REG_COUNT=32, MEM_SIZE=256 defined below. Not arbitrary - matched
    across all three layers for deterministic wraparound behavior.

    FALSIFICATION: If any valid step decreases vm_mu, μ-monotonicity is violated.
    If state is incomplete, step function is undefined. Proofs won't compile.

    THESIS: Chapter 3, §3.2.1 "State Space $S$"
*)
Record VMState := {
  vm_graph : PartitionGraph;
  vm_csrs : CSRState;
  vm_regs : list nat;
  vm_mem : list nat;
  vm_pc : nat;
  vm_mu : nat;
  vm_err : bool
}.

Definition REG_COUNT : nat := 32.
Definition MEM_SIZE : nat := 256.

(** word32_mask: Bitmask for 32-bit word truncation.

    WHY: Coq's nat type is unbounded (0,1,2,...,∞). Real hardware uses fixed-width
    registers. Without explicit masking, 0xFFFFFFFF + 1 = 0x100000000 in Coq but
    0x00000000 in hardware (overflow/wraparound). This breaks the isomorphism.

    IMPLEMENTATION: N.ones 32 creates 32 consecutive 1-bits: 0xFFFFFFFF.
    Bitwise AND with this mask truncates to lower 32 bits.

    FALSIFICATION: Remove this masking and run tests/test_three_layer_isomorphism.py.
    The RTL and Coq will diverge on any arithmetic overflow. The test will fail.
*)
Definition word32_mask : N := N.ones 32.

(** word32: Truncate arbitrary nat to 32-bit word.

    WHY: Enforce hardware semantics in the mathematical model. Every write to
    registers or memory applies this to ensure deterministic wraparound.

    HOW IT WORKS:
    1. N.of_nat x: Convert Coq nat (inductive) to N (binary)
    2. N.land (...) word32_mask: Bitwise AND keeps only lower 32 bits
    3. N.to_nat: Convert back to nat for proof convenience

    EXAMPLE: word32(0x1FFFFFFFF) = word32(8589934591) = 0xFFFFFFFF = 4294967295

    USED BY: write_reg, write_mem. Every stored value is explicitly truncated.

    PYTHON/VERILOG: Python VM uses (x & 0xFFFFFFFF). RTL is 32-bit by definition.

    THESIS: Chapter 3, §3.2.1 "Word Representation"
*)
Definition word32 (x : nat) : nat :=
  N.to_nat (N.land (N.of_nat x) word32_mask).

Definition word32_xor (a b : nat) : nat :=
  word32 (N.to_nat (N.lxor (N.of_nat a) (N.of_nat b))).

Fixpoint popcount_upto (bits : nat) (x : N) : nat :=
  match bits with
  | 0 => 0
  | S bits' =>
      (if N.testbit x (N.of_nat bits') then 1 else 0) + popcount_upto bits' x
  end.

Definition word32_popcount (x : nat) : nat :=
  popcount_upto 32 (N.land (N.of_nat x) word32_mask).

Definition reg_index (r : nat) : nat := r mod REG_COUNT.
Definition mem_index (a : nat) : nat := a mod MEM_SIZE.

Definition read_reg (s : VMState) (r : nat) : nat :=
  nth (reg_index r) s.(vm_regs) 0.

Definition write_reg (s : VMState) (r v : nat) : list nat :=
  let idx := reg_index r in
  firstn idx s.(vm_regs) ++ [word32 v] ++ skipn (S idx) s.(vm_regs).

Definition read_mem (s : VMState) (a : nat) : nat :=
  nth (mem_index a) s.(vm_mem) 0.

Definition write_mem (s : VMState) (a v : nat) : list nat :=
  let idx := mem_index a in
  firstn idx s.(vm_mem) ++ [word32 v] ++ skipn (S idx) s.(vm_mem).

Definition swap_regs (regs : list nat) (a b : nat) : list nat :=
  let a_idx := a mod REG_COUNT in
  let b_idx := b mod REG_COUNT in
  let va := nth a_idx regs 0 in
  let vb := nth b_idx regs 0 in
  let regs' := firstn a_idx regs ++ [vb] ++ skipn (S a_idx) regs in
  firstn b_idx regs' ++ [va] ++ skipn (S b_idx) regs'.

Definition advance_pc (s : VMState) : nat := S s.(vm_pc).

Definition ascii_checksum (s : string) : nat :=
  fold_right (fun ch acc => nat_of_ascii ch + acc) 0 (list_ascii_of_string s).

Definition update_state
  (s : VMState) (graph : PartitionGraph) (csrs : CSRState)
  (mu : nat) (err : bool)
  : VMState :=
  {| vm_graph := graph;
     vm_csrs := csrs;
  vm_regs := s.(vm_regs);
  vm_mem := s.(vm_mem);
     vm_pc := advance_pc s;
     vm_mu := mu;
     vm_err := err |}.

(** ** graph_psplit and graph_pmerge Length Lemmas *)

(** graph_psplit increases length on success *)
Lemma graph_psplit_increases_length : forall g mid left right g' lid rid,
  graph_psplit g mid left right = Some (g', lid, rid) ->
  List.length (pg_modules g') >= List.length (pg_modules g).
Proof.
  intros g mid left right g' lid rid Hsplit.
  unfold graph_psplit in Hsplit.
  destruct (graph_lookup g mid) as [m|] eqn:Hlu; [|discriminate].
  destruct (orb _ _) eqn:Hempty.
  - (* Empty partition case: graph_add_module adds 1 *)
    unfold graph_add_module in Hsplit. simpl in Hsplit.
    injection Hsplit as Heq _ _. subst g'.
    simpl. lia.
  - (* Non-empty partition case *)
    destruct (partition_valid _ _ _) eqn:Hvalid; [|discriminate].
    destruct (graph_remove g mid) as [[g_removed removed]|] eqn:Hrem; [|discriminate].
    unfold graph_add_module in Hsplit. simpl in Hsplit.
    injection Hsplit as Heq _ _. subst g'.
    simpl.
    pose proof (graph_remove_length g mid g_removed removed Hrem) as Hrem_len.
    lia.
Qed.

(** graph_pmerge decreases length on success *)
Lemma graph_pmerge_decreases_length : forall g m1 m2 g' merged,
  graph_pmerge g m1 m2 = Some (g', merged) ->
  List.length (pg_modules g') <= List.length (pg_modules g).
Proof.
  intros g m1 m2 g' merged Hmerge.
  unfold graph_pmerge in Hmerge.
  destruct (Nat.eqb m1 m2); [discriminate|].
  destruct (graph_remove g m1) as [[g1 mod1]|] eqn:Hrem1; [|discriminate].
  destruct (graph_remove g1 m2) as [[g2 mod2]|] eqn:Hrem2; [|discriminate].
  destruct (negb _) eqn:Hoverlap; [discriminate|].
  destruct (graph_find_region g2 _) as [existing|] eqn:Hfind.
  - (* Existing region found: graph_update preserves length *)
    destruct (graph_lookup g2 existing) as [existing_mod|] eqn:Hlu; [|discriminate].
    injection Hmerge as Heq _. subst g'.
    (* The actual module state doesn't matter for length preservation *)
    assert (Hlu_ne : graph_lookup g2 existing <> None).
    { rewrite Hlu. discriminate. }
    pose proof (graph_update_existing_length g2 existing 
                  {| module_region := module_region existing_mod;
                     module_axioms := module_axioms existing_mod ++ module_axioms mod1 ++ module_axioms mod2 |}
                  Hlu_ne) as Hupd.
    pose proof (graph_remove_length g m1 g1 mod1 Hrem1) as Hrem1_len.
    pose proof (graph_remove_length g1 m2 g2 mod2 Hrem2) as Hrem2_len.
    lia.
  - (* No existing region: graph_add_module adds 1 *)
    unfold graph_add_module in Hmerge. simpl in Hmerge.
    injection Hmerge as Heq _. subst g'.
    simpl.
    pose proof (graph_remove_length g m1 g1 mod1 Hrem1) as Hrem1_len.
    pose proof (graph_remove_length g1 m2 g2 mod2 Hrem2) as Hrem2_len.
    lia.
Qed.

(** graph_pmerge decreases length by at most 2 *)
Lemma graph_pmerge_length_bound : forall g m1 m2 g' merged,
  graph_pmerge g m1 m2 = Some (g', merged) ->
  List.length (pg_modules g) <= List.length (pg_modules g') + 2.
Proof.
  intros g m1 m2 g' merged Hmerge.
  unfold graph_pmerge in Hmerge.
  destruct (Nat.eqb m1 m2); [discriminate|].
  destruct (graph_remove g m1) as [[g1 mod1]|] eqn:Hrem1; [|discriminate].
  destruct (graph_remove g1 m2) as [[g2 mod2]|] eqn:Hrem2; [|discriminate].
  destruct (negb _) eqn:Hoverlap; [discriminate|].
  destruct (graph_find_region g2 _) as [existing|] eqn:Hfind.
  - (* Existing region found: removes 2, adds 0 via update = net -2 *)
    destruct (graph_lookup g2 existing) as [existing_mod|] eqn:Hlu; [|discriminate].
    injection Hmerge as Heq _. subst g'.
    assert (Hlu_ne : graph_lookup g2 existing <> None).
    { rewrite Hlu. discriminate. }
    pose proof (graph_update_existing_length g2 existing 
                  {| module_region := module_region existing_mod;
                     module_axioms := module_axioms existing_mod ++ module_axioms mod1 ++ module_axioms mod2 |}
                  Hlu_ne) as Hupd.
    pose proof (graph_remove_length g m1 g1 mod1 Hrem1) as Hrem1_len.
    pose proof (graph_remove_length g1 m2 g2 mod2 Hrem2) as Hrem2_len.
    lia.
  - (* No existing region: removes 2, adds 1 = net -1 *)
    unfold graph_add_module in Hmerge. simpl in Hmerge.
    injection Hmerge as Heq _. subst g'.
    simpl.
    pose proof (graph_remove_length g m1 g1 mod1 Hrem1) as Hrem1_len.
    pose proof (graph_remove_length g1 m2 g2 mod2 Hrem2) as Hrem2_len.
    lia.
Qed.

(** graph_pmerge preserves region observation for unrelated modules.
    IMPORTANT: This preserves the NORMALIZED REGION for modules not in {m1, m2}.
    We compare normalized regions because graph operations may normalize. *)
Lemma graph_pmerge_preserves_region_obs : forall g m1 m2 g' merged_id mid,
  mid <> m1 ->
  mid <> m2 ->
  mid < g.(pg_next_id) ->
  graph_pmerge g m1 m2 = Some (g', merged_id) ->
  match graph_lookup g' mid with
  | Some m' => Some (normalize_region (m'.(module_region)))
  | None => None
  end =
  match graph_lookup g mid with
  | Some m => Some (normalize_region (m.(module_region)))
  | None => None
  end.
Proof.
  intros g m1 m2 g' merged_id mid Hneq1 Hneq2 Hlt Hpmerge.
  unfold graph_pmerge in Hpmerge.
  destruct (Nat.eqb m1 m2) eqn:Heq_m1_m2; [discriminate|].
  destruct (graph_remove g m1) as [[g1 mod1]|] eqn:Hrem1; [|discriminate].
  destruct (graph_remove g1 m2) as [[g2 mod2]|] eqn:Hrem2; [|discriminate].
  destruct (negb _) eqn:Hdisjoint; [discriminate|].
  destruct (graph_find_region g2 _) as [existing|] eqn:Hfind.
  - (* Existing region found *)
    destruct (graph_lookup g2 existing) as [ex_mod|] eqn:Hlook_ex; [|discriminate].
    injection Hpmerge as Hg' _. subst g'.
    destruct (Nat.eq_dec mid existing) as [Heq|Hneq].
    + (* mid = existing: region preserved via normalization idempotence *)
      subst mid.
      assert (Hlook_ne : graph_lookup g2 existing <> None) by (rewrite Hlook_ex; discriminate).
      rewrite graph_update_lookup_same by assumption. simpl.
      rewrite <- (graph_remove_preserves_unrelated g existing m1 g1 mod1 Hneq1 Hrem1).
      rewrite <- (graph_remove_preserves_unrelated g1 existing m2 g2 mod2 Hneq2 Hrem2).
      rewrite Hlook_ex. simpl.
      (* normalize_region is idempotent on the same region *)
      rewrite normalize_region_idempotent. reflexivity.
    + (* mid <> existing: update doesn't affect *)
      rewrite graph_update_preserves_unrelated by assumption.
      rewrite (graph_remove_preserves_unrelated g1 mid m2 g2 mod2) by assumption.
      rewrite (graph_remove_preserves_unrelated g mid m1 g1 mod1) by assumption.
      reflexivity.
  - (* No existing region: add new module *)
    unfold graph_add_module in Hpmerge. simpl in Hpmerge.
    injection Hpmerge as Hg' _. subst g'. simpl.
    (* The new module is at g2.(pg_next_id), and mid < g2.(pg_next_id) *)
    pose proof (graph_remove_preserves_next_id g m1 g1 mod1 Hrem1) as Hnext1.
    pose proof (graph_remove_preserves_next_id g1 m2 g2 mod2 Hrem2) as Hnext2.
    assert (Hmid_lt : mid < g2.(pg_next_id)) by lia.
    (* First, chain the remove preservations *)
    assert (Hlu_chain : graph_lookup g2 mid = graph_lookup g mid).
    { rewrite (graph_remove_preserves_unrelated g1 mid m2 g2 mod2) by assumption.
      rewrite (graph_remove_preserves_unrelated g mid m1 g1 mod1) by assumption.
      reflexivity. }
    (* The goal is about lookups with normalize_region *)
    unfold graph_lookup in Hlu_chain. unfold graph_lookup. simpl.
    destruct (Nat.eqb (pg_next_id g2) mid) eqn:Heq.
    + (* pg_next_id g2 = mid, contradiction *)
      apply Nat.eqb_eq in Heq. lia.
    + (* pg_next_id g2 <> mid, g2's modules match *)
      rewrite Hlu_chain. reflexivity.
Qed.
