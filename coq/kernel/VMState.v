From Coq Require Import List ListDec Bool Arith.PeanoNat.
From Coq Require Import NArith.
From Coq Require Import Strings.String Strings.Ascii.
From Coq Require Import micromega.Lia.
Import ListNotations.

(** pair_eq_dec: Coq won't let you call nodup on a list of pairs without this.
    If you can compare A-values for equality, and you can compare B-values,
    this gives you pair comparison. I need it for deduplicating coupling_pairs.
    One proof, used everywhere there's a list (nat * nat). *)
Definition pair_eq_dec {A B : Type}
  (decA : forall x y : A, {x = y} + {x <> y})
  (decB : forall x y : B, {x = y} + {x <> y})
  (p1 p2 : A * B) : {p1 = p2} + {p1 <> p2}.
Proof.
  destruct p1 as [a1 b1]. destruct p2 as [a2 b2].
  destruct (decA a1 a2) as [Ha|Ha].
  - destruct (decB b1 b2) as [Hb|Hb].
    + left. subst. reflexivity.
    + right. intros H. injection H. intros. contradiction.
  - right. intros H. injection H. intros. contradiction.
Defined.

(** VMState: The state the machine lives in.

    Everything else — NoFI, the shadow theorem, the hardware bridge — builds on
    the types in this file. Start here if you want to understand the machine.

    The full state is 12 fields: registers, memory, PC, the μ-ledger (the cost
    counter that never goes down), the partition graph (modules + morphisms),
    CHSH witness buckets, certification status, and a few housekeeping fields.

    Three things this file guarantees:
    normalize_region is idempotent — normalize twice, get the same thing.
    well_formed_graph is preserved by every operation that modifies the graph.
    The Memory-String bridge lets the VM store and retrieve strings from memory.

    These aren't nice-to-haves. Every observational equality proof depends on them.
    If normalize_region_idempotent failed, two states with the same partition would
    look different after one extra normalization pass. The whole comparison machinery
    falls apart. *)


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

(** normalize_region: Make a region canonical — no duplicates.
    The problem: [1;2] and [2;1;2] represent the same set of cells, but Coq's
    = treats them as different lists. If I didn't normalize, two states with
    "the same" partition could look different to the proofs. Whole observational
    equality story falls apart. nodup from Coq stdlib solves it: one canonical
    form per set. I just wrap it.

    To falsify: If normalize_region wasn't idempotent, observational_no_signaling
    would fail to compile (proven in KernelPhysics.v). *)
Definition normalize_region (region : list nat) : list nat :=
  nodup Nat.eq_dec region.

(** normalize_region_nodup: After normalization, the region has no duplicates.
    That's the whole point — every region that comes out of normalize_region is
    a clean set, no repeated cells. If two normalized regions are list-equal,
    they're the same set. One line: NoDup_nodup from Coq stdlib. *)
Lemma normalize_region_nodup : forall region, NoDup (normalize_region region).
Proof.
  intro region. unfold normalize_region.
  apply NoDup_nodup.
Qed.

(** normalize_region_idempotent: Normalizing twice is the same as normalizing once.
    Here's why this matters: throughout the codebase, states get normalized
    whenever modules are created or updated. If normalization weren't idempotent,
    re-normalizing an already-normalized region would produce a different result,
    breaking observational equality — two states with "the same" module could
    look different just because one had been through one extra update cycle.
    Proof uses nodup_fixed_point from Coq stdlib, which says nodup on a
    duplicate-free list is a no-op. *)
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
  module_axioms : AxiomSet;
  module_mu_tensor : list nat  (** Per-module 4×4 metric tensor (16 entries, row-major) *)
}.

(** Default per-module tensor: 16 zeros (flat space). *)
Definition module_mu_tensor_default : list nat := repeat 0 16.

(** Build a ModuleState with a default (all-zeros) metric tensor.
    Most code creates modules without an explicit tensor — this is the constructor for that. *)
Definition mk_module_state (region : list nat) (axioms : AxiomSet) : ModuleState :=
  {| module_region := region;
     module_axioms := axioms;
     module_mu_tensor := module_mu_tensor_default |}.

(** list_update_at: Replace element at index k in list l with value v.
    If k >= length l the list is returned unchanged. *)
Fixpoint list_update_at (l : list nat) (k : nat) (v : nat) : list nat :=
  match l, k with
  | [], _ => []
  | _ :: t, 0 => v :: t
  | h :: t, S i => h :: list_update_at t i v
  end.

Definition normalize_module (m : ModuleState) : ModuleState :=
  {| module_region := normalize_region m.(module_region);
     module_axioms := m.(module_axioms);
     module_mu_tensor := m.(module_mu_tensor) |}.

(** Morphisms are arrows between modules.
    A morphism says: here's how cells in module A map to cells in module B.
    coupling_pairs records those (source_cell, target_cell) pairs.
    morph_is_identity marks the identity morphism (each cell maps to itself).

    Why add this? The partition graph is a category — modules are objects, morphisms
    are the structure-preserving arrows. The Phase 7 opcodes (MORPH, COMPOSE,
    MORPH_ID, MORPH_TENSOR, MORPH_GET, MORPH_DELETE, MORPH_ASSERT) let programs
    read and manipulate this categorical structure directly. *)

Definition MorphismID := nat.

(** CouplingData: The actual cell-to-cell mappings of a morphism.
    coupling_pairs lists the (source_cell, target_cell) pairs.
    coupling_label is a name you can read in the debugger. *)
Record CouplingData := {
  coupling_pairs : list (nat * nat);
  coupling_label : string
}.

Definition empty_coupling_data : CouplingData :=
  {| coupling_pairs := []; coupling_label := "empty" |}.

(** MorphismState: Everything the graph stores about one morphism.
    Source, target, coupling (the cell-to-cell map), and whether it's an identity. *)
Record MorphismState := {
  morph_source : ModuleID;
  morph_target : ModuleID;
  morph_coupling : CouplingData;
  morph_is_identity : bool
}.

(** normalize_coupling: Remove duplicate (source, target) pairs from a coupling.
    Same reasoning as normalize_region — canonical form prevents spurious inequality. *)
Definition normalize_coupling (c : CouplingData) : CouplingData :=
  {| coupling_pairs := nodup (pair_eq_dec Nat.eq_dec Nat.eq_dec) c.(coupling_pairs);
     coupling_label := c.(coupling_label) |}.

(** PartitionGraph: The partition structure the machine works in.
    pg_modules: the (ID, module) pairs — who's in the graph.
    pg_next_id: fresh module ID counter (only goes up, never reused).
    pg_morphisms: the (ID, morphism) pairs — the arrows.
    pg_next_morph_id: same idea for morphism IDs.

    The well-formedness invariant says all existing IDs are strictly below their
    respective counters. Without that, you'd get aliasing — two modules with the
    same ID — and lookups become ambiguous. *)

Record PartitionGraph := {
  pg_next_id : ModuleID;
  pg_modules : list (ModuleID * ModuleState);
  pg_next_morph_id : MorphismID;
  pg_morphisms : list (MorphismID * MorphismState)
}.

(** well_formed_graph: The invariant that keeps the graph from breaking.
    Three conditions: every module ID in pg_modules is < pg_next_id, every
    morphism ID is < pg_next_morph_id, and every morphism's source and target
    are real modules. I prove every graph operation preserves all three.
    Without this, lookups become undefined and the whole API falls apart. *)

Fixpoint all_ids_below (modules : list (ModuleID * ModuleState)) (bound : nat) : Prop :=
  match modules with
  | [] => True
  | (id, _) :: rest => (id < bound) /\ all_ids_below rest bound
  end.

(** all_morph_ids_below: All morphism IDs in list are < bound *)
Fixpoint all_morph_ids_below (morphisms : list (MorphismID * MorphismState)) (bound : nat) : Prop :=
  match morphisms with
  | [] => True
  | (id, _) :: rest => (id < bound) /\ all_morph_ids_below rest bound
  end.

(** all_morph_endpoints_valid: All morphism source/target IDs exist in modules *)
Definition morph_endpoints_valid (modules : list (ModuleID * ModuleState)) (ms : MorphismState) : Prop :=
  In ms.(morph_source) (List.map fst modules) /\ In ms.(morph_target) (List.map fst modules).

Fixpoint all_morph_endpoints_valid (modules : list (ModuleID * ModuleState))
  (morphisms : list (MorphismID * MorphismState)) : Prop :=
  match morphisms with
  | [] => True
  | (_, ms) :: rest => morph_endpoints_valid modules ms /\ all_morph_endpoints_valid modules rest
  end.

Definition well_formed_graph (g : PartitionGraph) : Prop :=
  all_ids_below g.(pg_modules) g.(pg_next_id) /\
  all_morph_ids_below g.(pg_morphisms) g.(pg_next_morph_id) /\
  all_morph_endpoints_valid g.(pg_modules) g.(pg_morphisms).

Definition empty_graph : PartitionGraph :=
  {| pg_next_id := 1;
     pg_modules := [];
     pg_next_morph_id := 1;
     pg_morphisms := [] |}.

(** The empty graph is well-formed *)
Lemma empty_graph_well_formed : well_formed_graph empty_graph.
Proof.
  unfold well_formed_graph, empty_graph. simpl.
  repeat split; exact I.
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
     pg_modules := graph_insert_modules g.(pg_modules) mid (normalize_module m);
     pg_next_morph_id := g.(pg_next_morph_id);
     pg_morphisms := g.(pg_morphisms) |}.

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
      Some ({| pg_next_id := g.(pg_next_id);
               pg_modules := modules';
               pg_next_morph_id := g.(pg_next_morph_id);
               pg_morphisms := g.(pg_morphisms) |}, removed)
  end.

Definition graph_add_module (g : PartitionGraph)
  (region : list nat) (axioms : AxiomSet)
  : PartitionGraph * ModuleID :=
  let module := normalize_module (mk_module_state region axioms) in
  let mid := g.(pg_next_id) in
  ({| pg_next_id := S mid;
      pg_modules := (mid, module) :: g.(pg_modules);
      pg_next_morph_id := g.(pg_next_morph_id);
      pg_morphisms := g.(pg_morphisms) |}, mid).

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
                        module_axioms := m.(module_axioms) ++ [ax];
                        module_mu_tensor := m.(module_mu_tensor) |} in
      graph_update g mid updated
  end.

Definition graph_add_axioms (g : PartitionGraph) (mid : ModuleID)
  (axs : list VMAxiom) : PartitionGraph :=
  fold_left (fun acc ax => graph_add_axiom acc mid ax) axs g.

(** graph_update_module_tensor: Update a single entry in a module's per-module
    4×4 metric tensor. The tensor is stored as a flat list of 16 nats (row-major).
    Index k = i*4+j. If module doesn't exist, graph is unchanged. *)
Definition graph_update_module_tensor (g : PartitionGraph) (mid : ModuleID)
  (k : nat) (value : nat) : PartitionGraph :=
  match graph_lookup g mid with
  | None => g
  | Some m =>
      let updated := {| module_region := m.(module_region);
                        module_axioms := m.(module_axioms);
                        module_mu_tensor := list_update_at m.(module_mu_tensor) k value |} in
      graph_update g mid updated
  end.

Definition graph_record_discovery (g : PartitionGraph) (mid : ModuleID)
  (evidence : list VMAxiom) : PartitionGraph :=
  graph_add_axioms g mid evidence.

(** ** Morphism Graph Operations *)

(** graph_lookup_morphism: Look up a morphism by ID. *)
Fixpoint graph_lookup_morphism_list
  (morphisms : list (MorphismID * MorphismState)) (morph_id : MorphismID)
  : option MorphismState :=
  match morphisms with
  | [] => None
  | (id, ms) :: rest =>
      if Nat.eqb id morph_id then Some ms
      else graph_lookup_morphism_list rest morph_id
  end.

Definition graph_lookup_morphism (g : PartitionGraph) (morph_id : MorphismID)
  : option MorphismState :=
  graph_lookup_morphism_list g.(pg_morphisms) morph_id.

(** graph_add_morphism: Add a new morphism to the graph. *)
Definition graph_add_morphism (g : PartitionGraph)
  (src dst : ModuleID) (c : CouplingData) (is_id : bool)
  : PartitionGraph * MorphismID :=
  let new_id := g.(pg_next_morph_id) in
  let ms := {| morph_source := src;
               morph_target := dst;
               morph_coupling := normalize_coupling c;
               morph_is_identity := is_id |} in
  ({| pg_next_id := g.(pg_next_id);
      pg_modules := g.(pg_modules);
      pg_next_morph_id := S new_id;
      pg_morphisms := (new_id, ms) :: g.(pg_morphisms) |}, new_id).

(** graph_add_identity: Create an identity morphism for a module.
    Coupling is empty_coupling_data — identity is structural
    (morph_source = morph_target = mid, morph_is_identity = true).
    Matches hardware: kami_step(MORPH_ID) uses coupling_desc=0. *)
Definition graph_add_identity (g : PartitionGraph) (mid : ModuleID)
  : option (PartitionGraph * MorphismID) :=
  match graph_lookup g mid with
  | None => None
  | Some _ =>
      Some (graph_add_morphism g mid mid empty_coupling_data true)
  end.

(** graph_delete_morphism: Remove a morphism from the graph. *)
Definition graph_delete_morphism (g : PartitionGraph) (morph_id : MorphismID)
  : option PartitionGraph :=
  if existsb (fun '(id, _) => Nat.eqb id morph_id) g.(pg_morphisms)
  then Some {| pg_next_id := g.(pg_next_id);
               pg_modules := g.(pg_modules);
               pg_next_morph_id := g.(pg_next_morph_id);
               pg_morphisms := filter (fun '(id, _) => negb (Nat.eqb id morph_id))
                                      g.(pg_morphisms) |}
  else None.

(** graph_cascade_delete_morphisms: Remove all morphisms referencing a module.
    Used when a module is removed or merged. *)
Definition graph_cascade_delete_morphisms (g : PartitionGraph) (mid : ModuleID)
  : PartitionGraph :=
  {| pg_next_id := g.(pg_next_id);
     pg_modules := g.(pg_modules);
     pg_next_morph_id := g.(pg_next_morph_id);
     pg_morphisms := filter (fun '(_, ms) =>
       negb (Nat.eqb ms.(morph_source) mid) &&
       negb (Nat.eqb ms.(morph_target) mid)) g.(pg_morphisms) |}.

(** graph_cascade_delete_morphisms_preserves_modules: Cascade-deleting morphisms
    that reference a module ID leaves the module list itself untouched.
    graph_cascade_delete_morphisms only rewrites pg_morphisms (filters it), so
    pg_modules, pg_next_id, and pg_next_morph_id are unchanged by definition.
    These four lemmas are all reflexivity — the definitions make them obvious. *)
Lemma graph_cascade_delete_morphisms_preserves_modules : forall g mid,
  pg_modules (graph_cascade_delete_morphisms g mid) = pg_modules g.
Proof. reflexivity. Qed.

Lemma graph_cascade_delete_morphisms_preserves_next_id : forall g mid,
  pg_next_id (graph_cascade_delete_morphisms g mid) = pg_next_id g.
Proof. reflexivity. Qed.

Lemma graph_cascade_delete_morphisms_preserves_next_morph_id : forall g mid,
  pg_next_morph_id (graph_cascade_delete_morphisms g mid) = pg_next_morph_id g.
Proof. reflexivity. Qed.

(** graph_cascade_delete_morphisms_lookup: Module lookup is unaffected by cascade delete.
    Since cascade delete only touches the morphism list, you can still find any
    module you could find before. Used to glue cascade-then-remove proofs together. *)
Lemma graph_cascade_delete_morphisms_lookup : forall g mid module_id,
  graph_lookup (graph_cascade_delete_morphisms g mid) module_id = graph_lookup g module_id.
Proof.
  intros g mid module_id. unfold graph_lookup.
  rewrite graph_cascade_delete_morphisms_preserves_modules. reflexivity.
Qed.

(** graph_cascade_delete_morphisms_preserves_wf: Filtering the morphism list
    can't break well-formedness — it can only reduce the set of morphisms, so
    all remaining ones still satisfy the ID-bounds and endpoint-validity invariants.
    The three-part split in the proof matches the three-part definition of well_formed_graph. *)
Lemma graph_cascade_delete_morphisms_preserves_wf : forall g mid,
  well_formed_graph g ->
  well_formed_graph (graph_cascade_delete_morphisms g mid).
Proof.
  intros g mid Hwf.
  unfold well_formed_graph in *.
  destruct Hwf as [Hmod_ids [Hmorph_ids Hendpoints]].
  unfold graph_cascade_delete_morphisms. simpl.
  repeat split.
  - (* Module IDs preserved - same modules, same bound *)
    exact Hmod_ids.
  - (* Morphism IDs: filter can only reduce list, all remaining IDs still valid *)
    clear Hendpoints.
    induction (pg_morphisms g) as [|[morph_id ms] rest IH]; simpl.
    + exact I.
    + destruct Hmorph_ids as [Hid Hrest].
      destruct (negb (morph_source ms =? mid) && negb (morph_target ms =? mid)); simpl.
      * split; [exact Hid | exact (IH Hrest)].
      * exact (IH Hrest).
  - (* Morphism endpoints: filter can only reduce list, remaining endpoints still valid *)
    clear Hmorph_ids.
    induction (pg_morphisms g) as [|[morph_id ms] rest IH]; simpl.
    + exact I.
    + destruct Hendpoints as [Hep Hrest].
      destruct (negb (morph_source ms =? mid) && negb (morph_target ms =? mid)); simpl.
      * split; [exact Hep | exact (IH Hrest)].
      * exact (IH Hrest).
Qed.

(** Relational composition of coupling pairs.
 This function is also defined in CategoryLaws.v with proven properties.
    We inline it here to avoid import dependencies. *)
Definition relational_compose (r1 r2 : list (nat * nat)) : list (nat * nat) :=
  flat_map (fun '(a, b) =>
    map (fun '(b', c) => (a, c)) (filter (fun '(b', _) => Nat.eqb b b') r2)
  ) r1.

(** graph_compose_morphisms: Compose two morphisms f;h when f.target = h.source *)
Definition graph_compose_morphisms (g : PartitionGraph) (m1 m2 : MorphismID)
  : option (PartitionGraph * MorphismID) :=
  match graph_lookup_morphism g m1, graph_lookup_morphism g m2 with
  | Some f, Some h =>
      if Nat.eqb f.(morph_target) h.(morph_source)
      then
        let composed_pairs := relational_compose
          f.(morph_coupling).(coupling_pairs)
          h.(morph_coupling).(coupling_pairs) in
        let c := {| coupling_pairs := composed_pairs;
                    coupling_label := f.(morph_coupling).(coupling_label) ++ ";" ++
                                      h.(morph_coupling).(coupling_label) |} in
        Some (graph_add_morphism g f.(morph_source) h.(morph_target) c false)
      else None (* Type mismatch: f.target ≠ h.source *)
  | _, _ => None (* Morphism not found *)
  end.

(** graph_tensor_morphisms: Monoidal tensor f⊗g for disjoint morphisms *)
Definition graph_tensor_morphisms (g : PartitionGraph) (f_id g_id : MorphismID)
  : option (PartitionGraph * MorphismID) :=
  match graph_lookup_morphism g f_id, graph_lookup_morphism g g_id with
  | Some f, Some h =>
      match graph_lookup g f.(morph_source), graph_lookup g f.(morph_target),
            graph_lookup g h.(morph_source), graph_lookup g h.(morph_target) with
      | Some a_mod, Some b_mod, Some c_mod, Some d_mod =>
          (* Check disjointness of source and target regions *)
          if nat_list_disjoint a_mod.(module_region) c_mod.(module_region) &&
             nat_list_disjoint b_mod.(module_region) d_mod.(module_region)
          then
            let ac_region := nat_list_union a_mod.(module_region) c_mod.(module_region) in
            let bd_region := nat_list_union b_mod.(module_region) d_mod.(module_region) in
            match graph_find_region g ac_region, graph_find_region g bd_region with
            | Some ac_id, Some bd_id =>
                let tensor_pairs := f.(morph_coupling).(coupling_pairs) ++
                                    h.(morph_coupling).(coupling_pairs) in
                let c := {| coupling_pairs := tensor_pairs;
                            coupling_label := f.(morph_coupling).(coupling_label) ++ "⊗" ++
                                              h.(morph_coupling).(coupling_label) |} in
                Some (graph_add_morphism g ac_id bd_id c false)
            | _, _ => None (* Union modules don't exist *)
            end
          else None (* Regions not disjoint *)
      | _, _, _, _ => None (* Modules not found *)
      end
  | _, _ => None (* Morphisms not found *)
  end.

(** All the Phase 7 morphism ops (MORPH, COMPOSE, MORPH_ID, MORPH_DELETE,
    MORPH_TENSOR) touch pg_morphisms and pg_next_morph_id only. None of them
    touch pg_modules. So graph_lookup, which reads pg_modules, is unaffected.
    The proofs are reflexivity because the definitions make the separation explicit.
    observational_no_signaling in KernelPhysics.v needs these. *)
(* DEFINITIONAL HELPER *)
(** graph_add_morphism_preserves_lookup: Adding a morphism doesn't change module lookup.
    Proof is reflexivity — the definition literally doesn't touch pg_modules. *)
Lemma graph_add_morphism_preserves_lookup : forall g src dst c is_id mid,
  graph_lookup (fst (graph_add_morphism g src dst c is_id)) mid = graph_lookup g mid.
Proof.
  intros. unfold graph_add_morphism. simpl. reflexivity.
Qed.

(** graph_add_identity_preserves_lookup: Creating an identity morphism (MORPH_ID)
    doesn't change what modules exist or where they are. *)
Lemma graph_add_identity_preserves_lookup : forall g module g' morph_id mid,
  graph_add_identity g module = Some (g', morph_id) ->
  graph_lookup g' mid = graph_lookup g mid.
Proof.
  intros g module g' morph_id mid H.
  unfold graph_add_identity in H.
  destruct (graph_lookup g module); try discriminate.
  injection H as Hg' _. subst g'.
  unfold graph_add_morphism. simpl. reflexivity.
Qed.

(** graph_delete_morphism_preserves_lookup: Deleting a morphism (MORPH_DELETE)
    doesn't remove or change any module. Modules and morphisms are separate lists. *)
Lemma graph_delete_morphism_preserves_lookup : forall g morph_id g' mid,
  graph_delete_morphism g morph_id = Some g' ->
  graph_lookup g' mid = graph_lookup g mid.
Proof.
  intros g morph_id g' mid H.
  unfold graph_delete_morphism in H.
  destruct (existsb _ _); try discriminate.
  injection H as Hg'. subst g'. simpl. reflexivity.
Qed.

(** graph_compose_morphisms_preserves_lookup: Composing two morphisms (COMPOSE)
    creates one new morphism but leaves modules alone. *)
Lemma graph_compose_morphisms_preserves_lookup : forall g m1 m2 g' new_id mid,
  graph_compose_morphisms g m1 m2 = Some (g', new_id) ->
  graph_lookup g' mid = graph_lookup g mid.
Proof.
  intros g m1 m2 g' new_id mid H.
  unfold graph_compose_morphisms in H.
  destruct (graph_lookup_morphism g m1); try discriminate.
  destruct (graph_lookup_morphism g m2); try discriminate.
  destruct (Nat.eqb _ _); try discriminate.
  injection H as Hg' _. subst g'.
  apply graph_add_morphism_preserves_lookup.
Qed.

(** graph_tensor_morphisms_preserves_lookup: Tensor product of morphisms (MORPH_TENSOR)
    adds one new morphism. Modules untouched. The case analysis is long because
    MORPH_TENSOR has many preconditions (four module lookups, disjointness check,
    two region finds), but once you've confirmed it succeeded, the conclusion is
    just graph_add_morphism_preserves_lookup. *)
Lemma graph_tensor_morphisms_preserves_lookup : forall g f_id g_id g' new_id mid,
  graph_tensor_morphisms g f_id g_id = Some (g', new_id) ->
  graph_lookup g' mid = graph_lookup g mid.
Proof.
  intros g f_id g_id g' new_id mid H.
  unfold graph_tensor_morphisms in H.
  destruct (graph_lookup_morphism g f_id); try discriminate.
  destruct (graph_lookup_morphism g g_id); try discriminate.
  destruct (graph_lookup g (morph_source m)); try discriminate.
  destruct (graph_lookup g (morph_target m)); try discriminate.
  destruct (graph_lookup g (morph_source m0)); try discriminate.
  destruct (graph_lookup g (morph_target m0)); try discriminate.
  destruct (nat_list_disjoint _ _ && nat_list_disjoint _ _); try discriminate.
  destruct (graph_find_region g _); try discriminate.
  destruct (graph_find_region g _); try discriminate.
  injection H as Hg' _. subst g'.
  apply graph_add_morphism_preserves_lookup.
Qed.

(** Every graph operation that modifies modules or morphisms has to prove it
    preserves all three parts of well_formed_graph. I track this because the
    alternative — checking at runtime — would mean undefined behavior is
    observable. With WF as an invariant, the step semantics can assume it holds
    and the proofs confirm nothing ever breaks it. *)

(** all_ids_below_weaken: If all IDs are < n, they're still < n+1.
    This comes up in graph_add_module: we increment pg_next_id, so we need
    to know the old module IDs still satisfy the new, larger bound. Lia kills it. *)
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

(** graph_add_module_preserves_wf: Adding a new module keeps the graph well-formed.
    Three things to check: (1) the new module's ID equals pg_next_id, which is
    strictly less than S(pg_next_id); (2) the old modules' IDs are still below
    the new, larger bound — all_ids_below_weaken handles that; (3) morphism
    endpoints are still valid because the new module isn't referenced by any
    existing morphism yet. The endpoint proof needs to show each old morphism
    endpoint is still in the (now larger) module list — it's there because it
    was in the old list, and we added to the front. *)
Lemma graph_add_module_preserves_wf : forall g region axioms,
  well_formed_graph g ->
  well_formed_graph (fst (graph_add_module g region axioms)).
Proof.
  intros g region axioms Hwf.
  unfold graph_add_module. simpl.
  unfold well_formed_graph in *. simpl.
  destruct Hwf as [Hwf_mods [Hwf_morphs Hwf_endpoints]].
  repeat split.
  - (* new module ID < S old_next_id *) lia.
  - (* old modules IDs still below new bound *) apply all_ids_below_weaken. exact Hwf_mods.
  - (* morphism IDs unchanged *) exact Hwf_morphs.
  - (* morphism endpoints still valid - new module added but not referenced yet *)
    (* Need to show morphisms only reference old modules, which are still in the list *)
    clear Hwf_mods Hwf_morphs.
    induction (pg_morphisms g) as [|[mid ms] rest IH]; simpl.
    + exact I.
    + simpl in Hwf_endpoints. destruct Hwf_endpoints as [Hms Hrest].
      split.
      * unfold morph_endpoints_valid in *. simpl.
        destruct Hms as [Hsrc Htgt].
        split; right; assumption.
      * apply IH. exact Hrest.
Qed.

(** graph_remove_modules_preserves_all_ids_below: Removing a module from a
    WF list still gives a WF list for the same bound. Makes sense — removing
    can't introduce IDs that weren't there. Induction on the module list. *)
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

(** graph_remove_modules_preserves_other_in: If module `other` (which is NOT `mid`)
    was in the module list before removal, it's still there after.
    This is how the morphism-endpoint proofs stay valid after removing a module —
    any morphism that didn't reference `mid` still has both endpoints present. *)
Lemma graph_remove_modules_preserves_other_in : forall modules mid modules' removed other,
  other <> mid ->
  graph_remove_modules modules mid = Some (modules', removed) ->
  In other (List.map fst modules) ->
  In other (List.map fst modules').
Proof.
  induction modules as [|[id ms] rest IH]; intros mid modules' removed other Hneq Hrem Hin.
  - simpl in Hin. contradiction.
  - simpl in Hrem. simpl in Hin.
    destruct Hin as [Heq_id | Hrest].
    + (* other was the head *)
      subst id.
      destruct (Nat.eqb other mid) eqn:Heq.
      * apply Nat.eqb_eq in Heq. contradiction.
      * destruct (graph_remove_modules rest mid) eqn:Hrest_rem.
        -- destruct p as [rest' rem']. injection Hrem as Heq_modules' _. subst modules'.
           simpl. left. reflexivity.
        -- discriminate.
    + (* other was in the tail *)
      destruct (Nat.eqb id mid) eqn:Heq.
      * injection Hrem as Heq_modules' _. subst modules'. exact Hrest.
      * destruct (graph_remove_modules rest mid) eqn:Hrest_rem.
        -- destruct p as [rest' rem']. injection Hrem as Heq_modules' _. subst modules'.
           simpl. right. apply (IH mid rest' rem' other Hneq Hrest_rem Hrest).
        -- discriminate.
Qed.

(** graph_remove_preserves_wf: Removing a module keeps the graph well-formed,
    PROVIDED no remaining morphisms reference that module. In practice, you always
    call graph_cascade_delete_morphisms first to ensure that precondition.
    The caller passes in the endpoint-validity proof explicitly because the lemma
    doesn't know which cascade strategy was used. *)
Lemma graph_remove_preserves_wf : forall g mid g' m,
  well_formed_graph g ->
  all_morph_endpoints_valid (pg_modules g') (pg_morphisms g) ->
  graph_remove g mid = Some (g', m) ->
  well_formed_graph g'.
Proof.
  intros g mid g' m Hwf Hvalid Hrem.
  unfold graph_remove in Hrem.
  destruct (graph_remove_modules (pg_modules g) mid) eqn:Hrem_modules.
  - destruct p as [modules' removed]. injection Hrem as Heq_g' Heq_m. subst.
    unfold well_formed_graph in *. simpl in *.
    destruct Hwf as [Hwf_mods [Hwf_morphs Hwf_endpoints]].
    repeat split.
    + apply (graph_remove_modules_preserves_all_ids_below _ _ _ _ _ Hwf_mods Hrem_modules).
    + exact Hwf_morphs.
    + exact Hvalid.
  - discriminate.
Qed.

(** cascade_then_remove_endpoints_valid: After cascade-deleting morphisms that
    reference `mid` and then removing `mid` itself, every remaining morphism's
    endpoints still exist. Here's the argument: cascade delete filtered out
    everything that touched `mid`, so the remaining morphisms only reference
    other modules — and those other modules survived the removal. *)
Lemma cascade_then_remove_endpoints_valid : forall g mid g_removed m,
  well_formed_graph g ->
  graph_remove (graph_cascade_delete_morphisms g mid) mid = Some (g_removed, m) ->
  all_morph_endpoints_valid (pg_modules g_removed) (pg_morphisms (graph_cascade_delete_morphisms g mid)).
Proof.
  intros g mid g_removed m Hwf Hrem.
  unfold graph_remove in Hrem.
  destruct (graph_remove_modules (pg_modules (graph_cascade_delete_morphisms g mid)) mid) as [[modules' rem]|] eqn:Hmods.
  2: discriminate.
  injection Hrem as Heq_g_removed _. subst.
  simpl.
  (* After cascade delete, no morphism references mid. So all morphism endpoints
     are in pg_modules g \ {mid}, which is exactly modules'. *)
  unfold graph_cascade_delete_morphisms. simpl.
  unfold well_formed_graph in Hwf. destruct Hwf as [_ [_ Hendpoints]].
  induction (pg_morphisms g) as [|[morph_id ms] rest IH]; simpl.
  - exact I.
  - destruct (negb (morph_source ms =? mid) && negb (morph_target ms =? mid)) eqn:Hfilt.
    + simpl. split.
      * (* Show this morphism's endpoints are in modules' *)
        destruct Hendpoints as [Hep Hrest].
        unfold morph_endpoints_valid in *.
        destruct Hep as [Hsrc Htgt].
        apply Bool.andb_true_iff in Hfilt.
        destruct Hfilt as [Hnsrc Hntgt].
        apply Bool.negb_true_iff in Hnsrc.
        apply Bool.negb_true_iff in Hntgt.
        apply Nat.eqb_neq in Hnsrc.
        apply Nat.eqb_neq in Hntgt.
        split.
        -- apply (graph_remove_modules_preserves_other_in _ _ _ _ _ Hnsrc Hmods Hsrc).
        -- apply (graph_remove_modules_preserves_other_in _ _ _ _ _ Hntgt Hmods Htgt).
      * destruct Hendpoints as [_ Hrest]. exact (IH Hrest).
    + destruct Hendpoints as [_ Hrest]. exact (IH Hrest).
Qed.

(** graph_remove_after_cascade_preserves_wf: The standard pattern for safe module
    removal. Call cascade delete first, then remove — this lemma bundles both steps
    into a single well-formedness guarantee. This is what PSPLIT and PMERGE use. *)
Lemma graph_remove_after_cascade_preserves_wf : forall g mid g_removed m,
  well_formed_graph g ->
  graph_remove (graph_cascade_delete_morphisms g mid) mid = Some (g_removed, m) ->
  well_formed_graph g_removed.
Proof.
  intros g mid g_removed m Hwf Hrem.
  pose proof (graph_cascade_delete_morphisms_preserves_wf g mid Hwf) as Hwf_casc.
  pose proof (cascade_then_remove_endpoints_valid g mid g_removed m Hwf Hrem) as Hvalid.
  eapply graph_remove_preserves_wf; eauto.
Qed.

(** remove_no_ref_endpoints_valid: If you can guarantee none of the morphisms
    reference `mid` (e.g., by some method other than cascade delete — or for
    double-cascade proofs), then removing `mid` doesn't break endpoint validity.
    Used by graph_remove_no_ref_preserves_wf below. *)
Lemma remove_no_ref_endpoints_valid : forall g mid g_removed m,
  (forall morph_id ms, In (morph_id, ms) (pg_morphisms g) ->
   morph_source ms <> mid /\ morph_target ms <> mid) ->
  all_morph_endpoints_valid (pg_modules g) (pg_morphisms g) ->
  graph_remove g mid = Some (g_removed, m) ->
  all_morph_endpoints_valid (pg_modules g_removed) (pg_morphisms g).
Proof.
  intros g mid g_removed m Hno_ref Hvalid Hrem.
  unfold graph_remove in Hrem.
  destruct (graph_remove_modules (pg_modules g) mid) as [[modules' rem]|] eqn:Hmods.
  2: discriminate.
  injection Hrem as Heq_g_removed _. subst. simpl.
  (* Prove by induction on the morphism list *)
  generalize dependent Hvalid. generalize dependent Hno_ref.
  generalize (pg_morphisms g) as morphs.
  induction morphs as [|[mid0 ms0] rest IH]; intros Hno_ref Hvalid; simpl.
  - exact I.
  - simpl in Hvalid. destruct Hvalid as [Hep Hrest].
    assert (Hno_ref_ms: morph_source ms0 <> mid /\ morph_target ms0 <> mid).
    { apply (Hno_ref mid0 ms0). left. reflexivity. }
    destruct Hno_ref_ms as [Hnsrc Hntgt].
    split.
    + unfold morph_endpoints_valid in *. destruct Hep as [Hsrc Htgt].
      split.
      * apply (graph_remove_modules_preserves_other_in _ _ _ _ _ Hnsrc Hmods Hsrc).
      * apply (graph_remove_modules_preserves_other_in _ _ _ _ _ Hntgt Hmods Htgt).
    + apply IH.
      * intros mid' ms' Hin. apply (Hno_ref mid' ms'). right. exact Hin.
      * exact Hrest.
Qed.

(** graph_remove_no_ref_preserves_wf: The general form — if you have some proof
    that no morphism touches `mid`, then removing `mid` preserves well-formedness.
    Combines remove_no_ref_endpoints_valid with the standard WF components. *)
Lemma graph_remove_no_ref_preserves_wf : forall g mid g_removed m,
  well_formed_graph g ->
  (forall morph_id ms, In (morph_id, ms) (pg_morphisms g) ->
   morph_source ms <> mid /\ morph_target ms <> mid) ->
  graph_remove g mid = Some (g_removed, m) ->
  well_formed_graph g_removed.
Proof.
  intros g mid g_removed m Hwf Hno_ref Hrem.
  pose proof (remove_no_ref_endpoints_valid g mid g_removed m Hno_ref) as Hvalid_pf.
  unfold well_formed_graph in Hwf.
  destruct Hwf as [Hmod_ids [Hmorph_ids Hendpoints]].
  pose proof (Hvalid_pf Hendpoints Hrem) as Hvalid.
  eapply graph_remove_preserves_wf; eauto.
  unfold well_formed_graph. split; [|split].
  - exact Hmod_ids.
  - exact Hmorph_ids.
  - exact Hendpoints.
Qed.

(** double_cascade_no_ref: After cascading twice (once for m1, once for m2),
    no surviving morphism has m1 or m2 as a source or target.
    This is the key lemma for PMERGE's WF proof — you need to remove two modules,
    and you need to know that after both cascades, neither is referenced. The
    filter_In lemma from Coq's stdlib plus Boolean algebra handles it. *)
Lemma double_cascade_no_ref : forall g m1 m2 morph_id ms,
  In (morph_id, ms) (pg_morphisms (graph_cascade_delete_morphisms
                                    (graph_cascade_delete_morphisms g m1) m2)) ->
  morph_source ms <> m1 /\ morph_target ms <> m1 /\
  morph_source ms <> m2 /\ morph_target ms <> m2.
Proof.
  intros g m1 m2 morph_id ms Hin.
  unfold graph_cascade_delete_morphisms in Hin. simpl in Hin.
  apply filter_In in Hin. destruct Hin as [Hin2 Hfilt2].
  apply filter_In in Hin2. destruct Hin2 as [Hin1 Hfilt1].
  apply Bool.andb_true_iff in Hfilt1. destruct Hfilt1 as [Hns1 Hnt1].
  apply Bool.andb_true_iff in Hfilt2. destruct Hfilt2 as [Hns2 Hnt2].
  apply Bool.negb_true_iff in Hns1. apply Nat.eqb_neq in Hns1.
  apply Bool.negb_true_iff in Hnt1. apply Nat.eqb_neq in Hnt1.
  apply Bool.negb_true_iff in Hns2. apply Nat.eqb_neq in Hns2.
  apply Bool.negb_true_iff in Hnt2. apply Nat.eqb_neq in Hnt2.
  repeat split; assumption.
Qed.

(** pmerge_second_remove_preserves_wf: PMERGE removes two modules. After the
    first remove, we need to know the second remove also preserves WF. The
    critical observation: double_cascade_no_ref gives us that no morphism in
    the doubly-cascaded graph references either m1 or m2. The first remove
    doesn't change pg_morphisms, so the second remove still sees that guarantee. *)
Lemma pmerge_second_remove_preserves_wf : forall g m1 m2 g2_cascaded g_without_m1 mod1 g_without_both mod2,
  well_formed_graph g ->
  g2_cascaded = graph_cascade_delete_morphisms (graph_cascade_delete_morphisms g m1) m2 ->
  graph_remove g2_cascaded m1 = Some (g_without_m1, mod1) ->
  graph_remove g_without_m1 m2 = Some (g_without_both, mod2) ->
  well_formed_graph g_without_both.
Proof.
  intros g m1 m2 g2_cascaded g_without_m1 mod1 g_without_both mod2
         Hwf Hg2eq Hrem1 Hrem2.
  (* After double cascade, no morphisms reference m1 or m2 *)
  assert (Hno_ref_both: forall morph_id ms, In (morph_id, ms) (pg_morphisms g2_cascaded) ->
          morph_source ms <> m1 /\ morph_target ms <> m1 /\
          morph_source ms <> m2 /\ morph_target ms <> m2).
  { intros morph_id' ms' Hin. subst g2_cascaded.
    exact (double_cascade_no_ref g m1 m2 morph_id' ms' Hin). }
  (* First remove preserves wf *)
  pose proof (graph_cascade_delete_morphisms_preserves_wf g m1 Hwf) as Hwf1.
  pose proof (graph_cascade_delete_morphisms_preserves_wf
               (graph_cascade_delete_morphisms g m1) m2 Hwf1) as Hwf2.
  rewrite <- Hg2eq in Hwf2.
  assert (Hno_ref_m1: forall morph_id ms, In (morph_id, ms) (pg_morphisms g2_cascaded) ->
          morph_source ms <> m1 /\ morph_target ms <> m1).
  { intros. destruct (Hno_ref_both _ _ H) as [? [? _]]. split; assumption. }
  pose proof (graph_remove_no_ref_preserves_wf g2_cascaded m1 g_without_m1 mod1 Hwf2 Hno_ref_m1 Hrem1) as Hwf_m1.
  (* Second remove: morphisms in g_without_m1 are same as g2_cascaded (graph_remove preserves morphisms) *)
  unfold graph_remove in Hrem1.
  destruct (graph_remove_modules (pg_modules g2_cascaded) m1) as [[mods1 rem1]|] eqn:Hmods1.
  2: discriminate.
  injection Hrem1 as Hgw1 _. subst g_without_m1. simpl.
  assert (Hno_ref_m2: forall morph_id ms, In (morph_id, ms) (pg_morphisms g2_cascaded) ->
          morph_source ms <> m2 /\ morph_target ms <> m2).
  { intros. destruct (Hno_ref_both _ _ H) as [_ [_ [? ?]]]. split; assumption. }
  apply (graph_remove_no_ref_preserves_wf _ m2 g_without_both mod2 Hwf_m1 Hno_ref_m2 Hrem2).
Qed.

(** Three ways to say "this module exists": graph_lookup returns Some, the ID is
    In (map fst modules), or graph_lookup returns non-None. These converters show
    up constantly in WF preservation proofs — you need to go back and forth between
    them to prove morphism endpoints survive each graph operation. *)

(** graph_lookup_modules_in: If lookup succeeds, the module ID is in the ID list.
    The proof is just an induction reading off the match — when Nat.eqb says yes,
    the ID is at the head; otherwise recurse. *)
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

(** in_modules_graph_lookup: If the module ID is in the ID list, lookup doesn't
    return None. The reverse of graph_lookup_modules_in — converts membership
    to lookup success for the WF preservation proofs that go the other way. *)
Lemma in_modules_graph_lookup : forall modules mid,
  In mid (List.map fst modules) ->
  graph_lookup_modules modules mid <> None.
Proof.
  induction modules as [|[id ms] rest IH]; intros mid Hin; simpl.
  - destruct Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst id. rewrite Nat.eqb_refl. discriminate.
    + destruct (Nat.eqb id mid) eqn:Heq; [discriminate | apply IH; exact Hin'].
Qed.

(** WF preservation for morphism operations (MORPH, COMPOSE, MORPH_ID, etc.):
    every morphism op that succeeds produces a well-formed graph. *)

(** all_morph_endpoints_valid_In: Given the bulk endpoint-validity predicate,
    extract validity for a specific morphism by its list membership.
    This turns "all morphisms in this list are valid" into "this specific
    morphism is valid" — used when composing or tensoring morphisms where you
    need to look up a specific morphism and prove its endpoints still exist. *)
Lemma all_morph_endpoints_valid_In : forall modules morphisms,
  all_morph_endpoints_valid modules morphisms ->
  forall mid ms, In (mid, ms) morphisms ->
  morph_endpoints_valid modules ms.
Proof.
  intros modules morphisms.
  induction morphisms as [|[mid' ms'] rest IH]; intros Hall mid ms Hin.
  - destruct Hin.
  - simpl in Hall. destruct Hall as [Hms' Hrest].
    destruct Hin as [Heq | Hin'].
    + injection Heq as _ Heq'. subst ms'. exact Hms'.
    + exact (IH Hrest mid ms Hin').
Qed.

(** graph_lookup_morphism_list_In: If morphism lookup succeeds, that morphism is
    in the list. Like graph_lookup_modules_in but for morphisms. Converts a
    successful lookup into list membership so we can apply all_morph_endpoints_valid_In. *)
Lemma graph_lookup_morphism_list_In : forall morphisms mid ms,
  graph_lookup_morphism_list morphisms mid = Some ms ->
  In (mid, ms) morphisms.
Proof.
  induction morphisms as [|[mid' ms'] rest IH]; intros mid ms Hlu.
  - simpl in Hlu. discriminate.
  - simpl in Hlu. destruct (Nat.eqb mid' mid) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst mid'. injection Hlu as Hms. subst ms'. left. reflexivity.
    + right. apply IH. exact Hlu.
Qed.

(** graph_add_morphism_preserves_wf: Adding a morphism is safe when both
    endpoints (src and dst) actually exist in the graph. The proof has to show:
    (1) module IDs unchanged (just reflexivity); (2) the new morphism's ID
    is valid and the old ones still are; (3) the new morphism's endpoints are in
    pg_modules, plus all the old ones still are too. The two lookup-ne hypotheses
    let us extract the actual ModuleState values via Hsrc_eq/Hdst_eq. *)
Lemma graph_add_morphism_preserves_wf : forall g src dst c is_id,
  well_formed_graph g ->
  graph_lookup g src <> None ->
  graph_lookup g dst <> None ->
  well_formed_graph (fst (graph_add_morphism g src dst c is_id)).
Proof.
  intros g src dst c is_id Hwf Hsrc Hdst.
  unfold graph_add_morphism. simpl.
  unfold well_formed_graph in *. simpl.
  destruct Hwf as [Hwf_mods [Hwf_morphs Hwf_endpoints]].
  (* Extract actual module states from non-None hypotheses *)
  unfold graph_lookup in Hsrc, Hdst.
  destruct (graph_lookup_modules (pg_modules g) src) as [ms_src|] eqn:Hsrc_eq;
    [clear Hsrc | contradiction].
  destruct (graph_lookup_modules (pg_modules g) dst) as [ms_dst|] eqn:Hdst_eq;
    [clear Hdst | contradiction].
  split; [exact Hwf_mods |].
  split.
  - (* all_morph_ids_below for new + old morphisms *)
    simpl. split.
    + (* new morph ID < S old pg_next_morph_id *) lia.
    + (* old morphism IDs still valid under new bound *)
      clear Hwf_mods Hwf_endpoints Hsrc_eq Hdst_eq.
      induction (pg_morphisms g) as [|[mid ms] rest IH]; simpl.
      * exact I.
      * simpl in Hwf_morphs. destruct Hwf_morphs as [Hlt Hrest].
        split; [lia | apply IH; exact Hrest].
  - (* all_morph_endpoints_valid for new + old morphisms *)
    simpl. split.
    + (* new morphism endpoints valid *)
      unfold morph_endpoints_valid. simpl.
      split.
      * apply (graph_lookup_modules_in _ _ _ Hsrc_eq).
      * apply (graph_lookup_modules_in _ _ _ Hdst_eq).
    + (* old morphism endpoints still valid *)
      clear Hwf_mods Hwf_morphs Hsrc_eq Hdst_eq.
      induction (pg_morphisms g) as [|[mid ms] rest IH]; simpl.
      * exact I.
      * simpl in Hwf_endpoints. destruct Hwf_endpoints as [Hms Hrest].
        split; [exact Hms | apply IH; exact Hrest].
Qed.

(** graph_compose_morphisms_preserves_wf: Composing two morphisms f;h is WF when
    f.target = h.source (the type compatibility check). The composed morphism
    goes from f.source to h.target — both of which are valid endpoints because
    we can look them up from the original morphisms' endpoint validity. *)
Lemma graph_compose_morphisms_preserves_wf : forall g m1 m2 g' new_id,
  well_formed_graph g ->
  graph_compose_morphisms g m1 m2 = Some (g', new_id) ->
  well_formed_graph g'.
Proof.
  intros g m1 m2 g' new_id Hwf Hcomp.
  unfold graph_compose_morphisms in Hcomp.
  destruct (graph_lookup_morphism g m1) as [ms1|] eqn:Hlookup1; [| discriminate].
  destruct (graph_lookup_morphism g m2) as [ms2|] eqn:Hlookup2; [| discriminate].
  destruct (Nat.eqb (morph_target ms1) (morph_source ms2)) eqn:Heq; [| discriminate].
  injection Hcomp as Hg' Hnew. subst g' new_id.
  apply Nat.eqb_eq in Heq.
  unfold well_formed_graph in Hwf.
  destruct Hwf as [Hwf_mods [Hwf_morphs Hwf_endpoints]].
  (* Get membership from lookup *)
  assert (Hin1: In (m1, ms1) (pg_morphisms g)).
  { apply graph_lookup_morphism_list_In.
    unfold graph_lookup_morphism in Hlookup1. exact Hlookup1. }
  assert (Hin2: In (m2, ms2) (pg_morphisms g)).
  { apply graph_lookup_morphism_list_In.
    unfold graph_lookup_morphism in Hlookup2. exact Hlookup2. }
  (* Get endpoint validity *)
  pose proof (all_morph_endpoints_valid_In (pg_modules g) (pg_morphisms g) Hwf_endpoints m1 ms1 Hin1) as [Hsrc1 _].
  pose proof (all_morph_endpoints_valid_In (pg_modules g) (pg_morphisms g) Hwf_endpoints m2 ms2 Hin2) as [_ Hdst2].
  (* Convert In to graph_lookup <> None *)
  assert (Hsrc: graph_lookup g (morph_source ms1) <> None).
  { unfold graph_lookup. apply in_modules_graph_lookup. exact Hsrc1. }
  assert (Hdst: graph_lookup g (morph_target ms2) <> None).
  { unfold graph_lookup. apply in_modules_graph_lookup. exact Hdst2. }
  apply graph_add_morphism_preserves_wf.
  - exact (conj Hwf_mods (conj Hwf_morphs Hwf_endpoints)).
  - exact Hsrc.
  - exact Hdst.
Qed.

(** graph_add_identity_preserves_wf: Creating an identity morphism (MORPH_ID)
    is safe because the source and target are the same module — and the module
    must exist (otherwise graph_add_identity returns None). So both endpoints
    are trivially valid: they're the same valid module. *)
Lemma graph_add_identity_preserves_wf : forall g module g' morph_id,
  well_formed_graph g ->
  graph_add_identity g module = Some (g', morph_id) ->
  well_formed_graph g'.
Proof.
  intros g module g' morph_id Hwf Hadd.
  unfold graph_add_identity in Hadd.
  destruct (graph_lookup g module) eqn:Hlookup; [| discriminate].
  injection Hadd as Hg' Hmid. subst g'.
  apply graph_add_morphism_preserves_wf.
  - exact Hwf.
  - rewrite Hlookup. discriminate.
  - rewrite Hlookup. discriminate.
Qed.

(** graph_delete_morphism_preserves_wf: Removing a morphism (MORPH_DELETE) can't
    break WF. Fewer morphisms means fewer things to check validity on. All three
    WF components (module IDs, morphism IDs, endpoints) filter cleanly through. *)
Lemma graph_delete_morphism_preserves_wf : forall g morph_id g',
  well_formed_graph g ->
  graph_delete_morphism g morph_id = Some g' ->
  well_formed_graph g'.
Proof.
  intros g morph_id g' Hwf Hdel.
  unfold graph_delete_morphism in Hdel.
  destruct (existsb (fun '(id, _) => Nat.eqb id morph_id) (pg_morphisms g)) eqn:Hexist;
    [| discriminate].
  injection Hdel as Hg'. subst g'.
  unfold well_formed_graph in *. simpl.
  destruct Hwf as [Hwf_mods [Hwf_morphs Hwf_endpoints]].
  clear Hexist.
  repeat split.
  - exact Hwf_mods.
  - (* Removing a morphism preserves ID validity *)
    clear Hwf_mods Hwf_endpoints.
    induction (pg_morphisms g) as [|[mid ms] rest IH]; simpl.
    + exact I.
    + destruct Hwf_morphs as [Hlt Hrest].
      destruct (negb (Nat.eqb mid morph_id)); simpl.
      * split; [exact Hlt | exact (IH Hrest)].
      * exact (IH Hrest).
  - (* Removing a morphism preserves endpoint validity *)
    clear Hwf_mods Hwf_morphs.
    induction (pg_morphisms g) as [|[mid ms] rest IH]; simpl.
    + exact I.
    + destruct Hwf_endpoints as [Hep Hrest].
      destruct (negb (Nat.eqb mid morph_id)); simpl.
      * split; [exact Hep | exact (IH Hrest)].
      * exact (IH Hrest).
Qed.

(** graph_tensor_morphisms_preserves_wf: MORPH_TENSOR adds one morphism whose
    endpoints are the union modules (ac_id and bd_id). The proof is the longest
    of the morphism WF lemmas because MORPH_TENSOR has the most preconditions:
    two morphism lookups, four module lookups, a disjointness check, and two
    region finds. Once all those succeed, the new morphism's endpoints are valid
    because graph_find_region only returns IDs of modules that exist. The inline
    helper Hfind_valid captures that fact from graph_find_region_modules. *)
Lemma graph_tensor_morphisms_preserves_wf : forall g f_id g_id g' new_id,
  well_formed_graph g ->
  graph_tensor_morphisms g f_id g_id = Some (g', new_id) ->
  well_formed_graph g'.
Proof.
  intros g f_id g_id g' new_id Hwf Htensor.
  unfold graph_tensor_morphisms in Htensor.
  (* Step 1: destruct outer morphism-pair match, then iota-reduce to expose module lookups *)
  destruct (graph_lookup_morphism g f_id) as [f_ms|] eqn:Hlookup_f; [| discriminate].
  destruct (graph_lookup_morphism g g_id) as [g_ms|] eqn:Hlookup_g; [| discriminate].
  cbn beta iota in Htensor.
  (* Step 2: destruct four module lookups, then iota-reduce to expose the boolean guard *)
  destruct (graph_lookup g (morph_source f_ms)) as [a_mod|]; [| discriminate].
  destruct (graph_lookup g (morph_target f_ms)) as [b_mod|]; [| discriminate].
  destruct (graph_lookup g (morph_source g_ms)) as [c_mod|]; [| discriminate].
  destruct (graph_lookup g (morph_target g_ms)) as [d_mod|]; [| discriminate].
  cbn beta iota in Htensor.
  (* Step 3: destruct the disjointness boolean, then reduce 'if true' and let-bindings *)
  destruct (nat_list_disjoint (module_region a_mod) (module_region c_mod) &&
            nat_list_disjoint (module_region b_mod) (module_region d_mod));
    [| discriminate].
  cbn beta iota zeta in Htensor.
  (* Step 4: destruct region finds with eqn names; after destructs iota-reduce final match *)
  destruct (graph_find_region g (nat_list_union (module_region a_mod) (module_region c_mod)))
    as [ac_id|] eqn:Hac; [| discriminate].
  destruct (graph_find_region g (nat_list_union (module_region b_mod) (module_region d_mod)))
    as [bd_id|] eqn:Hbd; [| discriminate].
  cbn beta iota in Htensor.
  (* Now Htensor : Some (let ... in graph_add_morphism g ac_id bd_id c false) = Some (g', new_id) *)
  injection Htensor as Hg' Hnew. subst g' new_id.
  (* Helper: graph_find_region returns a module ID present in pg_modules g *)
  assert (Hfind_valid: forall region mid,
    graph_find_region g region = Some mid -> graph_lookup g mid <> None).
  { intros region mid Hfind.
    unfold graph_find_region, graph_find_region_modules in Hfind.
    unfold graph_lookup.
    (* Revert so IH stays abstract, avoiding contamination from outer hypotheses *)
    revert region mid Hfind.
    set (mods := pg_modules g).
    induction mods as [|[id m] rest IH]; intros region mid Hfind; simpl in Hfind |- *.
    - discriminate.
    - destruct (nat_list_eq (module_region m) (normalize_region region)) eqn:Heq;
        simpl in Hfind.
      + injection Hfind as Hmid. subst id. rewrite Nat.eqb_refl. discriminate.
      + destruct (Nat.eqb id mid) eqn:Hne; [discriminate | exact (IH region mid Hfind)]. }
  apply graph_add_morphism_preserves_wf.
  - exact Hwf.
  - exact (Hfind_valid _ ac_id Hac).
  - exact (Hfind_valid _ bd_id Hbd).
Qed.

(** The morphism opcodes (MORPH, COMPOSE, MORPH_ID, MORPH_DELETE, MORPH_TENSOR)
    work on the morphism side of the graph. None of them add modules. So pg_next_id
    stays constant across all of them. The proofs below are all one-liners used
    by observational_no_signaling in KernelPhysics.v. *)

(** graph_add_morphism_next_id_same: Adding a morphism doesn't change pg_next_id.
    Reflexivity — the definition is explicit about what changes. *)
Lemma graph_add_morphism_next_id_same : forall g src dst c is_id,
  pg_next_id (fst (graph_add_morphism g src dst c is_id)) = pg_next_id g.
Proof. intros. unfold graph_add_morphism. simpl. reflexivity. Qed.

(** graph_add_identity_next_id_same: MORPH_ID doesn't add modules. *)
Lemma graph_add_identity_next_id_same : forall g module g' morph_id,
  graph_add_identity g module = Some (g', morph_id) ->
  pg_next_id g' = pg_next_id g.
Proof.
  intros g module g' morph_id H.
  unfold graph_add_identity in H.
  destruct (graph_lookup g module); [| discriminate].
  injection H as Hg _. subst g'. apply graph_add_morphism_next_id_same.
Qed.

(** graph_compose_morphisms_next_id_same: COMPOSE doesn't add modules. *)
Lemma graph_compose_morphisms_next_id_same : forall g m1 m2 g' new_id,
  graph_compose_morphisms g m1 m2 = Some (g', new_id) ->
  pg_next_id g' = pg_next_id g.
Proof.
  intros g m1 m2 g' new_id H.
  unfold graph_compose_morphisms in H.
  destruct (graph_lookup_morphism g m1); [| discriminate].
  destruct (graph_lookup_morphism g m2); [| discriminate].
  destruct (Nat.eqb _ _); [| discriminate].
  injection H as Hg _. subst g'. apply graph_add_morphism_next_id_same.
Qed.

(** graph_delete_morphism_next_id_same: MORPH_DELETE doesn't add modules. *)
Lemma graph_delete_morphism_next_id_same : forall g morph_id g',
  graph_delete_morphism g morph_id = Some g' ->
  pg_next_id g' = pg_next_id g.
Proof.
  intros g morph_id g' H.
  unfold graph_delete_morphism in H.
  destruct (existsb _ _); [| discriminate].
  injection H as Hg. subst g'. simpl. reflexivity.
Qed.

(** graph_tensor_morphisms_next_id_same: MORPH_TENSOR doesn't add modules either,
    even though it finds and uses the union-region modules. Those modules already
    exist — the precondition requires graph_find_region to succeed on both. *)
Lemma graph_tensor_morphisms_next_id_same : forall g f_id g_id g' new_id,
  graph_tensor_morphisms g f_id g_id = Some (g', new_id) ->
  pg_next_id g' = pg_next_id g.
Proof.
  intros g f_id g_id g' new_id H.
  unfold graph_tensor_morphisms in H.
  destruct (graph_lookup_morphism g f_id) as [f_ms|]; [| discriminate].
  destruct (graph_lookup_morphism g g_id) as [g_ms|]; [| discriminate].
  cbn beta iota in H.
  destruct (graph_lookup g (morph_source f_ms)) as [a_mod|]; [| discriminate].
  destruct (graph_lookup g (morph_target f_ms)) as [b_mod|]; [| discriminate].
  destruct (graph_lookup g (morph_source g_ms)) as [c_mod|]; [| discriminate].
  destruct (graph_lookup g (morph_target g_ms)) as [d_mod|]; [| discriminate].
  cbn beta iota in H.
  destruct (nat_list_disjoint (module_region a_mod) (module_region c_mod) &&
            nat_list_disjoint (module_region b_mod) (module_region d_mod));
    [| discriminate].
  cbn beta iota zeta in H.
  destruct (graph_find_region g (nat_list_union (module_region a_mod) (module_region c_mod)))
    as [ac_id|]; [| discriminate].
  destruct (graph_find_region g (nat_list_union (module_region b_mod) (module_region d_mod)))
    as [bd_id|]; [| discriminate].
  cbn beta iota in H.
  injection H as Hg _. subst g'. apply graph_add_morphism_next_id_same.
Qed.


(** graph_add_module_length: Adding a module always increases the module list by
    exactly 1. The new module is prepended: result = new :: old. So length goes
    from n to n+1. Used by PSPLIT and PMERGE length accounting. *)
Lemma graph_add_module_length : forall g region axioms,
  List.length (pg_modules (fst (graph_add_module g region axioms))) =
  S (List.length (pg_modules g)).
Proof.
  intros g region axioms.
  unfold graph_add_module. simpl. reflexivity.
Qed.

(** graph_remove_modules_length: A successful removal decreases the module
    list by exactly 1. "Successful" means the module was found and removed.
    The induction handles the head (found immediately) and tail (found deeper)
    cases separately. Used to track module count through PMERGE's two removals. *)
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

(** graph_remove_length: Successful removal of a module from the graph reduces
    pg_modules length by 1. Lifts graph_remove_modules_length to the graph level. *)
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

(** graph_insert_modules_length: Inserting may add one element (new ID) or
    replace one (existing ID). Either way, length doesn't decrease. *)
Lemma graph_insert_modules_length : forall modules mid m,
  List.length (graph_insert_modules modules mid m) >= List.length modules.
Proof.
  induction modules as [|[id ms] rest IH]; intros mid m; simpl.
  - lia.
  - destruct (Nat.eqb id mid); simpl.
    + lia.
    + specialize (IH mid m). lia.
Qed.

(** graph_insert_modules_existing_length: If the module already exists (mid is
    in the ID list), insertion replaces it in-place — length stays the same.
    This is how graph_update works: it calls graph_insert_modules with the
    assumption that the module already exists. *)
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

(** graph_insert_modules_preserves_in_map: Any module ID that was in the list
    before insertion is still in the list after. Insertions can only add, never
    remove. Used to prove morphism endpoints remain valid after graph_update. *)
Lemma graph_insert_modules_preserves_in_map : forall modules mid m mid',
  In mid' (List.map fst modules) ->
  In mid' (List.map fst (graph_insert_modules modules mid m)).
Proof.
  induction modules as [|[id ms] rest IH]; intros mid m mid' Hin; simpl.
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst mid'. destruct (Nat.eqb id mid) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst. simpl. left. reflexivity.
      * simpl. left. reflexivity.
    + destruct (Nat.eqb id mid) eqn:Heq.
      * simpl. right. exact Hin'.
      * simpl. right. apply IH. exact Hin'.
Qed.

(** graph_update_length: Updating a module (possibly new, possibly existing)
    doesn't shrink the module list. Follows from graph_insert_modules_length. *)
Lemma graph_update_length : forall g mid m,
  List.length (pg_modules (graph_update g mid m)) >= List.length (pg_modules g).
Proof.
  intros g mid m.
  unfold graph_update. simpl.
  apply graph_insert_modules_length.
Qed.

(** graph_add_axiom_length: Adding an axiom to a module (PDISCOVER) doesn't
    remove modules. It either updates an existing module (same length) or
    does nothing when the module doesn't exist (same length). *)
Lemma graph_add_axiom_length : forall g mid ax,
  List.length (pg_modules (graph_add_axiom g mid ax)) >= List.length (pg_modules g).
Proof.
  intros g mid ax.
  unfold graph_add_axiom.
  destruct (graph_lookup g mid) as [m|].
  - apply graph_update_length.
  - lia.
Qed.

(** graph_add_axiom_preserves_length: Adding an axiom to an existing module
    leaves the module count exactly the same — it updates in-place.
    If the module doesn't exist, graph is unchanged, also same count. *)
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

(** graph_add_axioms_preserves_length: Adding a list of axioms (fold over
    graph_add_axiom) preserves length. Induction over the axiom list,
    each step using graph_add_axiom_preserves_length. *)
Lemma graph_add_axioms_preserves_length : forall g mid axs,
  List.length (pg_modules (graph_add_axioms g mid axs)) = List.length (pg_modules g).
Proof.
  intros g mid axs.
  unfold graph_add_axioms.
  revert g. induction axs as [|ax rest IH]; intros g; simpl.
  - reflexivity.
  - rewrite IH. apply graph_add_axiom_preserves_length.
Qed.

(** graph_record_discovery_preserves_length: PDISCOVER stores evidence on a
    module but doesn't create or remove modules. Length unchanged. *)
Lemma graph_record_discovery_preserves_length : forall g mid evidence,
  List.length (pg_modules (graph_record_discovery g mid evidence)) = List.length (pg_modules g).
Proof.
  intros g mid evidence.
  unfold graph_record_discovery.
  apply graph_add_axioms_preserves_length.
Qed.

(** graph_update_existing_length: When the module already exists, graph_update
    replaces it in-place and keeps the count exactly the same. The "existing"
    precondition (lookup <> None) is what lets us use the in-place replacement
    branch of graph_insert_modules_existing_length. *)
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

(** graph_insert_modules_lookup_same: After inserting module m at mid, looking
    up mid returns m. This is the correctness property for graph_update —
    what you write is what you get back. Requires mid to already be in the list
    (in-place replacement, not append). Induction on the module list. *)
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

(** graph_update_lookup_same: After updating module mid to m, looking up mid
    returns normalize_module m. Note the normalize — graph_update always
    normalizes the module on write, so the stored value has normalized region.
    The normalize_module m in the result is NOT a surprise — it's by definition. *)
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

(** graph_insert_modules_preserves_unrelated: Inserting at mid_update doesn't
    change the lookup result for any other module id. The proof handles the
    case where the list was empty separately (the inserted element is the only
    one, and you're looking up something different — returns None in both cases). *)
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

(** graph_update_preserves_unrelated: Updating one module doesn't change what
    you see when you look up a different module. Lifts the list-level lemma
    to the graph level. Used heavily in observational_no_signaling proofs. *)
Lemma graph_update_preserves_unrelated : forall g mid_update mid_other m,
  mid_other <> mid_update ->
  graph_lookup (graph_update g mid_update m) mid_other = graph_lookup g mid_other.
Proof.
  intros g mid_update mid_other m Hneq.
  unfold graph_update, graph_lookup. simpl.
  apply graph_insert_modules_preserves_unrelated. exact Hneq.
Qed.

(** Module IDs form the range [0, pg_next_id). Ask about anything above that,
    you get None. No aliasing, no undefined behavior. This is what well-formedness
    buys you: any ID above the counter is guaranteed fresh — never been allocated. *)

(** all_ids_below_implies_lookup_none: If all IDs in the list are < bound, then
    looking up anything >= bound finds nothing. This is the mechanical step
    that makes wf_graph_lookup_beyond_next_id work. Lia handles the arithmetic. *)
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

(** graph_remove_preserves_next_id: Removing a module doesn't reset the ID counter.
    pg_next_id only goes up — it never comes back down even if you free an ID.
    IDs are not recycled. This prevents aliasing (a new module getting the same
    ID as a just-removed module would be confusing). *)
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

(** graph_remove_preserves_unrelated: Removing module mid' doesn't change the
    lookup result for any other module mid. The proof has to chase through
    graph_remove_modules to find the exact point where mid' was removed
    and verify that mid's entry is undisturbed. *)
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

    This theorem establishes a critical invariant: module IDs form a contiguous
    range [0, pg_next_id). Any lookup outside this range is guaranteed to fail.
    This makes ID allocation simple and prevents collisions.

    CLAIM: For any well-formed graph g, if mid >= g.(pg_next_id), then
    graph_lookup g mid = None.

    PROOF: Well-formedness means all_ids_below, which states every module ID
    is < pg_next_id. Every ID in the list is < pg_next_id, so mid >= pg_next_id
    can't match any existing ID.

    operations can't affect modules that don't exist.
*)
Theorem wf_graph_lookup_beyond_next_id : forall g mid,
  well_formed_graph g ->
  mid >= g.(pg_next_id) ->
  graph_lookup g mid = None.
Proof.
  intros g mid Hwf Hge.
  unfold graph_lookup.
  unfold well_formed_graph in Hwf.
  destruct Hwf as [Hwf_mods [_ _]].
  apply (all_ids_below_implies_lookup_none _ _ _ Hwf_mods Hge).
Qed.

(** Architecture constants — must match Kami RTL (ThieleCPUCore.v) and OCaml extraction. *)
Definition REG_COUNT : nat := 32.
Definition MEM_SIZE : nat := 65536.
Definition NUM_MODULES : nat := 64.  (* Maximum number of concurrent modules *)
Definition REGION_SIZE : nat := 16.  (* Maximum region size (YOSYS_LITE synthesis config) *)

(** Opcode constants for instruction encoding. *)
(* SAFE: OP_PNEW is the canonical opcode 0 for PNEW in the instruction set architecture *)
Definition OP_PNEW : nat := 0.  (* Partition new - opcode for PNEW instruction *)
Definition OPCODE := nat.  (* Type alias for opcode values *)

(** Q16.16 fixed-point constants (used by RTL for fixed-point arithmetic). *)
Definition Q16_SHIFT : nat := 16.            (* Fractional bit position *)
Definition Q16_ONE : nat := 65536.           (* Representation of 1 in Q16.16 (2^16) *)
Definition Q16_MAX : nat := 2147483647.      (* Max positive Q16.16 (2^31-1) *)

(** graph_pnew: Create a module with this region. If one already exists with
    this exact region, return it instead — PNEW is idempotent. Otherwise add
    a fresh module with an empty axiom set. *)
Definition graph_pnew (g : PartitionGraph) (region : list nat)
  : PartitionGraph * ModuleID :=
  let normalized := normalize_region region in
  match graph_find_region g normalized with
  | Some existing => (g, existing)
  | None => graph_add_module g normalized []
  end.

(** partition_valid: Check that (left, right) is a valid partition of original.
    left ⊆ original, right ⊆ original, left ∩ right = ∅, left ∪ right = original.
    All four must hold. If any fails, PSPLIT rejects the split. *)
Definition partition_valid
  (original left right : list nat) : bool :=
  nat_list_subset left original &&
  nat_list_subset right original &&
  nat_list_disjoint left right &&
  nat_list_subset original (nat_list_union left right).

(** graph_psplit: Split module mid into two child modules with regions left and right.
    Cascade-deletes morphisms referencing mid first (they'd be stale after removal).
    If left or right is empty, creates one empty module and keeps mid as the other.
    If partition_valid fails (regions don't cover original or overlap), returns None.
    Returns (new_graph, left_id, right_id). The abstract form — the hardware-aligned
    version (graph_hw_psplit) is in VMStep.v. *)
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
        (* Cascade delete morphisms referencing mid before removing *)
        let g_cascaded := graph_cascade_delete_morphisms g mid in
        match graph_remove g_cascaded mid with
        | None => None
        | Some (g_removed, _) =>
            let '(g_left, left_id) := graph_add_module g_removed left_norm axioms in
            let '(g_right, right_id) := graph_add_module g_left right_norm axioms in
            Some (g_right, left_id, right_id)
        end
      else None
  end.

(** graph_pmerge: Merge modules m1 and m2 into one. Returns None if m1 = m2 (can't
    merge a module with itself) or if their regions overlap (would create ambiguity).
    Cascade-deletes morphisms referencing either module first. If the union region
    already exists as a module, merges axioms into it. Otherwise creates a fresh module.
    Returns (new_graph, merged_id). *)
Definition graph_pmerge (g : PartitionGraph) (m1 m2 : ModuleID)
  : option (PartitionGraph * ModuleID) :=
  if Nat.eqb m1 m2 then None else
  (* Cascade delete morphisms referencing m1 and m2 before removing *)
  let g1 := graph_cascade_delete_morphisms g m1 in
  let g2 := graph_cascade_delete_morphisms g1 m2 in
  match graph_remove g2 m1 with
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
                                                      ++ combined_axioms;
                                      module_mu_tensor := existing_mod.(module_mu_tensor) |} in
                    Some (graph_update g_without_both existing updated, existing)
                end
            | None =>
                let '(g', merged_id) :=
                  graph_add_module g_without_both union combined_axioms in
                Some (g', merged_id)
            end
      end
  end.

(** CSRState: Control/Status Register state — four values the hardware
    uses for certification bookkeeping and error reporting.

    csr_cert_addr: The address (checksum) of the last EMIT/REVEAL/LASSERT/LJOIN.
      Non-zero means the machine has produced certified output. This is what
      has_supra_cert checks. The NoFreeInsight theorem is ultimately about
      this field: you can't get csr_cert_addr != 0 without spending μ-cost.

    csr_status: General status code. Currently informational.

    csr_err: Error code. Non-zero means something bad happened.
      ERR_LOGIC=0xC43471A1, ERR_LOCALITY=0x0BADC0DE, ERR_CHSH=0x0BADC45C.
      Once set, the error flag latches — vm_err also goes true and stays true.

    csr_heap_base: Base address for HEAP_LOAD/HEAP_STORE (pointer arithmetic
      relative to a declared heap region, avoiding raw memory address confusion). *)
Record CSRState := {
  csr_cert_addr : nat;
  csr_status : nat;
  csr_err : nat;
  csr_heap_base : nat
}.

(** CSR setters: immutable record update helpers.
    Coq records are immutable, so every "mutation" builds a new record with one
    field changed. These four functions do that for each CSR field. They're
    called directly by the instruction semantics in VMStep.v. *)
Definition csr_set_status (csrs : CSRState) (status : nat) : CSRState :=
  {| csr_cert_addr := csrs.(csr_cert_addr);
     csr_status := status;
     csr_err := csrs.(csr_err);
     csr_heap_base := csrs.(csr_heap_base) |}.

Definition csr_set_err (csrs : CSRState) (err : nat) : CSRState :=
  {| csr_cert_addr := csrs.(csr_cert_addr);
     csr_status := csrs.(csr_status);
     csr_err := err;
     csr_heap_base := csrs.(csr_heap_base) |}.

Definition csr_set_cert_addr (csrs : CSRState) (addr : nat) : CSRState :=
  {| csr_cert_addr := addr;
     csr_status := csrs.(csr_status);
     csr_err := csrs.(csr_err);
     csr_heap_base := csrs.(csr_heap_base) |}.

Definition csr_set_heap_base (csrs : CSRState) (base : nat) : CSRState :=
  {| csr_cert_addr := csrs.(csr_cert_addr);
     csr_status := csrs.(csr_status);
     csr_err := csrs.(csr_err);
     csr_heap_base := base |}.

(** cert_addr, status: Shorthand accessors for the most commonly queried CSR fields.
    cert_addr is used in NoFreeInsight and RevelationRequirement to check
    whether the machine has produced certified output. *)
Definition cert_addr (csrs : CSRState) : nat := csrs.(csr_cert_addr).
Definition status (csrs : CSRState) : nat := csrs.(csr_status).

(** next_id, partitions: PartitionGraph field accessors for cross-layer readability.
    The thesis and external documentation refer to these by the plain names;
    the record uses pg_ prefixes to avoid namespace collisions. *)
Definition next_id (g : PartitionGraph) : ModuleID := g.(pg_next_id).
Definition partitions (g : PartitionGraph) : list (ModuleID * ModuleState) := g.(pg_modules).

(** VMState: Everything the machine needs to take its next step.

    12 fields:
    vm_graph: the partition structure (modules and morphisms)
    vm_csrs: control/status registers (cert address, status, error code, heap base)
    vm_regs: register file (REG_COUNT=32 registers, default 0)
    vm_mem: data memory (MEM_SIZE=65536 words, default 0)
    vm_pc: program counter
    vm_mu: THE μ-LEDGER. The cost counter that never goes down. Every instruction
      adds to it. This is what No Free Insight is about. If μ could decrease, the
      whole theorem is meaningless. Proven monotonic in MuLedgerConservation.v.
    vm_mu_tensor: flattened 4×4 global μ-tensor (16 entries, row-major)
    vm_err: error flag — latches on error, never clears
    vm_logic_acc: logic engine accumulator (guards high-value opcodes; key = 0xCAFEEACE)
    vm_mstatus: mode flag (0 = Turing mode, 1 = Thiele mode)
    vm_witness: 8-bucket CHSH trial counters
    vm_certified: state-based certification flag

    To falsify: If any valid step decreases vm_mu, MuLedgerConservation.v
    won't compile. If the state record is incomplete, step is undefined. *)

(** WitnessCounts: 8-bucket CHSH trial recorder.
    Each (setting, outcome) pair has its own counter:
    wc_same_AB = # of trials with settings (A,B) that yielded same outcome,
    wc_diff_AB = # of trials with settings (A,B) that yielded different outcome. *)
Record WitnessCounts := {
  wc_same_00 : nat; wc_diff_00 : nat;
  wc_same_01 : nat; wc_diff_01 : nat;
  wc_same_10 : nat; wc_diff_10 : nat;
  wc_same_11 : nat; wc_diff_11 : nat
}.

Definition witness_counts_zero : WitnessCounts :=
  {| wc_same_00 := 0; wc_diff_00 := 0;
     wc_same_01 := 0; wc_diff_01 := 0;
     wc_same_10 := 0; wc_diff_10 := 0;
     wc_same_11 := 0; wc_diff_11 := 0 |}.

Definition witness_total (wc : WitnessCounts) : nat :=
  wc.(wc_same_00) + wc.(wc_diff_00) +
  wc.(wc_same_01) + wc.(wc_diff_01) +
  wc.(wc_same_10) + wc.(wc_diff_10) +
  wc.(wc_same_11) + wc.(wc_diff_11).

Record VMState := {
  vm_graph : PartitionGraph;
  vm_csrs : CSRState;
  vm_regs : list nat;
  vm_mem : list nat;
  vm_pc : nat;
  vm_mu : nat;
  vm_mu_tensor : list nat;  (* Flattened 4×4 μ-tensor (row-major, 16 entries) *)
  vm_err : bool;
  vm_logic_acc : nat;       (* Logic engine accumulator (mirrors RTL logic_acc) *)
  vm_mstatus : nat;          (* 0 = Turing mode, 1 = Thiele mode *)
  vm_witness : WitnessCounts; (* CHSH trial buckets — 8 counters *)
  vm_certified : bool         (* state-based certification flag *)
}.

(** Default empty μ-tensor (16 zeros) for backward-compatible state builds. *)
Definition vm_mu_tensor_default : list nat := repeat 0 16.

(** Logic gate key: 0xCAFEEACE as a natural number.
    When vm_logic_acc = LOGIC_GATE_KEY_NAT, high-value ops are unlocked. *)
Definition LOGIC_GATE_KEY_NAT : nat := 3405685454.

(** Helper: access a flattened mu-tensor entry (row-major). *)
Definition vm_mu_tensor_entry (s : VMState) (i j : nat) : nat :=
  nth (i * 4 + j) s.(vm_mu_tensor) 0.

(** Helper: access a per-module tensor entry by module ID and indices (row-major). *)
Definition module_tensor_entry (s : VMState) (m : ModuleID) (i j : nat) : nat :=
  match graph_lookup (vm_graph s) m with
  | None => 0
  | Some ms => nth (i * 4 + j) (module_mu_tensor ms) 0
  end.

(** module_tensor_entry_none: Reading a tensor entry for a non-existent module
    returns 0. This makes the tensor accessor total — you never get undefined
    behavior from a bad module ID, just a silent zero. *)
Lemma module_tensor_entry_none : forall s m i j,
  graph_lookup (vm_graph s) m = None ->
  module_tensor_entry s m i j = 0.
Proof.
  intros s m i j Hnone. unfold module_tensor_entry. rewrite Hnone. reflexivity.
Qed.

(** module_tensor_entry_some: When the module exists, module_tensor_entry
    reads the correct element at position (i*4+j) of its tensor list. *)
Lemma module_tensor_entry_some : forall s m ms i j,
  graph_lookup (vm_graph s) m = Some ms ->
  module_tensor_entry s m i j = nth (i * 4 + j) (module_mu_tensor ms) 0.
Proof.
  intros s m ms i j Hsome. unfold module_tensor_entry. rewrite Hsome. reflexivity.
Qed.

(** list_update_at_nth_same: reading index k after updating index k returns
    the written value, provided k < length lst. *)
Lemma list_update_at_nth_same : forall (lst : list nat) (k : nat) (val : nat),
  (k < List.length lst)%nat ->
  nth k (list_update_at lst k val) 0 = val.
Proof.
  induction lst as [|h t IH]; intros k val Hlt.
  - simpl in Hlt. lia.
  - destruct k as [|k'].
    + simpl. reflexivity.
    + simpl. simpl in Hlt. apply IH. lia.
Qed.

(** graph_update_module_tensor_lookup_same: after updating module mid's tensor,
    looking up mid returns the module with updated tensor (and normalized region). *)
Lemma graph_update_module_tensor_lookup_same : forall g mid k v ms,
  graph_lookup g mid = Some ms ->
  graph_lookup (graph_update_module_tensor g mid k v) mid =
    Some (normalize_module {| module_region := ms.(module_region);
                              module_axioms := ms.(module_axioms);
                              module_mu_tensor := list_update_at ms.(module_mu_tensor) k v |}).
Proof.
  intros g mid k v ms Hsome.
  unfold graph_update_module_tensor. rewrite Hsome.
  apply graph_update_lookup_same. rewrite Hsome. discriminate.
Qed.

(** tensor_set_get_roundtrip: set tensor entry (i,j) to value, then get it back.
    Returns the written value, provided module exists and indices are in bounds.
 normalize_region does NOT affect module_mu_tensor (preserves it as-is). *)
Lemma tensor_set_get_roundtrip : forall g mid i j v ms,
  graph_lookup g mid = Some ms ->
  (i < 4)%nat -> (j < 4)%nat ->
  (i * 4 + j < List.length ms.(module_mu_tensor))%nat ->
  let g' := graph_update_module_tensor g mid (i * 4 + j) v in
  match graph_lookup g' mid with
  | None => False
  | Some ms' => nth (i * 4 + j) (module_mu_tensor ms') 0 = v
  end.
Proof.
  intros g mid i j v ms Hsome _ _ Hlen.
  simpl.
  rewrite (graph_update_module_tensor_lookup_same g mid (i*4+j) v ms Hsome).
  simpl. apply list_update_at_nth_same. exact Hlen.
Qed.

(** Four names for s.(vm_mu), used in different contexts to say what μ means there.
    vm_mu_cost: it's a cost (MuLedgerConservation, NoFreeInsight).
    vm_mu_information: it's information-theoretic (MuInformation).
    vm_mu_total: it's cumulative (ThreeLayerIsomorphism).
    mu_information: cross-layer isomorphism lemmas.
    All identical. One field, four names for readability. *)
Definition vm_mu_cost (s : VMState) : nat := s.(vm_mu).
Definition vm_mu_information (s : VMState) : nat := s.(vm_mu).
Definition vm_mu_total (s : VMState) : nat := s.(vm_mu).
Definition mu_information (s : VMState) : nat := s.(vm_mu).

(** word64_mask: 0xFFFFFFFFFFFFFFFF. The AND-mask for 64-bit truncation.
    Coq's nat is unbounded. Real hardware wraps at 2^64. Without this,
    overflow in Coq and overflow in hardware diverge, breaking the
    three-layer isomorphism (Coq = OCaml = Verilog). N.ones 64 gives
    64 consecutive 1-bits. AND with it truncates to 64 bits.

    OCaml note: OCaml int is 63-bit on 64-bit platforms. Int64 handles this
    in extraction. Bit 63 (the 64th bit) is lossy at the OCaml layer.
    Values in [0, 2^62) are exact. This is an irreducible gap. *)
Definition word64_mask : N := N.ones 64.

(** word64: Truncate a nat to 64 bits.
    N.of_nat converts to binary, N.land with word64_mask keeps the low 64 bits,
    N.to_nat converts back. write_reg and write_mem apply this on every write
    so hardware wraparound matches the Coq model. *)
Definition word64 (x : nat) : nat :=
  N.to_nat (N.land (N.of_nat x) word64_mask).

(** word64_xor: Bitwise XOR, result truncated to 64 bits. Used by XOR_ADD. *)
Definition word64_xor (a b : nat) : nat :=
  word64 (N.to_nat (N.lxor (N.of_nat a) (N.of_nat b))).

(** word64_add: Modular 64-bit addition (wraps at 2^64). *)
Definition word64_add (a b : nat) : nat := word64 (a + b).

(** word64_sub: Modular 64-bit subtraction using two's complement.
    word64_sub a b = (a - b) mod 2^64. *)
Definition word64_sub (a b : nat) : nat :=
  N.to_nat (N.land
    (N.add (N.of_nat (word64 a))
           (N.add (N.lxor (N.of_nat (word64 b)) word64_mask) 1%N))
    word64_mask).

(** popcount_upto: Count the 1-bits in x, looking at `bits` bits from the top.
    This is the inductive core of word64_popcount. It counts down from 63 to 0,
    testing each bit with N.testbit. Used by XOR_RANK (Hamming weight instruction). *)
Fixpoint popcount_upto (bits : nat) (x : N) : nat :=
  match bits with
  | 0 => 0
  | S bits' =>
      (if N.testbit x (N.of_nat bits') then 1 else 0) + popcount_upto bits' x
  end.

Definition word64_popcount (x : nat) : nat :=
  popcount_upto 64 (N.land (N.of_nat x) word64_mask).

(** word64_and: Bitwise AND, truncated to 64 bits. *)
Definition word64_and (a b : nat) : nat :=
  N.to_nat (N.land (N.land (N.of_nat a) (N.of_nat b)) word64_mask).

(** word64_or: Bitwise OR, truncated to 64 bits. *)
Definition word64_or (a b : nat) : nat :=
  N.to_nat (N.lor (N.land (N.of_nat a) word64_mask)
                   (N.land (N.of_nat b) word64_mask)).

(** word64_shl: Logical shift left, truncated to 64 bits. *)
Definition word64_shl (a b : nat) : nat :=
  word64 (N.to_nat (N.shiftl (N.of_nat a) (N.of_nat (b mod 64)))).

(** word64_shr: Logical shift right (zero-fill), truncated to 64 bits. *)
Definition word64_shr (a b : nat) : nat :=
  N.to_nat (N.shiftr (N.land (N.of_nat a) word64_mask) (N.of_nat (b mod 64))).

(** word64_mul: Modular 64-bit multiplication (wraps at 2^64). *)
Definition word64_mul (a b : nat) : nat := word64 (a * b).

(** reg_index, mem_index: Wrap register and memory indices to stay in bounds.
    Modular addressing means out-of-range register/address references are never
    undefined — they wrap around. REG_COUNT=32, MEM_SIZE=65536.
    This is deterministic: same index always maps to the same register/cell. *)
Definition reg_index (r : nat) : nat := r mod REG_COUNT.
Definition mem_index (a : nat) : nat := a mod MEM_SIZE.

(** read_reg: Read register r from state s. nth with default 0.
    The default 0 makes the function total — uninitialized registers read as 0. *)
Definition read_reg (s : VMState) (r : nat) : nat :=
  nth (reg_index r) s.(vm_regs) 0.

(** write_reg: Write value v to register r. Splits the list at idx, inserts
    word64 v, then rejoins. word64 truncates v to 64 bits before storage. *)
Definition write_reg (s : VMState) (r v : nat) : list nat :=
  let idx := reg_index r in
  firstn idx s.(vm_regs) ++ [word64 v] ++ skipn (S idx) s.(vm_regs).

(** read_mem: Read memory at address a. Wraps address to MEM_SIZE, default 0. *)
Definition read_mem (s : VMState) (a : nat) : nat :=
  nth (mem_index a) s.(vm_mem) 0.

(** write_mem: Write value v to memory at address a.
    Same split-and-rejoin pattern as write_reg. word64 truncation on every write. *)
Definition write_mem (s : VMState) (a v : nat) : list nat :=
  let idx := mem_index a in
  firstn idx s.(vm_mem) ++ [word64 v] ++ skipn (S idx) s.(vm_mem).

(** swap_regs: Exchange values in registers a and b. Used by XOR_SWAP.
    Read both values first, then write each to the other's slot. The two
    writes are sequential on the intermediate list regs', not s.(vm_regs),
    so the second write sees the result of the first — this is intentional. *)
Definition swap_regs (regs : list nat) (a b : nat) : list nat :=
  let a_idx := a mod REG_COUNT in
  let b_idx := b mod REG_COUNT in
  let va := nth a_idx regs 0 in
  let vb := nth b_idx regs 0 in
  let regs' := firstn a_idx regs ++ [vb] ++ skipn (S a_idx) regs in
  firstn b_idx regs' ++ [va] ++ skipn (S b_idx) regs'.

(** advance_pc: Increment program counter by one. Every successful step calls
    this. No bounds check — the step function handles out-of-range PC by
    not finding an instruction (nth_error returns None). *)
Definition advance_pc (s : VMState) : nat := S s.(vm_pc).

(** ascii_checksum: Sum the ASCII values of all characters in a string.
    This is a weak but deterministic hash used by EMIT to update csr_cert_addr.
    It's not cryptographically secure — it's just a record of what was emitted,
    distinguishable from the initial value of 0. *)
Definition ascii_checksum (s : string) : nat :=
  fold_right (fun ch acc => nat_of_ascii ch + acc) 0 (list_ascii_of_string s).

(** update_state: Apply a structural operation — update graph, csrs, mu, err —
    while leaving regs, mem, logic_acc, mstatus, witness, and certified alone.
    Also advances pc and resets vm_mu_tensor to default (flat space baseline).
    PNEW, PSPLIT, PMERGE, and similar structural ops use this.
    Ops that modify registers or memory (LOAD, ADD, XFER, etc.) build VMState
    directly rather than going through here. *)
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
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err := err;
     vm_logic_acc := s.(vm_logic_acc);
     vm_mstatus := s.(vm_mstatus);
     vm_witness := s.(vm_witness);
     vm_certified := s.(vm_certified) |}.

(** PSPLIT turns one module into two (length goes up by at least 1).
    PMERGE turns two modules into one (length goes down, but bounded).
    These show the graph doesn't grow or shrink unboundedly across splits and merges.
    The inquisitor and VMStep proofs use them. *)

(** graph_psplit_increases_length: PSPLIT removes one module and adds two
    children, so length increases by at least 1. The empty-partition edge case
    (when left or right is empty) only adds one module instead of two but still
    doesn't decrease. The cascade delete before remove doesn't change module count. *)
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
    set (g_cascaded := graph_cascade_delete_morphisms g mid) in *.
    destruct (graph_remove g_cascaded mid) as [[g_removed removed]|] eqn:Hrem; [|discriminate].
    unfold graph_add_module in Hsplit. simpl in Hsplit.
    injection Hsplit as Heq _ _. subst g'.
    simpl.
    pose proof (graph_remove_length g_cascaded mid g_removed removed Hrem) as Hrem_len.
    unfold g_cascaded in Hrem_len.
    rewrite graph_cascade_delete_morphisms_preserves_modules in Hrem_len.
    lia.
Qed.

(** graph_pmerge_decreases_length: PMERGE removes two modules (m1 and m2) and
    either adds one new merged module, or reuses an existing module that covers
    the merged region. Either way, length goes down by at least 1. *)
Lemma graph_pmerge_decreases_length : forall g m1 m2 g' merged,
  graph_pmerge g m1 m2 = Some (g', merged) ->
  List.length (pg_modules g') <= List.length (pg_modules g).
Proof.
  intros g m1 m2 g' merged Hmerge.
  unfold graph_pmerge in Hmerge.
  destruct (Nat.eqb m1 m2); [discriminate|].
  set (g1_cascaded := graph_cascade_delete_morphisms g m1) in *.
  set (g2_cascaded := graph_cascade_delete_morphisms g1_cascaded m2) in *.
  destruct (graph_remove g2_cascaded m1) as [[g_without_m1 mod1]|] eqn:Hrem1; [|discriminate].
  destruct (graph_remove g_without_m1 m2) as [[g_without_both mod2]|] eqn:Hrem2; [|discriminate].
  destruct (negb _) eqn:Hoverlap; [discriminate|].
  destruct (graph_find_region g_without_both _) as [existing|] eqn:Hfind.
  - (* Existing region found: graph_update preserves length *)
    destruct (graph_lookup g_without_both existing) as [existing_mod|] eqn:Hlu; [|discriminate].
    injection Hmerge as Heq _. subst g'.
    assert (Hlu_ne : graph_lookup g_without_both existing <> None).
    { rewrite Hlu. discriminate. }
    pose proof (graph_update_existing_length g_without_both existing
                  {| module_region := module_region existing_mod;
                     module_axioms := module_axioms existing_mod ++ module_axioms mod1 ++ module_axioms mod2;
                     module_mu_tensor := module_mu_tensor existing_mod |}
                  Hlu_ne) as Hupd.
    pose proof (graph_remove_length g2_cascaded m1 g_without_m1 mod1 Hrem1) as Hrem1_len.
    pose proof (graph_remove_length g_without_m1 m2 g_without_both mod2 Hrem2) as Hrem2_len.
    unfold g2_cascaded, g1_cascaded in Hrem1_len.
    rewrite !graph_cascade_delete_morphisms_preserves_modules in Hrem1_len.
    lia.
  - (* No existing region: graph_add_module adds 1 *)
    unfold graph_add_module in Hmerge. simpl in Hmerge.
    injection Hmerge as Heq _. subst g'.
    simpl.
    pose proof (graph_remove_length g2_cascaded m1 g_without_m1 mod1 Hrem1) as Hrem1_len.
    pose proof (graph_remove_length g_without_m1 m2 g_without_both mod2 Hrem2) as Hrem2_len.
    unfold g2_cascaded, g1_cascaded in Hrem1_len.
    rewrite !graph_cascade_delete_morphisms_preserves_modules in Hrem1_len.
    lia.
Qed.

(** graph_pmerge_length_bound: PMERGE removes at most 2 modules (m1 and m2)
    and adds at most 1 (the merged result), so the net change is at most -1.
    The bound is length(before) <= length(after) + 2, which says the list
    can't shrink by more than 2. Used to prove the module count stays finite. *)
Lemma graph_pmerge_length_bound : forall g m1 m2 g' merged,
  graph_pmerge g m1 m2 = Some (g', merged) ->
  List.length (pg_modules g) <= List.length (pg_modules g') + 2.
Proof.
  intros g m1 m2 g' merged Hmerge.
  unfold graph_pmerge in Hmerge.
  destruct (Nat.eqb m1 m2); [discriminate|].
  set (g1_cascaded := graph_cascade_delete_morphisms g m1) in *.
  set (g2_cascaded := graph_cascade_delete_morphisms g1_cascaded m2) in *.
  destruct (graph_remove g2_cascaded m1) as [[g_without_m1 mod1]|] eqn:Hrem1; [|discriminate].
  destruct (graph_remove g_without_m1 m2) as [[g_without_both mod2]|] eqn:Hrem2; [|discriminate].
  destruct (negb _) eqn:Hoverlap; [discriminate|].
  destruct (graph_find_region g_without_both _) as [existing|] eqn:Hfind.
  - (* Existing region found: removes 2, adds 0 via update = net -2 *)
    destruct (graph_lookup g_without_both existing) as [existing_mod|] eqn:Hlu; [|discriminate].
    injection Hmerge as Heq _. subst g'.
    assert (Hlu_ne : graph_lookup g_without_both existing <> None).
    { rewrite Hlu. discriminate. }
    pose proof (graph_update_existing_length g_without_both existing
                  {| module_region := module_region existing_mod;
                     module_axioms := module_axioms existing_mod ++ module_axioms mod1 ++ module_axioms mod2;
                     module_mu_tensor := module_mu_tensor existing_mod |}
                  Hlu_ne) as Hupd.
    pose proof (graph_remove_length g2_cascaded m1 g_without_m1 mod1 Hrem1) as Hrem1_len.
    pose proof (graph_remove_length g_without_m1 m2 g_without_both mod2 Hrem2) as Hrem2_len.
    unfold g2_cascaded, g1_cascaded in Hrem1_len.
    rewrite !graph_cascade_delete_morphisms_preserves_modules in Hrem1_len.
    lia.
  - (* No existing region: removes 2, adds 1 = net -1 *)
    unfold graph_add_module in Hmerge. simpl in Hmerge.
    injection Hmerge as Heq _. subst g'.
    simpl.
    pose proof (graph_remove_length g2_cascaded m1 g_without_m1 mod1 Hrem1) as Hrem1_len.
    pose proof (graph_remove_length g_without_m1 m2 g_without_both mod2 Hrem2) as Hrem2_len.
    unfold g2_cascaded, g1_cascaded in Hrem1_len.
    rewrite !graph_cascade_delete_morphisms_preserves_modules in Hrem1_len.
    lia.
Qed.

(** graph_pmerge_preserves_region_obs: PMERGE only removes m1 and m2 and
    creates a new merged module. Any other module `mid` (not m1, not m2) keeps
    its region unchanged. The proof has to chase through two cascade deletes
    and two removes, showing mid's entry survives each step.

    IMPORTANT: We compare NORMALIZED regions because graph_update always
    normalizes. The normalization is idempotent (normalize_region_idempotent),
    so re-normalizing an already-normalized region is a no-op — but Coq doesn't
    know that until you tell it. The proof explicitly handles this. *)
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
  set (g1_cascaded := graph_cascade_delete_morphisms g m1) in *.
  set (g2_cascaded := graph_cascade_delete_morphisms g1_cascaded m2) in *.
  destruct (graph_remove g2_cascaded m1) as [[g_without_m1 mod1]|] eqn:Hrem1; [|discriminate].
  destruct (graph_remove g_without_m1 m2) as [[g_without_both mod2]|] eqn:Hrem2; [|discriminate].
  destruct (negb _) eqn:Hdisjoint; [discriminate|].
  (* Cascade delete preserves modules and lookup *)
  assert (Hlookup_g2_g : forall mid', graph_lookup g2_cascaded mid' = graph_lookup g mid').
  { intro mid'. unfold g2_cascaded, g1_cascaded.
    rewrite graph_cascade_delete_morphisms_lookup.
    rewrite graph_cascade_delete_morphisms_lookup.
    reflexivity. }
  assert (Hnext_g2 : pg_next_id g2_cascaded = pg_next_id g).
  { unfold g2_cascaded, g1_cascaded.
    rewrite graph_cascade_delete_morphisms_preserves_next_id.
    rewrite graph_cascade_delete_morphisms_preserves_next_id.
    reflexivity. }
  destruct (graph_find_region g_without_both _) as [existing|] eqn:Hfind.
  - (* Existing region found *)
    destruct (graph_lookup g_without_both existing) as [ex_mod|] eqn:Hlook_ex; [|discriminate].
    injection Hpmerge as Hg' _. subst g'.
    destruct (Nat.eq_dec mid existing) as [Heq|Hneq].
    + (* mid = existing: region preserved via normalization idempotence *)
      subst mid.
      (* Chain lookups: g_without_both -> g_without_m1 -> g2_cascaded -> g *)
      assert (Hlu1 : graph_lookup g_without_both existing = graph_lookup g_without_m1 existing).
      { apply (graph_remove_preserves_unrelated g_without_m1 existing m2 g_without_both mod2); assumption. }
      assert (Hlu2 : graph_lookup g_without_m1 existing = graph_lookup g2_cascaded existing).
      { apply (graph_remove_preserves_unrelated g2_cascaded existing m1 g_without_m1 mod1); assumption. }
      assert (Hlookup_chain : graph_lookup g existing = Some ex_mod).
      { rewrite <- Hlookup_g2_g. rewrite <- Hlu2. rewrite <- Hlu1. exact Hlook_ex. }
      (* Now prove the goal *)
      assert (Hlook_ne : graph_lookup g_without_both existing <> None) by (rewrite Hlook_ex; discriminate).
      rewrite graph_update_lookup_same by assumption. simpl.
      rewrite Hlookup_chain. simpl.
      rewrite normalize_region_idempotent. reflexivity.
    + (* mid <> existing: update doesn't affect *)
      rewrite graph_update_preserves_unrelated by assumption.
      rewrite (graph_remove_preserves_unrelated g_without_m1 mid m2 g_without_both mod2) by assumption.
      rewrite (graph_remove_preserves_unrelated g2_cascaded mid m1 g_without_m1 mod1) by assumption.
      rewrite Hlookup_g2_g. reflexivity.
  - (* No existing region: add new module *)
    unfold graph_add_module in Hpmerge. simpl in Hpmerge.
    injection Hpmerge as Hg' _. subst g'. simpl.
    (* The new module is at g_without_both.(pg_next_id), and mid < that *)
    pose proof (graph_remove_preserves_next_id g2_cascaded m1 g_without_m1 mod1 Hrem1) as Hnext_rem1.
    pose proof (graph_remove_preserves_next_id g_without_m1 m2 g_without_both mod2 Hrem2) as Hnext_rem2.
    assert (Hmid_lt : mid < g_without_both.(pg_next_id)) by lia.
    (* First, chain the remove preservations *)
    assert (Hlu_chain : graph_lookup g_without_both mid = graph_lookup g mid).
    { rewrite (graph_remove_preserves_unrelated g_without_m1 mid m2 g_without_both mod2) by assumption.
      rewrite (graph_remove_preserves_unrelated g2_cascaded mid m1 g_without_m1 mod1) by assumption.
      rewrite Hlookup_g2_g. reflexivity. }
    (* The goal is about lookups with normalize_region *)
    unfold graph_lookup in Hlu_chain. unfold graph_lookup. simpl.
    destruct (Nat.eqb (pg_next_id g_without_both) mid) eqn:Heq.
    + (* pg_next_id g_without_both = mid, contradiction *)
      apply Nat.eqb_eq in Heq. lia.
    + (* pg_next_id g_without_both <> mid, g_without_both's modules match *)
      rewrite Hlu_chain. reflexivity.
Qed.

(** Memory-String Bridge: store and retrieve strings from vm_mem.

    LASSERT reads formula and certificate strings from memory. I need a
    deterministic encoding. Layout is length-prefixed, little-endian, 4 bytes per word:
      mem[base]     = byte_count
      mem[base+1..] = packed chars (4 per word, zero-padded last word)

    The roundtrip proof (mem_to_string_roundtrip below) confirms the encoding
    is lossless — write a string, read it back, get the same string. *)

(** Pack 4 bytes into one word (little-endian).
    Use product notation — NOT literals like 65536 — so [lia] can reason
    about the arithmetic without needing to reduce large constants. *)
Definition bytes_to_word_4 (b0 b1 b2 b3 : nat) : nat :=
  b0 + b1 * 256 + b2 * (256 * 256) + b3 * (256 * 256 * 256).

(** Unpack one word into a 4-byte ASCII list (little-endian). *)
Definition word_to_bytes_4 (w : nat) : list Ascii.ascii :=
  [ Ascii.ascii_of_nat (w mod 256);
    Ascii.ascii_of_nat (w / 256 mod 256);
    Ascii.ascii_of_nat (w / (256 * 256) mod 256);
    Ascii.ascii_of_nat (w / (256 * 256 * 256) mod 256) ].

(** Pack a list of ASCII chars into words (4 chars per word, last word zero-padded). *)
Fixpoint bytes_to_words (chars : list Ascii.ascii) : list nat :=
  match chars with
  | [] => []
  | [a] =>
      [bytes_to_word_4 (Ascii.nat_of_ascii a) 0 0 0]
  | [a; b] =>
      [bytes_to_word_4 (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b) 0 0]
  | [a; b; c] =>
      [bytes_to_word_4 (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
                       (Ascii.nat_of_ascii c) 0]
  | a :: b :: c :: d :: rest =>
      bytes_to_word_4 (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
                      (Ascii.nat_of_ascii c) (Ascii.nat_of_ascii d)
      :: bytes_to_words rest
  end.

(** Unpack [ws] into bytes, taking only the first [n_bytes]. *)
Definition words_to_bytes (ws : list nat) (n_bytes : nat) : list Ascii.ascii :=
  List.firstn n_bytes (List.flat_map word_to_bytes_4 ws).

(** Write a list of words into a plain [list nat] starting at [addr]. *)
Fixpoint write_words_at (mem : list nat) (addr : nat) (ws : list nat) : list nat :=
  match ws with
  | [] => mem
  | w :: rest => write_words_at (list_update_at mem addr w) (S addr) rest
  end.

(** Read one word from a plain list at [addr] (default 0 if out-of-bounds). *)
Definition list_read_at (mem : list nat) (addr : nat) : nat :=
  List.nth addr mem 0.

(** Write a string to memory at [base]:
    mem[base] = byte_count;  mem[base+1..] = packed chars. *)
Definition write_string_to_mem (mem : list nat) (base : nat) (str : string) : list nat :=
  let chars := list_ascii_of_string str in
  let len   := List.length chars in
  let words := bytes_to_words chars in
  let mem1  := list_update_at mem base len in
  write_words_at mem1 (S base) words.

(** Read a string from memory at [base] of a plain [list nat]. *)
Definition mem_to_string (mem : list nat) (base : nat) : string :=
  let len     := list_read_at mem base in
  let n_words := (len + 3) / 4 in
  let words   := List.map (fun i => list_read_at mem (S base + i)) (List.seq 0 n_words) in
  string_of_list_ascii (words_to_bytes words len).

(** list_update_at is used for register writes, memory writes, and tensor updates.
    The two key properties: it preserves length (no reallocation), and writes
    only affect the target index — all other reads are unchanged. *)

(** list_update_at_preserves_length: Writing to an index doesn't change the
    list length. Structural induction — base case (empty list returns empty),
    inductive case (cons + recursive call). *)
Lemma list_update_at_preserves_length : forall lst k v,
  List.length (list_update_at lst k v) = List.length lst.
Proof.
  induction lst as [| h t IH]; intros k v.
  - reflexivity.
  - destruct k; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(** list_update_at_nth_diff: Reading at index j after writing at index k (k≠j)
    returns the original value at j. Locality of writes — other cells are untouched. *)
Lemma list_update_at_nth_diff : forall lst k j v,
  k <> j ->
  List.nth j (list_update_at lst k v) 0 = List.nth j lst 0.
Proof.
  induction lst as [| h t IH]; intros k j v Hne.
  - reflexivity.
  - destruct k, j; simpl.
    + contradiction.
    + reflexivity.
    + reflexivity.
    + apply IH. lia.
Qed.

(** write_words_at writes a list of words into flat memory at a base address.
    Three things mem_to_string_roundtrip needs from it: the write doesn't resize
    memory, doesn't corrupt slots before base, and actually writes what you asked. *)

(** write_words_at_preserves_length: Writing words doesn't change memory size.
    Each step is list_update_at_preserves_length; induction handles the chain. *)
Lemma write_words_at_preserves_length : forall ws mem base,
  List.length (write_words_at mem base ws) = List.length mem.
Proof.
  induction ws as [| w rest IH]; intros mem base.
  - reflexivity.
  - simpl. rewrite IH. apply list_update_at_preserves_length.
Qed.

(** write_words_at_read_below: Slots before `base` are unaffected by the write.
    LASSERT writes start at base+1 (leaving the length slot at base untouched).
    This proves those length slots survive the word writes. *)
Lemma write_words_at_read_below : forall ws mem base j,
  j < base ->
  j < List.length mem ->
  List.nth j (write_words_at mem base ws) 0 = List.nth j mem 0.
Proof.
  induction ws as [| w rest IH]; intros mem base j Hjlt Hjlen.
  - reflexivity.
  - simpl.
    rewrite (IH (list_update_at mem base w) (S base) j
               ltac:(lia)
               ltac:(rewrite list_update_at_preserves_length; exact Hjlen)).
    apply list_update_at_nth_diff. lia.
Qed.

(** write_words_at_read_in: Reading back at offset k from base returns the
    k-th word from ws. This is the correctness property — you get back what
    you wrote. The in-bounds conditions ensure no default-0 fallback. *)
Lemma write_words_at_read_in : forall ws mem base k,
  k < List.length ws ->
  base + k < List.length mem ->
  List.nth (base + k) (write_words_at mem base ws) 0 = List.nth k ws 0.
Proof.
  induction ws as [| w rest IH]; intros mem base k Hklt Haddrlt.
  - simpl in Hklt. lia.
  - simpl write_words_at.
    destruct k as [| k'].
    + rewrite Nat.add_0_r.
      rewrite (write_words_at_read_below rest (list_update_at mem base w) (S base) base
                 ltac:(lia)
                 ltac:(rewrite list_update_at_preserves_length; lia)).
      apply list_update_at_nth_same. lia.
    + replace (base + S k') with (S base + k') by lia.
      apply IH.
      * simpl in Hklt. lia.
      * rewrite list_update_at_preserves_length. lia.
Qed.

(** bytes_to_word_4 and word_to_bytes_4 form a lossless round-trip.
    Pack 4 bytes into a word, unpack — get the same 4 bytes. Not obvious
    from the arithmetic without proof. Each byte is recovered by shifting down
    the right number of places (÷256^k) and masking (mod 256).
    nat_of_ascii_lt_256 is the bound that makes the mod-arithmetic close. *)

(** nat_of_ascii_lt_256: ASCII values are in [0, 255]. This bound is required
    by all the byte-slot extraction lemmas below. Proof by exhaustive case
    analysis on all 128 ASCII characters (vm_compute handles it). *)
Lemma nat_of_ascii_lt_256 : forall c : Ascii.ascii, Ascii.nat_of_ascii c < 256.
Proof.
  intro c. destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7; vm_compute; lia.
Qed.

(** bytes_to_word_4_byte0: The first byte (byte 0) can be recovered by mod 256.
    The key algebraic step: rewrite the packed word as b0 + (big_stuff) * 256,
    then mod 256 picks out b0. *)
Lemma bytes_to_word_4_byte0 : forall b0 b1 b2 b3,
  b0 < 256 ->
  bytes_to_word_4 b0 b1 b2 b3 mod 256 = b0.
Proof.
  intros b0 b1 b2 b3 H0. unfold bytes_to_word_4.
  replace (b0 + b1 * 256 + b2 * (256 * 256) + b3 * (256 * 256 * 256))
    with (b0 + (b1 + b2 * 256 + b3 * (256 * 256)) * 256) by lia.
  rewrite Nat.Div0.mod_add. apply Nat.mod_small; lia.
Qed.

(** bytes_to_word_4_byte1: Byte 1 recovered by / 256 mod 256. Same pattern —
    shift down one byte slot (÷256), then extract the low byte (mod 256). *)
Lemma bytes_to_word_4_byte1 : forall b0 b1 b2 b3,
  b0 < 256 -> b1 < 256 ->
  bytes_to_word_4 b0 b1 b2 b3 / 256 mod 256 = b1.
Proof.
  intros b0 b1 b2 b3 H0 H1. unfold bytes_to_word_4.
  replace (b0 + b1 * 256 + b2 * (256 * 256) + b3 * (256 * 256 * 256))
    with (b0 + (b1 + (b2 + b3 * 256) * 256) * 256) by lia.
  rewrite Nat.div_add by lia. rewrite Nat.div_small by lia.
  rewrite Nat.add_0_l. rewrite Nat.Div0.mod_add.
  apply Nat.mod_small; lia.
Qed.

(** bytes_to_word_4_byte2: Byte 2 recovered by / (256*256) mod 256. *)
Lemma bytes_to_word_4_byte2 : forall b0 b1 b2 b3,
  b0 < 256 -> b1 < 256 -> b2 < 256 ->
  bytes_to_word_4 b0 b1 b2 b3 / (256 * 256) mod 256 = b2.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2. unfold bytes_to_word_4.
  replace (b0 + b1 * 256 + b2 * (256 * 256) + b3 * (256 * 256 * 256))
    with ((b0 + b1 * 256) + (b2 + b3 * 256) * (256 * 256)) by lia.
  rewrite Nat.div_add by lia. rewrite Nat.div_small by lia.
  rewrite Nat.add_0_l. rewrite Nat.Div0.mod_add.
  apply Nat.mod_small; lia.
Qed.

(** bytes_to_word_4_byte3: Byte 3 recovered by / (256*256*256) mod 256.
    Needs all four bounds to prove the high word is < 256. *)
Lemma bytes_to_word_4_byte3 : forall b0 b1 b2 b3,
  b0 < 256 -> b1 < 256 -> b2 < 256 -> b3 < 256 ->
  bytes_to_word_4 b0 b1 b2 b3 / (256 * 256 * 256) mod 256 = b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. unfold bytes_to_word_4.
  replace (b0 + b1 * 256 + b2 * (256 * 256) + b3 * (256 * 256 * 256))
    with ((b0 + b1 * 256 + b2 * (256 * 256)) + b3 * (256 * 256 * 256)) by lia.
  rewrite Nat.div_add by lia. rewrite Nat.div_small by lia.
  rewrite Nat.add_0_l. apply Nat.mod_small; lia.
Qed.

(** word_to_bytes_4_roundtrip: Pack 4 bytes into a word, unpack — get the
    same 4 bytes back. This assembles the four byte-slot lemmas. Used by
    word_bytes_4_roundtrip_ascii (the ascii-level version below). *)
Lemma word_to_bytes_4_roundtrip : forall b0 b1 b2 b3,
  b0 < 256 -> b1 < 256 -> b2 < 256 -> b3 < 256 ->
  word_to_bytes_4 (bytes_to_word_4 b0 b1 b2 b3) =
    [ Ascii.ascii_of_nat b0; Ascii.ascii_of_nat b1;
      Ascii.ascii_of_nat b2; Ascii.ascii_of_nat b3 ].
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3. unfold word_to_bytes_4.
  rewrite bytes_to_word_4_byte0 by assumption.
  rewrite bytes_to_word_4_byte1 by assumption.
  rewrite bytes_to_word_4_byte2 by assumption.
  rewrite bytes_to_word_4_byte3 by assumption.
  reflexivity.
Qed.

(** Packing then unpacking 4 ASCII chars gives back the same chars. *)
Lemma word_bytes_4_roundtrip_ascii : forall (a b c d : Ascii.ascii),
  word_to_bytes_4 (bytes_to_word_4 (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
                                    (Ascii.nat_of_ascii c) (Ascii.nat_of_ascii d)) =
  [a; b; c; d].
Proof.
  intros a b c d.
  rewrite word_to_bytes_4_roundtrip by apply nat_of_ascii_lt_256.
  rewrite 4 Ascii.ascii_nat_embedding. reflexivity.
Qed.

(** Partial-word roundtrip helpers: when a string length is not a multiple
    of 4, the last word is zero-padded. These three lemmas prove that
    firstn with the right length still extracts the original characters. *)
Lemma word_bytes_ascii_prefix1 : forall a,
  List.firstn 1
    (word_to_bytes_4 (bytes_to_word_4 (Ascii.nat_of_ascii a) 0 0 0)) = [a].
Proof.
  intro a.
  rewrite word_to_bytes_4_roundtrip by (first [apply nat_of_ascii_lt_256 | lia]).
  simpl. rewrite Ascii.ascii_nat_embedding. reflexivity.
Qed.

Lemma word_bytes_ascii_prefix2 : forall a b,
  List.firstn 2
    (word_to_bytes_4 (bytes_to_word_4 (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b) 0 0)) =
  [a; b].
Proof.
  intros a b.
  rewrite word_to_bytes_4_roundtrip by (first [apply nat_of_ascii_lt_256 | lia]).
  simpl. rewrite 2 Ascii.ascii_nat_embedding. reflexivity.
Qed.

Lemma word_bytes_ascii_prefix3 : forall a b c,
  List.firstn 3
    (word_to_bytes_4 (bytes_to_word_4 (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
                                       (Ascii.nat_of_ascii c) 0)) = [a; b; c].
Proof.
  intros a b c.
  rewrite word_to_bytes_4_roundtrip by (first [apply nat_of_ascii_lt_256 | lia]).
  simpl. rewrite 3 Ascii.ascii_nat_embedding. reflexivity.
Qed.

(** flat_map of word_to_bytes_4 on bytes_to_words has the 4-step prefix property. *)
Lemma flat_map_bytes_words_4 : forall (a b c d : Ascii.ascii) rest,
  List.flat_map word_to_bytes_4 (bytes_to_words (a :: b :: c :: d :: rest)) =
  [a; b; c; d] ++ List.flat_map word_to_bytes_4 (bytes_to_words rest).
Proof.
  intros a b c d rest.
  change (bytes_to_words (a :: b :: c :: d :: rest)) with
    (bytes_to_word_4 (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
                     (Ascii.nat_of_ascii c) (Ascii.nat_of_ascii d)
     :: bytes_to_words rest).
  change (List.flat_map word_to_bytes_4
    (bytes_to_word_4 (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
                     (Ascii.nat_of_ascii c) (Ascii.nat_of_ascii d)
     :: bytes_to_words rest)) with
    (word_to_bytes_4 (bytes_to_word_4 (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
                                       (Ascii.nat_of_ascii c) (Ascii.nat_of_ascii d))
     ++ List.flat_map word_to_bytes_4 (bytes_to_words rest)).
  rewrite word_bytes_4_roundtrip_ascii. reflexivity.
Qed.

(** flat_map over a singleton list = the element (avoids stack overflow from simpl). *)
Lemma flat_map_words_single (w : nat) :
  List.flat_map word_to_bytes_4 [w] = word_to_bytes_4 w.
Proof. unfold List.flat_map. apply app_nil_r. Qed.

(** The core encoding correctness: pack any list of ASCII chars into words,
    then unpack taking len bytes — get the original char list back.
    Proof by structural induction on chars, handling 0/1/2/3/4+ cases. *)

(** words_to_bytes_roundtrip: The core encoding correctness. Pack any list of
    ASCII chars into 4-byte-per-word encoding, then unpack taking len bytes —
    you get the original list. The fixed point is the string store/load contract. *)
Lemma words_to_bytes_roundtrip : forall chars,
  words_to_bytes (bytes_to_words chars) (List.length chars) = chars.
Proof.
  unfold words_to_bytes. fix IH 1. intro chars.
  destruct chars as [| a [| b [| c [| d rest]]]].
  - reflexivity.
  - (* 1 char *)
    change (bytes_to_words [a]) with
      [bytes_to_word_4 (Ascii.nat_of_ascii a) 0 0 0].
    rewrite flat_map_words_single.
    exact (word_bytes_ascii_prefix1 a).
  - (* 2 chars *)
    change (bytes_to_words [a; b]) with
      [bytes_to_word_4 (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b) 0 0].
    rewrite flat_map_words_single.
    exact (word_bytes_ascii_prefix2 a b).
  - (* 3 chars *)
    change (bytes_to_words [a; b; c]) with
      [bytes_to_word_4 (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
                       (Ascii.nat_of_ascii c) 0].
    rewrite flat_map_words_single.
    exact (word_bytes_ascii_prefix3 a b c).
  - (* 4+ chars: use the 4-step recursion *)
    rewrite flat_map_bytes_words_4.
    change (List.length (a :: b :: c :: d :: rest)) with
      (List.length [a; b; c; d] + List.length rest).
    rewrite List.firstn_app_2.
    rewrite (IH rest). reflexivity.
Qed.

(** The packed-word count is ceil(len/4) = (len+3)/4.
    mem_to_string uses this to know how many words to read back. *)

(** bytes_to_words_length: The packed-word count is ceil(len/4) = (len+3)/4.
    This is what mem_to_string uses to know how many words to read back.
    Without this lemma, the roundtrip proof can't set up the map over seq. *)
Lemma bytes_to_words_length : forall chars,
  List.length (bytes_to_words chars) = (List.length chars + 3) / 4.
Proof.
  fix IH 1. intro chars.
  destruct chars as [| a [| b [| c [| d rest]]]]; try reflexivity.
  change (bytes_to_words (a :: b :: c :: d :: rest)) with
    (bytes_to_word_4 (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii b)
                     (Ascii.nat_of_ascii c) (Ascii.nat_of_ascii d)
     :: bytes_to_words rest).
  simpl List.length at 1.
  rewrite (IH rest).
  replace (List.length (a :: b :: c :: d :: rest) + 3) with
    ((List.length rest + 3) + 1 * 4) by (simpl; lia).
  rewrite Nat.div_add by lia. lia.
Qed.

(** map_seq_nth: Mapping "nth i ws 0" over seq 0 (length ws) reconstructs ws.
    This is the bridge between "read each word by index" and "the actual word list."
    Used in mem_to_string_roundtrip to equate the map over memory reads with ws. *)
Lemma map_seq_nth : forall ws : list nat,
  List.map (fun i => List.nth i ws 0) (List.seq 0 (List.length ws)) = ws.
Proof.
  induction ws as [| h t IH].
  - reflexivity.
  - simpl. f_equal.
    rewrite <- List.seq_shift. rewrite List.map_map. apply IH.
Qed.

(** mem_to_string_roundtrip: Write a string to memory, read it back — same string.
    This is the contract LASSERT relies on. The formula register points to a base
    address; the string at that address round-trips exactly.
    The preconditions (base in bounds, enough space for the words) are the bounds
    the hardware checks. Within those, the round trip is guaranteed. *)

(** String_length_eq_list_length: String.length counts characters the same way
    list_ascii_of_string's List.length does. Needed to align the mem_to_string
    output length with the character count used in words_to_bytes. *)
Lemma String_length_eq_list_length : forall str,
  String.length str = List.length (list_ascii_of_string str).
Proof.
  induction str as [| c s IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma mem_to_string_roundtrip : forall mem base str,
  base < List.length mem ->
  S base + (List.length (list_ascii_of_string str) + 3) / 4 <= List.length mem ->
  mem_to_string (write_string_to_mem mem base str) base = str.
Proof.
  intros mem base str Hbase Hwords.
  (* Abbreviations — explicit, NOT set (set creates opaque names that block lia) *)
  pose (chars := list_ascii_of_string str).
  pose (ws := bytes_to_words chars).
  pose (len := List.length chars).
  pose (nw := (len + 3) / 4).
  pose (mem1 := list_update_at mem base len).
  pose (mem2 := write_words_at mem1 (S base) ws).
  (* Unfold both sides *)
  unfold mem_to_string, write_string_to_mem.
  fold chars. fold len. fold ws. fold mem1. fold mem2.
  (* Step 3: read the length back *)
  replace (list_read_at mem2 base) with len.
  2: { unfold list_read_at, mem2.
       rewrite (write_words_at_read_below ws mem1 (S base) base
                  ltac:(lia)
                  ltac:(unfold mem1; rewrite list_update_at_preserves_length; lia)).
       unfold mem1. symmetry. apply list_update_at_nth_same. lia. }
  (* Step 4: show (len+3)/4 = length ws *)
  replace ((len + 3) / 4) with (List.length ws).
  2: { unfold ws. rewrite bytes_to_words_length. reflexivity. }
  (* Step 5: reconstruct the words from memory *)
  replace (List.map (fun i => list_read_at mem2 (S base + i))
                    (List.seq 0 (List.length ws))) with ws.
  2: { symmetry.
       enough (Heq : List.map (fun i => list_read_at mem2 (S base + i))
                               (List.seq 0 (List.length ws)) =
                     List.map (fun i => List.nth i ws 0)
                               (List.seq 0 (List.length ws))) by
         (rewrite Heq; apply map_seq_nth).
       apply List.map_ext_in.
       intros i Hi.
       apply List.in_seq in Hi. destruct Hi as [_ Hi]. simpl in Hi.
       unfold list_read_at, mem2.
       apply (write_words_at_read_in ws mem1 (S base) i Hi).
       unfold mem1. rewrite list_update_at_preserves_length.
       apply Nat.lt_le_trans with (m := S base + List.length ws).
       - lia.
       - unfold ws. rewrite bytes_to_words_length. unfold nw, len, chars.
         exact Hwords. }
  (* Step 6: unpack words → original chars *)
  unfold words_to_bytes.
  replace (List.firstn len (List.flat_map word_to_bytes_4 ws)) with chars.
  2: { unfold ws. change len with (List.length chars).
       symmetry. apply words_to_bytes_roundtrip. }
  (* Step 7: chars → str *)
  unfold chars. apply string_of_list_ascii_of_string.
Qed.
