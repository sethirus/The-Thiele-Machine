(** * Entanglement Entropy Over PSPLIT Subsystems

    WHY THIS FILE EXISTS:
    The PSPLIT instruction creates a bipartite decomposition of a parent
    module region into two disjoint child regions. This file adds the minimal
    formal scaffolding needed to talk about reduced states and entropy over
    that split.

    SCOPE OF THIS FILE:
    - partial trace is represented at support level (projection of joint
      support onto one subsystem)
    - entanglement entropy is represented in bits via log2_up of reduced
      support size
    - area law is expressed as a boundary-scaling theorem under a locality
      hypothesis that reduced support is bounded by boundary degrees of freedom

    This is the next formal step toward a Srednicki-style chain inside the
    current VM/PSPLIT representation.
*)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.
From Kernel Require Import LocalMorphismSemantics.

(** A successful PSPLIT witness over a partition graph. *)
Definition psplit_subsystems
  (g g' : PartitionGraph)
  (parent : ModuleID)
  (left right : list nat)
  (left_id right_id : ModuleID) : Prop :=
  graph_psplit g parent left right = Some (g', left_id, right_id).

(** Boundary edges on a 1D cell lattice: an edge crosses the split when
    consecutive cells belong to opposite regions. *)
Definition cut_edge_1d (left right : list nat) (x : nat) : bool :=
  orb (andb (nat_list_mem x left) (nat_list_mem (S x) right))
      (andb (nat_list_mem x right) (nat_list_mem (S x) left)).

(** Boundary size of the split interface (1D discretization). *)
Definition boundary_size_1d (left right : list nat) : nat :=
  List.length (filter (cut_edge_1d left right)
    (normalize_region (left ++ right))).

(** Joint support of a bipartite state in finite coordinates (a,b). *)
Definition joint_support := list (nat * nat).

(** Partial trace over the right subsystem at support level:
    project support onto left coordinates. *)
Definition partial_trace_right_support (support : joint_support) : list nat :=
  nodup Nat.eq_dec (map fst support).

(** Symmetric projection onto right coordinates. *)
Definition partial_trace_left_support (support : joint_support) : list nat :=
  nodup Nat.eq_dec (map snd support).

(** Reduced-state support on subsystem A after tracing out B. *)
Definition reduced_state_support (support : joint_support) : list nat :=
  partial_trace_right_support support.

(** Entanglement entropy in bits for this finite support model.
    (Support/rank-level surrogate for von Neumann entropy in this setting.) *)
Definition entanglement_entropy_vn_bits (support : joint_support) : nat :=
  Nat.log2_up (List.length (reduced_state_support support)).

(** Locality hypothesis: reduced support is controlled by boundary dof.
    This is the discrete boundary-scaling input corresponding to the
    Srednicki-style area-law step. *)
Definition boundary_local_support
  (left right : list nat)
  (support : joint_support) : Prop :=
  List.length (reduced_state_support support) <=
  Nat.pow 2 (boundary_size_1d left right).

Lemma length_nodup_le :
  forall xs,
    List.length (nodup Nat.eq_dec xs) <= List.length xs.
Proof.
  induction xs as [|x xs IH]; simpl; [lia|].
  destruct (in_dec Nat.eq_dec x xs); simpl; lia.
Qed.

(** Partial-trace support cannot exceed joint support size. *)
Lemma partial_trace_right_support_length_le :
  forall support,
    List.length (partial_trace_right_support support) <= List.length support.
Proof.
  intro support.
  unfold partial_trace_right_support.
  eapply Nat.le_trans.
  - apply length_nodup_le.
  - rewrite map_length. lia.
Qed.

(** If PSPLIT succeeds from a known parent module, either the split is in the
    explicit empty-branch case, or partition_valid holds on normalized regions. *)
Lemma graph_psplit_success_partition_or_empty :
  forall g g' parent left right left_id right_id m,
    graph_lookup g parent = Some m ->
    graph_psplit g parent left right = Some (g', left_id, right_id) ->
    orb (Nat.eqb (List.length (normalize_region left)) 0)
        (Nat.eqb (List.length (normalize_region right)) 0) = true \/
    partition_valid (module_region m)
      (normalize_region left)
      (normalize_region right) = true.
Proof.
  intros g g' parent left right left_id right_id m Hlookup Hsplit.
  unfold graph_psplit in Hsplit.
  rewrite Hlookup in Hsplit.
  destruct (orb (Nat.eqb (List.length (normalize_region left)) 0)
                (Nat.eqb (List.length (normalize_region right)) 0)) eqn:Hempty.
  - left. reflexivity.
  - destruct (partition_valid (module_region m)
      (normalize_region left) (normalize_region right)) eqn:Hpart.
    + right. reflexivity.
    + discriminate Hsplit.
Qed.

(** Area-law theorem (bits): if reduced support is boundary-local,
    entanglement entropy is bounded by interface size. *)
Theorem entanglement_entropy_area_law_bits :
  forall left right support,
    boundary_local_support left right support ->
    entanglement_entropy_vn_bits support <= boundary_size_1d left right.
Proof.
  intros left right support Hlocal.
  unfold boundary_local_support, entanglement_entropy_vn_bits in *.
  destruct (List.length (reduced_state_support support)) as [|n] eqn:Hlen.
  - rewrite (Nat.log2_up_nonpos 0) by lia. lia.
  - pose proof (Nat.log2_up_le_pow2
      (S n)
      (boundary_size_1d left right)
      (Nat.lt_0_succ n)) as Hiff.
    apply (proj1 Hiff).
    exact Hlocal.
Qed.

(** PSPLIT-indexed form: same bound over normalized split regions. *)
Theorem psplit_entanglement_entropy_area_law_bits :
  forall g g' parent left right left_id right_id support,
    psplit_subsystems g g' parent left right left_id right_id ->
    boundary_local_support (normalize_region left) (normalize_region right) support ->
    entanglement_entropy_vn_bits support <=
    boundary_size_1d (normalize_region left) (normalize_region right).
Proof.
  intros g g' parent left right left_id right_id support _ Hlocal.
  apply entanglement_entropy_area_law_bits.
  exact Hlocal.
Qed.

(** Bridge theorem: locality can be discharged from split-morphism semantics.
    This connects the nearest-neighbor morphism assumption to the
    boundary_local_support premise used by area-law arithmetic. *)
Theorem local_morphism_entropy_area_law_bits :
  forall (P : LocalMorphismSemantics.SplitMorphism)
         (support : LocalMorphismSemantics.joint_support),
    LocalMorphismSemantics.is_nearest_neighbor P ->
    In support (LocalMorphismSemantics.morphism_support_semantics P) ->
    entanglement_entropy_vn_bits support <=
    boundary_size_1d
      (LocalMorphismSemantics.split_left P)
      (LocalMorphismSemantics.split_right P).
Proof.
  intros P support Hnn Hin.
  apply entanglement_entropy_area_law_bits.
  unfold boundary_local_support,
    LocalMorphismSemantics.boundary_local_support,
    reduced_state_support,
    LocalMorphismSemantics.reduced_state_support,
    partial_trace_right_support,
    LocalMorphismSemantics.partial_trace_right_support,
    boundary_size_1d,
    LocalMorphismSemantics.boundary_size_1d,
    cut_edge_1d,
    LocalMorphismSemantics.cut_edge_1d.
  exact (LocalMorphismSemantics.local_morphism_support_bound P support Hnn Hin).
Qed.
