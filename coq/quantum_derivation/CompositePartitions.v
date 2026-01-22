(** =========================================================================
    PHASE 1.1: COMPOSITE PARTITIONS
    =========================================================================
    
    STATUS: VERIFIED
    ADMITS: 0
    AXIOMS: A1 (Variables), A2 (Cardinality)
    
    GOAL: Formalize composition of disjoint partition modules and prove
    that composite state space dimensions multiply.
    
    KEY THEOREM: composite_state_space_multiplicative
      - dim(P1 ∪ P2) = dim(P1) × dim(P2) for disjoint partitions
      - This is the foundation for tensor product necessity (Phase 1.2)
    
    ========================================================================= *)

From Coq Require Import List ZArith Lia Bool Nat.
Import ListNotations.
Local Open Scope Z_scope.

(** Use existing partition definitions from thielemachine proofs *)
Require Import ThieleMachine.CoreSemantics.
Require Import ThieleMachine.CompositionPrimitive.

(** =========================================================================
    DEFINITIONS: Composite Partition Systems
    ========================================================================= *)

(** Two partitions are disjoint if they operate on separate variable sets *)
Definition partitions_disjoint (p1 p2 : Partition) : Prop :=
  forall mid1 r1 mid2 r2,
    In (mid1, r1) p1.(modules) ->
    In (mid2, r2) p2.(modules) ->
    forall v, In v r1 -> ~ In v r2.

(** Composition of two disjoint partitions *)
Definition partition_compose (p1 p2 : Partition) : Partition :=
  {| modules := p1.(modules) ++ p2.(modules);
     next_module_id := max p1.(next_module_id) p2.(next_module_id) |}.

(** Import helper definitions from CoreSemantics *)
Definition disjoint_b (r1 r2 : Region) : bool :=
  forallb (fun x => negb (existsb (Nat.eqb x) r2)) r1.

Fixpoint regions_disjoint_b (regions : list Region) : bool :=
  match regions with
  | [] => true
  | r :: rest =>
      (forallb (fun r' => disjoint_b r r') rest) &&
      regions_disjoint_b rest
  end.

(** Helper: appending disjoint region lists preserves disjointness *)
Lemma regions_disjoint_b_app : forall l1 l2,
  regions_disjoint_b l1 = true ->
  regions_disjoint_b l2 = true ->
  (forall r1 r2, In r1 l1 -> In r2 l2 -> disjoint_b r1 r2 = true) ->
  regions_disjoint_b (l1 ++ l2) = true.
Proof.
  induction l1 as [| r1 rest1 IH].
  - (* Base: [] ++ l2 = l2 *)
    intros l2 _ H2 _.
    simpl. exact H2.
  - (* Inductive: (r1 :: rest1) ++ l2 *)
    intros l2 H1 H2 Hcross.
    simpl in H1.
    apply Bool.andb_true_iff in H1.
    destruct H1 as [Hforall Hrest].
    simpl.
    apply Bool.andb_true_iff.
    split.
    + (* r1 disjoint from all in rest1 ++ l2 *)
      apply forallb_forall.
      intros r' Hin'.
      apply in_app_or in Hin'.
      destruct Hin' as [Hin'_rest | Hin'_l2].
      * (* r' in rest1 *)
        apply forallb_forall with (x := r') in Hforall; auto.
      * (* r' in l2 *)
        apply Hcross; simpl; auto.
    + (* rest1 ++ l2 disjoint *)
      apply IH; auto.
      intros r1' r2' Hin1 Hin2.
      apply Hcross; simpl; auto.
Qed.

(** Well-formedness of composite partition *)
Theorem composite_partition_valid : forall p1 p2,
  partition_valid p1 ->
  partition_valid p2 ->
  partitions_disjoint p1 p2 ->
  partition_valid (partition_compose p1 p2).
Proof.
  intros p1 p2 Hvalid1 Hvalid2 Hdisj.
  unfold partition_valid, partition_valid_b in *.
  unfold partition_compose.
  simpl modules.
  
  (* Goal: regions_disjoint_b (map snd (modules p1 ++ modules p2)) = true *)
  rewrite map_app.
  (* Goal: regions_disjoint_b (map snd (modules p1) ++ map snd (modules p2)) = true *)
  
  apply regions_disjoint_b_app.
  - (* regions_disjoint_b (map snd p1.modules) = true *)
    exact Hvalid1.
  - (* regions_disjoint_b (map snd p2.modules) = true *)
    exact Hvalid2.
  - (* Cross disjointness *)
    intros r1 r2 Hin1 Hin2.
    (* r1 from p1, r2 from p2, must show disjoint_b r1 r2 = true *)
    apply forallb_forall.
    intros v Hv.
    apply Bool.negb_true_iff.
    apply Bool.not_true_iff_false.
    intro Hexists.
    apply existsb_exists in Hexists.
    destruct Hexists as [v' [Hin' Heq]].
    apply Nat.eqb_eq in Heq.
    subst v'.
    
    (* Now we need to connect to partitions_disjoint *)
    (* r1 ∈ map snd p1.modules, so ∃ mid1, (mid1, r1) ∈ p1.modules *)
    apply in_map_iff in Hin1.
    destruct Hin1 as [[mid1 r1'] [Hr1_eq Hin1]].
    simpl in Hr1_eq. subst r1'.
    
    (* Similarly for r2 *)
    apply in_map_iff in Hin2.
    destruct Hin2 as [[mid2 r2'] [Hr2_eq Hin2]].
    simpl in Hr2_eq. subst r2'.
    
    (* Apply partitions_disjoint *)
    unfold partitions_disjoint in Hdisj.
    eapply Hdisj; eauto.
Qed.

(** =========================================================================
    STATE SPACE STRUCTURE
    ========================================================================= *)

(** State space of a partition is the Cartesian product of module spaces *)
(** For now, we define this abstractly - will connect to tensor products *)

(** The "state space dimension" for a list of modules *)
Fixpoint modules_state_dim (mods : list (ModuleId * Region)) : nat :=
  match mods with
  | [] => 1  (* Empty has trivial 1D space *)
  | (_, r) :: rest => 
      (* Each module with n variables contributes 2^n dimensions *)
      (2 ^ (length r)) * (modules_state_dim rest)
  end.

(** The state space dimension of a partition *)
Definition partition_state_dim (p : Partition) : nat :=
  modules_state_dim p.(modules).

(** Helper lemma: dimensions multiply over list append *)
Lemma modules_state_dim_app : forall l1 l2,
  (modules_state_dim (l1 ++ l2) = modules_state_dim l1 * modules_state_dim l2)%nat.
Proof.
  induction l1 as [| [mid r] rest IH].
  - (* Base case: [] ++ l2 = l2 *)
    simpl.
    lia.
  - (* Inductive case: ((mid, r) :: rest) ++ l2 *)
    intro l2.
    simpl.
    rewrite IH.
    (* Goal: (2^|r| * (modules_state_dim rest * modules_state_dim l2))%nat
            = (2^|r| * modules_state_dim rest) * modules_state_dim l2 *)
    lia.
Qed.

(** KEY THEOREM: Composite state space dimensions multiply *)
Theorem composite_state_space_multiplicative : forall p1 p2,
  partitions_disjoint p1 p2 ->
  partition_state_dim (partition_compose p1 p2) = 
    ((partition_state_dim p1) * (partition_state_dim p2))%nat.
Proof.
  intros p1 p2 Hdisj.
  unfold partition_compose, partition_state_dim.
  simpl.
  
  (* Apply the helper lemma directly *)
  apply modules_state_dim_app.
Qed.

(** =========================================================================
    INDEPENDENCE PROPERTY
    ========================================================================= *)

(** Operations on p1 don't affect state of p2 when disjoint *)
(** This is the KEY property that will force tensor product structure *)

(** FUTURE WORK: Connect to State and step_state from CoreSemantics
    This is deferred to maintain current proof obligations focus. *)
(*
Definition partition_operation_local (p : Partition) (op : Instruction) : Prop :=
  forall s s',
    step_state s op = Some s' ->
    (* If op only touches variables in p, other partitions unchanged *)
    True. (* FUTURE WORK: Formalize precisely - see Phase 1.3 *)
*)

(** =========================================================================
    NEXT STEPS
    ========================================================================= *)

(** FUTURE WORK for Phase 1.2 (TensorNecessity.v):
    
    1. Show that direct sum composition violates no-signaling
       - Direct sum: state = (state_p1, state_p2)
       - Problem: Measuring p1 might give info about p2
       
    2. Show that tensor product composition preserves locality
       - Tensor: state = state_p1 ⊗ state_p2  
       - Property: Tr_p1(ρ) independent of operations on p2
       
    3. Prove: Multiplicative dimensions + independence → tensor structure
    
    This will establish that tensor products are NECESSARY for
    partition consistency.
    *)

(** =========================================================================
    ADDITIONAL LEMMAS
    ========================================================================= *)

(** Partition state dimension is always at least 1 *)
Lemma partition_state_dim_positive : forall p : Partition,
  (partition_state_dim p >= 1)%nat.
Proof.
  intro p.
  unfold partition_state_dim.
  induction (modules p) as [| [mid r] rest IH].
  - (* Base case: empty modules list has dimension 1 *)
    simpl. lia.
  - (* Inductive case: (2^n) * dim(rest) where both >= 1 *)
    simpl.
    (* 2^(length r) is at least 2^0 = 1 *)
    (* dim(rest) >= 1 by IH *)
    (* So their product >= 1 *)
    destruct (2 ^ length r)%nat eqn:Hpow.
    + (* Impossible: 2^n is never 0 *)
      exfalso. apply (Nat.pow_nonzero 2 (length r)). lia. exact Hpow.
    + (* 2^n = S k, and rest >= 1, so (S k) * rest >= 1 *)
      lia.
Qed.

(** =========================================================================
    VERIFICATION
    ========================================================================= *)

(** Print assumptions to verify we're not using hidden axioms *)
(* Print Assumptions composite_partition_valid. *)
(* Expected: Closed under the global context *)
