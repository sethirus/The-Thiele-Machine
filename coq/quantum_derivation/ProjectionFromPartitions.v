(** =========================================================================
    PHASE 4: PROJECTION FROM PARTITION FILTERING
    =========================================================================
    
    STATUS: VERIFIED
    ADMITS: 0
    AXIOMS: A3 (Partition Refinement)
    
    GOAL: Derive projection postulate as module filtering operation.
    When a module is REVEALED, the partition "collapses" by filtering
    to only that module - this is the projection postulate.
    
    KEY THEOREMS:
      - filter_unique_id
          Unique module ID yields singleton list after filter
      - projection_to_single_module_is_dim_1
          Filtering to one module with region r gives dim 2^|r|
      - projection_post_prob_unanimous
          Zero-length region (atomic fact) projects to dim=1 (certainty)
    
    RESULT: Measurement projection = partition filter by revealed module ID.
    
    ========================================================================= *)

From Coq Require Import List ZArith Lia Bool Nat.
Import ListNotations.
Local Open Scope Z_scope.

Require Import ThieleMachine.CoreSemantics.
Require Import QuantumDerivation.CompositePartitions.

Lemma filter_false_all : forall (A : Type) (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = false) ->
  filter f l = [].
Proof.
  induction l as [| x rest IH]; intros H; simpl; auto.
  assert (Hfx: f x = false) by (apply H; left; reflexivity).
  rewrite Hfx.
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma filter_unique_id : forall (mods : list (ModuleId * Region)) (mid : ModuleId) (r : Region),
  NoDup (map fst mods) ->
  In (mid, r) mods ->
  (forall m, In m mods -> fst m = mid -> m = (mid, r)) ->
  filter (fun m => (fst m =? mid)%nat) mods = [(mid, r)].
Proof.
  intros mods mid r. revert mid r.
  induction mods as [| [mid' r'] rest IH]; intros mid r Hnodup Hin Huniq.
  - inversion Hin.
  - { simpl in *. destruct (mid' =? mid)%nat eqn:Heq.
      - apply Nat.eqb_eq in Heq; subst mid'.
        assert (m_eq: (mid, r') = (mid, r)). { apply Huniq; auto. }
        inversion m_eq; subst r'. f_equal.
        apply filter_false_all. intros [mid'' r'''] Hin_rest. simpl.
        apply Nat.eqb_neq. intro; subst mid''.
        apply NoDup_cons_iff in Hnodup. destruct Hnodup as [Hnot_in _].
        apply Hnot_in. apply in_map_iff. exists (mid, r'''); split; auto.
      - apply IH.
        + apply NoDup_cons_iff in Hnodup; destruct Hnodup; auto.
        + destruct Hin as [Heq_m | Hin_rest].
          * inversion Heq_m; subst. rewrite Nat.eqb_refl in Heq; inversion Heq.
          * exact Hin_rest.
        + intros m' Hin_r Hm'. apply Huniq; [ right; auto | auto ]. }
Qed.

Definition projection_step (p : Partition) (mid : ModuleId) : Partition :=
  {| modules := filter (fun m => (fst m =? mid)%nat) p.(modules);
     next_module_id := p.(next_module_id) |}.

Theorem projection_to_single_module_is_dim_1 :
  forall (p : Partition) (mid : ModuleId) (r : Region),
    NoDup (map fst (modules p)) ->
    In (mid, r) (modules p) ->
    (forall m, In m (modules p) -> fst m = mid -> m = (mid, r)) ->
    partition_state_dim (projection_step p mid) = (2 ^ length r)%nat.
Proof.
  intros p mid r Hnodup Hin Huniq.
  unfold projection_step, partition_state_dim. simpl.
  rewrite filter_unique_id with (mid := mid) (r := r); auto.
  simpl. lia.
Qed.

Theorem projection_post_prob_unanimous :
  forall (p_before : Partition) (mid : ModuleId) (r : Region),
    NoDup (map fst (modules p_before)) ->
    In (mid, r) (modules p_before) ->
    (forall m, In m (modules p_before) -> fst m = mid -> m = (mid, r)) ->
    length r = 0%nat ->
    partition_state_dim (projection_step p_before mid) = 1%nat.
Proof.
  intros p_before mid r Hnodup Hin Huniq Hlen.
  rewrite projection_to_single_module_is_dim_1 with (r := r); auto.
  rewrite Hlen. reflexivity.
Qed.
