(** * Thiele manifold: an infinite-dimensional tower handling self-reference and projections.

    This file introduces a lightweight model of the Thiele manifold as an
    infinite tower of computational systems.  Each level can reason about
    the level below, gains strictly more structural "dimensions", and the
    whole tower provides a natural home for self-reference that any single
    level cannot internalise.  A lossy projection onto 4D spacetime (π₄)
    captures the information loss that motivates a meta-level.
 *)

From Coq Require Import Arith.Arith Lia.
From SelfReference Require Import SelfReference.
From Spacetime Require Import Spacetime.

(** ** Tower structure *)
Record ThieleManifold := {
  level : nat -> System;
  level_strictly_richer : forall n, dimensionally_richer (level (S n)) (level n);
  level_can_reason : forall n, can_reason_about (level (S n)) (level n);
  base_at_least_four : 4 <= dimension (level 0)
}.

(** A canonical infinite tower where each level adds one dimension and can
    reason about everything the previous level could express. *)
Definition canonical_level (n : nat) : System :=
  {| dimension := 4 + n;
     sentences := fun P => P |}.

Lemma canonical_level_strict : forall n, dimensionally_richer (canonical_level (S n)) (canonical_level n).
Proof. intros n; unfold dimensionally_richer, canonical_level; simpl; lia. Qed.

Lemma canonical_level_reasoning : forall n, can_reason_about (canonical_level (S n)) (canonical_level n).
Proof. intros n P HP; exact HP. Qed.

Lemma canonical_base_dim : 4 <= dimension (canonical_level 0).
Proof. simpl; lia. Qed.

Definition canonical_manifold : ThieleManifold :=
  {| level := canonical_level;
     level_strictly_richer := canonical_level_strict;
     level_can_reason := canonical_level_reasoning;
     base_at_least_four := canonical_base_dim |}.

(** ** Self-reference handled by lifting to the next level *)
Lemma level_dimension_le : forall (M : ThieleManifold) n, dimension (level M 0) <= dimension (level M n).
Proof.
  intros M n; induction n as [|n IH]; simpl.
  - lia.
  - eapply Nat.le_trans; [apply IH|].
    specialize (level_strictly_richer M n). intros Hlt.
    apply Nat.lt_le_incl in Hlt; exact Hlt.
Qed.

Lemma level_dimension_gt_four : forall (M : ThieleManifold) n, n > 0 -> 4 < dimension (level M n).
Proof.
  intros M n Hpos.
  destruct n as [|n']; [lia|].
  revert M Hpos.
  induction n' as [|k IH]; intros M _.
  - (* n = 1 *)
    specialize (level_strictly_richer M 0) as Hlt.
    unfold dimensionally_richer in Hlt.
    specialize (base_at_least_four M) as Hbase.
    lia.
  - (* n >= 2 *)
    specialize (IH M).
    specialize (level_strictly_richer M (S k)) as Hlt.
    unfold dimensionally_richer in Hlt.
    lia.
Qed.

Lemma tower_self_reference_escalates :
  forall (M : ThieleManifold) n,
    contains_self_reference (level M n) ->
    exists Meta,
      Meta = level M (S n) /\
      can_reason_about Meta (level M n) /\
      dimensionally_richer Meta (level M n).
Proof.
  intros M n Hself.
  exists (level M (S n)).
  split; [reflexivity|].
  split; [apply level_can_reason|apply level_strictly_richer].
Qed.

(** A whole-tower closure: every level's self-reference is answered by the
    immediately higher level, so the tower forms a self-contained witness. *)
Theorem tower_closed_under_self_reference :
  forall (M : ThieleManifold),
    (forall n, contains_self_reference (level M n)) ->
    forall n, exists Meta, can_reason_about Meta (level M n) /\ dimensionally_richer Meta (level M n).
Proof.
  intros M Hsr n.
  destruct (tower_self_reference_escalates M n (Hsr n)) as [Meta [HMeta [Hcr Hrich]]].
  subst Meta.
  exists (level M (S n)); auto.
Qed.

(** ** Projection to 4D spacetime *)
Definition pi4 (M : ThieleManifold) : System :=
  {| dimension := 4;
     sentences := sentences (level M 0) |}.

Definition mu_cost (S Target : System) : nat := dimension S - dimension Target.

Lemma pi4_lossy_for_higher_levels :
  forall (M : ThieleManifold) n,
    n > 0 -> dimensionally_richer (level M n) (pi4 M).
Proof.
  intros M n Hn.
  unfold dimensionally_richer, pi4; simpl.
  specialize (level_dimension_gt_four M n Hn) as Hdim.
  lia.
Qed.

Lemma mu_cost_positive_for_projection :
  forall (M : ThieleManifold) n,
    n > 0 -> mu_cost (level M n) (pi4 M) > 0.
Proof.
  intros M n Hn; unfold mu_cost, pi4; simpl.
  specialize (level_dimension_gt_four M n Hn) as Hdim.
  lia.
Qed.

(** ** Spacetime as a lossy shadow of the manifold *)
Definition spacetime_shadow (M : ThieleManifold) : System := pi4 M.

Lemma tower_projects_to_spacetime :
  can_reason_about (spacetime_shadow canonical_manifold) spacetime_system.
Proof.
  unfold spacetime_shadow, pi4, spacetime_system, spacetime_sentences; simpl.
  intros P HP; exact HP.
Qed.

Lemma projection_discards_dimensions :
  dimensionally_richer (level canonical_manifold 1) (spacetime_shadow canonical_manifold).
Proof.
  unfold spacetime_shadow; apply pi4_lossy_for_higher_levels; lia.
Qed.

Lemma projection_mu_cost :
  mu_cost (level canonical_manifold 1) (spacetime_shadow canonical_manifold) > 0.
Proof.
  unfold spacetime_shadow; apply mu_cost_positive_for_projection; lia.
Qed.
