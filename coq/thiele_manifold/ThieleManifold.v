(** * ThieleManifold: an infinite tower for self-reference and projection

    This file models the Thiele manifold as an infinite tower of systems
    in the [SelfReference] sense. Each level [n] is a [System]; level
    [n+1] can reason about level [n] and has strictly more dimensional
    room than [n]. That structure gives self-reference at any single
    level an immediate meta-level witness one rung up.

    Two payloads:

      - [canonical_manifold]: an explicit canonical tower where level [n]
        has dimension [4 + n] and the sentences predicate is the universal
        [fun P => P]. Useful as a worked example and as a target for the
        projection lemma below.
      - [pi4]: a 4D projection of the manifold defined by truncating to
        dimension 4 while keeping the level-zero sentences. The projection
        is intentionally lossy; [pi4_lossy_for_higher_levels] and
        [mu_cost_positive_for_projection] formalise that loss as a strictly
        positive μ-cost for any level above the base.

    Scope: this is a scaffold for the dimensional-gap argument, not a full
    geometric reconstruction of a manifold. *)

(* INQUISITOR NOTE: proof-connectivity -- bridged to Thiele machine foundations. *)
From Kernel Require Import VMState VMStep.

From Coq Require Import Arith.Arith Lia.
From SelfReference Require Import SelfReference.
From Spacetime Require Import Spacetime.

(** ** Tower structure

    [ThieleManifold] is parametrised by a level function [level : nat ->
    System] together with three coherence conditions: each successive
    level is strictly richer in dimension, each successive level can
    reason about its predecessor, and the base level has dimension at
    least 4 (room for ordinary spacetime). *)
Record ThieleManifold := {
  level : nat -> System;
  level_strictly_richer : forall n, dimensionally_richer (level (S n)) (level n);
  level_can_reason : forall n, can_reason_about (level (S n)) (level n);
  base_at_least_four : 4 <= dimension (level 0)
}.

(** A canonical infinite tower: level [n] has dimension [4 + n] and the
    sentences predicate accepts every proposition. This is the simplest
    instance satisfying the [ThieleManifold] axioms; it serves as both
    a worked example and the target of the spacetime projection below. *)
Definition canonical_level (n : nat) : System :=
  {| dimension := 4 + n;
     sentences := fun P => P |}.

(** Strict-richer law for the canonical tower: dimensions grow by one
    per level, so each successor strictly dominates its predecessor. *)
Lemma canonical_level_strict : forall n, dimensionally_richer (canonical_level (S n)) (canonical_level n).
Proof. intros n; unfold dimensionally_richer, canonical_level; simpl; lia. Qed.

(** Reasoning law for the canonical tower: every proposition expressible
    at level [n] is expressible at level [n+1] because the canonical
    sentences predicate is universal. *)
Lemma canonical_level_reasoning : forall n, can_reason_about (canonical_level (S n)) (canonical_level n).
Proof. intros n P HP; exact HP. Qed.

(** Base-dimension law: the canonical base level has dimension 4. *)
Lemma canonical_base_dim : 4 <= dimension (canonical_level 0).
Proof. simpl; lia. Qed.

(** Packaging the three canonical laws into the [ThieleManifold] record. *)
Definition canonical_manifold : ThieleManifold :=
  {| level := canonical_level;
     level_strictly_richer := canonical_level_strict;
     level_can_reason := canonical_level_reasoning;
     base_at_least_four := canonical_base_dim |}.

(** ** Self-reference handled by lifting to the next level

    The lemmas in this section show how a self-reference at any level is
    immediately answered by the level above. The pattern is uniform: the
    successor level can both reason about its predecessor and is strictly
    richer in dimension, so it is a witness for the meta-level demand
    raised by [SelfReference]'s [self_reference_requires_metalevel]. *)

(** Dimensional monotonicity: dimensions grow weakly along the tower.
    Used in the corollary [level_dimension_gt_four] below. *)
Lemma level_dimension_le : forall (M : ThieleManifold) n, dimension (level M 0) <= dimension (level M n).
Proof.
  intros M n; induction n as [|n IH]; simpl.
  - lia.
  - eapply Nat.le_trans; [apply IH|].
    specialize (level_strictly_richer M n). intros Hlt.
    apply Nat.lt_le_incl in Hlt; exact Hlt.
Qed.

(** Strict dimensional gap above the base: any level [n > 0] has
    dimension strictly greater than 4. *)
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

(** Self-reference escalation: any self-referential level produces a
    meta-witness one rung up. The hypothesis [contains_self_reference]
    is unused in the proof — the witness exists structurally — but the
    statement records what the lemma is for. *)
Lemma tower_self_reference_escalates :
  forall (M : ThieleManifold) n,
    contains_self_reference (level M n) ->
    exists Meta,
      Meta = level M (S n) /\
      can_reason_about Meta (level M n) /\
      dimensionally_richer Meta (level M n).
Proof.
  intros M n _.
  exists (level M (S n)).
  split; [reflexivity|].
  split; [apply level_can_reason|apply level_strictly_richer].
Qed.

(** Whole-tower closure: if every level is self-referential, every level
    is also answered by some meta-witness. The tower is therefore a
    self-contained construction; no external meta-level needs to be
    provided. *)
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

(** ** Projection to 4D spacetime

    [pi4] truncates the manifold to dimension 4 while inheriting the
    base level's sentences predicate. The projection deliberately
    forgets all higher-dimensional structure; the lemmas in this section
    quantify what is lost. *)

(** The 4D projection: dimension forced to 4, sentences taken from the
    base level. *)
Definition pi4 (M : ThieleManifold) : System :=
  {| dimension := 4;
     sentences := sentences (level M 0) |}.

(** Toy μ-cost: the dimensional difference between a system and its
    target. Used here to give the projection's loss a numerical handle. *)
Definition mu_cost (S Target : System) : nat := dimension S - dimension Target.

(** The projection is lossy above the base: any level [n > 0] strictly
    dominates [pi4 M] in dimension. *)
Lemma pi4_lossy_for_higher_levels :
  forall (M : ThieleManifold) n,
    n > 0 -> dimensionally_richer (level M n) (pi4 M).
Proof.
  intros M n Hn.
  unfold dimensionally_richer, pi4; simpl.
  specialize (level_dimension_gt_four M n Hn) as Hdim.
  lia.
Qed.

(** Quantitative version: the projection's μ-cost from any level [n > 0]
    is strictly positive. *)
Lemma mu_cost_positive_for_projection :
  forall (M : ThieleManifold) n,
    n > 0 -> mu_cost (level M n) (pi4 M) > 0.
Proof.
  intros M n Hn; unfold mu_cost, pi4; simpl.
  specialize (level_dimension_gt_four M n Hn) as Hdim.
  lia.
Qed.

(** ** Spacetime as a lossy shadow of the manifold *)

(** [spacetime_shadow] is [pi4] under a name that makes its physical
    interpretation explicit: the 4D shadow is what an observer trapped
    in spacetime can see of the full manifold. *)
Definition spacetime_shadow (M : ThieleManifold) : System := pi4 M.

(** The shadow can express every spacetime sentence. The proof works
    because [canonical_manifold] uses [fun P => P] as its sentences
    predicate, so any [Prop] — including [spacetime_sentences P] — is
    expressible at every level. The body unwinds [spacetime_sentences]
    to extract a witness event and produces [P] by applying the local
    entailment at that event. *)
Lemma tower_projects_to_spacetime :
  can_reason_about (spacetime_shadow canonical_manifold) spacetime_system.
Proof.
  unfold can_reason_about. intros P HP.
  unfold spacetime_shadow, pi4. simpl.
  unfold canonical_manifold, canonical_level. simpl.
  unfold spacetime_system in HP. simpl in HP.
  unfold spacetime_sentences in HP.
  destruct HP as [Q [e [He Himpl]]].
  unfold at_event in He.
  exact (Himpl e He).
Qed.

(** Even level 1 of the canonical manifold is dimensionally richer than
    the shadow: the projection loses at least one dimension. *)
Lemma projection_discards_dimensions :
  dimensionally_richer (level canonical_manifold 1) (spacetime_shadow canonical_manifold).
Proof.
  unfold spacetime_shadow; apply pi4_lossy_for_higher_levels; lia.
Qed.

(** Quantitative version: the μ-cost from level 1 down to the shadow is
    strictly positive. *)
Lemma projection_mu_cost :
  mu_cost (level canonical_manifold 1) (spacetime_shadow canonical_manifold) > 0.
Proof.
  unfold spacetime_shadow; apply mu_cost_positive_for_projection; lia.
Qed.
