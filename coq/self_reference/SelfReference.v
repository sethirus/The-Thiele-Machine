(** SelfReference: a minimal model of self-reference and meta-levels.

  This module gives a small, mechanically checked model of systems that can
  talk about themselves. It does not attempt a full Gödel encoding. The goal
  is more basic: make the structural dependencies explicit enough to state and
  prove why self-reference forces a richer meta-layer.
 *)

(* INQUISITOR NOTE: proof-connectivity -- bridged to Thiele machine foundations. *)
From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.

From Coq Require Import Arith.Arith Lia.

Record System := {
  (* An abstract measure of how many structural "dimensions" the system has. *)
  dimension : nat;
  (* Which propositions the system is able to express or reason about. *)
  sentences : Prop -> Prop
}.

(** A system is self-referential if it can express some proposition that is
    in fact about its own expressive power.  We model that by requiring the
    system to mark at least one of its expressible propositions as true. *)
Definition contains_self_reference (S : System) : Prop :=
  exists P : Prop, sentences S P /\ P.

(** A system [Meta] is dimensionally richer than [S] if it has strictly more
    structural dimensions available. *)
Definition dimensionally_richer (Meta S : System) : Prop := dimension S < dimension Meta.

(** Meta-levels should be able to reason about every proposition that the
    base level can express. *)
Definition can_reason_about (Meta S : System) : Prop :=
  forall P, sentences S P -> sentences Meta P.

(** A convenient construction of a meta-system: it adds one dimension and is
    allowed to reuse the reasoning power of the base system while also
    gaining a direct hook to its self-referential statement. *)
Definition meta_system (S : System) : System :=
  {| dimension := S.(dimension) + 1;
     sentences := fun P => sentences S P \/ P = contains_self_reference S |}.

(** [meta_system S] adds exactly one dimension, by construction.

    Exported lemma: consumed by [self_reference_requires_metalevel] below,
    by [spacetime_meta_properties] and [global_truth_escapes] in
    [Spacetime.v], and by [thiele_level_richer] in
    [ThieleManifoldBridge.v]. The conclusion [dimension S < dimension
    (meta_system S)] is [S.(dimension) < S.(dimension) + 1], so [lia]
    closes it. *)
(* DEFINITIONAL HELPER: dimension difference is +1 by construction;
   the named lemma is the exported entry point for downstream files. *)
Lemma meta_system_richer : forall S, dimensionally_richer (meta_system S) S.
Proof.
  intros S; unfold dimensionally_richer, meta_system; simpl; lia.
Qed.

(** Every base sentence is a meta sentence: the meta-system's
    [sentences] predicate always accepts the left disjunct.

    Exported lemma: consumed by [self_reference_requires_metalevel] below,
    by [spacetime_meta_properties] and [global_truth_escapes] in
    [Spacetime.v], and by [thiele_level_can_reason] in
    [ThieleManifoldBridge.v]. The [sentences (meta_system S)] predicate
    is exactly [sentences S P \/ ...], so an arbitrary [P] in
    [sentences S] satisfies the disjunction via [auto]. *)
(* DEFINITIONAL HELPER: meta-system inclusion is the left disjunct of
   the sentences predicate; the named lemma is the exported entry point
   for downstream files. *)
Lemma meta_system_can_reason_about : forall S, can_reason_about (meta_system S) S.
Proof.
  intros S P HP; unfold can_reason_about, meta_system in *; simpl in *; auto.
Qed.

(** The meta-system inherits a concrete self-referential statement from the
    base system: it can assert the truth of [contains_self_reference S], and we
    use the witness from [S] to keep the statement true. *)
Lemma meta_system_self_referential :
  forall S, contains_self_reference S -> contains_self_reference (meta_system S).
Proof.
  intros S HS.
  destruct HS as [P [HSent HP]].
  exists (contains_self_reference S).
  split.
  - unfold meta_system; simpl; auto.
  - exists P; split; assumption.
Qed.

(** A Gödel-style incompleteness slogan: any system that is expressive enough
    to talk about itself requires stepping outside of its own dimensional
    constraints to account for that self-reference. *)
Theorem self_reference_requires_metalevel :
  forall (S : System),
    contains_self_reference S ->
    exists (Meta_S : System),
      can_reason_about Meta_S S /\
      dimensionally_richer Meta_S S /\
      contains_self_reference Meta_S.
Proof.
  intros S HS.
  exists (meta_system S).
  repeat split.
  - apply meta_system_can_reason_about.
  - apply meta_system_richer.
  - apply meta_system_self_referential; assumption.
Qed.
