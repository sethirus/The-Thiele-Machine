(** * Formalising self-reference and the need for a meta-level.

    This module gives a minimal, mechanically checked model of systems
    that can talk about themselves.  The goal is not to encode a full
    Gödel numbering, but to make the structural dependencies explicit
    enough to reason about the need for a richer meta-layer. *)

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

(* ARITHMETIC — meta_system adds 1 dimension, so dim+1 > dim *)
(** [meta_system_richer]: formal specification. *)
Lemma meta_system_richer : forall S, dimensionally_richer (meta_system S) S.
Proof.
  intros S; unfold dimensionally_richer, meta_system; simpl; lia.
Qed.

(* DEFINITIONAL — meta_system includes base sentences via left disjunct *)
(** [meta_system_can_reason_about]: formal specification. *)
Lemma meta_system_can_reason_about : forall S, can_reason_about (meta_system S) S.
Proof.
  intros S P HP; unfold can_reason_about, meta_system in *; simpl in *; auto.
Qed.

(** The meta-system inherits a concrete self-referential statement from the
    base system: it can assert the truth of [contains_self_reference S], and we
    leverage the witness from [S] to keep the statement true. *)
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
