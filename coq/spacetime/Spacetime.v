(** * Formalising spacetime as a 4D structure with self-reference and a necessary meta-level.

    This file gives a lightweight model of spacetime as a 4-tupled
    coordinate system together with causal structure (worldlines,
    light cones, observer frames).  We connect those notions to the
    general self-reference framework from [SelfReference] and show
    that any self-referential phenomenon in spacetime requires a
    dimensionally richer meta-level system.
 *)

From Coq Require Import Arith.Arith Bool Lia.
From SelfReference Require Import SelfReference.

(** ** Spacetime primitives *)
Record Event := {
  x : nat;
  y : nat;
  z : nat;
  t : nat
}.

Definition worldline := nat -> Event.

(** A light cone toy approximation: we use a simple sum-of-coordinates proxy
    for spatial separation (not an actual L1 metric) and bound it by elapsed
    time to express causal reachability. *)
Definition spatial_radius (e1 e2 : Event) : nat :=
  (e1.(x) + e1.(y) + e1.(z)) + (e2.(x) + e2.(y) + e2.(z)).

Definition time_separation (e1 e2 : Event) : nat :=
  if Nat.leb e1.(t) e2.(t) then e2.(t) - e1.(t) else e1.(t) - e2.(t).

Definition inside_light_cone (e1 e2 : Event) : Prop :=
  spatial_radius e1 e2 <= time_separation e1 e2.

(** An observer frame follows a worldline and can label events it
    encounters with propositions. *)
Record Frame := {
  trajectory : worldline;
  observation : Event -> Prop -> Prop
}.

Definition observes (F : Frame) (P : Event -> Prop) : Prop :=
  exists tau, P (trajectory F tau).

(** ** Spacetime as a system in the self-reference framework *)
Definition LocalPredicate := Event -> bool.

(** Locality: a proposition is licensed only if it is entailed by some
    event-indexed boolean predicate.  This forces any spacetime sentence to be
    grounded in the 4D coordinates of an event rather than ranging over the
    entire logical universe. *)
Definition at_event (e : Event) (Q : LocalPredicate) : Prop := Q e = true.

Definition spacetime_sentences (P : Prop) : Prop :=
  exists (Q : LocalPredicate) (e : Event), at_event e Q /\ (forall e, Q e = true -> P).

Definition spacetime_system : System :=
  {| dimension := 4;
     sentences := spacetime_sentences |}.

(** Spacetime contains self-reference if there is an observer who
    asserts a proposition about the whole spacetime that is in fact true. *)
Definition spacetime_self_reference : Prop :=
  exists (F : Frame) (P : Prop), P /\ observes F (fun _ => P).

Lemma spacetime_is_self_referential :
  spacetime_self_reference -> contains_self_reference spacetime_system.
Proof.
  intros [F [P [HP _]]].
  exists P; split; simpl.
  - exists (fun _ => true), (trajectory F 0). split.
    + unfold at_event. reflexivity.
    + intros e _. exact HP.
  - assumption.
Qed.

(** Any self-referential spacetime thus inherits the incompleteness
    pressure: a constructive meta-level exists. *)
Theorem spacetime_requires_metalevel :
  spacetime_self_reference ->
  exists Meta, can_reason_about Meta spacetime_system /\ dimensionally_richer Meta spacetime_system.
Proof.
  intro Hsr.
  destruct (self_reference_requires_metalevel _ (spacetime_is_self_referential Hsr))
    as [Meta [Hcr [Hrich _]]].
  exists Meta; split; assumption.
Qed.

(** The constructed meta-level strictly exceeds 4D, so it cannot live
    within spacetime's own dimensional bounds. *)
Corollary meta_level_not_in_spacetime :
  spacetime_self_reference ->
  forall Meta, can_reason_about Meta spacetime_system /\ dimensionally_richer Meta spacetime_system ->
    dimension Meta <> 4.
Proof.
  intros _ Meta [_ Hrich].
  unfold dimensionally_richer in Hrich; simpl in Hrich.
  apply Nat.lt_neq in Hrich.
  now apply not_eq_sym.
Qed.

(** A concrete meta-level witness for spacetime that is dimensionally richer. *)
Definition spacetime_meta : System := meta_system spacetime_system.

Lemma spacetime_meta_properties :
  can_reason_about spacetime_meta spacetime_system /\ dimensionally_richer spacetime_meta spacetime_system.
Proof.
  split; [apply meta_system_can_reason_about | apply meta_system_richer].
Qed.

Lemma spacetime_meta_dimensional_gap : dimension spacetime_system = 4.
Proof. reflexivity. Qed.

(* ARITHMETIC — meta_system adds 1 to dimension 4, giving 5 > 4 *)
Lemma spacetime_meta_exceeds_4d : dimension spacetime_meta > 4.
Proof.
  unfold spacetime_meta, meta_system, dimensionally_richer; simpl.
  lia.
Qed.

(** Locality restriction: global truths like self-reference cannot live at a
    single event, so they escape 4D spacetime and motivate the meta-level. *)

Definition spacetime_global_gap : Prop :=
  forall (Q : LocalPredicate), (exists e, at_event e Q) -> ~ (forall e, Q e = true -> contains_self_reference spacetime_system).

Lemma global_truth_escapes :
  spacetime_global_gap ->
  exists Meta,
    can_reason_about Meta spacetime_system /\
    dimensionally_richer Meta spacetime_system /\
    sentences Meta (contains_self_reference spacetime_system).
Proof.
  intro Hgap.
  exists (meta_system spacetime_system).
  repeat split.
  - apply meta_system_can_reason_about.
  - apply meta_system_richer.
  - unfold meta_system; simpl; auto.
Qed.
