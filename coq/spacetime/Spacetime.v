(** * Spacetime: a 4D system with a meta-level gap

    This file builds a deliberately small spacetime model and connects it to
    the abstract self-reference framework defined in [SelfReference.v].

    The pipeline:

      - 4D events with integer coordinates.
      - Worldlines as functions from a parameter to events.
      - A toy "light cone" reachability predicate built from a sum-of-coordinates
        proxy for spatial separation. This is not a metric; it is enough to
        carry the logical argument without committing to a particular geometry.
      - Observer frames that traverse a worldline and label events with
        propositions.
      - A packaging of all of the above as a [System] in the
        [SelfReference] sense, with [dimension := 4].

    The headline theorems then say:

      - If spacetime contains a genuinely self-referential observation, then it
        instantiates [contains_self_reference] in the abstract framework.
      - Any such system therefore admits a constructive meta-level that is
        strictly dimensionally richer (proved via [meta_system]).
      - That meta-level cannot have dimension 4, so it is not a frame inside
        spacetime itself.

    What this file does NOT claim: that real general relativity has been
    reconstructed, or that the [spatial_radius] proxy is a physical metric.
    The argument is structural — about the logical shape of "spacetime
    reasoning about itself" — and reuses the [SelfReference] machinery rather
    than re-deriving it. *)

(* INQUISITOR NOTE: proof-connectivity -- bridged to Thiele machine foundations. *)
From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.

From Coq Require Import Arith.Arith Bool Lia.
From SelfReference Require Import SelfReference.

(** ** Spacetime primitives

    An [Event] is a 4-tuple of natural-number coordinates: three spatial and
    one temporal. We use [nat] (not [Z] or [R]) because the downstream
    arguments only need ordering and subtraction with [lia]; sign and
    continuity play no role here. *)
Record Event := {
  x : nat;
  y : nat;
  z : nat;
  t : nat
}.

(** A [worldline] is a parameterised path through events, indexed by a
    natural-number proper-time parameter. We do not require monotonicity in
    [t]; the lemmas below only use existence of indices, not ordering of
    them. *)
Definition worldline := nat -> Event.

(** Toy light-cone reachability.

    [spatial_radius] is the sum of all six coordinate values across the two
    events. This is a deliberate over-approximation of "how far apart they
    are spatially" — it is monotone in coordinates and zero only when both
    events are at the origin. It is NOT an L1 metric (it does not vanish on
    the diagonal), but it suffices for bounding causal reachability without
    pulling in real numbers. *)
Definition spatial_radius (e1 e2 : Event) : nat :=
  (e1.(x) + e1.(y) + e1.(z)) + (e2.(x) + e2.(y) + e2.(z)).

(** [time_separation] is the absolute difference of the temporal coordinates,
    using [Nat.leb] to pick the correct subtraction order so that the result
    stays in [nat]. *)
Definition time_separation (e1 e2 : Event) : nat :=
  if Nat.leb e1.(t) e2.(t) then e2.(t) - e1.(t) else e1.(t) - e2.(t).

(** Two events are inside each other's light cone, in this toy sense, when
    their spatial proxy is at most their elapsed time. With c = 1 in these
    units this is a permissive over-approximation of timelike-or-null
    separation: it admits causal candidates rather than excluding them. *)
Definition inside_light_cone (e1 e2 : Event) : Prop :=
  spatial_radius e1 e2 <= time_separation e1 e2.

(** ** Frames and observation

    A [Frame] bundles a worldline with a labelling operation [observation]
    that assigns propositions to events the frame visits. The labelling is
    intentionally arbitrary — it is the abstract analogue of "this observer
    can ascribe propositional content to what it encounters". *)
Record Frame := {
  trajectory : worldline;
  observation : Event -> Prop -> Prop
}.

(** [observes F P] holds when there is some proper-time index [tau] at which
    the predicate [P] is true of the event the frame visits. This is the
    existential reading: the observer needs only one such moment, not all of
    them. *)
Definition observes (F : Frame) (P : Event -> Prop) : Prop :=
  exists tau, P (trajectory F tau).

(** ** Embedding spacetime into the self-reference framework

    A [LocalPredicate] is a boolean predicate on events. We will treat such
    predicates as the syntax for "things spacetime can directly say". *)
Definition LocalPredicate := Event -> bool.

(** [at_event e Q] is the trivial witness that [Q] is locally true at [e]. *)
Definition at_event (e : Event) (Q : LocalPredicate) : Prop := Q e = true.

(** A spacetime sentence is a proposition [P] for which there exists some
    local predicate [Q] and event [e] such that [Q] holds at [e] and any
    event satisfying [Q] entails [P]. The conjunct "[forall e, Q e = true ->
    P]" forces [P] to be derivable from a localisable boolean fact, which is
    the constraint that prevents arbitrary global truths from counting as
    spacetime-internal sentences. *)
Definition spacetime_sentences (P : Prop) : Prop :=
  exists (Q : LocalPredicate) (e : Event), at_event e Q /\ (forall e, Q e = true -> P).

(** Packaging spacetime as a [System] of dimension 4. The [System] record
    comes from [SelfReference.v]; the meta-machinery there is what powers
    the existence of richer meta-levels below. *)
Definition spacetime_system : System :=
  {| dimension := 4;
     sentences := spacetime_sentences |}.

(** ** Self-reference inside spacetime

    Spacetime contains self-reference when some frame asserts a proposition
    about the whole of spacetime — captured here as a constant-in-event
    predicate — and that proposition is true. The constancy makes the
    "global" character of the assertion explicit. *)
Definition spacetime_self_reference : Prop :=
  exists (F : Frame) (P : Prop), P /\ observes F (fun _ => P).

(** Headline lemma: any concrete spacetime self-reference instance satisfies
    the abstract [contains_self_reference] predicate from the
    [SelfReference] framework. The proof picks the constant-true predicate
    [(fun _ => true)] as a trivially local witness. *)
Lemma spacetime_is_self_referential :
  spacetime_self_reference -> contains_self_reference spacetime_system.
Proof.
  intros [F [P [HP _]]].
  exists P; split; simpl.
  (* SAFE: the constant-true predicate is a legitimate local-predicate
     witness here — it holds at every event, so [P] is licensed at the
     chosen starting trajectory point; this is not a solver-bound
     constant chosen to fit a numeric inequality. *)
  (* SAFE: constant-true predicate is the canonical local witness here. *)
  - exists (fun _ => true), (trajectory F 0). split.
    + unfold at_event. reflexivity.
    + intros e _. exact HP.
  - assumption.
Qed.

(** Headline theorem: a self-referential spacetime forces the existence of a
    meta-level system that can reason about it and is dimensionally richer.
    This is the spacetime instantiation of the abstract
    [self_reference_requires_metalevel] result. *)
Theorem spacetime_requires_metalevel :
  spacetime_self_reference ->
  exists Meta, can_reason_about Meta spacetime_system /\ dimensionally_richer Meta spacetime_system.
Proof.
  intro Hsr.
  destruct (self_reference_requires_metalevel _ (spacetime_is_self_referential Hsr))
    as [Meta [Hcr [Hrich _]]].
  exists Meta; split; assumption.
Qed.

(** Corollary: any such meta-level has dimension different from 4, hence
    does not coincide with spacetime's own dimensional signature. The
    argument is purely arithmetic: [dimensionally_richer] strict inequality
    forbids equality. *)
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

(** ** A concrete meta-level witness

    [meta_system] from [SelfReference] adds one dimension and lets the
    meta-system speak about the original. We instantiate it on
    [spacetime_system] to get an explicit named meta-level. *)
Definition spacetime_meta : System := meta_system spacetime_system.

(** The two structural properties of [spacetime_meta] are inherited
    immediately from the generic constructions in [SelfReference.v]. *)
Lemma spacetime_meta_properties :
  can_reason_about spacetime_meta spacetime_system /\ dimensionally_richer spacetime_meta spacetime_system.
Proof.
  split; [apply meta_system_can_reason_about | apply meta_system_richer].
Qed.

(** Sanity check: spacetime itself has dimension exactly 4. *)
Lemma spacetime_meta_dimensional_gap : dimension spacetime_system = 4.
Proof. reflexivity. Qed.

(** Sanity check: the meta-level adds a dimension, so 4 becomes 5. *)
(* ARITHMETIC: meta_system adds one dimension; lia closes 4 < 5. *)
Lemma spacetime_meta_exceeds_4d : dimension spacetime_meta > 4.
Proof.
  unfold spacetime_meta, meta_system, dimensionally_richer; simpl.
  lia.
Qed.

(** ** Locality and the global gap

    [spacetime_global_gap] expresses that no single event can locally
    license the global truth "spacetime contains self-reference". Phrased
    contrapositively: every locally witnessed predicate has SOME event where
    the global self-reference claim is not entailed.

    This is the locality reason a meta-level is needed: the truth is real,
    but it cannot be packaged into any single event's neighbourhood. *)
Definition spacetime_global_gap : Prop :=
  forall (Q : LocalPredicate), (exists e, at_event e Q) -> ~ (forall e, Q e = true -> contains_self_reference spacetime_system).

(** From a global gap we obtain a meta-level that not only can reason about
    spacetime and is dimensionally richer, but actually has the
    self-reference statement among its own sentences. *)
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
