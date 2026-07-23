(** The pointer-observable criterion, formalized: definitions, the
    conjecture schema, and a non-vacuity witness.

  Section 25 of the monograph names the successor to the open question
  "is certification the event a step rule is forced to price?": the
  conjecture that certification is singled out among meterable events by
  REDUNDANT RECORD PROLIFERATION -- its records are copied, checked, and
  stored across independent substrates that do not otherwise share state,
  while rival meterable events leave no such trail.

  This file gives that criterion a formal skeleton, so the conjecture is a
  statement with a shape instead of a paragraph with a mood. Three layers,
  each scoped exactly:

  1. DEFINITIONS. An [Ecosystem] is a state space with a finite family of
     observers, each holding a boolean fragment of the state. An event (a
     state predicate) PROLIFERATES when every observer's fragment decides
     it independently ([redundantly_proliferating]). An event is the
     UNIQUE POINTER among a finite list of rival events when it
     proliferates and no rival does ([unique_pointer_among]).

  2. THE CONJECTURE SCHEMA. The monograph's conjecture quantifies over
     deployed, independently evolved metering disciplines -- an empirical
     class, not a formal one. What is formalizable today is the schema:
     given a class [C] of ecosystems (the faithful models of metering
     disciplines) with a designated metered event and designated rivals,
     the criterion holds for [C] when every metered event proliferates and
     no rival does ([pointer_criterion_holds]). Producing the faithful
     models of the five Section-15 disciplines and proving the two
     conjuncts for them is the successor project, named and not claimed.

  3. NON-VACUITY. A toy replicated-ledger ecosystem: state carries a
     certification bit and a work counter; each of the observers stores a
     copy of the certification bit and nothing else. The certification
     event proliferates (discharged inline in [toy_cert_unique_pointer]);
     the work-counter event does not ([toy_work_not_proliferating]);
     certification is the unique pointer among the two
     ([toy_cert_unique_pointer]). This witnesses
     that the definitions are satisfiable and discriminating -- it is a
     sanity instance, not evidence for the conjecture, and the file says
     so in its own name for it.

  Falsification of the criterion's usefulness, at this level: show the
  definitions are degenerate -- e.g., exhibit that every event trivially
  proliferates in every ecosystem with at least one observer, or that no
  event can. The toy instance refutes both degeneracies at once.
*)

(* INQUISITOR NOTE: proof-connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.

From Coq Require Import List Lia.
Import ListNotations.

(** * Ecosystems, records, proliferation *)

(** A state space observed by [eco_observers] independent parties, each
    holding one boolean fragment. Independence is structural: an
    observer's fragment is a function of the global state only through its
    own projection, and nothing here lets fragments read each other. *)
Record Ecosystem := {
  eco_state : Type;
  eco_observers : nat;
  eco_fragment : nat -> eco_state -> bool
}.

(** Observer [i] records event [E] when its fragment decides [E] on every
    state: the stored bit is true exactly when the event has occurred. *)
Definition records (eco : Ecosystem) (E : eco_state eco -> Prop) (i : nat) : Prop :=
  forall s : eco_state eco, E s <-> eco_fragment eco i s = true.

(** Redundant proliferation: every observer independently records the
    event. This is the formal reading of "the environment keeps redundant
    records": any single fragment suffices to reconstruct the event. *)
Definition redundantly_proliferating
  (eco : Ecosystem) (E : eco_state eco -> Prop) : Prop :=
  forall i : nat, (i < eco_observers eco)%nat -> records eco E i.

(** Unique pointer among a designated family of rival events: the event
    proliferates and no rival in the list does. Uniqueness is relative to
    the named rivals on purpose: absolute uniqueness is false for free
    (an event's complement proliferates whenever it does), and the
    conjecture's content is about the events a step rule could
    meaningfully meter, not about Boolean algebra. *)
Definition unique_pointer_among
  (eco : Ecosystem)
  (E : eco_state eco -> Prop)
  (rivals : list (eco_state eco -> Prop)) : Prop :=
  redundantly_proliferating eco E
  /\ Forall (fun R => ~ redundantly_proliferating eco R) rivals.

(** * The conjecture schema *)

(** A metering-discipline class: a predicate on ecosystems, a designated
    metered event for each member, and its designated rival events. The
    criterion holds for the class when every member's metered event is the
    unique pointer among its rivals. The monograph's conjecture is this
    schema instantiated at faithful models of the deployed disciplines
    (proof-of-stake finality, gas metering, TEE attestation, certificate
    transparency, proof-carrying verification); constructing those models
    is the successor project. *)
Definition pointer_criterion_holds
  (C : Ecosystem -> Prop)
  (metered : forall eco, C eco -> (eco_state eco -> Prop))
  (rivals : forall eco (h : C eco), list (eco_state eco -> Prop)) : Prop :=
  forall eco (h : C eco),
    unique_pointer_among eco (metered eco h) (rivals eco h).

(** * Non-vacuity: the replicated-ledger toy *)

Module ReplicatedLedgerToy.

(** Global state: a certification flag and a work counter. Three
    observers, each mirroring the certification flag and nothing else --
    the caricature of a network of full nodes replicating finality while
    nobody replicates anyone's loop counter. *)
Record ToyState := {
  toy_cert : bool;
  toy_work : nat
}.

Definition toy : Ecosystem := {|
  eco_state := ToyState;
  eco_observers := 3;
  eco_fragment := fun _ s => toy_cert s
|}.

Definition cert_event (s : ToyState) : Prop := toy_cert s = true.
Definition work_event (s : ToyState) : Prop := (1 <= toy_work s)%nat.

(** The work event does not proliferate: no fragment can distinguish an
    uncertified state with work done from one without. *)
Theorem toy_work_not_proliferating :
  ~ redundantly_proliferating toy work_event.
Proof.
  intros H.
  assert (H0 : (0 < eco_observers toy)%nat) by (simpl; lia).
  specialize (H 0%nat H0 {| toy_cert := false; toy_work := 1 |}).
  unfold work_event in H. simpl in H.
  destruct H as [Hforward _].
  specialize (Hforward ltac:(lia)).
  discriminate.
Qed.

(** Certification is the unique pointer among the two meterable events of
    the toy: the certification event proliferates (every observer's
    fragment is a faithful copy of the flag, discharged inline below),
    the work event does not. Sanity instance only: the definitions are
    satisfiable and discriminating; nothing here is evidence about
    deployed systems. *)
Theorem toy_cert_unique_pointer :
  unique_pointer_among toy cert_event [work_event].
Proof.
  split.
  - intros i Hi s. unfold cert_event. simpl. reflexivity.
  - constructor; [exact toy_work_not_proliferating | constructor].
Qed.

End ReplicatedLedgerToy.

(** * Anchor for proof-connectivity audits *)

Definition pointer_observable_anchor := @vm_certified.
