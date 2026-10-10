(** The pointer-observable criterion, formalized: definitions, the
    conjecture schema, and a non-vacuity witness.

  The pointer-observable criterion is the successor to the open question
  "is certification the event a step rule is forced to price?": the
  conjecture that certification is singled out among meterable events by
  REDUNDANT RECORD PROLIFERATION: its records are copied, checked, and
  stored across independent substrates that do not otherwise share state,
  while rival meterable events leave no such trail.

  None of that world is in the formal objects below. They have indexed
  Boolean observers and nothing else: no deployment, no independence
  predicate, no cost law, no protocol.

  This file gives that criterion a formal skeleton, so the conjecture is a
  statement with a shape instead of a paragraph with a mood. Three layers,
  each scoped exactly:

  1. DEFINITIONS. An [Ecosystem] is a state space with a finite family of
     observers, each holding a boolean fragment of the state. An event (a
     state predicate) PROLIFERATES when every observer's fragment decides
     it independently ([redundantly_proliferating]). An event is the
     UNIQUE POINTER among a finite list of rival events when it
     proliferates and no rival does ([unique_pointer_among]).

  2. THE CONJECTURE SCHEMA. The conjecture quantifies over
     deployed, independently evolved metering disciplines, an empirical
     class, not a formal one. What is formalizable today is the schema:
     given a class [C] of ecosystems with a designated metered event and
     designated rivals, the criterion holds for [C] when every metered
     event proliferates and no rival does ([pointer_criterion_holds]).
     Membership in [C] and the choice of events are inputs; the definition
     does not justify them. Building models faithful to real metering
     disciplines and proving the two conjuncts for them is the successor
     project, named and not claimed.

  3. NON-VACUITY. A toy replicated-ledger ecosystem: state carries a
     certification bit and a work counter; each of the observers stores a
     copy of the certification bit and nothing else. The certification
     event proliferates (discharged inline in [toy_cert_unique_pointer]);
     the work-counter event does not ([toy_work_not_proliferating]);
     certification is the unique pointer among the two
     ([toy_cert_unique_pointer]). This witnesses
     that the definitions are satisfiable and discriminating; it is a
     sanity instance, not evidence for the conjecture, and the file says
     so in its own name for it.

  Falsification of the criterion's usefulness, at this level: show the
  definitions are degenerate: e.g., exhibit that every event trivially
  proliferates in every ecosystem with at least one observer, or that no
  event can. The toy instance refutes both degeneracies at once.
*)

(* SCOPE NOTE: standalone proof scope. This file is about
   ecosystems and record proliferation, not a machine's semantics. No
   definition or theorem here mentions a certification system or a ledger;
   the criterion is deliberately stated over an abstract
   state type, so that a discipline owing nothing to this development could
   instantiate it.

   The audit is waived rather than satisfied: importing the kernel without
   using it would assert a bridge that isn't here. The connection to the
   mu-ledger is made by the conjecture the criterion is about, argued in
   prose, not by an import line. *)

From Coq Require Import List Lia PeanoNat.
Import ListNotations.

(** * Ecosystems, records, proliferation *)

(** A state space observed by [eco_observers] parties, each holding one
    boolean fragment. Nothing here lets fragments read each other. Nothing
    here makes the parties independent either: each fragment is a function
    of the whole state, and the record has no predicate saying two
    observers draw on separate parts of it. *)
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
    the named rivals on purpose: absolute uniqueness is false for free (any
    event equal to [E] on every state proliferates whenever [E] does), and
    the conjecture's content is about the events a step rule could
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
    unique pointer among its rivals. The conjecture is this schema
    instantiated at models of real disciplines (proof-of-stake finality,
    gas metering, TEE attestation, certificate transparency, proof-carrying
    verification). PointerObservableReductions.v builds one small observer
    map per discipline; models faithful to the real disciplines are not
    built here. The word "metered" is a
    label here: the definition contains no metering semantics. *)
Definition pointer_criterion_holds
  (C : Ecosystem -> Prop)
  (metered : forall eco, C eco -> (eco_state eco -> Prop))
  (rivals : forall eco (h : C eco), list (eco_state eco -> Prop)) : Prop :=
  forall eco (h : C eco),
    unique_pointer_among eco (metered eco h) (rivals eco h).

(** * Non-vacuity: the replicated-ledger toy *)

Module ReplicatedLedgerToy.

(** Global state: a certification flag and a work counter. Three
    observers, each mirroring the certification flag and nothing else,
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

(** * Copied and relied on, by parties who didn't produce it

    The definitions above give every observer one bit, so two events an
    observer records always agree, and "proliferates" cannot even state
    the obvious objection: in a replicated system every full node holds
    the whole shared state, so every predicate of it ("gas used is at
    least k" in a block header as much as "finalized") is copied to every
    node. The definitions below give each observer a view (anything it
    holds), an action it takes on what it holds, and a flag saying whether
    it produced the record. An event is COPIED on a set of reachable
    states when every observer can decide it from its own view there. An
    observer RELIES on an event when it acts only where the event holds,
    and acts somewhere. The tightened criterion asks for both: copied by
    every observer, and relied on by every observer that didn't produce
    it, with at least one such observer. The POINTER on the reachable
    states is the strongest event copied and relied on in that sense:
    every event that is copied and relied on holds wherever it does.
    Uniqueness then needs no list of rivals: two pointers agree on every
    reachable state.

    INDEPENDENT CARRIERS are a family of relations, one per observer,
    saying when two states agree on that observer's own part of the world;
    each view reads only its own part, and any two observers' parts can be
    set separately. A theorem below shows independence and exact copying
    on EVERY state together force the event to be constant, so the copies
    of a real record agree only on the states the world reaches, where the
    agreement is made by the copying. That is why the criterion is stated
    on a set of reachable states.

    The ledger toy is a sanity instance with three full nodes, each holding
    its own copy of a block header (finalized, gas used), a proposer that
    produced it, and two nodes that act (credit a deposit, say) only on a
    finalized header. Gas used is copied as well as finality, which is the
    objection; only finality is relied on, and finality is the pointer. The
    maps are mine, and the toy is evidence of nothing about deployed
    systems. *)

Record RelianceEcosystem := {
  re_state : Type;
  re_observers : nat;
  re_obs : Type;
  re_view : nat -> re_state -> re_obs;
  re_act : nat -> re_obs -> bool;
  re_producer : nat -> bool
}.

(** An event a step rule could meter: one decided by a Boolean reading of
    the state, so a price list can charge exactly the steps that turn it
    on. *)
Definition meterable (eco : RelianceEcosystem) (E : re_state eco -> Prop) : Prop :=
  exists b : re_state eco -> bool, forall s, E s <-> b s = true.

Section Reliance.

Variable eco : RelianceEcosystem.
Variable reach : re_state eco -> Prop.

Definition copied_on (E : re_state eco -> Prop) : Prop :=
  forall i, (i < re_observers eco)%nat ->
    exists d : re_obs eco -> bool,
      forall s, reach s -> (E s <-> d (re_view eco i s) = true).

Definition relies_on (E : re_state eco -> Prop) (i : nat) : Prop :=
  (forall s, reach s -> re_act eco i (re_view eco i s) = true -> E s)
  /\ (exists s, reach s /\ re_act eco i (re_view eco i s) = true).

Definition relied_on_by_others (E : re_state eco -> Prop) : Prop :=
  (exists i, (i < re_observers eco)%nat /\ re_producer eco i = false)
  /\ forall i, (i < re_observers eco)%nat -> re_producer eco i = false ->
       relies_on E i.

Definition copied_and_relied_on (E : re_state eco -> Prop) : Prop :=
  copied_on E /\ relied_on_by_others E.

Definition pointer_on (E : re_state eco -> Prop) : Prop :=
  copied_and_relied_on E
  /\ forall E', copied_and_relied_on E' -> forall s, reach s -> E s -> E' s.

(** Two pointers agree on every reachable state. *)
Theorem pointer_on_unique :
  forall E1 E2, pointer_on E1 -> pointer_on E2 ->
    forall s, reach s -> (E1 s <-> E2 s).
Proof.
  intros E1 E2 [H1 M1] [H2 M2] s Hs. split.
  - intro HE. exact (M1 E2 H2 s Hs HE).
  - intro HE. exact (M2 E1 H1 s Hs HE).
Qed.

End Reliance.

Definition independent_carriers (eco : RelianceEcosystem)
    (part : nat -> re_state eco -> re_state eco -> Prop) : Prop :=
  (forall i s t, (i < re_observers eco)%nat -> part i s t ->
     re_view eco i s = re_view eco i t)
  /\ (forall i j s t, (i < re_observers eco)%nat -> (j < re_observers eco)%nat ->
       i <> j -> exists u, part i u s /\ part j u t).

(** Independence plus exact copying on every state leaves only constant
    events. *)
Theorem independent_copies_everywhere_are_constant :
  forall (eco : RelianceEcosystem) part (E : re_state eco -> Prop),
    independent_carriers eco part ->
    (2 <= re_observers eco)%nat ->
    copied_on eco (fun _ => True) E ->
    forall s t, E s <-> E t.
Proof.
  intros eco part E [Hread Hsep] H2 Hcopy s t.
  assert (H0 : (0 < re_observers eco)%nat) by lia.
  assert (H1 : (1 < re_observers eco)%nat) by lia.
  destruct (Hcopy 0%nat H0) as [d0 Hd0].
  destruct (Hcopy 1%nat H1) as [d1 Hd1].
  destruct (Hsep 0%nat 1%nat s t H0 H1 ltac:(lia)) as [u [Hus Hut]].
  pose proof (Hread 0%nat u s H0 Hus) as Hv0.
  pose proof (Hread 1%nat u t H1 Hut) as Hv1.
  rewrite (Hd0 s I), (Hd1 t I), <- Hv0, <- Hv1, <- (Hd0 u I), <- (Hd1 u I).
  tauto.
Qed.

(** The pointer thesis as a schema: for every member of a class, the
    certification event is the pointer on the states the discipline
    reaches, and every record the discipline prices is copied and relied
    on by parties who didn't produce it. The class, its reachable states,
    its certification event and its priced records are inputs; nothing
    about them is proved. *)
Definition pointer_thesis_schema
  (C : RelianceEcosystem -> Prop)
  (reach : forall eco, C eco -> re_state eco -> Prop)
  (cert : forall eco, C eco -> re_state eco -> Prop)
  (priced : forall eco, C eco -> (re_state eco -> Prop) -> Prop) : Prop :=
  forall eco (h : C eco),
    pointer_on eco (reach eco h) (cert eco h)
    /\ forall E, priced eco h E -> copied_and_relied_on eco (reach eco h) E.

Module ReplicatedHeaderToy.

(** A block header: finalized, and gas used. *)
Definition Header : Type := (bool * nat)%type.

Record LState := {
  l_src : Header;
  l_c0 : Header;
  l_c1 : Header;
  l_c2 : Header
}.

Definition copy (i : nat) (s : LState) : Header :=
  match i with
  | 0 => l_c0 s
  | 1 => l_c1 s
  | _ => l_c2 s
  end.

Definition set_copy (j : nat) (h : Header) (s : LState) : LState :=
  match j with
  | 0 => {| l_src := l_src s; l_c0 := h; l_c1 := l_c1 s; l_c2 := l_c2 s |}
  | 1 => {| l_src := l_src s; l_c0 := l_c0 s; l_c1 := h; l_c2 := l_c2 s |}
  | _ => {| l_src := l_src s; l_c0 := l_c0 s; l_c1 := l_c1 s; l_c2 := h |}
  end.

(** Node 0 proposed the block; nodes 1 and 2 act (credit a deposit) only
    on a header they hold that says finalized. *)
Definition ledger : RelianceEcosystem := {|
  re_state := LState;
  re_observers := 3;
  re_obs := Header;
  re_view := copy;
  re_act := fun _ h => fst h;
  re_producer := fun i => Nat.eqb i 0
|}.

(** The states the network reaches: every node's copy equals the header. *)
Definition synced (s : LState) : Prop :=
  l_c0 s = l_src s /\ l_c1 s = l_src s /\ l_c2 s = l_src s.

Definition part (i : nat) (s t : LState) : Prop := copy i s = copy i t.

Definition finalized (s : LState) : Prop := fst (l_src s) = true.
Definition gas_used_positive (s : LState) : Prop := (1 <= snd (l_src s))%nat.

Lemma synced_copy : forall i s, (i < 3)%nat -> synced s -> copy i s = l_src s.
Proof.
  intros i s Hi [H0 [H1 H2]].
  destruct i as [| [| [| i]]]; simpl; auto; lia.
Qed.

Theorem ledger_carriers_independent : independent_carriers ledger part.
Proof.
  split.
  - intros i s t _ H. exact H.
  - intros i j s t Hi Hj Hij. simpl in Hi, Hj.
    exists (set_copy j (copy j t) s). unfold part.
    destruct i as [| [| [| i]]]; destruct j as [| [| [| j]]];
      simpl; try lia; split; reflexivity.
Qed.

(** The objection, as a theorem: copying alone doesn't separate them. *)
Theorem ledger_copying_alone_does_not_separate :
  copied_on ledger synced finalized /\ copied_on ledger synced gas_used_positive.
Proof.
  split.
  - intros i Hi. exists fst. intros s Hs. simpl.
    rewrite (synced_copy i s Hi Hs). unfold finalized. tauto.
  - intros i Hi. exists (fun h => Nat.leb 1 (snd h)). intros s Hs.
    change (re_view ledger i s) with (copy i s).
    rewrite (synced_copy i s Hi Hs). unfold gas_used_positive.
    rewrite Nat.leb_le. tauto.
Qed.

Definition final_empty : LState :=
  {| l_src := (true, 0); l_c0 := (true, 0); l_c1 := (true, 0); l_c2 := (true, 0) |}.

Lemma final_empty_synced : synced final_empty.
Proof. repeat split. Qed.

Theorem ledger_finalized_is_pointer : pointer_on ledger synced finalized.
Proof.
  assert (Hrel : relied_on_by_others ledger synced finalized).
  { split.
    - exists 1%nat. split; simpl; [lia | reflexivity].
    - intros i Hi Hprod. split.
      + intros s Hs Hact. simpl in Hact.
        rewrite (synced_copy i s Hi Hs) in Hact. exact Hact.
      + exists final_empty. split; [exact final_empty_synced |].
        simpl in Hi. destruct i as [| [| [| i]]]; simpl; try reflexivity; lia. }
  split.
  - split; [exact (proj1 ledger_copying_alone_does_not_separate) | exact Hrel].
  - intros E' [_ [_ Hothers]] s Hs Hfin.
    destruct (Hothers 1%nat ltac:(simpl; lia) eq_refl) as [Hgate _].
    apply Hgate; [exact Hs |].
    simpl. destruct Hs as [_ [H1 _]]. rewrite H1. exact Hfin.
Qed.

Theorem ledger_gas_not_relied_on :
  ~ relied_on_by_others ledger synced gas_used_positive.
Proof.
  intros [_ Hothers].
  destruct (Hothers 1%nat ltac:(simpl; lia) eq_refl) as [Hgate _].
  specialize (Hgate final_empty final_empty_synced eq_refl).
  unfold gas_used_positive in Hgate. simpl in Hgate. lia.
Qed.

End ReplicatedHeaderToy.

Print Assumptions pointer_on_unique.
Print Assumptions independent_copies_everywhere_are_constant.
Print Assumptions ReplicatedHeaderToy.ledger_carriers_independent.
Print Assumptions ReplicatedHeaderToy.ledger_copying_alone_does_not_separate.
Print Assumptions ReplicatedHeaderToy.ledger_finalized_is_pointer.
Print Assumptions ReplicatedHeaderToy.ledger_gas_not_relied_on.
