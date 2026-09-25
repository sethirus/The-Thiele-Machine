From Coq Require Import List Lia Arith.PeanoNat.
From Coq Require Import Classes.RelationClasses.

From Kernel Require Import VMState VMStep KernelPhysics.

Import ListNotations.

(* SCOPE NOTE: foundation connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

(** ObserverDerivation: observer functions and projection relations.

  This file defines observers as functions out of [VMState], compares them
  by equality of observations, and proves the equivalence, refinement,
  projection, and locality consequences used below. The selected observer
  codomain determines what information is retained. No observer here is
  declared to be a complete physical observation interface. *)

(** Observer: abstract measurement device.

  An observer is just a function from VMState into some observation type. The
  choice of codomain fixes how coarse or fine the observation is. States that
  map to the same observation are indistinguishable to that observer. *)
Record Observer (A : Type) := {
  observe : VMState -> A
}.

(** observer_equiv: observational equivalence relation.

  Two states are observationally equivalent for O when O maps them to the
  same measurement result. This is the basic equivalence relation used
  throughout the rest of the file. *)
Definition observer_equiv {A : Type} (O : Observer A) (s1 s2 : VMState) : Prop :=
  observe A O s1 = observe A O s2.

(** observer_collapses_partition_physics: a witness that an observer loses a
    selected partition observation. The definition compares equality under an
    arbitrary observer with inequality under [ObservableRegion]. It is a
    statement about these two functions, not a claim about all measurements
    or about an exhaustive notion of physics. *)
(** A concrete notion of "physics collapse" for an observer:
    the observer identifies (treats as equivalent) two states that differ in
    partition-only observation for at least one module id. *)
Definition observer_collapses_partition_physics {A : Type} (O : Observer A) : Prop :=
  exists s1 s2 mid,
    observer_equiv O s1 s2 /\ ObservableRegion s1 mid <> ObservableRegion s2 mid.

(** observer_equiv_equivalence: equality of an observer's outputs is an
    equivalence relation. The instance is proved directly from reflexivity,
    symmetry, and transitivity of Coq equality. *)
Instance observer_equiv_equivalence {A : Type} (O : Observer A) : Equivalence (observer_equiv O).
Proof.
  split.
  - intros s. reflexivity.
  - intros s1 s2 H. symmetry. exact H.
  - intros s1 s2 s3 H12 H23. transitivity (observe A O s2); assumption.
Qed.

(** observer_le: an ordering between observers (a refinement preorder)

    The definition records the implication between the two observers' equality
    relations.

    DEFINITION (coq/kernel/ObserverDerivation.v:179-180):
    observer_le Oa Ob := ∀ s1 s2. observer_equiv Ob s1 s2 → observer_equiv Oa s1 s2

    INTERPRETATION: Oa ≤ Ob means "Oa's equivalence classes are refinements of
    Ob's classes". Every Ob-equivalence class is a union of Oa-equivalence classes.
    Oa can distinguish states that Ob cannot, but not vice versa.

    STRUCTURE: This is a preorder (reflexive, transitive), proven in:
    - observer_le_refl (line 182): Oa ≤ Oa (reflexivity)
    - observer_le_trans (line 187): Oa ≤ Ob ∧ Ob ≤ Oc → Oa ≤ Oc (transitivity)

    SCOPE: This compares equality of the selected observer outputs. It does not
    assert that either observer is physically complete or that information has
    been characterized outside the codomains named here.

*)
Definition observer_le {A B : Type} (Oa : Observer A) (Ob : Observer B) : Prop :=
  forall s1 s2, observer_equiv Ob s1 s2 -> observer_equiv Oa s1 s2.

(** observer_le_refl: observer_le is reflexive

    CLAIM (coq/kernel/ObserverDerivation.v:214-216):
    ∀ A (O : Observer A). observer_le O O

    Trivial. Given observer_equiv O s1 s2, return the same hypothesis.
    The implication H → H is always valid.

    SCOPE: The proof is the identity implication required for the preorder;
    it carries no claim about measurement precision outside this relation.

*)
Lemma observer_le_refl : forall A (O : Observer A), observer_le O O.
Proof.
  intros A O s1 s2 H. exact H.
Qed.

(** observer_le_trans: observer_le is transitive

    CLAIM (coq/kernel/ObserverDerivation.v:239-242):
    ∀ A B C (Oa : Observer A) (Ob : Observer B) (Oc : Observer C).
      observer_le Oa Ob → observer_le Ob Oc → observer_le Oa Oc

    Chain implications.
    - Given: Oa ≤ Ob (Hab) and Ob ≤ Oc (Hbc)
    - Want: Oa ≤ Oc (for arbitrary s1, s2)
    - Assume: observer_equiv Oc s1 s2 (Hc)
    - Apply Hbc: get observer_equiv Ob s1 s2
    - Apply Hab: get observer_equiv Oa s1 s2 ✓

    SCOPE: The proof composes the two equality implications. It establishes
    transitivity of this defined relation, not a general law about observers.

*)
Lemma observer_le_trans :
  forall A B C (Oa : Observer A) (Ob : Observer B) (Oc : Observer C),
    observer_le Oa Ob -> observer_le Ob Oc -> observer_le Oa Oc.
Proof.
  intros A B C Oa Ob Oc Hab Hbc s1 s2 Hc.
  apply Hab. apply Hbc. exact Hc.
Qed.

(** ObserverObservable: the observer that returns the selected graph payload.

    For each module id it returns [Observable s mid], namely either the stored
    region/evidence pair or [None]. The observer type records exactly this
    payload and says nothing about information outside the graph lookup. *)
Definition ObserverObservable : Observer (nat -> option (list nat * nat)) :=
  {| observe := fun s => fun mid => Observable s mid |}.

(** ObserverObservableRegion: the region projection of the graph observer.

    For each module id it returns [ObservableRegion s mid], dropping the
    evidence component of the graph payload. It is therefore coarser than
    [ObserverObservable] with respect to the data named here. The later
    equality about [mu_gauge_shift] follows because this projection reads the
    graph field and that operation changes [vm_mu], not because a physical
    gauge principle has been established. *)
Definition ObserverObservableRegion : Observer (nat -> option (list nat)) :=
  {| observe := fun s => fun mid => ObservableRegion s mid |}.

(** obs_equiv_implies_region_equiv: equality of the full graph payload implies
    equality of its region projection. The proof unfolds both lookups and uses
    the resulting constructor equalities. *)
(* Definitional lemma: This equality is by definition, not vacuous *)
Lemma obs_equiv_implies_region_equiv : forall s1 s2,
  obs_equiv s1 s2 ->
  forall mid, ObservableRegion s1 mid = ObservableRegion s2 mid.
Proof.
  intros s1 s2 Heq mid.
  specialize (Heq mid).
  unfold ObservableRegion, Observable in *.
  destruct (graph_lookup (vm_graph s1) mid) eqn:Hlk1;
    destruct (graph_lookup (vm_graph s2) mid) eqn:Hlk2;
    simpl in *;
    try discriminate;
    inversion Heq; subst; reflexivity.
Qed.

(** The region observation is unchanged by [mu_gauge_shift] because the
    projection reads [vm_graph] while the shift changes [vm_mu]. This is a
    field-dependency fact about the two definitions. It does not make μ a
    physical gauge quantity or say that only changes in μ are observable. *)
(** Note: the previous standalone [observer_region_gauge_invariant]
    lemma was inlined into [Observer_Minimality] below — the gauge-
    invariance equality is the definitional projection of
    [ObserverObservableRegion]'s [observe] field against [mu_gauge_shift],
    so we close it on demand at the one call site. *)

(** Observational_Locality_Iff_Physics: under the stated graph-validity,
    module-range, and step premises, a changed [ObservableRegion] implies that
    the module occurs in [instr_targets]. This is the contrapositive of
    [observational_no_signaling] for this projection. The theorem does not
    establish a relativistic causal law or a broader physical locality claim. *)
Theorem Observational_Locality_Iff_Physics :
  forall s s' instr mid,
    well_formed_graph s.(vm_graph) ->
    mid < pg_next_id s.(vm_graph) ->
    vm_step s instr s' ->
    (ObservableRegion s mid <> ObservableRegion s' mid -> In mid (instr_targets instr)).
Proof.
  intros s s' instr mid Hwf Hmid Hstep Hneq.
  destruct (in_dec Nat.eq_dec mid (instr_targets instr)) as [Hin|Hnot].
  - exact Hin.
  - exfalso.
    apply Hneq.
    apply (observational_no_signaling s s' instr mid Hwf Hmid Hstep Hnot).
Qed.

(** Observer_Minimality packages two properties of the selected region
    projection: equality of its outputs is an equivalence relation, and its
    outputs are unchanged by [mu_gauge_shift]. The theorem does not establish
    maximality, canonicity, or completeness for physical observation. *)
(** Minimal observer deliverable (constructive form).

    This theorem packages the two properties needed by the TOE attack plan:
    - observational equivalence is an equivalence relation, and
    - μ-gauge shifts are unobservable for the partition-only observer.

    The maximality / "any weaker observer collapses physics" clause is stated
    in a witness-based, axiom-free way via [observer_collapses_partition_physics]. *)
Theorem Observer_Minimality :
  (Equivalence (observer_equiv ObserverObservableRegion)) /\
  (forall s k mid,
      observe _ ObserverObservableRegion s mid =
      observe _ ObserverObservableRegion (mu_gauge_shift k s) mid).
Proof.
  split.
  - exact (observer_equiv_equivalence ObserverObservableRegion).
  - intros s k mid.
    unfold ObserverObservableRegion. simpl.
    unfold ObservableRegion, mu_gauge_shift. simpl.
    reflexivity.
Qed.

(** weaker_observer_collapse_witness: the supplied equality and inequality are
    exactly the existential witnesses required by
    [observer_collapses_partition_physics]. *)
(** If an observer conflates two states that differ in partition-only observation,
    then (by definition) it collapses the partition physics. *)
Lemma weaker_observer_collapse_witness :
  forall A (O : Observer A) s1 s2 mid,
    observer_equiv O s1 s2 ->
    ObservableRegion s1 mid <> ObservableRegion s2 mid ->
    observer_collapses_partition_physics O.
Proof.
  intros A O s1 s2 mid Heq Hneq.
  exists s1, s2, mid.
  split; assumption.
Qed.
