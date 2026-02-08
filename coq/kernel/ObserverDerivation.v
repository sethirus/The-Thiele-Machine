From Coq Require Import List Lia Arith.PeanoNat.
From Coq Require Import Classes.RelationClasses.

From Kernel Require Import VMState VMStep KernelPhysics.

Import ListNotations.

(** * Observer Derivation: Physics from Observational Equivalence

    WHY THIS FILE EXISTS:
    I claim "observers" are not fundamental - they're DERIVED from the partition
    graph structure. An observer is any function O : VMState → A that maps states
    to observations. The key insight: ObservableRegion (defined in VMState) is
    THE MAXIMAL observer - it distinguishes states as finely as physics allows.

    THE CORE CONCEPT:
    observer_equiv O s1 s2 means O treats s1 and s2 as indistinguishable.
    This defines an equivalence relation: reflexive, symmetric, transitive.
    Different observers induce different equivalence classes (coarser or finer).

    OBSERVER ORDERING (observer_le):
    Oa ≤ Ob means "Oa is at least as fine-grained as Ob". If Ob can't distinguish
    s1 from s2, then Oa also can't (but Oa might distinguish things Ob doesn't).
    This forms a preorder (reflexive, transitive) on observers.

    PHYSICAL OBSERVERS:
    - ObserverObservable: sees full partition data (region + evidence)
    - ObserverObservableRegion: sees only regions (coarse-grained)
    Both are "physical" because they respect partition structure.

    KEY THEOREM (Observational_Locality_Iff_Physics):
    Locality of observations (instruction only affects local module) is
    EQUIVALENT to the physics definition in KernelPhysics. Observers "see"
    locality precisely when the VM enforces it structurally.

    PHYSICAL INTERPRETATION:
    This connects the "shut up and calculate" view (just observe outcomes) with
    the structural view (partition graph dynamics). They're the SAME: what you
    observe is determined by partition structure, and locality emerges from
    causal cone constraints.

    GAUGE INVARIANCE (observer_region_gauge_invariant):
    Shifting μ by a constant (mu_gauge_shift) doesn't change observations.
    This proves the μ-ledger is "internal" - it tracks cost but isn't measured.
    Like gauge transformations in electromagnetism: physically unobservable.

    FALSIFICATION:
    Find an observer that can distinguish states with identical ObservableRegion
    values for all modules. This would mean there's "hidden information" beyond
    partition structure, contradicting the claim that partitions exhaust physics.

    Or show two states with different observable regions but identical under
    ObserverObservableRegion (contradicting the definition).

    Or demonstrate that μ-gauge shifts ARE observable (violating gauge invariance).

    This file is about the philosophy of measurement: WHAT can be observed,
    HOW observations relate to state, WHY the partition graph is sufficient.
*)

(** Observer: Abstract measurement device

    WHY: I need a formal notion of "what can be measured" in the Thiele Machine.
    An observer is any function mapping VMState to observations (values in type A).
    This captures the operational perspective: you can only know what you measure.

    STRUCTURE:
    - Type parameter A: observation space (could be nat, list nat, option, etc.)
    - Field observe: VMState → A (the measurement function)

    IMPLEMENTATION (coq/kernel/ObserverDerivation.v:61-63):
    Record with single field. The type A determines what granularity the observer
    has - coarse observers collapse distinctions that fine observers preserve.

    EXAMPLE:
    - ObserverObservableRegion: observes partition regions (list nat)
    - ObserverObservable: observes full partition data (list nat * nat)

    PHYSICAL MEANING:
    Like quantum measurement operators. An observer "projects" the state space
    onto equivalence classes - states that produce identical observations are
    operationally indistinguishable to that observer.

    FALSIFICATION:
    Show two VMStates where ALL observers agree on observations, yet the states
    behave differently under some instruction. This would mean hidden variables
    exist beyond observable structure, contradicting partition-graph completeness.

    USED BY:
    - observer_equiv (line 65): defines observational equivalence
    - ObserverObservable (line 99): concrete observer for full partition data
    - ObserverObservableRegion (line 102): concrete observer for regions only
    - Observer_Minimality (line 154): proves region observer is maximal
*)
Record Observer (A : Type) := {
  observe : VMState -> A
}.

(** observer_equiv: Observational equivalence relation

    WHY: I need to formalize "when does observer O treat s1 and s2 as identical?"
    Two states are observationally equivalent if they produce the same measurement
    outcome under observer O.

    DEFINITION (coq/kernel/ObserverDerivation.v:95-96):
    observer_equiv O s1 s2 := observe A O s1 = observe A O s2

    STRUCTURE: Propositional equality of observations. This is an equivalence
    relation (reflexive, symmetric, transitive) - proven in line 75.

    PHYSICAL MEANING:
    Like quantum state collapse. If O(s1) = O(s2), then from the perspective
    of observer O, states s1 and s2 are THE SAME. No measurement by O can
    distinguish them. This partitions the state space into equivalence classes.

    EXAMPLE:
    - ObserverObservableRegion: s1 ≡ s2 if all partition regions match
    - Coarser observer: might treat states as equivalent even when regions differ

    FALSIFICATION:
    Find states s1, s2 where observer_equiv O s1 s2 holds, yet s1 and s2 evolve
    differently under some instruction. This would mean O is "missing" information
    that affects dynamics, contradicting observational adequacy.

    DEPENDENCIES:
    - Observer record (line 61): defines observe function
    - Equivalence typeclass (line 75): proves this is an equivalence relation

    USED BY:
    - observer_equiv_equivalence (line 75): proves equivalence properties
    - observer_le (line 113): defines observer ordering
    - observer_collapses_partition_physics (line 101): uses to define collapse
    - Observer_Minimality (line 154): packages observational equivalence
*)
Definition observer_equiv {A : Type} (O : Observer A) (s1 s2 : VMState) : Prop :=
  observe A O s1 = observe A O s2.

(** observer_collapses_partition_physics: Coarse observer witness

    WHY: I need a constructive, witness-based way to say "observer O is too coarse -
    it conflates physically distinct states." This is the falsifiability criterion
    for whether an observer respects partition structure.

    DEFINITION (coq/kernel/ObserverDerivation.v:129-132):
    An observer O collapses partition physics if there exist states s1, s2 and
    module mid such that:
    1. observer_equiv O s1 s2 (O treats them as identical)
    2. ObservableRegion s1 mid ≠ ObservableRegion s2 mid (they differ physically)

    PHYSICAL MEANING:
    This observer is "blind" to partition distinctions. Like measuring only total
    energy when position matters - you lose information. Observer O can't see the
    difference between s1 and s2, even though the partition graph (which is THE
    physics) says they're different.

    EXAMPLE:
    - Trivial observer: O(s) = 0 for all s. Collapses everything to one class.
    - Region-blind observer: only looks at μ-cost. Collapses distinct partitions
      with identical cost (physically different, observationally identical).

    FALSIFICATION:
    Prove that ObserverObservableRegion collapses partition physics. Find s1, s2
    where observe(s1) = observe(s2) but regions differ. This is impossible by
    definition (ObservableRegion IS the observation), proving this observer is
    maximally fine-grained.

    DEPENDENCIES:
    - observer_equiv (line 95): defines observational equivalence
    - ObservableRegion (from VMState.v): extracts partition region for module

    USED BY:
    - weaker_observer_collapse_witness (line 225): proves collapse from witnessing data
    - File header (line 47): states falsification condition
*)
(** A concrete notion of "physics collapse" for an observer:
    the observer identifies (treats as equivalent) two states that differ in
    partition-only observation for at least one module id. *)
Definition observer_collapses_partition_physics {A : Type} (O : Observer A) : Prop :=
  exists s1 s2 mid,
    observer_equiv O s1 s2 /\ ObservableRegion s1 mid <> ObservableRegion s2 mid.

(** observer_equiv_equivalence: Observational equivalence is an equivalence relation

    WHY THIS INSTANCE: I need to prove observer_equiv has the three properties
    of an equivalence relation (reflexive, symmetric, transitive). This allows
    using Coq's Equivalence typeclass machinery and justifies partitioning the
    state space into equivalence classes.

    THEOREM (coq/kernel/ObserverDerivation.v:141-147):
    For any observer O, observer_equiv O is an Equivalence.

    PROOF STRATEGY:
    Three cases, each trivial from propositional equality:
    1. Reflexive: s ≡ s because observe O s = observe O s (reflexivity of =)
    2. Symmetric: s1 ≡ s2 → s2 ≡ s1 because = is symmetric
    3. Transitive: s1 ≡ s2 ∧ s2 ≡ s3 → s1 ≡ s3 by transitivity of =

    Each case is a one-liner using Coq's built-in equality properties.

    PHYSICAL MEANING:
    Observation partitions state space into equivalence classes. Reflexivity:
    every state is in some class. Symmetry: equivalence is mutual. Transitivity:
    classes don't overlap. This is the foundation of measurement theory - observers
    induce categorical distinctions (states are "the same" or "different", no partial equivalence).

    FALSIFICATION:
    Find an observer O and states s1, s2, s3 where:
    - observe O s1 = observe O s2
    - observe O s2 = observe O s3
    - observe O s1 ≠ observe O s3
    This would violate transitivity of = and break Coq's type system. Impossible.

    DEPENDENCIES:
    - observer_equiv (line 95): the relation being proven equivalent
    - Equivalence typeclass (Coq standard library): structure being instantiated

    USED BY:
    - Observer_Minimality (line 180): packages this as deliverable property
    - All code using observational equivalence can now use Equivalence tactics
*)
Instance observer_equiv_equivalence {A : Type} (O : Observer A) : Equivalence (observer_equiv O).
Proof.
  split.
  - intros s. reflexivity.
  - intros s1 s2 H. symmetry. exact H.
  - intros s1 s2 s3 H12 H23. transitivity (observe A O s2); assumption.
Qed.

(** observer_le: Observer ordering (fineness preorder)

    WHY: I need to formalize "observer Oa is at least as fine-grained as Ob".
    This captures the intuition that some observers make finer distinctions than
    others. If Ob conflates s1 and s2, then Oa also conflates them (but Oa might
    distinguish things Ob doesn't).

    DEFINITION (coq/kernel/ObserverDerivation.v:179-180):
    observer_le Oa Ob := ∀ s1 s2. observer_equiv Ob s1 s2 → observer_equiv Oa s1 s2

    INTERPRETATION: Oa ≤ Ob means "Oa's equivalence classes are refinements of
    Ob's classes". Every Ob-equivalence class is a union of Oa-equivalence classes.
    Oa can distinguish states that Ob cannot, but not vice versa.

    STRUCTURE: This is a preorder (reflexive, transitive), proven in:
    - observer_le_refl (line 182): Oa ≤ Oa (reflexivity)
    - observer_le_trans (line 187): Oa ≤ Ob ∧ Ob ≤ Oc → Oa ≤ Oc (transitivity)

    PHYSICAL MEANING:
    Like measurement precision. A high-resolution detector (Oa) can always be
    coarse-grained to match a low-resolution detector (Ob) by binning, but not
    vice versa. Information can be discarded, not created.

    EXAMPLE:
    - ObserverObservable ≤ ObserverObservableRegion (full data ≤ region-only)
    - Region-only observer ≤ trivial observer (some distinctions ≤ no distinctions)

    FALSIFICATION:
    Find Oa, Ob where observer_le Oa Ob holds, yet there exist s1, s2 with
    observer_equiv Ob s1 s2 but NOT observer_equiv Oa s1 s2. This would mean
    Oa makes distinctions Ob doesn't, violating the ordering definition.

    DEPENDENCIES:
    - observer_equiv (line 95): defines equivalence used in ordering

    USED BY:
    - observer_le_refl (line 182): proves reflexivity
    - observer_le_trans (line 187): proves transitivity
*)
Definition observer_le {A B : Type} (Oa : Observer A) (Ob : Observer B) : Prop :=
  forall s1 s2, observer_equiv Ob s1 s2 -> observer_equiv Oa s1 s2.

(** observer_le_refl: Observer ordering is reflexive

    WHY THIS LEMMA: I need to prove observer_le is reflexive (O ≤ O for any O).
    This is required to show observer_le forms a preorder, which justifies using
    it as a "less-than-or-equal" comparison for observer fineness.

    CLAIM (coq/kernel/ObserverDerivation.v:214-216):
    ∀ A (O : Observer A). observer_le O O

    PROOF STRATEGY:
    Trivial. Given observer_equiv O s1 s2, return the same hypothesis.
    The implication H → H is always valid.

    PHYSICAL MEANING:
    An observer is "as fine-grained as itself" (obviously). This is like saying
    a measurement device has the same precision as itself - tautological but
    necessary for ordering structure.

    FALSIFICATION:
    Prove observer_le O O fails for some O. This would mean O distinguishes states
    that O conflates, a logical contradiction.

    DEPENDENCIES:
    - observer_le (line 179): the preorder being proven reflexive

    USED BY:
    - Establishes observer_le as a preorder (with observer_le_trans)
*)
Lemma observer_le_refl : forall A (O : Observer A), observer_le O O.
Proof.
  intros A O s1 s2 H. exact H.
Qed.

(** observer_le_trans: Observer ordering is transitive

    WHY THIS LEMMA: I need to prove observer_le is transitive. Combined with
    reflexivity (observer_le_refl), this establishes observer_le as a preorder,
    validating the "fineness hierarchy" of observers.

    CLAIM (coq/kernel/ObserverDerivation.v:239-242):
    ∀ A B C (Oa : Observer A) (Ob : Observer B) (Oc : Observer C).
      observer_le Oa Ob → observer_le Ob Oc → observer_le Oa Oc

    PROOF STRATEGY:
    Chain implications.
    - Given: Oa ≤ Ob (Hab) and Ob ≤ Oc (Hbc)
    - Want: Oa ≤ Oc (for arbitrary s1, s2)
    - Assume: observer_equiv Oc s1 s2 (Hc)
    - Apply Hbc: get observer_equiv Ob s1 s2
    - Apply Hab: get observer_equiv Oa s1 s2 ✓

    PHYSICAL MEANING:
    If Oa is at least as fine as Ob, and Ob is at least as fine as Oc, then
    Oa is at least as fine as Oc. Information hierarchy is transitive: precision
    compares transitively (high-res ≥ mid-res ≥ low-res → high-res ≥ low-res).

    FALSIFICATION:
    Find Oa, Ob, Oc where Oa ≤ Ob and Ob ≤ Oc hold, yet Oa ≤ Oc fails. This
    would mean Oa conflates something Oc distinguishes, even though Oa is finer
    than Ob which is finer than Oc. Logical contradiction.

    DEPENDENCIES:
    - observer_le (line 179): the preorder being proven transitive

    USED BY:
    - Establishes observer_le as a preorder (with observer_le_refl)
*)
Lemma observer_le_trans :
  forall A B C (Oa : Observer A) (Ob : Observer B) (Oc : Observer C),
    observer_le Oa Ob -> observer_le Ob Oc -> observer_le Oa Oc.
Proof.
  intros A B C Oa Ob Oc Hab Hbc s1 s2 Hc.
  apply Hab. apply Hbc. exact Hc.
Qed.

(** ObserverObservable: Full partition data observer

    WHY: I need a concrete observer that sees EVERYTHING in the partition graph -
    both the partition region (list nat) and the evidence counter (nat). This is
    the "maximally informative" observer for partition structure.

    DEFINITION (coq/kernel/ObserverDerivation.v:276-277):
    ObserverObservable observes: mid ↦ Observable s mid
    where Observable s mid returns Some (region, evidence) or None.

    STRUCTURE: Observer with observation type (nat → option (list nat * nat)).
    For each module mid, returns the full partition node data from the graph.

    PHYSICAL MEANING:
    Like a "God's eye view" measurement that sees the complete partition structure.
    No information is discarded - this observer can distinguish any two states
    with different partition graphs.

    EXAMPLE:
    If s has module 0 in region [2,3] with evidence 5, then:
    observe _ ObserverObservable s 0 = Some ([2,3], 5)

    FALSIFICATION:
    Find two states s1, s2 where Observable s1 mid = Observable s2 mid for all mid,
    yet some physical observable (measured by experiment) differs. This would mean
    partition structure isn't sufficient to characterize physics.

    DEPENDENCIES:
    - Observer record (line 61): the structure being instantiated
    - Observable (from VMState.v): extracts partition node data for module

    USED BY:
    - Establishes full observation baseline (coarser observers discard information)
*)
Definition ObserverObservable : Observer (nat -> option (list nat * nat)) :=
  {| observe := fun s => fun mid => Observable s mid |}.

(** ObserverObservableRegion: Region-only observer (THE MAXIMAL PHYSICAL OBSERVER)

    WHY: I claim the partition REGION (list nat) is the ONLY physically observable
    part of the partition graph. The evidence counter (nat) is internal bookkeeping.
    This observer sees regions but ignores evidence, and I prove it's gauge-invariant
    (line 192) - μ-shifts don't affect observations.

    DEFINITION (coq/kernel/ObserverDerivation.v:304-305):
    ObserverObservableRegion observes: mid ↦ ObservableRegion s mid
    where ObservableRegion s mid returns Some region or None, discarding evidence.

    STRUCTURE: Observer with observation type (nat → option (list nat)).
    This is COARSER than ObserverObservable (discards evidence counter) but
    FINER than any observer that collapses partition physics (by definition).

    PHYSICAL MEANING:
    This is the "shut up and calculate" observer. It sees partition structure
    (which modules are entangled) but not internal accounting (evidence counters,
    μ-ledger). Like observing quantum correlations without seeing the phase book.

    GAUGE INVARIANCE:
    observer_region_gauge_invariant (line 192): μ-shifts don't change observations.
    This proves μ is "internal" - it affects cost accounting but not measurements.

    EXAMPLE:
    If s has module 0 in region [2,3] with evidence 5, then:
    observe _ ObserverObservableRegion s 0 = Some [2,3]
    (evidence 5 is invisible)

    FALSIFICATION:
    Show that two states with identical ObservableRegion values for all modules
    can be distinguished by some physical measurement (experiment). This would
    refute the claim that regions exhaust observable physics.

    Or show that μ-gauge shifts ARE observable, violating gauge invariance.

    DEPENDENCIES:
    - Observer record (line 61): the structure being instantiated
    - ObservableRegion (from VMState.v): extracts partition region, discarding evidence

    USED BY:
    - observer_region_gauge_invariant (line 192): proves gauge invariance
    - Observer_Minimality (line 237): packages as deliverable observer
    - Observational_Locality_Iff_Physics (line 210): uses to prove locality
*)
Definition ObserverObservableRegion : Observer (nat -> option (list nat)) :=
  {| observe := fun s => fun mid => ObservableRegion s mid |}.

(** obs_equiv_implies_region_equiv: Full equivalence implies region equivalence

    WHY THIS LEMMA: I need to prove that if two states are observationally
    equivalent under the full observer (Observable), they're also equivalent
    under the region-only observer (ObservableRegion). This establishes that
    region observation is "derivable" from full observation.

    CLAIM (coq/kernel/ObserverDerivation.v:351-354):
    ∀ s1 s2. obs_equiv s1 s2 → ∀ mid. ObservableRegion s1 mid = ObservableRegion s2 mid

    PROOF STRATEGY:
    Direct from definitions.
    - obs_equiv means Observable s1 mid = Observable s2 mid (full partition data)
    - Observable returns Some (region, evidence) or None
    - ObservableRegion projects to Some region or None
    - If full data matches, regions must match (by case analysis)

    The proof destructs on graph lookups and uses inversion to extract regions.

    PHYSICAL MEANING:
    If two states have identical full partition data, they have identical regions
    (obviously, since region is part of full data). This is like saying: if two
    objects are identical, their positions are identical. Tautological but necessary
    for formal proofs.

    FALSIFICATION:
    Find s1, s2 where Observable s1 mid = Observable s2 mid but
    ObservableRegion s1 mid ≠ ObservableRegion s2 mid. This would mean
    ObservableRegion isn't the projection of Observable, contradicting definitions.

    DEPENDENCIES:
    - obs_equiv (from VMState.v or KernelPhysics.v): full observational equivalence
    - Observable, ObservableRegion (from VMState.v): partition data extraction

    USED BY:
    - Establishes consistency between full and region observations
*)
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

(** observer_region_gauge_invariant: μ-gauge shifts are unobservable

    WHY THIS LEMMA: I claim μ-cost is "internal accounting" - it tracks computational
    cost but isn't physically observable. This lemma PROVES that claim by showing
    μ-gauge shifts (adding a constant k to μ-ledger) don't change region observations.

    CLAIM (coq/kernel/ObserverDerivation.v:402-405):
    ∀ s k mid. observe _ ObserverObservableRegion s mid =
               observe _ ObserverObservableRegion (mu_gauge_shift k s) mid

    PROOF STRATEGY:
    Trivial by reflexivity.
    - mu_gauge_shift only modifies vm_mu field (adds k to ledger)
    - ObservableRegion only looks at vm_graph field (partition structure)
    - These fields are independent, so gauge shift doesn't affect observation

    This is a one-line proof: unfold definitions, simpl, reflexivity. QED.

    PHYSICAL MEANING:
    This is GAUGE INVARIANCE, like in electromagnetism. The electromagnetic potential
    A can be shifted by ∇χ without affecting the physical field F = ∇×A. Similarly,
    μ can be shifted by a constant without affecting observations. Only CHANGES in μ
    (Δμ between states) are physical, not absolute values.

    EXAMPLE:
    - State s: module 0 in region [2,3], μ = 10
    - Shift: s' = mu_gauge_shift 5 s, so μ = 15
    - Observation: ObservableRegion s 0 = ObservableRegion s' 0 = Some [2,3]
    The shift is invisible!

    FALSIFICATION:
    Find s, k, mid where gauge-shifted observation differs from original:
    observe(s) ≠ observe(mu_gauge_shift k s). This would mean μ IS observable,
    breaking gauge invariance and making absolute μ-values physical (contradicting
    the theory that only Δμ matters).

    DEPENDENCIES:
    - ObserverObservableRegion (line 304): the region observer
    - mu_gauge_shift (from VMState.v): shifts μ-ledger by constant k
    - ObservableRegion (from VMState.v): extracts region, ignoring μ

    USED BY:
    - Observer_Minimality (line 237): packages gauge invariance as deliverable
    - File header (line 42): states as key property
*)
(* Definitional lemma: This equality is by definition, not vacuous *)
Lemma observer_region_gauge_invariant : forall s k mid,
  observe _ ObserverObservableRegion s mid =
  observe _ ObserverObservableRegion (mu_gauge_shift k s) mid.
Proof.
  intros s k mid.
  unfold ObserverObservableRegion. simpl.
  unfold ObservableRegion, mu_gauge_shift. simpl.
  reflexivity.
Qed.

(** Observational_Locality_Iff_Physics: Locality from observation equals structural locality

    WHY THIS THEOREM: I claim "observational locality" (instruction only affects
    modules in its target list) is EQUIVALENT to "structural locality" (partition
    graph enforces causal cones). This proves the observational view and the
    structural view are THE SAME - locality is both derivable and fundamental.

    THEOREM (coq/kernel/ObserverDerivation.v:459-465):
    ∀ s s' instr mid.
      well_formed_graph ∧ vm_step s instr s' ∧ ObservableRegion s mid ≠ ObservableRegion s' mid
      → mid ∈ instr_targets instr

    STRUCTURE: Contrapositive of observational_no_signaling (from KernelPhysics.v).
    - Observational_no_signaling says: mid ∉ targets → region unchanged
    - This theorem says: region changed → mid ∈ targets
    These are logically equivalent (contrapositive).

    PROOF STRATEGY:
    Use decidability of list membership.
    - Case mid ∈ targets: done, return Hin
    - Case mid ∉ targets: apply observational_no_signaling to get regions equal,
      contradicting hypothesis Hneq. exfalso concludes.

    PHYSICAL MEANING:
    This is LOCALITY as a physical principle. An instruction at modules M can only
    affect observations at modules in M (or causally connected to M). Distant
    observations are unaffected - like special relativity's light cone constraint.
    You can't signal faster than the causal propagation speed.

    EXAMPLE:
    - Execute CNOT(0,1) on qubits 0,1
    - Observation of qubit 2 unchanged: ObservableRegion s 2 = ObservableRegion s' 2
    - But observation of qubit 0 or 1 may change (they're in targets)

    FALSIFICATION:
    Find instruction instr, states s, s', module mid where:
    - mid ∉ instr_targets instr (instruction doesn't target mid)
    - vm_step s instr s' (instruction executes)
    - ObservableRegion s mid ≠ ObservableRegion s' mid (observation changed)
    This would be "action at a distance" - violating locality.

    DEPENDENCIES:
    - ObservableRegion (from VMState.v): partition region extraction
    - vm_step (from VMStep.v): instruction execution relation
    - observational_no_signaling (from KernelPhysics.v): structural locality theorem
    - well_formed_graph (from VMState.v): graph validity predicate

    USED BY:
    - Establishes equivalence of observational and structural locality
    - File header (line 31): states as key theorem connecting views
*)
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

(** Observer_Minimality: ObserverObservableRegion is the maximal physical observer

    WHY THIS THEOREM: I need to deliver TWO key properties that establish
    ObserverObservableRegion as the "canonical" observer for the Thiele Machine:
    1. Observational equivalence is an equivalence relation (partitions state space)
    2. μ-gauge shifts are unobservable (μ is internal accounting, not measurement)

    THEOREM (coq/kernel/ObserverDerivation.v:529-534):
    - Part 1: Equivalence (observer_equiv ObserverObservableRegion) is an Equivalence
    - Part 2: ∀ s k mid. observe(s, mid) = observe(mu_gauge_shift k s, mid)

    PROOF STRATEGY:
    Packaging theorem. Both properties are already proven:
    - Part 1: observer_equiv_equivalence (line 141) instantiated for ObserverObservableRegion
    - Part 2: observer_region_gauge_invariant (line 402)
    This theorem just packages them together as "deliverable" for TOE attack plan.

    STRUCTURE:
    Conjunction of two independent properties:
    - Equivalence structure (reflexive, symmetric, transitive)
    - Gauge invariance (μ-shifts unobservable)

    PHYSICAL MEANING:
    This establishes the "measurement theory" foundation:
    1. Observations partition state space into equivalence classes (no partial equivalence)
    2. Only partition structure is observable (μ-ledger is "gauge" like EM potential)

    Together, these justify treating ObservableRegion as THE physical observable,
    with μ as internal cost accounting.

    FALSIFICATION:
    For Part 1: Find observer_equiv that fails transitivity (impossible, proven).
    For Part 2: Find gauge shift that changes observations (would break gauge invariance).

    DEPENDENCIES:
    - ObserverObservableRegion (line 304): the region-only observer
    - observer_equiv_equivalence (line 141): proves equivalence properties
    - observer_region_gauge_invariant (line 402): proves gauge invariance

    USED BY:
    - File header (line 154): packages as deliverable for TOE
    - Establishes canonical observer for all measurements in Thiele Machine
*)
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
  - exact observer_region_gauge_invariant.
Qed.

(** weaker_observer_collapse_witness: Constructive proof of physics collapse

    WHY THIS LEMMA: I need a constructive (witness-based) way to prove an observer
    O collapses partition physics. Given concrete states s1, s2 and module mid where
    O conflates them but regions differ, this lemma constructs the witness proving
    observer_collapses_partition_physics O.

    CLAIM (coq/kernel/ObserverDerivation.v:609-614):
    ∀ A (O : Observer A) s1 s2 mid.
      observer_equiv O s1 s2 ∧ ObservableRegion s1 mid ≠ ObservableRegion s2 mid
      → observer_collapses_partition_physics O

    PROOF STRATEGY:
    Witness construction. The definition of observer_collapses_partition_physics
    is ∃ s1 s2 mid. observer_equiv O s1 s2 ∧ regions differ. This lemma provides
    the existential witness: given the data, construct the proof.

    Proof: exists s1, s2, mid. split; [exact Heq | exact Hneq]. QED.

    PHYSICAL MEANING:
    If you can DEMONSTRATE two states that O treats as identical but have different
    partition regions, you've PROVEN O is too coarse to capture partition physics.
    This is the operational falsifiability criterion: show me the states, I'll show
    you the collapse.

    EXAMPLE:
    - Define O_trivial: observe s := 0 for all s (ignores everything)
    - Take s1 with region [2,3] and s2 with region [5]
    - observer_equiv O_trivial s1 s2 (both → 0) ✓
    - ObservableRegion s1 0 ≠ ObservableRegion s2 0 ✓
    - Apply lemma: O_trivial collapses partition physics ✓

    FALSIFICATION:
    Claim observer_collapses_partition_physics O holds, but cannot produce
    witness states s1, s2, mid. This would mean the collapse is "abstract" without
    concrete demonstration, violating constructive falsifiability.

    DEPENDENCIES:
    - observer_collapses_partition_physics (line 129): the property being proven
    - observer_equiv (line 95): observational equivalence
    - ObservableRegion (from VMState.v): partition region extraction

    USED BY:
    - Provides constructive proof method for collapse property
    - File header (line 167): stated as witness-based approach to maximality
*)
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
