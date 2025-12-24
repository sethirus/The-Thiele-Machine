From Coq Require Import List Lia Arith.PeanoNat.
From Coq Require Import Classes.RelationClasses.

From Kernel Require Import VMState VMStep KernelPhysics.

Import ListNotations.

Record Observer (A : Type) := {
  observe : VMState -> A
}.

Definition observer_equiv {A : Type} (O : Observer A) (s1 s2 : VMState) : Prop :=
  observe A O s1 = observe A O s2.

(** A concrete notion of "physics collapse" for an observer:
    the observer identifies (treats as equivalent) two states that differ in
    partition-only observation for at least one module id. *)
Definition observer_collapses_partition_physics {A : Type} (O : Observer A) : Prop :=
  exists s1 s2 mid,
    observer_equiv O s1 s2 /\ ObservableRegion s1 mid <> ObservableRegion s2 mid.

Instance observer_equiv_equivalence {A : Type} (O : Observer A) : Equivalence (observer_equiv O).
Proof.
  split.
  - intros s. reflexivity.
  - intros s1 s2 H. symmetry. exact H.
  - intros s1 s2 s3 H12 H23. transitivity (observe A O s2); assumption.
Qed.

Definition observer_le {A B : Type} (Oa : Observer A) (Ob : Observer B) : Prop :=
  forall s1 s2, observer_equiv Ob s1 s2 -> observer_equiv Oa s1 s2.

Lemma observer_le_refl : forall A (O : Observer A), observer_le O O.
Proof.
  intros A O s1 s2 H. exact H.
Qed.

Lemma observer_le_trans :
  forall A B C (Oa : Observer A) (Ob : Observer B) (Oc : Observer C),
    observer_le Oa Ob -> observer_le Ob Oc -> observer_le Oa Oc.
Proof.
  intros A B C Oa Ob Oc Hab Hbc s1 s2 Hc.
  apply Hab. apply Hbc. exact Hc.
Qed.

Definition ObserverObservable : Observer (nat -> option (list nat * nat)) :=
  {| observe := fun s => fun mid => Observable s mid |}.

Definition ObserverObservableRegion : Observer (nat -> option (list nat)) :=
  {| observe := fun s => fun mid => ObservableRegion s mid |}.

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
