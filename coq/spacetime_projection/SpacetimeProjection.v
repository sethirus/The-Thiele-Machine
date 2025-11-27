(** * Spacetime as a projection of the Thiele manifold.

    This study connects the infinite-dimensional Thiele manifold to the
    4D spacetime model and makes the projection properties explicit.  The
    projection is intentionally lossy: many manifold states collapse to
    the same spacetime event, and a positive \u03bc-cost records the lost
    dimensional information.  Simplified quantum- and consciousness-like
    phenomena fall out of this projection view. *)

From Coq Require Import Arith.Arith Lia.
From SelfReference Require Import SelfReference.
From Spacetime Require Import Spacetime.
From ThieleManifold Require Import ThieleManifold.

(** ** Thiele states and a concrete projection to spacetime events *)
Record ThieleState := {
  state_level : nat;   (* which tower level this state inhabits *)
  state_payload : nat  (* abstract payload interpreted at that level *)
}.

(** A coarse projection: we keep only the payload as an x-coordinate and
    discard the level entirely.  All other spacetime coordinates are
    zeroed, exhibiting dimensional loss. *)
Definition project_event (s : ThieleState) : Event :=
  {| x := state_payload s;
     y := 0;
     z := 0;
     t := 0 |}.

Definition project_operation (pre post : ThieleState) : Event * Event :=
  (project_event pre, project_event post).

Lemma projection_many_to_one :
  exists s1 s2, s1 <> s2 /\ project_event s1 = project_event s2.
Proof.
  refine (ex_intro _ {| state_level := 0; state_payload := 1 |} _).
  refine (ex_intro _ {| state_level := 1; state_payload := 1 |} _).
  split; [discriminate|reflexivity].
Qed.

(** ** Projection at the system level *)
Definition manifold_to_spacetime_system (M : ThieleManifold) : System := pi4 M.

Lemma projection_dimension_gap :
  forall (M : ThieleManifold) n,
    n > 0 -> dimensionally_richer (level M n) (manifold_to_spacetime_system M).
Proof.
  intros M n Hn; unfold manifold_to_spacetime_system.
  apply pi4_lossy_for_higher_levels; lia.
Qed.

Lemma projection_mu_cost_positive :
  forall (M : ThieleManifold) n,
    n > 0 -> mu_cost (level M n) (manifold_to_spacetime_system M) > 0.
Proof.
  intros M n Hn; unfold manifold_to_spacetime_system.
  apply mu_cost_positive_for_projection; lia.
Qed.

Lemma canonical_projection_can_reason :
  can_reason_about (manifold_to_spacetime_system canonical_manifold) spacetime_system.
Proof.
  unfold manifold_to_spacetime_system, pi4, spacetime_system, spacetime_sentences, canonical_manifold, canonical_level; simpl.
  intros P HP; exact HP.
Qed.

(** ** Quantum-like projection artefacts *)
Definition superposition (s1 s2 : ThieleState) : Prop := s1 <> s2.

Definition measurement (s1 s2 : ThieleState) : Event := project_event s1.

Lemma measurement_collapses_superposition :
  forall s1 s2, superposition s1 s2 -> measurement s1 s2 = project_event s1.
Proof. intros; reflexivity. Qed.

Lemma superposed_states_can_coincide_after_projection :
  exists s1 s2, superposition s1 s2 /\ measurement s1 s2 = project_event s2.
Proof.
  destruct projection_many_to_one as [s1 [s2 [Hneq Heq]]].
  exists s1, s2; split; [assumption|].
  unfold measurement; now rewrite Heq.
Qed.

Definition entangled (sA sB : ThieleState) : Prop := state_payload sA = state_payload sB.

Lemma entanglement_survives_projection :
  forall sA sB, entangled sA sB -> project_event sA = project_event sB.
Proof.
  intros sA sB H; unfold entangled in H; unfold project_event; now f_equal.
Qed.

(** ** Consciousness as meta-level access *)
Definition observer_at_level (M : ThieleManifold) (n : nat) : System := level M n.

Definition can_access_meta (M : ThieleManifold) (n : nat) : Prop :=
  can_reason_about (observer_at_level M (S n)) (observer_at_level M n).

Lemma observers_have_meta_access :
  forall (M : ThieleManifold) n, can_access_meta M n.
Proof.
  intros; unfold can_access_meta, observer_at_level; apply level_can_reason.
Qed.

Lemma free_will_as_partition_choice :
  forall (M : ThieleManifold) n,
    can_access_meta M n ->
    exists richer, dimensionally_richer richer (observer_at_level M n).
Proof.
  intros M n _; exists (observer_at_level M (S n)).
  unfold observer_at_level; apply level_strictly_richer.
Qed.

(** ** Projection summarised: spacetime is a lossy shadow *)
Theorem spacetime_is_projection_shadow :
  can_reason_about (manifold_to_spacetime_system canonical_manifold) spacetime_system /\
  (forall n, n > 0 -> mu_cost (observer_at_level canonical_manifold n) (manifold_to_spacetime_system canonical_manifold) > 0).
Proof.
  split.
  - apply canonical_projection_can_reason.
  - intros n Hn; unfold observer_at_level; apply projection_mu_cost_positive; lia.
Qed.
