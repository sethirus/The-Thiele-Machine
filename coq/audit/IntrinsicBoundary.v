(* Countermodels use the actual SlicedInterface, without adding an axiom
   that a raise or a nontrivial fibre must exist. *)
From Coq Require Import Bool Arith Lia.
From Minimal Require Import SlicedEstablishment.

Section AnyBase.
Context {Base Input : Type}.
Variable base_step : Input -> Base -> Base.

Definition identity_slice : SlicedInterface Base Base Input unit.
Proof.
  refine {| view := fun s => s;
            verdict := fun _ => false;
            horizontal := base_step;
            vertical := fun _ s => s;
            shadow_step := base_step;
            vertical_price := fun _ => 0 |};
    intros; try reflexivity; try discriminate.
  exists b; reflexivity.
Defined.

Theorem every_base_has_a_slice_without_hidden_distinctions :
  exists M : SlicedInterface Base Base Input unit,
    (forall i s, horizontal M i s = base_step i s) /\
    (~ exists s t, s <> t /\ view M s = view M t) /\
    (forall s, verdict M s = false) /\
    (forall i, vertical_price M i = 0).
Proof.
  exists identity_slice; repeat split; try reflexivity.
  intros [s [t [Hneq Heq]]]; apply Hneq; exact Heq.
Qed.

Theorem identity_slice_never_raises : forall s,
  verdict identity_slice s = false.
Proof. reflexivity. Qed.

Theorem identity_slice_has_zero_vertical_price : forall i,
  vertical_price identity_slice i = 0.
Proof. reflexivity. Qed.

Theorem identity_slice_preserves_every_base_step : forall i s,
  horizontal identity_slice i s = base_step i s.
Proof. reflexivity. Qed.
End AnyBase.

(* Even requiring a reachable raise does not select a unique slice.
   Both examples have a one-state base and all full states are reachable
   from the false state by repeated vertical steps. *)
Definition two_state_slice : SlicedInterface bool unit unit unit.
Proof.
  refine {| view := fun _ => tt; verdict := fun s => s;
            horizontal := fun _ s => s; vertical := fun _ _ => true;
            shadow_step := fun _ _ => tt; vertical_price := fun _ => 1 |};
    intros; try reflexivity; try lia.
  destruct b; exists false; reflexivity.
Defined.

Definition double_price_slice : SlicedInterface bool unit unit unit.
Proof.
  refine {| view := fun _ => tt; verdict := fun s => s;
            horizontal := fun _ s => s; vertical := fun _ _ => true;
            shadow_step := fun _ _ => tt; vertical_price := fun _ => 2 |};
    intros; try reflexivity; try lia.
  destruct b; exists false; reflexivity.
Defined.

Theorem identical_dynamics_do_not_determine_price :
  (forall s, view two_state_slice s = view double_price_slice s) /\
  (forall s, verdict two_state_slice s = verdict double_price_slice s) /\
  (forall i s, horizontal two_state_slice i s = horizontal double_price_slice i s) /\
  (forall i s, vertical two_state_slice i s = vertical double_price_slice i s) /\
  vertical_price two_state_slice tt <> vertical_price double_price_slice tt.
Proof. repeat split; intros; try reflexivity; discriminate. Qed.

Inductive Three := first | second | third.
Definition advance (s : Three) :=
  match s with first => second | second => third | third => third end.
Definition three_reading (s : Three) :=
  match s with first => false | _ => true end.

Definition three_state_slice : SlicedInterface Three unit unit unit.
Proof.
  refine {| view := fun _ => tt; verdict := three_reading;
            horizontal := fun _ s => s; vertical := fun _ => advance;
            shadow_step := fun _ _ => tt; vertical_price := fun _ => 1 |};
    intros; try reflexivity; try lia.
  - destruct b; exists first; reflexivity.
  - destruct s; simpl in *; congruence.
Defined.

Theorem both_slices_have_a_raise :
  verdict two_state_slice false = false /\
  verdict two_state_slice (vertical two_state_slice tt false) = true /\
  verdict three_state_slice first = false /\
  verdict three_state_slice (vertical three_state_slice tt first) = true.
Proof. repeat split; reflexivity. Qed.

Theorem three_states_reachable : forall s,
  s = first \/ s = vertical three_state_slice tt first \/
  s = vertical three_state_slice tt (vertical three_state_slice tt first).
Proof. destruct s; simpl; auto. Qed.

Theorem collapse_preserves_slice_operations :
  (forall s, three_reading (horizontal three_state_slice tt s) =
    horizontal two_state_slice tt (three_reading s)) /\
  (forall s, three_reading (vertical three_state_slice tt s) =
    vertical two_state_slice tt (three_reading s)) /\
  (forall s, verdict two_state_slice (three_reading s) = verdict three_state_slice s) /\
  (forall s, view two_state_slice (three_reading s) = view three_state_slice s).
Proof. repeat split; intros []; reflexivity. Qed.

Theorem no_injection_from_three_to_two :
  ~ exists f : Three -> bool, forall x y, f x = f y -> x = y.
Proof.
  intros [f H].
  destruct (f first) eqn:E1, (f second) eqn:E2, (f third) eqn:E3;
    first [assert (first = second) by (apply H; congruence); discriminate
          |assert (first = third) by (apply H; congruence); discriminate
          |assert (second = third) by (apply H; congruence); discriminate].
Qed.

Print Assumptions identity_slice.
Print Assumptions every_base_has_a_slice_without_hidden_distinctions.
Print Assumptions identity_slice_never_raises.
Print Assumptions identity_slice_has_zero_vertical_price.
Print Assumptions identity_slice_preserves_every_base_step.
Print Assumptions two_state_slice.
Print Assumptions double_price_slice.
Print Assumptions identical_dynamics_do_not_determine_price.
Print Assumptions three_state_slice.
Print Assumptions both_slices_have_a_raise.
Print Assumptions three_states_reachable.
Print Assumptions collapse_preserves_slice_operations.
Print Assumptions no_injection_from_three_to_two.

(* The unpointed toggle has a renaming symmetry exchanging its two states.
   A reading selected from that dynamics alone must respect this symmetry.
   Distinguished starts, tasks and meanings are additional input, not excluded. *)
Theorem toggle_symmetry_forces_constant_reading : forall r : bool -> bool,
  (forall s, r (negb s) = r s) -> forall s t, r s = r t.
Proof.
  intros r H [] []; try reflexivity;
    first [exact (H false) | symmetry; exact (H false)].
Qed.

Theorem no_nonconstant_renaming_invariant_toggle_reading :
  ~ exists r : bool -> bool,
      (forall s, r (negb s) = r s) /\ exists s t, r s <> r t.
Proof.
  intros [r [H [s [t Hneq]]]].
  apply Hneq; apply toggle_symmetry_forces_constant_reading; exact H.
Qed.

(* Finite runs can agree with a permanent latch through any chosen horizon
   and still revoke it later. Both readings satisfy the actual toll at unit
   instruction price. This is a mathematical validation boundary, not a claim
   that every physical record eventually fails. *)
From Kernel Require Import CostSemanticsComparison.
Definition clock_step (s : nat) (_ : unit) := S s.
Definition enduring_reading (s : nat) := negb (Nat.eqb s 0).
Definition delayed_reset_reading (h s : nat) :=
  andb (Nat.leb 1 s) (Nat.leb s (S h)).

Theorem finite_observations_do_not_establish_permanence : forall h,
  (forall n, n <= S h -> delayed_reset_reading h n = enduring_reading n) /\
  (forall n, enduring_reading n = true -> enduring_reading (S n) = true) /\
  delayed_reset_reading h 0 = false /\
  delayed_reset_reading h 1 = true /\
  delayed_reset_reading h (S h) = true /\
  delayed_reset_reading h (S (S h)) = false /\
  (~ forall n, delayed_reset_reading h n = true ->
     delayed_reset_reading h (S n) = true) /\
  CostSemanticsComparison.a2 nat unit clock_step (fun _ => 1) enduring_reading /\
  CostSemanticsComparison.a2 nat unit clock_step (fun _ => 1) (delayed_reset_reading h).
Proof.
  intro h.
  assert (Hlast : delayed_reset_reading h (S h) = true).
  { unfold delayed_reset_reading; rewrite Nat.leb_refl; reflexivity. }
  assert (Hreset : delayed_reset_reading h (S (S h)) = false).
  { unfold delayed_reset_reading.
    assert (H : Nat.leb (S (S h)) (S h) = false) by (apply Nat.leb_gt; lia).
    rewrite H; reflexivity. }
  split.
  - intros [|n] Hn; [reflexivity|].
    unfold delayed_reset_reading, enduring_reading.
    assert (H : Nat.leb (S n) (S h) = true) by (apply Nat.leb_le; lia).
    rewrite H; reflexivity.
  - split.
    + intros [|n] H; reflexivity.
    + split; [reflexivity|].
      split; [reflexivity|].
      split; [exact Hlast|].
      split; [exact Hreset|].
      split.
      * intro H; specialize (H (S h) Hlast); congruence.
      * split; intros s i H0 H1; lia.
Qed.

Print Assumptions toggle_symmetry_forces_constant_reading.
Print Assumptions no_nonconstant_renaming_invariant_toggle_reading.
Print Assumptions finite_observations_do_not_establish_permanence.
