(* Instruction prices for the actual a2 toll and finite-trace floor.
   A finite covering list gives the constructive least schedule. The
   all-readings result uses decidable state equality. Permanence plus the
   toll forces free reading preservation; no physical calibration is assumed. *)
From Coq Require Import List Bool Arith Lia.
From Kernel Require Import CostSemanticsComparison NecFFloor.

Theorem free_reading_invariance : forall (S I : Type)
  (step : S -> I -> S) (cost : I -> nat) (r : S -> bool),
  a2 S I step cost r ->
  (forall s i, r s = true -> r (step s i) = true) ->
  forall s i, cost i = 0 -> r (step s i) = r s.
Proof.
  intros S I step cost r Ht Hp s i Hz.
  destruct (r s) eqn:E; [apply Hp; exact E|].
  destruct (r (step s i)) eqn:F; [|reflexivity].
  specialize (Ht s i E F); lia.
Qed.

Section FiniteMinimum.
Context {S I : Type}.
Variable step : S -> I -> S.
Variable reading : S -> bool.
Variable states : list S.
Hypothesis covers : forall s, In s states.

Definition can_raise (i : I) :=
  existsb (fun s => negb (reading s) && reading (step s i)) states.
Definition least_price (i : I) : nat := if can_raise i then 1 else 0.

Lemma can_raise_exact : forall i,
  can_raise i = true <->
  exists s, reading s = false /\ reading (step s i) = true.
Proof.
  intro i; unfold can_raise; rewrite existsb_exists; split.
  - intros [s [_ H]]. exists s.
    apply andb_true_iff in H; destruct H as [H0 H1].
    apply negb_true_iff in H0; auto.
  - intros [s [H0 H1]]. exists s; split; [apply covers|].
    rewrite H0, H1; reflexivity.
Qed.

Theorem least_price_satisfies_toll : a2 S I step least_price reading.
Proof.
  intros s i H0 H1; unfold least_price.
  assert (H : can_raise i = true).
  { apply can_raise_exact; exists s; auto. }
  rewrite H; lia.
Qed.

Theorem toll_exactly_dominates_least_price : forall cost : I -> nat,
  a2 S I step cost reading <-> forall i, least_price i <= cost i.
Proof.
  intro cost; split.
  - intros H i; unfold least_price; destruct (can_raise i) eqn:E; [|lia].
    apply can_raise_exact in E; destruct E as [s [H0 H1]].
    exact (H s i H0 H1).
  - intros H s i H0 H1.
    pose proof (least_price_satisfies_toll s i H0 H1).
    specialize (H i); lia.
Qed.

Theorem trace_floor_exactly_dominates_least_price : forall cost : I -> nat,
  nec_f_floor_everywhere S I step cost reading <->
  forall i, least_price i <= cost i.
Proof.
  intro cost; rewrite <- nec_f_floor_iff_a2.
  apply toll_exactly_dominates_least_price.
Qed.

Theorem unique_least_valid_price : forall cost : I -> nat,
  a2 S I step cost reading ->
  (forall other : I -> nat, a2 S I step other reading ->
    forall i, cost i <= other i) ->
  forall i, cost i = least_price i.
Proof.
  intros cost Hvalid Hleast i.
  pose proof (proj1 (toll_exactly_dominates_least_price cost) Hvalid i).
  specialize (Hleast least_price least_price_satisfies_toll i); lia.
Qed.
End FiniteMinimum.

Section AllReadings.
Context {S I : Type}.
Variable step : S -> I -> S.
Variable cost : I -> nat.
Variable state_eq : forall s t : S, {s = t} + {s <> t}.

Theorem every_reading_toll_prices_every_change :
  (forall reading : S -> bool, a2 S I step cost reading) ->
  forall s i, step s i <> s -> 1 <= cost i.
Proof.
  intros Hall s i Hchange.
  specialize (Hall (fun x => if state_eq x (step s i) then true else false) s i).
  cbn in Hall.
  destruct (state_eq s (step s i)) as [E|E]; [congruence|].
  destruct (state_eq (step s i) (step s i)) as [F|F]; [|congruence].
  apply Hall; reflexivity.
Qed.

Theorem every_reading_toll_iff_free_moves_are_identity :
  (forall reading : S -> bool, a2 S I step cost reading) <->
  (forall i, cost i = 0 -> forall s, step s i = s).
Proof.
  split.
  - intros Hall i Hzero s.
    destruct (state_eq (step s i) s) as [E|E]; [exact E|].
    pose proof (every_reading_toll_prices_every_change Hall s i E); lia.
  - intros H reading s i H0 H1.
    destruct (cost i) eqn:E; [|lia].
    rewrite (H i E s) in H1; congruence.
Qed.
End AllReadings.
