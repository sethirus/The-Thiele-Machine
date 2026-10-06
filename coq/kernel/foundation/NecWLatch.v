(** NecWLatch: the latch theorem pushed to its limits.

    - The record factors as a latch exactly when it is driven by the
      computation and permanent. The other three clauses of an honest
      extension (the ledger never goes down, A2, some reachable write) are
      not used, so the theorem holds without them.
    - The toggle meets every clause but permanence, and the clock meets
      every clause but being driven by the computation; neither factors.
    - The event is fixed on every base state seen with the record off, and
      nowhere else: an honest extension can factor through two different
      events.
    - The latch of an event is honest exactly when the supposition holds
      (a run reaches a state with the record off and the event on); the
      same for the history latch.
    - The history latch is injective exactly when the base step is.
    - A finite, permanent, injective single step never writes the record,
      and each of the three hypotheses is needed.
    - Two records factor as two latches exactly when the pair is driven and
      each record is permanent.
    - The event is a free choice (the corollary the book argues in the
      text). *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import StructuralCore StructuralCoreCover StructuralCoreAnyBase.
From Kernel Require Import StructuralRecordAxis RecordAxisDiscrimination PermanentCertification.

(* ================================================================= *)
(** * 1. The latch, exactly                                           *)
(* ================================================================= *)

Theorem nec_w_latch_from_driven_permanent :
  forall M B (C : BaseCover M B),
    computation_driven M B C -> record_permanent M ->
    exists h, latch_factorization M B C h.
Proof.
  intros M B C [f Hf] Hperm.
  exists (fun b => f b false).
  intro m. unfold latch_next. simpl.
  rewrite (base_step M B C m).
  destruct (rc_cert M m) eqn:Hc.
  - rewrite (Hperm m Hc). reflexivity.
  - rewrite Hf, Hc. reflexivity.
Qed.

Theorem nec_w_latch_iff :
  forall M B (C : BaseCover M B),
    (exists h, latch_factorization M B C h) <->
    (computation_driven M B C /\ record_permanent M).
Proof.
  intros M B C. split.
  - intros [h Hh]. split.
    + exists (fun b r => orb r (h b)). intro m.
      specialize (Hh m). unfold latch_next in Hh. simpl in Hh.
      injection Hh as _ H2. exact H2.
    + intros m Hm. specialize (Hh m). unfold latch_next in Hh. simpl in Hh.
      injection Hh as _ H2. rewrite H2, Hm. reflexivity.
  - intros [Hd Hp]. exact (nec_w_latch_from_driven_permanent M B C Hd Hp).
Qed.

(** The repository's theorem is a corollary. *)
Corollary nec_w_record_axis_is_latch : record_axis_is_latch.
Proof.
  intros M B C [Hd [_ [_ [Hp _]]]]. exact (nec_w_latch_from_driven_permanent M B C Hd Hp).
Qed.

(** The toggle meets every clause of an honest extension except
    permanence, and does not factor. *)
Theorem nec_w_toggle_meets_rest :
  computation_driven ToggleCore counter_base toggle_cover /\
  ledger_carried ToggleCore /\ rc_a2 ToggleCore /\
  reachable_record_write ToggleCore /\
  ~ record_permanent ToggleCore /\
  ~ exists h, latch_factorization ToggleCore counter_base toggle_cover h.
Proof.
  split; [exact toggle_computation_driven |].
  split; [intros [n r]; cbn; lia |].
  split; [intros [n r] _ _; unfold step_cost; cbn -[Nat.sub]; lia |].
  split; [exists (0, false), 0; split; [exact I | split; reflexivity] |].
  split; [exact toggle_not_permanent | exact toggle_not_latch].
Qed.

(** The clock meets every clause except being driven by the computation,
    and does not factor. *)
Theorem nec_w_clock_meets_rest :
  ledger_carried ClockCore /\ rc_a2 ClockCore /\
  record_permanent ClockCore /\ reachable_record_write ClockCore /\
  ~ computation_driven ClockCore counter_base clock_cover /\
  ~ exists h, latch_factorization ClockCore counter_base clock_cover h.
Proof.
  split; [intros [[b k] r]; cbn; lia |].
  split; [intros [[b k] r] _ _; unfold step_cost; cbn -[Nat.sub]; lia |].
  split; [exact clock_record_permanent |].
  split; [exists (0, 0, false), 5; split; [exact I | split; reflexivity] |].
  split; [exact clock_record_not_driven |].
  intro H. apply (nec_w_latch_iff ClockCore counter_base clock_cover) in H.
  exact (clock_record_not_driven (proj1 H)).
Qed.

(* ================================================================= *)
(** * 2. How unique is the event?                                     *)
(* ================================================================= *)

(** Two events that both factor the record agree on every base state seen
    with the record off. *)
Theorem nec_w_latch_event_determined :
  forall M B (C : BaseCover M B) h1 h2,
    latch_factorization M B C h1 -> latch_factorization M B C h2 ->
    forall m, rc_cert M m = false -> h1 (base_state M B C m) = h2 (base_state M B C m).
Proof.
  intros M B C h1 h2 H1 H2 m Hm.
  specialize (H1 m). specialize (H2 m). unfold latch_next in H1, H2. simpl in H1, H2.
  rewrite Hm in H1, H2. simpl in H1, H2. rewrite H1 in H2. injection H2 as E. exact E.
Qed.

(** A record that is already on at every base state but the first. *)
Definition nec_w_early : RCM := {|
  rc_state := nat;
  rc_next := S;
  rc_init := fun _ => True;
  rc_cert := fun n => negb (Nat.eqb n 0);
  rc_mu := fun n => n;
  rc_halted := fun _ => False
|}.

Definition nec_w_early_cover : BaseCover nec_w_early counter_base.
Proof.
  refine (Build_BaseCover nec_w_early counter_base (fun n => n) _ _ _ _).
  - intros; exact I.
  - intros b _. exists b. split; [exact I | reflexivity].
  - intros m. reflexivity.
  - intros m. simpl. tauto.
Defined.

(** Elsewhere the event is free: an honest extension that factors through
    two events differing at base state 1. *)
Theorem nec_w_latch_event_not_unique :
  HonestBaseExtension nec_w_early counter_base nec_w_early_cover /\
  latch_factorization nec_w_early counter_base nec_w_early_cover (fun _ => true) /\
  latch_factorization nec_w_early counter_base nec_w_early_cover (fun b => Nat.eqb b 0) /\
  (fun _ : nat => true) 1 <> (fun b => Nat.eqb b 0) 1.
Proof.
  split; [| split; [| split]].
  - split; [exists (fun _ _ => true); intros m; reflexivity |].
    split; [intros m; cbn; lia |].
    split; [intros m _ _; unfold step_cost; cbn -[Nat.sub]; lia |].
    split; [intros m _; reflexivity |].
    exists 0, 0. split; [exact I | split; reflexivity].
  - intros m. unfold latch_next. simpl. destruct m; reflexivity.
  - intros m. unfold latch_next. simpl. destruct m; reflexivity.
  - simpl. discriminate.
Qed.

(* ================================================================= *)
(** * 3. The converse: the supposition is exactly honesty             *)
(* ================================================================= *)

Theorem nec_w_latch_honest_iff :
  forall (B : BaseMachine) (h : b_state B -> bool),
    HonestBaseExtension (LatchCore B h) B (latch_cover B h) <->
    (exists b0 n, b_init B b0 /\
       let '(b, r, _) := rc_run (LatchCore B h) n (b0, false, 0) in
       r = false /\ h b = true).
Proof.
  intros B h. split; [| apply latch_core_honest].
  intros [_ [_ [_ [_ [s [n [Hinit [H0 H1]]]]]]]].
  destruct s as [[b0 r0] m0]. destruct Hinit as [Hb [-> ->]].
  exists b0, n. split; [exact Hb |].
  set (x := rc_run (LatchCore B h) n (b0, false, 0)) in *.
  destruct x as [[b r] m]. simpl in H0, H1. subst r. split; [reflexivity | exact H1].
Qed.

(** Without the supposition the latch is not honest: the latch of the
    event that never happens. *)
Corollary nec_w_latch_never_not_honest :
  forall B : BaseMachine,
    ~ HonestBaseExtension (LatchCore B (fun _ => false)) B (latch_cover B (fun _ => false)).
Proof.
  intros B H. apply nec_w_latch_honest_iff in H.
  destruct H as [b0 [n [_ H]]].
  destruct (rc_run (LatchCore B (fun _ => false)) n (b0, false, 0)) as [[b r] m].
  destruct H as [_ H]. discriminate.
Qed.

Theorem nec_w_history_honest_iff :
  forall (B : BaseMachine) (h : b_state B -> bool),
    HonestBaseExtension (HistoryLatch B h) B (history_cover B h) <->
    (exists b0 n, b_init B b0 /\
       let '(b, r, _, _) := rc_run (HistoryLatch B h) n (b0, false, [], 0) in
       r = false /\ h b = true).
Proof.
  intros B h. split; [| apply history_latch_honest].
  intros [_ [_ [_ [_ [s [n [Hinit [H0 H1]]]]]]]].
  destruct s as [[[b0 r0] hist0] m0]. destruct Hinit as [Hb [-> [-> ->]]].
  exists b0, n. split; [exact Hb |].
  set (x := rc_run (HistoryLatch B h) n (b0, false, [], 0)) in *.
  destruct x as [[[b r] hist] m]. simpl in H0, H1. subst r. split; [reflexivity | exact H1].
Qed.

(* ================================================================= *)
(** * 4. Reversible machines                                          *)
(* ================================================================= *)

(** The history latch is injective exactly when the base step is. *)
Theorem nec_w_history_injective_iff :
  forall (B : BaseMachine) (h : b_state B -> bool),
    (forall x y, rc_next (HistoryLatch B h) x = rc_next (HistoryLatch B h) y -> x = y) <->
    (forall a b, b_next B a = b_next B b -> a = b).
Proof.
  intros B h. split; [| apply history_latch_injective].
  intros Hinj a b E.
  specialize (Hinj (a, true, [], 0) (b, true, [], 0)).
  simpl in Hinj. rewrite E in Hinj. specialize (Hinj eq_refl).
  injection Hinj as Hab. exact Hab.
Qed.

(** Finiteness is needed: on the naturals the successor is injective, the
    reading "nonzero" is permanent, and the first step writes it. *)
Theorem nec_w_reversible_needs_finite :
  let step := fun (n : nat) (_ : unit) => S n in
  let cert := fun n => negb (Nat.eqb n 0) in
  permanent step cert /\ step_injective step tt /\
  cert 0 = false /\ cert (step 0 tt) = true.
Proof.
  intros step cert. split; [| split; [| split; reflexivity]].
  - intros s i _. reflexivity.
  - intros a b E. injection E as E. exact E.
Qed.

(** Permanence is needed: negation on one bit is injective and turns the
    reading on. *)
Theorem nec_w_reversible_needs_permanent :
  let step := fun (b : bool) (_ : unit) => negb b in
  let cert := fun b : bool => b in
  finite_states [true; false] /\ step_injective step tt /\
  cert false = false /\ cert (step false tt) = true /\ ~ permanent step cert.
Proof.
  intros step cert. split; [| split; [| split; [reflexivity | split; [reflexivity |]]]].
  - split; [repeat constructor; simpl; intuition discriminate | intros []; simpl; auto].
  - intros a b E. destruct a, b; simpl in E; congruence.
  - intros H. specialize (H true tt eq_refl). discriminate.
Qed.

(** Injectivity is needed: the constant step to true is permanent, finite
    and turns the reading on. *)
Theorem nec_w_reversible_needs_injective :
  let step := fun (_ : bool) (_ : unit) => true in
  let cert := fun b : bool => b in
  finite_states [true; false] /\ permanent step cert /\
  cert false = false /\ cert (step false tt) = true /\ ~ step_injective step tt.
Proof.
  intros step cert. split; [| split; [| split; [reflexivity | split; [reflexivity |]]]].
  - split; [repeat constructor; simpl; intuition discriminate | intros []; simpl; auto].
  - intros s i _. reflexivity.
  - intros H. specialize (H true false eq_refl). discriminate.
Qed.

(* ================================================================= *)
(** * 5. Two records                                                  *)
(* ================================================================= *)

Theorem nec_w_pair_iff :
  forall M B (C : BaseCover M B) c1 c2,
    (exists h1 h2, pair_latch_factorization M B C c1 c2 h1 h2) <->
    (pair_computation_driven M B C c1 c2 /\ pair_permanent M c1 /\ pair_permanent M c2).
Proof.
  intros M B C c1 c2. split.
  - intros [h1 [h2 H]]. split; [| split].
    + exists (fun b r1 r2 => (orb r1 (h1 b r2), orb r2 (h2 b r1))).
      intro m. destruct (H m) as [E1 E2]. rewrite E1, E2. reflexivity.
    + intros m Hm. destruct (H m) as [E1 _]. rewrite E1, Hm. reflexivity.
    + intros m Hm. destruct (H m) as [_ E2]. rewrite E2, Hm. reflexivity.
  - intros [[f Hf] [Hp1 Hp2]].
    exists (fun b r2 => fst (f b false r2)), (fun b r1 => snd (f b r1 false)).
    intro m. pose proof (Hf m) as Hm. split.
    + destruct (c1 m) eqn:H1.
      * rewrite (Hp1 m H1). reflexivity.
      * simpl. rewrite <- Hm. reflexivity.
    + destruct (c2 m) eqn:H2.
      * rewrite (Hp2 m H2). reflexivity.
      * simpl. rewrite <- Hm. reflexivity.
Qed.

(** The case the iff excludes is not empty: a driven pair whose first
    record is the toggle does not factor. *)
Theorem nec_w_pair_toggle_not_two_latches :
  pair_computation_driven ToggleCore counter_base toggle_cover snd snd /\
  ~ exists h1 h2, pair_latch_factorization ToggleCore counter_base toggle_cover snd snd h1 h2.
Proof.
  split.
  - exists (fun _ r1 r2 => (negb r1, negb r2)). intros m. reflexivity.
  - intros H. apply nec_w_pair_iff in H. destruct H as [_ [Hp _]].
    specialize (Hp (0, true) eq_refl). discriminate.
Qed.

(* ================================================================= *)
(** * 6. The event is a free choice                                   *)
(* ================================================================= *)

Theorem nec_w_event_free_choice :
  forall (B : BaseMachine) (h1 h2 : b_state B -> bool),
    (exists b0 n, b_init B b0 /\
       let '(b, r, _) := rc_run (LatchCore B h1) n (b0, false, 0) in r = false /\ h1 b = true) ->
    (exists b0 n, b_init B b0 /\
       let '(b, r, _) := rc_run (LatchCore B h2) n (b0, false, 0) in r = false /\ h2 b = true) ->
    HonestBaseExtension (LatchCore B h1) B (latch_cover B h1) /\
    HonestBaseExtension (LatchCore B h2) B (latch_cover B h2) /\
    forall b, h1 b = true -> h2 b = false ->
      rc_cert (LatchCore B h1) (rc_next (LatchCore B h1) (b, false, 0)) = true /\
      rc_cert (LatchCore B h2) (rc_next (LatchCore B h2) (b, false, 0)) = false.
Proof.
  intros B h1 h2 H1 H2.
  split; [apply latch_core_honest; exact H1 |].
  split; [apply latch_core_honest; exact H2 |].
  intros b E1 E2. simpl. rewrite E1, E2. split; reflexivity.
Qed.

Print Assumptions nec_w_latch_from_driven_permanent.
Print Assumptions nec_w_latch_iff.
Print Assumptions nec_w_record_axis_is_latch.
Print Assumptions nec_w_toggle_meets_rest.
Print Assumptions nec_w_clock_meets_rest.
Print Assumptions nec_w_latch_event_determined.
Print Assumptions nec_w_latch_event_not_unique.
Print Assumptions nec_w_latch_honest_iff.
Print Assumptions nec_w_latch_never_not_honest.
Print Assumptions nec_w_history_honest_iff.
Print Assumptions nec_w_history_injective_iff.
Print Assumptions nec_w_reversible_needs_finite.
Print Assumptions nec_w_reversible_needs_permanent.
Print Assumptions nec_w_reversible_needs_injective.
Print Assumptions nec_w_pair_iff.
Print Assumptions nec_w_pair_toggle_not_two_latches.
Print Assumptions nec_w_event_free_choice.
