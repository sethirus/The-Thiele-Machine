(** NecFPhysics: the counter against physics, the parts that need no real
    numbers.

    - What a collapse is. Raising a yes-or-no property one way (some false
      state goes to a true one, no true state goes to a false one) is not
      enough on an infinite machine: INC A raises "A is at least one" one
      way, is injective, and costs nothing ([nec_f_one_way_injective]). So
      a collapse also sends two distinct states to one. On a finite state
      space the extra clause is automatic ([nec_f_finite_one_way_merges]).
    - The premise pair on the small machine. Counting every instruction that
      collapses some yes-or-no property, no dissipation can charge each of
      them at least one and stay under the small machine's prices: DEC A 2
      collapses "A is zero or the line is 2", merging a state where it is
      false with one where it is true, and costs nothing
      ([nec_f_small_premise_pair_fails]). Counting only the instructions
      that raise the flag, the pair holds ([nec_f_small_premise_pair_on_flag]).
    - Keeping history. The history step is injective for any step. The
      history has to be unbounded for that: a lift on a finite state space
      that tracks a step through a cover onto a finite machine, and is
      injective, forces the tracked step itself to be injective
      ([nec_f_finite_lift_forces_injective]). So no finite memory makes a
      merging step reversible. *)

From Coq Require Import List Bool Arith Lia.
From Coq Require Import Logic.FinFun.
Import ListNotations.
Require Minimal.EarnedCore.
Require Import Minimal.FragmentSmall.
From Kernel Require Import PermanentCertification.
From Kernel Require Import ObservationPolicy.

Module E := Minimal.EarnedCore.

(** * The premise pair on the small machine *)

(** An instruction raises a yes-or-no property one way when it sends some
    state where the property is false to one where it is true, and never
    sends a true one to a false one. *)
Definition nec_f_one_way (i : E.instr) (P : E.state -> bool) : Prop :=
  (exists s, P s = false /\ P (E.exec s i) = true) /\
  (forall s, P s = true -> P (E.exec s i) = true).

(** An instruction collapses a yes-or-no property when it raises it one way
    and also sends two distinct states to one. *)
Definition nec_f_collapses (i : E.instr) (P : E.state -> bool) : Prop :=
  nec_f_one_way i P /\ exists s t, s <> t /\ E.exec s i = E.exec t i.

Definition nec_f_collapses_some (i : E.instr) : Prop := exists P, nec_f_collapses i P.

Definition nec_f_zero_or_line2 (s : E.state) : bool :=
  Nat.eqb (E.ca (E.core_of s)) 0 || Nat.eqb (E.pc (E.core_of s)) 2.

Lemma nec_f_dec_one_way : nec_f_one_way (E.DEC E.CA 2) nec_f_zero_or_line2.
Proof.
  split.
  - exists (E.mkst (E.mkcore 1 0 0 0 1 [] None false) 0 false). split; reflexivity.
  - intros [[a b va vb p f ch er] m c] H. unfold nec_f_zero_or_line2 in *. simpl in *.
    unfold E.cexec. destruct er; simpl; [exact H |].
    destruct a as [| a]; simpl; [reflexivity | apply orb_true_r].
Qed.

(** DEC A 2 sends a state where "A is zero or the line is 2" is false and a
    state where it is true to the same state. *)
Lemma nec_f_dec_merges_false_with_true :
  exists s t, nec_f_zero_or_line2 s = false /\ nec_f_zero_or_line2 t = true /\
              E.exec s (E.DEC E.CA 2) = E.exec t (E.DEC E.CA 2).
Proof.
  exists (E.mkst (E.mkcore 1 0 0 0 1 [] None false) 0 false),
         (E.mkst (E.mkcore 0 0 1 0 1 [] None false) 0 false).
  repeat split; reflexivity.
Qed.

Lemma nec_f_dec_collapses : nec_f_collapses (E.DEC E.CA 2) nec_f_zero_or_line2.
Proof.
  split; [exact nec_f_dec_one_way |].
  destruct nec_f_dec_merges_false_with_true as [s [t [Hs [Ht E0]]]].
  exists s, t. split; [intro Est; subst t; congruence | exact E0].
Qed.

(** Why the merge clause is needed. INC A raises "A is at least one" one way,
    yet it is injective and free: on an infinite machine a one-way step need
    not forget anything. Read without the merge clause, the floor would
    charge a step that Landauer's principle charges nothing. *)
Definition nec_f_a_positive (s : E.state) : bool := Nat.leb 1 (E.ca (E.core_of s)).

Theorem nec_f_one_way_injective :
  nec_f_one_way (E.INC E.CA) nec_f_a_positive /\
  frag_injective E.state E.instr E.exec (E.INC E.CA) /\ E.cost (E.INC E.CA) = 0.
Proof.
  split; [split | split; [| reflexivity]].
  - exists (E.start 0 0). split; reflexivity.
  - intros [[a b va vb p f ch er] m c] H. unfold nec_f_a_positive in *. simpl in *.
    unfold E.cexec. destruct er; simpl; [exact H | reflexivity].
  - intros [[a1 b1 va1 vb1 p1 f1 ch1 er1] m1 c1] [[a2 b2 va2 vb2 p2 f2 ch2 er2] m2 c2] H.
    unfold E.exec, E.cexec in H. simpl in H.
    rewrite !Nat.add_0_r, !orb_false_r in H.
    destruct er1, er2; simpl in H; inversion H; subst; reflexivity.
Qed.

(** Read without the merge clause, the premise pair already fails at an
    injective step of the small machine. *)
Theorem nec_f_small_one_way_pair_fails :
  ~ calibrated_positive_model (fun i => exists P, nec_f_one_way i P) E.cost.
Proof.
  intro H0.
  pose proof (proj1 (calibrated_model_exists_iff_positive_cost (fun i => exists P, nec_f_one_way i P) E.cost) H0) as H.
  specialize (H (E.INC E.CA) (ex_intro _ _ (proj1 nec_f_one_way_injective))). simpl in H. lia.
Qed.

(** On a finite state space the merge clause comes for free: a step that
    raises a property one way sends two distinct states to one. *)
Lemma nec_f_pigeonhole :
  forall (S : Type) (eq_dec : forall x y : S, {x = y} + {x <> y}) (f : S -> S)
         (l m : list S),
    NoDup l -> (forall x, In x l -> In (f x) m) -> length m < length l ->
    exists a b, a <> b /\ f a = f b.
Proof.
  intros S eq_dec f l. induction l as [| x xs IH]; intros m Hnd Hin Hlen; [simpl in Hlen; lia |].
  inversion Hnd as [| ? ? Hx Hxs]; subst.
  destruct (in_dec eq_dec (f x) (map f xs)) as [Hy | Hy].
  - apply in_map_iff in Hy as [y [Ey Iy]].
    exists x, y. split; [intro Exy; subst y; contradiction | symmetry; exact Ey].
  - apply (IH (remove eq_dec (f x) m) Hxs).
    + intros x' Ix'. apply in_in_remove; [| apply Hin; right; exact Ix'].
      intro E0. apply Hy. rewrite <- E0. apply in_map. exact Ix'.
    + pose proof (remove_length_lt eq_dec m (f x) (Hin x (or_introl eq_refl))).
      simpl in Hlen. lia.
Qed.

Theorem nec_f_finite_one_way_merges :
  forall (S I : Type) (eq_dec : forall x y : S, {x = y} + {x <> y}) (allS : list S)
         (step : S -> I -> S) (i : I) (P : S -> bool),
    finite_states allS ->
    (exists s, P s = false /\ P (step s i) = true) ->
    (forall s, P s = true -> P (step s i) = true) ->
    exists s t, s <> t /\ step s i = step t i.
Proof.
  intros S I eq_dec allS step i P [Hnd Hall] [s0 [H0 H1]] Hkeep.
  apply (nec_f_pigeonhole S eq_dec (fun s => step s i) (s0 :: filter P allS) (filter P allS)).
  - constructor; [| apply NoDup_filter; exact Hnd].
    intro Hin. apply filter_In in Hin as [_ Hp]. congruence.
  - intros x [<- | Hx]; apply filter_In; split; try apply Hall.
    + exact H1.
    + apply filter_In in Hx as [_ Hp]. apply Hkeep. exact Hp.
  - simpl. lia.
Qed.

(** The premise pair, counting every collapsing instruction, fails on the
    small machine, and it fails at a merge. *)
Theorem nec_f_small_premise_pair_fails :
  ~ calibrated_positive_model nec_f_collapses_some E.cost.
Proof.
  intro H0. pose proof (proj1 (calibrated_model_exists_iff_positive_cost nec_f_collapses_some E.cost) H0) as H.
  specialize (H (E.DEC E.CA 2) (ex_intro _ _ nec_f_dec_collapses)). simpl in H. lia.
Qed.

(** And DEC A 2 is the merge the book points at: it merges two full states
    and costs nothing (the repo's frag_small_dec_free_merge). *)
Theorem nec_f_small_free_collapse_is_merge :
  nec_f_collapses_some (E.DEC E.CA 2) /\
  ~ frag_injective E.state E.instr E.exec (E.DEC E.CA 2) /\ E.cost (E.DEC E.CA 2) = 0.
Proof.
  split; [exists nec_f_zero_or_line2; exact nec_f_dec_collapses | exact frag_small_dec_free_merge].
Qed.

(** Counting only the instructions that raise the flag, the pair holds. *)
Theorem nec_f_small_premise_pair_on_flag :
  calibrated_positive_model (fun i => exists s, E.cert s = false /\ E.cert (E.exec s i) = true) E.cost.
Proof.
  apply (proj2 (calibrated_model_exists_iff_positive_cost _ E.cost)).
  intros i [s [H0 H1]]. destruct (frag_small_certifying_step_priced_merge s i H0 H1) as [_ [_ H]].
  exact H.
Qed.

(** * Keeping history needs unbounded memory *)

Lemma nec_f_nodup_map_inj :
  forall (A B : Type) (f : A -> B) (l : list A) a b,
    NoDup (map f l) -> In a l -> In b l -> f a = f b -> a = b.
Proof.
  intros A B f l. induction l as [| x xs IH]; intros a b Hnd Ha Hb E; [destruct Ha |].
  simpl in Hnd. inversion Hnd as [| ? ? Hx Hxs]; subst.
  destruct Ha as [<- | Ha]; destruct Hb as [<- | Hb].
  - reflexivity.
  - exfalso. apply Hx. rewrite E. apply in_map. exact Hb.
  - exfalso. apply Hx. rewrite <- E. apply in_map. exact Ha.
  - apply IH; assumption.
Qed.

(** A lift on a finite state space X, through a cover pi onto every state of
    a finite machine, that tracks the machine's step and is injective,
    forces the machine's step to be injective. *)
Theorem nec_f_finite_lift_forces_injective :
  forall (X S I : Type) (allX : list X) (allS : list S)
         (lift : X -> I -> X) (step : S -> I -> S) (pi : X -> S) (i : I),
    finite_states allX -> finite_states allS ->
    (forall s, exists x, pi x = s) ->
    (forall x, pi (lift x i) = step (pi x) i) ->
    step_injective lift i ->
    step_injective step i.
Proof.
  intros X S I allX allS lift step pi i [HndX HX] [HndS HS] Hcov Htrack Hinj.
  (* the lift, injective on a finite set, reaches every state *)
  assert (Hsurj : forall x', exists x, lift x i = x').
  { assert (Hnd : NoDup (map (fun x => lift x i) allX)).
    { apply Injective_map_NoDup; [intros a b E; exact (Hinj a b E) | exact HndX]. }
    assert (Hback : incl allX (map (fun x => lift x i) allX)).
    { apply NoDup_length_incl; [exact Hnd | rewrite map_length; lia | intros y _; apply HX]. }
    intro x'. pose proof (Hback x' (HX x')) as Hx. apply in_map_iff in Hx as [x [E _]].
    exists x. exact E. }
  (* so the step reaches every state *)
  assert (Hcover : incl allS (map (fun s => step s i) allS)).
  { intros s _. destruct (Hcov s) as [x' <-]. destruct (Hsurj x') as [x <-].
    rewrite Htrack. apply (in_map (fun s => step s i)). apply HS. }
  (* a step reaching every state of a finite set forgets nothing *)
  assert (Hnd : NoDup (map (fun s => step s i) allS)).
  { apply (NoDup_incl_NoDup HndS); [rewrite map_length; lia | exact Hcover]. }
  intros a b E. apply (nec_f_nodup_map_inj _ _ (fun s => step s i) allS); auto.
Qed.

(** The history step itself, for the record: injective for any step, its
    first component the original step (the repo's own theorems). *)
Theorem nec_f_history_step_facts :
  forall (St Ins : Type) (step : St -> Ins -> St) i,
    (forall sh th, ObservationPolicy.history_step step sh i = ObservationPolicy.history_step step th i -> sh = th) /\
    (forall sh, fst (ObservationPolicy.history_step step sh i) = step (fst sh) i).
Proof.
  intros St Ins step i. split.
  - apply retained_history_step_injective.
  - intro sh. apply history_simulates_observed_step.
Qed.

Print Assumptions nec_f_one_way_injective.
Print Assumptions nec_f_small_one_way_pair_fails.
Print Assumptions nec_f_finite_one_way_merges.
Print Assumptions nec_f_small_premise_pair_fails.
Print Assumptions nec_f_small_free_collapse_is_merge.
Print Assumptions nec_f_small_premise_pair_on_flag.
Print Assumptions nec_f_finite_lift_forces_injective.
Print Assumptions nec_f_history_step_facts.
