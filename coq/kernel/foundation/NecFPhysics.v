(** NecFPhysics: the counter against physics, the parts that need no real
    numbers.

    - The premise pair on the small machine. Counting every instruction that
      collapses some yes-or-no property, no dissipation can charge each of
      them at least one and stay under the small machine's prices: DEC A 2
      collapses "A is zero or the line is 2" and costs nothing
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

(** An instruction collapses a yes-or-no property when it sends some state
    where the property is false to one where it is true, and never sends a
    true one to a false one. *)
Definition nec_f_collapses (i : E.instr) (P : E.state -> bool) : Prop :=
  (exists s, P s = false /\ P (E.exec s i) = true) /\
  (forall s, P s = true -> P (E.exec s i) = true).

Definition nec_f_collapses_some (i : E.instr) : Prop := exists P, nec_f_collapses i P.

Definition nec_f_zero_or_line2 (s : E.state) : bool :=
  Nat.eqb (E.ca (E.core_of s)) 0 || Nat.eqb (E.pc (E.core_of s)) 2.

Lemma nec_f_dec_collapses : nec_f_collapses (E.DEC E.CA 2) nec_f_zero_or_line2.
Proof.
  split.
  - exists (E.mkst (E.mkcore 1 0 0 0 1 [] None false) 0 false). split; reflexivity.
  - intros [[a b va vb p f ch er] m c] H. unfold nec_f_zero_or_line2 in *. simpl in *.
    unfold E.cexec. destruct er; simpl; [exact H |].
    destruct a as [| a]; simpl; [reflexivity | apply orb_true_r].
Qed.

(** The premise pair, counting every collapsing instruction, fails on the
    small machine. *)
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

Print Assumptions nec_f_small_premise_pair_fails.
Print Assumptions nec_f_small_free_collapse_is_merge.
Print Assumptions nec_f_small_premise_pair_on_flag.
Print Assumptions nec_f_finite_lift_forces_injective.
Print Assumptions nec_f_history_step_facts.
