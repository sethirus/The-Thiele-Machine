(** KnowledgeNarrowingMinimal: free learning in a run, and the smallest
    machine that does it.

    - The demon of [KnowledgeNarrowing] refutes the incremental reading too
      ([demon_refutes_incremental]): its first window shows a blank display
      at both starting states, so the observer starts with two candidates,
      and one free measurement leaves one.
    - Three states are enough ([free_incremental_narrowing_with_three]).
      A cycle through three states, seen as false, false, true, splits the
      two states that look alike at the start, and a cycle forgets nothing,
      so it is free.
    - Two states are not ([no_free_incremental_narrowing_below_three]).
      Two starting states that look alike at the start are then every
      state, so the window shows the same thing everywhere and never
      teaches anything. *)

(* SCOPE NOTE: standalone proof scope. The machines here are the demon and
   small cycles, stated over any step function and window, so the file
   imports no machine semantics; the demon's free narrowing is
   [observer_narrowing_can_be_free] in [KnowledgeNarrowing]. *)

From Coq Require Import List Bool Arith.PeanoNat Lia FinFun.
Import ListNotations.
From Kernel Require Import PermanentCertification PermanentRecordPricing.
From Kernel Require Import KnowledgeNarrowing.
From Kernel Require Import KnowledgeNarrowingIncremental.

(** * The demon *)

Theorem demon_refutes_incremental :
  ~ incremental_observer_narrowing_priced dstep dcost display Bool.bool_dec.
Proof.
  intro H.
  assert (Hnd : NoDup demon_prior)
    by (repeat constructor; simpl; intuition discriminate).
  specialize (H demon_prior [Measure] (true, false) Hnd (or_intror (or_introl eq_refl))).
  vm_compute in H. lia.
Qed.

(** * Three states are enough *)

Inductive Tri3 : Type := U3 | V3 | W3.

Definition tri3_eq_dec : forall a b : Tri3, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition tri3_step (x : Tri3) (_ : unit) : Tri3 :=
  match x with U3 => V3 | V3 => W3 | W3 => U3 end.

Definition tri3_window (x : Tri3) : bool :=
  match x with W3 => true | _ => false end.

Lemma tri3_finite : finite_states [U3; V3; W3].
Proof.
  split; [repeat constructor; simpl; intuition discriminate |].
  intros []; simpl; auto.
Qed.

Lemma tri3_step_injective : forall i, Injective (fun x => tri3_step x i).
Proof. intros i [] [] H; simpl in H; congruence. Qed.

Lemma tri3_compression_priced :
  compression_priced tri3_step (fun _ => 0) tri3_eq_dec.
Proof.
  intros i D HD. unfold image_size. simpl.
  rewrite nodup_fixed_point.
  - rewrite map_length. lia.
  - apply Injective_map_NoDup; [apply tri3_step_injective | exact HD].
Qed.

Theorem free_incremental_narrowing_with_three : free_incremental_narrowing_with 3.
Proof.
  exists Tri3, unit, bool, [U3; V3; W3], tri3_step, (fun _ => 0), tri3_eq_dec,
         tri3_window, Bool.bool_dec, [U3; V3], [tt], U3.
  split; [exact tri3_finite |].
  split; [reflexivity |].
  split; [exact tri3_compression_priced |].
  split; [repeat constructor; simpl; intuition discriminate |].
  split; [left; reflexivity |].
  split; [reflexivity |].
  vm_compute. lia.
Qed.

(** * Two states are not *)

Section TwoStates.

Variables (St It Ot : Type).
Variable step : St -> It -> St.
Variable obs : St -> Ot.
Variable obs_eq_dec : forall a b : Ot, {a = b} + {a <> b}.

Lemma states_along_length : forall t s,
  length (states_along St It step s t) = S (length t).
Proof. induction t; intro s; simpl; [reflexivity | rewrite IHt; reflexivity]. Qed.

Lemma map_constant : forall (c : Ot) (l : list St),
  (forall s, obs s = c) -> map obs l = repeat c (length l).
Proof.
  intros c l Hc. induction l; simpl; [reflexivity |]. rewrite Hc, IHl. reflexivity.
Qed.

(** When the window shows the same thing at every state, no candidate is
    ever crossed off. *)
Lemma knowledge_constant_window : forall Omega t s0,
  (forall s, obs s = obs s0) ->
  knowledge step obs obs_eq_dec Omega t s0 = Omega.
Proof.
  intros Omega t s0 Hc. unfold knowledge.
  apply forallb_filter_id. apply forallb_forall. intros s _.
  unfold same_view, seen.
  rewrite (map_constant (obs s0) _ Hc), (map_constant (obs s0) _ Hc),
          !states_along_length.
  destruct (list_eq_dec obs_eq_dec _ _) as [_ | Hne]; [reflexivity |].
  exfalso. apply Hne. reflexivity.
Qed.

(** A starting candidate looks like the actual starting state in the first
    window. *)
Lemma initial_knowledge_same_window : forall Omega s0 s1,
  In s1 (knowledge step obs obs_eq_dec Omega [] s0) -> obs s1 = obs s0.
Proof.
  intros Omega s0 s1 H. unfold knowledge in H.
  apply filter_In in H as [_ H]. unfold same_view in H.
  destruct (list_eq_dec obs_eq_dec _ _) as [Heq | _]; [| discriminate].
  unfold seen in Heq. simpl in Heq. injection Heq. auto.
Qed.

End TwoStates.

Theorem no_free_incremental_narrowing_below_three :
  forall n, n <= 2 -> ~ free_incremental_narrowing_with n.
Proof.
  intros n Hn
    [St [It [Ot [all [step [cost [eq_dec [obs [od [Omega [t [s0
      [[Hnd Hall] [Hlen [_ [HndO [Hin [_ Hlt]]]]]]]]]]]]]]]]]].
  set (K0 := knowledge step obs od Omega [] s0) in *.
  assert (HK0nd : NoDup K0) by (apply NoDup_filter; exact HndO).
  assert (HsubO : length K0 <= length Omega) by apply knowledge_sublist.
  assert (Hs0Kt : In s0 (knowledge step obs od Omega t s0))
    by (apply knowledge_contains_actual; exact Hin).
  (* The run leaves at least one candidate, so the start had at least two. *)
  assert (Hlong : 2 <= length K0).
  { destruct (knowledge step obs od Omega t s0) as [| x rest] eqn:Kt.
    - inversion Hs0Kt.
    - simpl in Hlt. lia. }
  (* A second starting candidate, distinct from s0. *)
  assert (Hs1 : exists s1, In s1 K0 /\ s1 <> s0).
  { destruct K0 as [| a [| b rest]] eqn:HK; simpl in Hlong; try lia.
    inversion HK0nd as [| ? ? Hab _]; subst.
    destruct (eq_dec a s0) as [-> | Ha].
    - exists b. split; [right; left; reflexivity |].
      intros ->. apply Hab. left; reflexivity.
    - exists a. split; [left; reflexivity | exact Ha]. }
  destruct Hs1 as [s1 [Hs1K Hs1ne]].
  pose proof (initial_knowledge_same_window St It Ot step obs od Omega s0 s1 Hs1K)
    as Hobs1.
  (* With at most two states, s0 and s1 are all of them. *)
  assert (Hcover : forall s, s = s0 \/ s = s1).
  { intro s. destruct (eq_dec s s0) as [-> | H0]; [left; reflexivity |].
    destruct (eq_dec s s1) as [-> | H1]; [right; reflexivity |].
    exfalso.
    assert (Hthree : NoDup [s0; s1; s]).
    { constructor; [simpl; intros [H | [H | []]]; congruence |].
      constructor; [simpl; intros [H | []]; congruence |].
      constructor; [intros [] | constructor]. }
    pose proof (NoDup_incl_length Hthree (fun x _ => Hall x)). simpl in *. lia. }
  assert (Hconst : forall s, obs s = obs s0).
  { intro s. destruct (Hcover s) as [-> | ->]; [reflexivity | exact Hobs1]. }
  rewrite (knowledge_constant_window St It Ot step obs od Omega t s0 Hconst) in Hlt.
  lia.
Qed.

Print Assumptions demon_refutes_incremental.
Print Assumptions free_incremental_narrowing_with_three.
Print Assumptions no_free_incremental_narrowing_below_three.
