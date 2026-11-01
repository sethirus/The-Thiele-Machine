(* SCOPE NOTE: standalone proof scope.
   Defines and bounds external merger and visited-state counts on finite orbit prefixes.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Arith Lia Bool.
From Minimal Require Import CompleteHost.
Import ListNotations.

(* An external structural statistic of a finite observed prefix.
   It is not the existing instruction-price ledger. *)
Section Meter.
  Context {X : Type}.
  Variable eq_dec : forall a b : X, {a=b}+{a<>b}.
  Variable F : X -> X.
  Variable entry : X.

  Definition sources L := map (fun n => iter F n entry) (seq 0 L).
  Definition samples L := map (fun n => iter F (S n) entry) (seq 0 L).
  Definition room L := length (nodup eq_dec (samples L)).
  Definition bad_pair (ab : X*X) : bool :=
    if eq_dec (fst ab) (snd ab) then false
    else if eq_dec (F (fst ab)) (F (snd ab)) then true else false.
  Definition merge_targets L := nodup eq_dec
    (map (fun ab => F (fst ab))
      (filter bad_pair (list_prod (sources L) (sources L)))).
  (* Count distinct observed landing states with at least two distinct
     observed predecessors; revisiting a target does not count it again. *)
  Definition merges L := length (merge_targets L).
  Definition structural_mu L := merges L + room L.
  Definition collision L := exists a b,
    In a (sources L) /\ In b (sources L) /\ a<>b /\ F a=F b.

  Lemma bad_pair_exact : forall a b,
    bad_pair (a,b)=true <-> a<>b /\ F a=F b.
  Proof.
    intros a b; unfold bad_pair; simpl.
    destruct (eq_dec a b); destruct (eq_dec (F a) (F b)); intuition discriminate.
  Qed.
  Lemma merge_target_exact : forall L z, In z (merge_targets L) <->
    exists a b, In a (sources L) /\ In b (sources L) /\
      a<>b /\ F a=z /\ F b=z.
  Proof.
    intros L z; unfold merge_targets; rewrite nodup_In,in_map_iff; split.
    - intros [[a b] [He Hin]]; simpl in He.
      apply filter_In in Hin as [Hin Hb]; apply in_prod_iff in Hin.
      apply bad_pair_exact in Hb; exists a,b; intuition congruence.
    - intros [a [b [Ha [Hb [Hneq [Hfa Hfb]]]]]].
      exists (a,b); split; [exact Hfa|].
      apply filter_In; split; [apply in_prod_iff; auto|].
      apply bad_pair_exact; split; [assumption|congruence].
  Qed.
  Theorem merges_zero_iff : forall L, merges L=0 <-> ~collision L.
  Proof.
    intro L; split.
    - intros Hz [a [b [Ha [Hb [Hneq Heq]]]]].
      assert (Hin:In (F a) (merge_targets L)).
      { apply merge_target_exact; exists a,b; intuition congruence. }
      unfold merges in Hz; apply length_zero_iff_nil in Hz; rewrite Hz in Hin; exact Hin.
    - intros Hnone; unfold merges.
      destruct (merge_targets L) as [|z zs] eqn:E; [reflexivity|].
      exfalso; apply Hnone.
      assert (Hin:In z (merge_targets L)) by (rewrite E; left; reflexivity).
      apply merge_target_exact in Hin as [a [b [Ha [Hb [Hneq [Hfa Hfb]]]]]].
      exists a,b; intuition congruence.
  Qed.
  Lemma source_member : forall L n, n<L -> In (iter F n entry) (sources L).
  Proof.
    intros L n Hn; unfold sources; apply in_map_iff; exists n;
      split; [reflexivity|apply in_seq; lia].
  Qed.
  Lemma no_collision_retains : forall L, ~collision L -> retains F entry L.
  Proof.
    intros L Hnone i j Hi Hj E.
    destruct (eq_dec (iter F i entry) (iter F j entry)); [assumption|].
    exfalso; apply Hnone; exists (iter F i entry),(iter F j entry).
    repeat split; auto using source_member.
  Qed.
  Lemma retains_no_collision : forall L, retains F entry L -> ~collision L.
  Proof.
    intros L Hr [a [b [Ha [Hb [Hneq Heq]]]]].
    unfold sources in Ha,Hb.
    apply in_map_iff in Ha as [i [<- Hi]].
    apply in_map_iff in Hb as [j [<- Hj]].
    apply in_seq in Hi; apply in_seq in Hj; apply Hneq; apply Hr; try lia; exact Heq.
  Qed.
  Theorem zero_merges_iff_retains : forall L, merges L=0 <-> retains F entry L.
  Proof.
    intro L; rewrite merges_zero_iff; split;
      auto using no_collision_retains,retains_no_collision.
  Qed.
  (* Positivity of the sum alone is weak: even an arbitrary nonempty
     constant trajectory has a visited state. The holding assumptions
     below are needed for the horizon-dependent tradeoff, not this fact. *)
  Lemma nonempty_run_has_room : forall L, 0<L -> 0<room L.
  Proof.
    intros L HL.
    assert (Hin:In (F entry) (nodup eq_dec (samples L))).
    { apply nodup_In; unfold samples; apply in_map_iff; exists 0.
      split; [reflexivity|apply in_seq; lia]. }
    unfold room; destruct (nodup eq_dec (samples L)); simpl in *; [contradiction|lia].
  Qed.
  Theorem any_nonempty_run_has_positive_structural_mu : forall L,
    0<L -> 0<structural_mu L.
  Proof. intros L HL; unfold structural_mu; pose proof (nonempty_run_has_room L HL); lia. Qed.

  Variable H : X -> Prop.
  Hypothesis outside : ~H entry.
  Hypothesis enters : H (F entry).
  Hypothesis closed : forall s, H s -> H (F s).

  Theorem zero_merges_exact_room : forall L, merges L=0 -> room L=L.
  Proof.
    intros L Hz; apply merges_zero_iff in Hz.
    assert (Hnd:NoDup (samples L)).
    { unfold samples; apply nodup_map_on; [apply seq_NoDup|].
      intros a b Ha Hb E; apply in_seq in Ha; apply in_seq in Hb.
      assert (He:S a=S b).
      { eapply (@held_prefix_distinct X F H entry outside enters closed L);
          eauto using no_collision_retains; lia. }
      lia. }
    unfold room; rewrite nodup_fixed_point by exact Hnd.
    unfold samples; rewrite map_length,seq_length; reflexivity.
  Qed.
  Theorem merge_or_room : forall L, 0<merges L \/ room L=L.
  Proof.
    intro L; destruct (Nat.eq_dec (merges L) 0) as [Hz|Hz].
    - right; apply zero_merges_exact_room; assumption.
    - left; lia.
  Qed.
  Theorem room_shortfall_forces_merge : forall L, room L<L -> 0<merges L.
  Proof. intro L; destruct (merge_or_room L); lia. Qed.

  Theorem room_bounded_by_held_capacity : forall L hs,
    (forall s, H s -> In s hs) -> room L<=length hs.
  Proof.
    intros L hs Hcover; unfold room; apply NoDup_incl_length; [apply NoDup_nodup|].
    intros s Hin; apply nodup_In in Hin; unfold samples in Hin.
    apply in_map_iff in Hin as [n [<- Hn]].
    apply Hcover; apply (@positive_iter_held X F H entry enters closed n).
  Qed.
  Theorem finite_room_forces_merge : forall L hs,
    (forall s, H s -> In s hs) -> length hs<L -> 0<merges L.
  Proof.
    intros L hs Hcover Hlen; apply room_shortfall_forces_merge.
    pose proof (room_bounded_by_held_capacity L hs Hcover); lia.
  Qed.
  Theorem structural_mu_positive : forall L, 0<L -> 0<structural_mu L.
  Proof. intros L HL; unfold structural_mu; destruct (merge_or_room L); lia. Qed.
End Meter.

(* A positive per-tick additive meter cannot be an unchanged coordinate
   of a finite absorbing host. Instrumenting it changes the state space. *)
Theorem fixed_point_blocks_positive_internal_ledger {X : Type}
    (F : X -> X) (s : X) (p : nat) :
  F s=s -> 0<p -> ~exists mu : X -> nat, forall x, mu (F x)=mu x+p.
Proof.
  intros Hfix Hp [mu Hmu]; pose proof (Hmu s) as H;
    rewrite Hfix in H; lia.
Qed.

(* The external sum has no positive floor for every subsequent tick:
   a run may have already reached its final structural counts. *)
Theorem structural_meter_can_plateau :
  structural_mu Bool.bool_dec (fun _ : bool => true) false 2=2 /\
  structural_mu Bool.bool_dec (fun _ : bool => true) false 3=2.
Proof. split; reflexivity. Qed.
