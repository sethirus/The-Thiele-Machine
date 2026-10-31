(** NecWCasper: accountable safety pushed to its limits.

    The repository's setting record carries two premises as fields: quorum
    intersection and "at most one parent". To test them, this file states
    the Casper definitions over a setting without those fields
    ([nec_w_pre]); for a repository setting, the definitions here are
    implied by the repository's ([nec_w_fork_of_repo]) and give back its
    conclusion ([nec_w_accountable_safety_repo]).

    - At most one parent is not needed: accountable safety holds under
      quorum intersection alone. Two finalized blocks at one epoch are two
      justified blocks at one epoch, which already expose a double vote.
    - Quorum intersection is needed, and the thresholds of the three-
      validator instance are tight: lowering the first class to one third
      gives a fork with nobody slashed; raising the second class to two
      thirds gives a fork with no slashed set in that class (only B is
      slashed). In both, quorum intersection fails. *)

(* SCOPE NOTE: standalone proof scope. Accountable safety is stated over
   validator sets, quorums and votes of the Casper model; no machine is
   fixed. *)

From Coq Require Import Arith.PeanoNat Lia Relations List.
Import ListNotations.
From Kernel Require Import CasperFFG CasperRecordReading CasperForkWitness.

(** A setting without the two premise fields. *)
Record nec_w_pre : Type := {
  pv : Type;
  ph : Type;
  pq1 : (pv -> Prop) -> Prop;
  pq2 : (pv -> Prop) -> Prop;
  pparent : ph -> ph -> Prop;
  pgenesis : ph
}.

Definition nec_w_qi (P : nec_w_pre) : Prop :=
  forall q1 q2, pq1 P q1 -> pq1 P q2 ->
    exists q3, pq2 P q3 /\ (forall n, q3 n -> q1 n) /\ (forall n, q3 n -> q2 n).

Section Pre.

Variable P : nec_w_pre.
Variable vote : pv P -> ph P -> nat -> nat -> bool.

Definition nec_w_anc (h1 h2 : ph P) : Prop := clos_refl_trans_1n _ (pparent P) h1 h2.

Lemma nec_w_anc_base : forall h1 h2, pparent P h1 h2 -> nec_w_anc h1 h2.
Proof. intros h1 h2 H. econstructor; [exact H | constructor]. Qed.

Lemma nec_w_anc_concat : forall h1 h2 h3,
  nec_w_anc h2 h3 -> nec_w_anc h1 h2 -> nec_w_anc h1 h3.
Proof.
  intros h1 h2 h3 H23 H12. induction H12 as [| x y z Hxy _ IH]; [exact H23 |].
  econstructor; [exact Hxy | exact (IH H23)].
Qed.

Lemma nec_w_anc_other : forall h1 h2 p,
  nec_w_anc h1 h2 -> ~ nec_w_anc p h2 -> ~ nec_w_anc p h1.
Proof. intros h1 h2 p H12 Hp2 Hp1. apply Hp2. exact (nec_w_anc_concat _ _ _ H12 Hp1). Qed.

Inductive nec_w_nth : nat -> ph P -> ph P -> Prop :=
| nec_w_nth0 : forall h, nec_w_nth 0 h h
| nec_w_nthS : forall n h1 h2 h3, nec_w_nth n h1 h2 -> pparent P h2 h3 -> nec_w_nth (S n) h1 h3.

Lemma nec_w_nth_anc : forall n h1 h2, nec_w_nth n h1 h2 -> nec_w_anc h1 h2.
Proof.
  intros n h1 h2 H. induction H as [h | n h1 h2 h3 _ IH Hp]; [constructor |].
  exact (nec_w_anc_concat _ _ _ (nec_w_anc_base _ _ Hp) IH).
Qed.

Definition nec_w_link (q : pv P -> Prop) (parent : ph P) (pre : nat) (new : ph P) (now : nat) : Prop :=
  pq1 P q /\ (forall n, q n -> vote n new now pre = true) /\
  nec_w_nth (now - pre) parent new /\ now > pre.

Inductive nec_w_just : ph P -> nat -> Prop :=
| nec_w_orig : nec_w_just (pgenesis P) 0
| nec_w_follow : forall parent pre q new now,
    nec_w_just parent pre -> nec_w_link q parent pre new now -> nec_w_just new now.

Definition nec_w_fin (q : pv P -> Prop) (h : ph P) (v : nat) (child : ph P) : Prop :=
  pparent P h child /\ nec_w_just h v /\ nec_w_link q h v child (S v).

Definition nec_w_fork : Prop :=
  exists h1 h2 q1 q2 v1 v2 c1 c2,
    nec_w_fin q1 h1 v1 c1 /\ nec_w_fin q2 h2 v2 c2 /\
    ~ nec_w_anc h2 h1 /\ ~ nec_w_anc h1 h2 /\ h1 <> h2.

Definition nec_w_slashed (n : pv P) : Prop :=
  (exists h1 h2, h1 <> h2 /\ exists v s1 s2, vote n h1 v s1 = true /\ vote n h2 v s2 = true) \/
  (exists h1 h2 v1 v2 s1 s2, vote n h1 v1 s1 = true /\ vote n h2 v2 s2 = true /\ v1 > v2 /\ s2 > s1).

Definition nec_w_qslashed : Prop :=
  exists q, pq2 P q /\ forall n, q n -> nec_w_slashed n.

Lemma nec_w_link_epochs : forall q h2 v2 h1 v1, nec_w_link q h2 v2 h1 v1 -> v1 > v2.
Proof. intros q h2 v2 h1 v1 [_ [_ [_ H]]]. exact H. Qed.

Lemma nec_w_link_anc : forall q parent pre new now,
  nec_w_link q parent pre new now -> nec_w_anc parent new.
Proof. intros q parent pre new now [_ [_ [Hn _]]]. exact (nec_w_nth_anc _ _ _ Hn). Qed.

(** A voter whose only votes are one link at epoch 1 from source 0 and one
    at epoch 2 from source 1 is not slashed. *)
Lemma nec_w_two_link_not_slashed : forall n hx hy,
  (forall h t src, vote n h t src = true ->
     (h = hx /\ t = 1 /\ src = 0) \/ (h = hy /\ t = 2 /\ src = 1)) ->
  ~ nec_w_slashed n.
Proof.
  intros n hx hy Hv
    [[h1 [h2 [Hne [v [s1 [s2 [H1 H2]]]]]]] |
     [h1 [h2 [v1 [v2 [s1 [s2 [H1 [H2 [Hlt Hlt']]]]]]]]]].
  - apply Hv in H1. apply Hv in H2.
    destruct H1 as [[-> [-> ->]] | [-> [-> ->]]];
      destruct H2 as [[-> [? ->]] | [-> [? ->]]]; try lia; apply Hne; reflexivity.
  - apply Hv in H1. apply Hv in H2.
    destruct H1 as [[-> [-> ->]] | [-> [-> ->]]];
      destruct H2 as [[-> [-> ->]] | [-> [-> ->]]]; lia.
Qed.

Section WithQI.

Variable QI : nec_w_qi P.

Lemma nec_w_both_votes : forall (q1 q2 : pv P -> Prop) (P1 P2 : pv P -> Prop),
  pq1 P q1 -> pq1 P q2 ->
  (forall n, q1 n -> P1 n) -> (forall n, q2 n -> P2 n) ->
  exists q, pq2 P q /\ forall n, q n -> P1 n /\ P2 n.
Proof.
  intros q1 q2 P1 P2 Hq1 Hq2 H1 H2.
  destruct (QI q1 q2 Hq1 Hq2) as [q [Hq [Hin1 Hin2]]].
  exists q. split; [exact Hq |]. intros n Hn. split; [apply H1, Hin1 | apply H2, Hin2]; exact Hn.
Qed.

Lemma nec_w_dbl_vote_case : forall q1 q2 h2 v2 h1 h3 v3 c3,
  nec_w_link q1 h2 v2 h1 (S v3) -> nec_w_fin q2 h3 v3 c3 -> ~ nec_w_anc h3 h1 ->
  nec_w_qslashed.
Proof.
  intros q1 q2 h2 v2 h1 h3 v3 c3 [Hq1 [Hv1 _]] [Hp [_ [Hq2 [Hv2 _]]]] Hh.
  destruct (nec_w_both_votes q1 q2 _ _ Hq1 Hq2 Hv1 Hv2) as [q [Hq Hboth]].
  exists q. split; [exact Hq |]. intros n Hn. left.
  destruct (Hboth n Hn) as [Ha Hb].
  exists h1, c3. split.
  - intros ->. apply Hh. exact (nec_w_anc_base _ _ Hp).
  - exists (S v3), v2, v3. split; assumption.
Qed.

Lemma nec_w_surround_case : forall q1 q2 h2 v2 h1 v1 h3 v3 c3,
  nec_w_link q1 h2 v2 h1 v1 -> nec_w_fin q2 h3 v3 c3 -> S v3 < v1 -> v2 < v3 ->
  nec_w_qslashed.
Proof.
  intros q1 q2 h2 v2 h1 v1 h3 v3 c3 [Hq1 [Hv1 _]] [_ [_ [Hq2 [Hv2 _]]]] Hlt Hlt'.
  destruct (nec_w_both_votes q1 q2 _ _ Hq1 Hq2 Hv1 Hv2) as [q [Hq Hboth]].
  exists q. split; [exact Hq |]. intros n Hn. right.
  destruct (Hboth n Hn) as [Ha Hb].
  exists h1, c3, v1, (S v3), v2, v3. repeat split; assumption.
Qed.

Lemma nec_w_crossing_link : forall q1 q2 h2 v2 h1 h3 v1 v3 c3,
  nec_w_link q1 h2 v2 h1 v1 -> nec_w_fin q2 h3 v3 c3 -> v1 > v3 ->
  ~ nec_w_anc h3 h1 -> v2 < v3 -> nec_w_qslashed.
Proof.
  intros q1 q2 h2 v2 h1 h3 v1 v3 c3 Hj Hf Hv Hh Hv'.
  destruct (Nat.eq_dec v1 (S v3)) as [-> | Hne].
  - exact (nec_w_dbl_vote_case q1 q2 h2 v2 h1 h3 v3 c3 Hj Hf Hh).
  - apply (nec_w_surround_case q1 q2 h2 v2 h1 v1 h3 v3 c3 Hj Hf); lia.
Qed.

Lemma nec_w_same_epoch_distinct : forall q q1 parent1 pre1 h1 v1 parent pre new now,
  nec_w_link q parent pre new now -> nec_w_link q1 parent1 pre1 h1 v1 ->
  now = v1 -> h1 <> new -> nec_w_qslashed.
Proof.
  intros q q1 parent1 pre1 h1 v1 parent pre new now [Hq [Hv _]] [Hq1 [Hv1 _]] -> Hne.
  destruct (nec_w_both_votes q q1 _ _ Hq Hq1 Hv Hv1) as [q2 [Hq2 Hboth]].
  exists q2. split; [exact Hq2 |]. intros n Hn. left.
  destruct (Hboth n Hn) as [Ha Hb].
  exists new, h1. split; [intro H; apply Hne; symmetry; exact H |].
  exists v1, pre, pre1. split; assumption.
Qed.

Lemma nec_w_distinct_justified_same_epoch : forall h1 h2 v,
  nec_w_just h1 v -> nec_w_just h2 v -> h1 <> h2 -> nec_w_qslashed.
Proof.
  intros h1 h2 v Hj1 Hj2 Hneq.
  inversion Hj1 as [| parent1 pre1 q1 new1 now1 Hjp1 Hlink1]; subst;
    inversion Hj2 as [| parent2 pre2 q2 new2 now2 Hjp2 Hlink2]; subst.
  - exfalso. apply Hneq. reflexivity.
  - pose proof (nec_w_link_epochs _ _ _ _ _ Hlink2). lia.
  - pose proof (nec_w_link_epochs _ _ _ _ _ Hlink1). lia.
  - exact (nec_w_same_epoch_distinct _ _ _ _ _ _ _ _ _ _ Hlink1 Hlink2 eq_refl
      (fun Heq => Hneq (eq_sym Heq))).
Qed.

Lemma nec_w_non_equal_case_ind : forall q2 h2 v2 xa,
  nec_w_fin q2 h2 v2 xa ->
  forall k v1 h1, v1 - v2 = k -> nec_w_just h1 v1 -> ~ nec_w_anc h2 h1 ->
  h1 <> h2 -> v1 > v2 -> nec_w_qslashed.
Proof.
  intros q2 h2 v2 xa Hf k.
  induction k as [k IH] using (well_founded_induction Wf_nat.lt_wf).
  intros v1 h1 Hk Hj Hh Hh' Hv.
  destruct Hj as [| parent pre q new now Hjp Hlink]; [lia |].
  assert (Hp : ~ nec_w_anc h2 parent)
    by exact (nec_w_anc_other _ _ _ (nec_w_link_anc _ _ _ _ _ Hlink) Hh).
  assert (Hpe : parent <> h2) by (intros ->; apply Hp; constructor).
  pose proof (nec_w_link_epochs _ _ _ _ _ Hlink) as Hpre.
  destruct (Nat.lt_trichotomy v2 pre) as [Hlt | [Heq | Hgt]].
  - apply (IH (pre - v2)) with (v1 := pre) (h1 := parent); try assumption; lia.
  - subst pre. exact (nec_w_distinct_justified_same_epoch _ _ _ Hjp (proj1 (proj2 Hf)) Hpe).
  - exact (nec_w_crossing_link _ _ _ _ _ _ _ _ _ Hlink Hf Hv Hh Hgt).
Qed.

(** Accountable safety under quorum intersection alone. *)
Theorem nec_w_accountable_safety_no_parent_premise : nec_w_fork -> nec_w_qslashed.
Proof.
  intros [h1 [h2 [q1 [q2 [v1 [v2 [c1 [c2 [Hf1 [Hf2 [Hh [Hh' Hn]]]]]]]]]]]].
  destruct (Nat.lt_trichotomy v1 v2) as [Hlt | [-> | Hgt]].
  - exact (nec_w_non_equal_case_ind q1 h1 v1 c1 Hf1 (v2 - v1) v2 h2 eq_refl
             (proj1 (proj2 Hf2)) Hh' (fun E => Hn (eq_sym E)) Hlt).
  - exact (nec_w_distinct_justified_same_epoch h1 h2 v2 (proj1 (proj2 Hf1)) (proj1 (proj2 Hf2)) Hn).
  - exact (nec_w_non_equal_case_ind q2 h2 v2 c2 Hf2 (v1 - v2) v1 h1 eq_refl
             (proj1 (proj2 Hf1)) Hh Hn Hgt).
Qed.

End WithQI.

End Pre.

(* ================================================================= *)
(** * The repository's theorem is a corollary                         *)
(* ================================================================= *)

Definition nec_w_forget (C : CasperSetting) : nec_w_pre := {|
  pv := Validator C; ph := Hash C; pq1 := quorum_1 C; pq2 := quorum_2 C;
  pparent := hash_parent C; pgenesis := genesis C
|}.

Lemma nec_w_nth_of_repo : forall C n h1 h2,
  nth_ancestor C n h1 h2 -> nec_w_nth (nec_w_forget C) n h1 h2.
Proof.
  intros C n h1 h2 H. induction H as [h | n h1 h2 h3 _ IH Hp].
  - apply nec_w_nth0.
  - exact (nec_w_nthS (nec_w_forget C) n h1 h2 h3 IH Hp).
Qed.

Lemma nec_w_link_of_repo : forall C s q parent pre new now,
  justified_link C s q parent pre new now ->
  nec_w_link (nec_w_forget C) (vote_msg C s) q parent pre new now.
Proof.
  intros C s q parent pre new now [Hq [Hv [Hn Ht]]].
  split; [exact Hq | split; [exact Hv | split; [apply nec_w_nth_of_repo; exact Hn | exact Ht]]].
Qed.

Lemma nec_w_just_of_repo : forall C s h v,
  justified C s h v -> nec_w_just (nec_w_forget C) (vote_msg C s) h v.
Proof.
  intros C s h v H. induction H as [s | s parent pre q new now _ IH Hl].
  - apply nec_w_orig.
  - exact (nec_w_follow (nec_w_forget C) (vote_msg C s) parent pre q new now IH (nec_w_link_of_repo C s q parent pre new now Hl)).
Qed.

Lemma nec_w_fork_of_repo : forall C s,
  finalization_fork C s -> nec_w_fork (nec_w_forget C) (vote_msg C s).
Proof.
  intros C s [h1 [h2 [q1 [q2 [v1 [v2 [c1 [c2 [[Hp1 [Hj1 Hl1]] [[Hp2 [Hj2 Hl2]] [Hh [Hh' Hn]]]]]]]]]]]].
  exists h1, h2, q1, q2, v1, v2, c1, c2.
  split; [split; [exact Hp1 | split; [apply nec_w_just_of_repo; exact Hj1 | apply nec_w_link_of_repo; exact Hl1]] |].
  split; [split; [exact Hp2 | split; [apply nec_w_just_of_repo; exact Hj2 | apply nec_w_link_of_repo; exact Hl2]] |].
  split; [exact Hh | split; [exact Hh' | exact Hn]].
Qed.

Corollary nec_w_accountable_safety_repo :
  forall C s, finalization_fork C s -> quorum_slashed C s.
Proof.
  intros C s Hf.
  destruct (nec_w_accountable_safety_no_parent_premise (nec_w_forget C) (vote_msg C s)
              (quorums_intersection C) (nec_w_fork_of_repo C s Hf)) as [q [Hq Hs]].
  exists q. split; [exact Hq |]. intros n Hn. exact (Hs n Hn).
Qed.

(* ================================================================= *)
(** * Quorum intersection is needed; the thresholds are tight         *)
(* ================================================================= *)

(** The three-validator tree of [CasperForkWitness] with both classes set
    at one third of the stake. *)
Definition nec_w_third_setting : nec_w_pre := {|
  pv := FV; ph := FH; pq1 := fork_quorum_2; pq2 := fork_quorum_2;
  pparent := fork_parent; pgenesis := HG
|}.

(** A votes the first branch, C the second, B nothing. *)
Definition nec_w_split_vote (n : FV) (h : FH) (t src : nat) : bool :=
  match n with
  | VB => false
  | _ => fork_vote n h t src
  end.

Definition nec_w_only_a (n : FV) : Prop := n = VA.
Definition nec_w_only_c (n : FV) : Prop := n = VC.

Lemma nec_w_only_a_third : fork_quorum_2 nec_w_only_a.
Proof.
  exists [VA]. split; [repeat constructor; simpl; tauto |].
  split; [intros n [<- | []]; reflexivity | unfold total_stake; simpl; lia].
Qed.

Lemma nec_w_only_c_third : fork_quorum_2 nec_w_only_c.
Proof.
  exists [VC]. split; [repeat constructor; simpl; tauto |].
  split; [intros n [<- | []]; reflexivity | unfold total_stake; simpl; lia].
Qed.

Lemma nec_w_third_nonempty : forall q, fork_quorum_2 q -> exists n, q n.
Proof.
  intros q [[| x l] [_ [Hin Hw]]].
  - unfold total_stake in Hw. simpl in Hw. lia.
  - exists x. apply Hin. left. reflexivity.
Qed.

Theorem nec_w_casper_first_class_one_third :
  nec_w_fork nec_w_third_setting nec_w_split_vote /\
  ~ nec_w_qslashed nec_w_third_setting nec_w_split_vote /\
  ~ nec_w_qi nec_w_third_setting.
Proof.
  split; [| split].
  - exists HA1, HB1, nec_w_only_a, nec_w_only_c, 1, 1, HA2, HB2.
    split; [| split; [| split; [exact b1_not_ancestor_a1 | split; [exact a1_not_ancestor_b1 | discriminate]]]].
    + split; [reflexivity |]. split.
      * apply (nec_w_follow nec_w_third_setting nec_w_split_vote HG 0 nec_w_only_a HA1 1);
          [constructor |].
        split; [exact nec_w_only_a_third |]. split; [intros n ->; reflexivity |].
        split; [| lia]. apply (nec_w_nthS nec_w_third_setting 0 HG HG HA1); [constructor | reflexivity].
      * split; [exact nec_w_only_a_third |]. split; [intros n ->; reflexivity |].
        split; [| lia]. apply (nec_w_nthS nec_w_third_setting 0 HA1 HA1 HA2); [constructor | reflexivity].
    + split; [reflexivity |]. split.
      * apply (nec_w_follow nec_w_third_setting nec_w_split_vote HG 0 nec_w_only_c HB1 1);
          [constructor |].
        split; [exact nec_w_only_c_third |]. split; [intros n ->; reflexivity |].
        split; [| lia]. apply (nec_w_nthS nec_w_third_setting 0 HG HG HB1); [constructor | reflexivity].
      * split; [exact nec_w_only_c_third |]. split; [intros n ->; reflexivity |].
        split; [| lia]. apply (nec_w_nthS nec_w_third_setting 0 HB1 HB1 HB2); [constructor | reflexivity].
  - intros [q [Hq Hs]]. destruct (nec_w_third_nonempty q Hq) as [n Hn].
    specialize (Hs n Hn). destruct n.
    + exact (nec_w_two_link_not_slashed nec_w_third_setting nec_w_split_vote VA HA1 HA2 vote_va Hs).
    + destruct Hs as [[h1 [h2 [_ [v [s1 [s2 [H1 _]]]]]]] | [h1 [h2 [v1 [v2 [s1 [s2 [H1 _]]]]]]]];
        discriminate.
    + exact (nec_w_two_link_not_slashed nec_w_third_setting nec_w_split_vote VC HB1 HB2 vote_vc Hs).
  - intros Hqi. destruct (Hqi nec_w_only_a nec_w_only_c nec_w_only_a_third nec_w_only_c_third)
      as [q [Hq [Ha Hc]]].
    destruct (nec_w_third_nonempty q Hq) as [n Hn].
    pose proof (Ha n Hn) as E1. pose proof (Hc n Hn) as E2.
    unfold nec_w_only_a, nec_w_only_c in *. congruence.
Qed.

(** The repository's instance with the second class raised to two thirds. *)
Definition nec_w_two_thirds_setting : nec_w_pre := {|
  pv := FV; ph := FH; pq1 := fork_quorum_1; pq2 := fork_quorum_1;
  pparent := fork_parent; pgenesis := HG
|}.

Lemma nec_w_vote_vb_slashed_only : forall n,
  nec_w_slashed nec_w_two_thirds_setting fork_vote n -> n = VB.
Proof.
  intros [] H; [| reflexivity |].
  - exfalso. exact (nec_w_two_link_not_slashed nec_w_two_thirds_setting fork_vote VA HA1 HA2 vote_va H).
  - exfalso. exact (nec_w_two_link_not_slashed nec_w_two_thirds_setting fork_vote VC HB1 HB2 vote_vc H).
Qed.

Lemma nec_w_two_thirds_two_members : forall q, fork_quorum_1 q ->
  exists a b, a <> b /\ q a /\ q b.
Proof.
  intros q [[| a [| b l]] [Hnd [Hin Hw]]]; unfold total_stake in Hw; simpl in Hw; try lia.
  exists a, b. split; [| split; apply Hin; simpl; auto].
  intros ->. inversion Hnd as [| ? ? Hn _]. apply Hn. left. reflexivity.
Qed.

Theorem nec_w_casper_second_class_two_thirds :
  nec_w_fork nec_w_two_thirds_setting fork_vote /\
  ~ nec_w_qslashed nec_w_two_thirds_setting fork_vote /\
  ~ nec_w_qi nec_w_two_thirds_setting.
Proof.
  split; [| split].
  - exists HA1, HB1, q_branch_a, q_branch_b, 1, 1, HA2, HB2.
    split; [| split; [| split; [exact b1_not_ancestor_a1 | split; [exact a1_not_ancestor_b1 | discriminate]]]].
    + split; [reflexivity |]. split.
      * apply (nec_w_follow nec_w_two_thirds_setting fork_vote HG 0 q_branch_a HA1 1); [constructor |].
        split; [exact q_branch_a_quorum |]. split; [intros n [-> | ->]; reflexivity |].
        split; [| lia]. apply (nec_w_nthS nec_w_two_thirds_setting 0 HG HG HA1); [constructor | reflexivity].
      * split; [exact q_branch_a_quorum |]. split; [intros n [-> | ->]; reflexivity |].
        split; [| lia]. apply (nec_w_nthS nec_w_two_thirds_setting 0 HA1 HA1 HA2); [constructor | reflexivity].
    + split; [reflexivity |]. split.
      * apply (nec_w_follow nec_w_two_thirds_setting fork_vote HG 0 q_branch_b HB1 1); [constructor |].
        split; [exact q_branch_b_quorum |]. split; [intros n [-> | ->]; reflexivity |].
        split; [| lia]. apply (nec_w_nthS nec_w_two_thirds_setting 0 HG HG HB1); [constructor | reflexivity].
      * split; [exact q_branch_b_quorum |]. split; [intros n [-> | ->]; reflexivity |].
        split; [| lia]. apply (nec_w_nthS nec_w_two_thirds_setting 0 HB1 HB1 HB2); [constructor | reflexivity].
  - intros [q [Hq Hs]]. destruct (nec_w_two_thirds_two_members q Hq) as [a [b [Hab [Ha Hb]]]].
    apply Hab. rewrite (nec_w_vote_vb_slashed_only a (Hs a Ha)), (nec_w_vote_vb_slashed_only b (Hs b Hb)).
    reflexivity.
  - intros Hqi. destruct (Hqi q_branch_a q_branch_b q_branch_a_quorum q_branch_b_quorum)
      as [q [Hq [Ha Hb]]].
    destruct (nec_w_two_thirds_two_members q Hq) as [x [y [Hxy [Hx Hy]]]].
    assert (Hvb : forall n, q n -> n = VB).
    { intros n Hn. specialize (Ha n Hn). specialize (Hb n Hn).
      unfold q_branch_a, q_branch_b in Ha, Hb.
      destruct Ha as [-> | ->]; destruct Hb as [E | E]; congruence. }
    apply Hxy. rewrite (Hvb x Hx), (Hvb y Hy). reflexivity.
Qed.

Print Assumptions nec_w_accountable_safety_no_parent_premise.
Print Assumptions nec_w_accountable_safety_repo.
Print Assumptions nec_w_casper_first_class_one_third.
Print Assumptions nec_w_casper_second_class_two_thirds.
