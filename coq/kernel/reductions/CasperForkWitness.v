(** CasperForkWitness: a concrete Casper FFG fork, so the premise of
    accountable safety is inhabited.

    [accountable_safety] (CasperFFG) and [conflicting_records_are_priced]
    (CasperRecordReading) both assume two finalized blocks on conflicting
    branches. This file builds a finite instance in which that premise
    holds, and checks the conclusion on it.

    The instance:
    - three validators [VA], [VB], [VC], each with stake 1 (total 3);
    - the "2/3" class [quorum_1] holds of a predicate containing a
      duplicate-free list of validators with 3 * stake >= 2 * total, and
      the "1/3" class [quorum_2] of one with 3 * stake >= total;
    - a block tree with two branches from genesis,
      [HG -> HA1 -> HA2] and [HG -> HB1 -> HB2];
    - votes: [VA] and [VB] justify [HA1] at epoch 1 and finalize it with a
      link to [HA2] at epoch 2; [VB] and [VC] do the same on the other
      branch with [HB1] and [HB2]. Validator [VB] votes on both branches.

    Results:
    - [casper_fork_exists]: [HA1] and [HB1] are both finalized, neither is
      an ancestor of the other, they are distinct, and so the premises of
      [accountable_safety] and of [conflicting_records_are_priced] hold.
    - [casper_fork_slashable]: [accountable_safety] applies to the
      instance, and the concrete set [{VB}] is in the "1/3" class (checked
      by computation), every member is slashed (a double vote at epoch 1),
      and the two other validators are not slashed. *)

(* SCOPE NOTE: standalone proof scope. The Casper model is an abstract
   protocol model with no machine semantics, and this file only instantiates it. *)

From Coq Require Import Arith.PeanoNat Lia Relations List.
From Kernel Require Import CasperFFG CasperRecordReading.
Import ListNotations.

(** * Validators and stake *)

Inductive FV : Type := VA | VB | VC.

Definition fv_eq_dec : forall x y : FV, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition all_validators : list FV := [VA; VB; VC].

Lemma all_validators_complete : forall x, In x all_validators.
Proof. intros []; simpl; auto. Qed.

(** Every validator has stake 1. *)
Definition stake (_ : FV) : nat := 1.

Fixpoint weight (l : list FV) : nat :=
  match l with
  | [] => 0
  | x :: t => stake x + weight t
  end.

Definition total_stake : nat := weight all_validators.

Lemma weight_length : forall l, weight l = length l.
Proof. induction l as [| x t IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(** "2/3" of the stake or more, and "1/3" of the stake or more. *)
Definition fork_quorum_1 (q : FV -> Prop) : Prop :=
  exists l, NoDup l /\ (forall n, In n l -> q n) /\ 3 * weight l >= 2 * total_stake.

Definition fork_quorum_2 (q : FV -> Prop) : Prop :=
  exists l, NoDup l /\ (forall n, In n l -> q n) /\ 3 * weight l >= total_stake.

Lemma nodup_app_disjoint : forall (l1 l2 : list FV),
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [| a t IH]; intros l2 H1 H2 Hd; simpl; [exact H2 |].
  inversion H1 as [| a' t' Hna Ht]; subst.
  constructor.
  - intros Hin. apply in_app_or in Hin as [Hin | Hin].
    + exact (Hna Hin).
    + exact (Hd a (or_introl eq_refl) Hin).
  - apply IH; [exact Ht | exact H2 |].
    intros x Hx. apply Hd. right. exact Hx.
Qed.

(** Two duplicate-free lists of at least two validators each share a
    validator, since three validators cannot hold four distinct entries. *)
Lemma two_thirds_lists_meet : forall l1 l2 : list FV,
  NoDup l1 -> NoDup l2 -> 2 <= length l1 -> 2 <= length l2 ->
  exists x, In x l1 /\ In x l2.
Proof.
  intros l1 l2 H1 H2 Hlen1 Hlen2.
  destruct (Exists_dec (fun x : FV => In x l2) l1 (fun x : FV => in_dec fv_eq_dec x l2))
    as [Hex | Hnex].
  - apply Exists_exists in Hex. exact Hex.
  - exfalso.
    assert (Hd : forall x, In x l1 -> ~ In x l2).
    { intros x Hx Hx2. apply Hnex. apply Exists_exists. exists x. split; assumption. }
    pose proof (nodup_app_disjoint l1 l2 H1 H2 Hd) as Hnd.
    pose proof (NoDup_incl_length Hnd (fun x _ => all_validators_complete x)) as Hle.
    rewrite app_length in Hle. simpl in Hle. lia.
Qed.

Lemma fork_quorums_intersection : forall q1 q2,
  fork_quorum_1 q1 -> fork_quorum_1 q2 ->
  exists q3, fork_quorum_2 q3 /\ (forall n, q3 n -> q1 n) /\ (forall n, q3 n -> q2 n).
Proof.
  intros q1 q2 [l1 [Hnd1 [Hin1 Hw1]]] [l2 [Hnd2 [Hin2 Hw2]]].
  rewrite weight_length in Hw1, Hw2. unfold total_stake in Hw1, Hw2. simpl in Hw1, Hw2.
  destruct (two_thirds_lists_meet l1 l2 Hnd1 Hnd2 ltac:(lia) ltac:(lia))
    as [x [Hx1 Hx2]].
  exists (fun n => q1 n /\ q2 n). split; [| split; intros n Hn; apply Hn].
  exists [x]. split; [repeat constructor; simpl; tauto |]. split.
  - intros n [<- | []]. split; [apply Hin1 | apply Hin2]; assumption.
  - unfold total_stake. simpl. lia.
Qed.

(** * The block tree *)

Inductive FH : Type := HG | HA1 | HA2 | HB1 | HB2.

Definition parent_of (h : FH) : option FH :=
  match h with
  | HG => None
  | HA1 => Some HG
  | HA2 => Some HA1
  | HB1 => Some HG
  | HB2 => Some HB1
  end.

(** [fork_parent h1 h2]: h1 is the parent of h2. *)
Definition fork_parent (h1 h2 : FH) : Prop := parent_of h2 = Some h1.

Lemma fork_at_most_one_parent : forall h1 h2 h3,
  fork_parent h2 h1 -> fork_parent h3 h1 -> h2 = h3.
Proof.
  unfold fork_parent. intros h1 h2 h3 H2 H3. rewrite H2 in H3.
  injection H3 as H. exact H.
Qed.

(** * The setting *)

Definition fork_setting : CasperSetting := {|
  Validator := FV;
  Hash := FH;
  quorum_1 := fork_quorum_1;
  quorum_2 := fork_quorum_2;
  quorums_intersection := fork_quorums_intersection;
  hash_parent := fork_parent;
  genesis := HG;
  hash_at_most_one_parent := fork_at_most_one_parent
|}.

(** Each block's ancestors, listed by hand from the tree. *)
Definition ancestors (h : FH) : list FH :=
  match h with
  | HG => [HG]
  | HA1 => [HA1; HG]
  | HA2 => [HA2; HA1; HG]
  | HB1 => [HB1; HG]
  | HB2 => [HB2; HB1; HG]
  end.

Lemma ancestors_parent_closed : forall x y z,
  fork_parent x y -> In y (ancestors z) -> In x (ancestors z).
Proof.
  unfold fork_parent. intros x y z Hp Hin.
  destruct x, y, z; simpl in Hp, Hin |- *; try discriminate; intuition congruence.
Qed.

Lemma hash_ancestor_in : forall x y,
  hash_ancestor fork_setting x y -> In x (ancestors y).
Proof.
  intros x y H. induction H as [y | x w y Hp _ IH].
  - destruct y; simpl; tauto.
  - exact (ancestors_parent_closed x w y Hp IH).
Qed.

(** * The votes *)

(** [fork_vote n h t src]: validator n voted for target h at epoch t with
    source epoch src. *)
Definition fork_vote (n : FV) (h : FH) (t src : nat) : bool :=
  match n, h, t, src with
  | VA, HA1, 1, 0 => true
  | VA, HA2, 2, 1 => true
  | VB, HA1, 1, 0 => true
  | VB, HA2, 2, 1 => true
  | VB, HB1, 1, 0 => true
  | VB, HB2, 2, 1 => true
  | VC, HB1, 1, 0 => true
  | VC, HB2, 2, 1 => true
  | _, _, _, _ => false
  end.

Definition fork_state : State fork_setting := mkSt fork_setting fork_vote.

(** The quorum on each branch. *)
Definition q_branch_a (n : FV) : Prop := n = VA \/ n = VB.
Definition q_branch_b (n : FV) : Prop := n = VB \/ n = VC.

Lemma q_branch_a_quorum : quorum_1 fork_setting q_branch_a.
Proof.
  exists [VA; VB]. split; [repeat constructor; simpl; intuition discriminate |].
  split; [intros n [<- | [<- | []]]; unfold q_branch_a; auto |].
  unfold total_stake. simpl. lia.
Qed.

Lemma q_branch_b_quorum : quorum_1 fork_setting q_branch_b.
Proof.
  exists [VB; VC]. split; [repeat constructor; simpl; intuition discriminate |].
  split; [intros n [<- | [<- | []]]; unfold q_branch_b; auto |].
  unfold total_stake. simpl. lia.
Qed.

Lemma one_step : forall h1 h2, fork_parent h1 h2 -> nth_ancestor fork_setting 1 h1 h2.
Proof.
  intros h1 h2 Hp. exact (nth_ancestor_nth fork_setting 0 h1 h1 h2
    (nth_ancestor_0 fork_setting h1) Hp).
Qed.

Lemma finalized_a : finalized fork_setting fork_state q_branch_a HA1 1 HA2.
Proof.
  split; [reflexivity |]. split.
  - apply (follow fork_setting fork_state HG 0 q_branch_a HA1 1).
    + constructor.
    + split; [exact q_branch_a_quorum |].
      split; [intros n [-> | ->]; reflexivity |].
      split; [apply one_step; reflexivity | lia].
  - split; [exact q_branch_a_quorum |].
    split; [intros n [-> | ->]; reflexivity |].
    split; [apply one_step; reflexivity | lia].
Qed.

Lemma finalized_b : finalized fork_setting fork_state q_branch_b HB1 1 HB2.
Proof.
  split; [reflexivity |]. split.
  - apply (follow fork_setting fork_state HG 0 q_branch_b HB1 1).
    + constructor.
    + split; [exact q_branch_b_quorum |].
      split; [intros n [-> | ->]; reflexivity |].
      split; [apply one_step; reflexivity | lia].
  - split; [exact q_branch_b_quorum |].
    split; [intros n [-> | ->]; reflexivity |].
    split; [apply one_step; reflexivity | lia].
Qed.

Lemma b1_not_ancestor_a1 : ~ hash_ancestor fork_setting HB1 HA1.
Proof.
  intros H. apply hash_ancestor_in in H. simpl in H. intuition discriminate.
Qed.

Lemma a1_not_ancestor_b1 : ~ hash_ancestor fork_setting HA1 HB1.
Proof.
  intros H. apply hash_ancestor_in in H. simpl in H. intuition discriminate.
Qed.

(** * The premise of accountable safety holds *)

Theorem casper_fork_exists :
  finalized fork_setting fork_state q_branch_a HA1 1 HA2 /\
  finalized fork_setting fork_state q_branch_b HB1 1 HB2 /\
  ~ hash_ancestor fork_setting HB1 HA1 /\
  ~ hash_ancestor fork_setting HA1 HB1 /\
  HA1 <> HB1 /\
  finalization_fork fork_setting fork_state /\
  finalized_record fork_setting fork_state HA1 /\
  finalized_record fork_setting fork_state HB1.
Proof.
  assert (Hne : HA1 <> HB1) by discriminate.
  split; [exact finalized_a |]. split; [exact finalized_b |].
  split; [exact b1_not_ancestor_a1 |]. split; [exact a1_not_ancestor_b1 |].
  split; [exact Hne |]. split.
  - exists HA1, HB1, q_branch_a, q_branch_b, 1, 1, HA2, HB2.
    exact (conj finalized_a (conj finalized_b
      (conj b1_not_ancestor_a1 (conj a1_not_ancestor_b1 Hne)))).
  - split; [exists q_branch_a, 1, HA2; exact finalized_a |
            exists q_branch_b, 1, HB2; exact finalized_b].
Qed.

(** * The conclusion, by the theorem and by a concrete set *)

(** The slashable set: the validator who voted on both branches. *)
Definition slashers (n : FV) : Prop := n = VB.

Lemma vote_va : forall h t src, fork_vote VA h t src = true ->
  (h = HA1 /\ t = 1 /\ src = 0) \/ (h = HA2 /\ t = 2 /\ src = 1).
Proof.
  intros h t src H.
  destruct h; destruct t as [| [| [| t]]]; destruct src as [| [| src]];
    simpl in H; try discriminate; auto.
Qed.

Lemma vote_vc : forall h t src, fork_vote VC h t src = true ->
  (h = HB1 /\ t = 1 /\ src = 0) \/ (h = HB2 /\ t = 2 /\ src = 1).
Proof.
  intros h t src H.
  destruct h; destruct t as [| [| [| t]]]; destruct src as [| [| src]];
    simpl in H; try discriminate; auto.
Qed.

(** A validator whose only votes are one link at epoch 1 from source 0 and
    one at epoch 2 from source 1 is not slashed. *)
Lemma two_link_voter_not_slashed : forall n hx hy,
  (forall h t src, fork_vote n h t src = true ->
     (h = hx /\ t = 1 /\ src = 0) \/ (h = hy /\ t = 2 /\ src = 1)) ->
  ~ slashed fork_setting fork_state n.
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

Theorem casper_fork_slashable :
  quorum_slashed fork_setting fork_state /\
  quorum_2 fork_setting slashers /\
  (forall n, slashers n -> slashed fork_setting fork_state n) /\
  Nat.leb total_stake (3 * weight [VB]) = true /\
  ~ slashed fork_setting fork_state VA /\
  ~ slashed fork_setting fork_state VC.
Proof.
  assert (Hw : Nat.leb total_stake (3 * weight [VB]) = true) by reflexivity.
  split.
  - apply accountable_safety. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 casper_fork_exists)))))).
  - split.
    + exists [VB]. split; [repeat constructor; simpl; tauto |].
      split; [intros n [<- | []]; reflexivity |].
      apply Nat.leb_le in Hw. exact Hw.
    + split; [| split; [exact Hw | split]].
      * intros n ->. left. exists HA1, HB1. split; [discriminate |].
        exists 1, 0, 0. split; reflexivity.
      * exact (two_link_voter_not_slashed VA HA1 HA2 vote_va).
      * exact (two_link_voter_not_slashed VC HB1 HB2 vote_vc).
Qed.

Print Assumptions casper_fork_exists.
Print Assumptions casper_fork_slashable.
