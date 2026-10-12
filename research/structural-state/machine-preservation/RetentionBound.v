(** RetentionBound.v: the finite-capacity retention bound of Result.txt,
    Section 7, Theorem 3, checked.

    Door one of the toll chapter is the endless strip: keep every history and
    nothing ever merges. The chapter says a strip that ends must reuse a box.
    This file says how soon, for any deterministic implementation at all.

    Setting. An implementation has states X with a complete duplicate-free
    list (finite). A fixed operation F : X -> X is sampled at operation
    boundaries. An abstraction q : X -> A says which abstract state each
    implementation state represents, and the operation is a reset: whatever
    the state, after F it represents the fixed abstract state q0. There are
    representatives: x0 representing q0, and a list of others representing
    pairwise distinct abstract states different from q0.

    The hypothesis under test is retention: F is injective on the states
    reachable from the representatives in fewer than T applications. That is
    the exact sense in which the implementation keeps the history of the
    reset through T repetitions. The theorem is that the state space must
    then hold at least 1 + (T+1) * (number of other representatives) states.

    So a finite implementation retains injectively for at most
    (|X| - 1) / (N - 1) resets of an N-state family. Result.txt also shows
    the bound is attained for the reset-only experiment; this file proves
    the inequality only. No claim about heat is made: the theorem counts
    states, and pricing a merge is a separate premise.

    Dependencies: the standard library only. No axioms, no Admitted. *)

From Coq Require Import List Arith Lia.
Import ListNotations.

(* ================================================================= *)
(* List facts.                                                        *)
(* ================================================================= *)

Lemma nodup_app_disjoint {X : Type} : forall (l m : list X),
  NoDup l -> NoDup m -> (forall z, In z l -> ~ In z m) -> NoDup (l ++ m).
Proof.
  induction l as [| a l IH]; intros m Hl Hm Hd; simpl; [exact Hm |].
  inversion Hl as [| ? ? Ha Hl']; subst.
  constructor.
  - rewrite in_app_iff. intros [H | H]; [exact (Ha H) |].
    apply (Hd a); [left; reflexivity | exact H].
  - apply IH; [exact Hl' | exact Hm |].
    intros z Hz. apply Hd. right. exact Hz.
Qed.

Lemma nodup_flat_map {X Y : Type} : forall (f : Y -> list X) (l : list Y),
  NoDup l ->
  (forall a, In a l -> NoDup (f a)) ->
  (forall a b, In a l -> In b l -> a <> b -> forall z, In z (f a) -> ~ In z (f b)) ->
  NoDup (flat_map f l).
Proof.
  induction l as [| a l IH]; intros Hl Hin Hdis; simpl; [constructor |].
  inversion Hl as [| ? ? Ha Hl']; subst.
  apply nodup_app_disjoint.
  - apply Hin. left. reflexivity.
  - apply IH; [exact Hl' | intros; apply Hin; right; assumption |].
    intros b c Hb Hc Hbc. apply Hdis; [right; exact Hb | right; exact Hc | exact Hbc].
  - intros z Hz Hz'. apply in_flat_map in Hz'. destruct Hz' as [b [Hb Hzb]].
    assert (Hab : a <> b) by (intro E; subst; exact (Ha Hb)).
    apply (Hdis a b (or_introl eq_refl) (or_intror Hb) Hab z Hz Hzb).
Qed.

Lemma nodup_map_inj_on {X Y : Type} : forall (f : X -> Y) (l : list X),
  NoDup (map f l) -> forall a b, In a l -> In b l -> f a = f b -> a = b.
Proof.
  induction l as [| c l IH]; intros Hnd a b Ha Hb E; [destruct Ha |].
  simpl in Hnd. inversion Hnd as [| ? ? Hc Hl']; subst.
  destruct Ha as [-> | Ha]; destruct Hb as [-> | Hb].
  - reflexivity.
  - exfalso. apply Hc. rewrite E. apply in_map. exact Hb.
  - exfalso. apply Hc. rewrite <- E. apply in_map. exact Ha.
  - apply IH; assumption.
Qed.

Lemma nodup_map_of_inj_on {X Y : Type} : forall (f : X -> Y) (l : list X),
  (forall a b, In a l -> In b l -> f a = f b -> a = b) -> NoDup l -> NoDup (map f l).
Proof.
  induction l as [| c l IH]; intros Hinj Hnd; simpl; [constructor |].
  inversion Hnd as [| ? ? Hc Hl']; subst. constructor.
  - rewrite in_map_iff. intros [a [E Ha]].
    apply Hc. rewrite <- (Hinj a c (or_intror Ha) (or_introl eq_refl) E). exact Ha.
  - apply IH; [| exact Hl'].
    intros a b Ha Hb E. apply Hinj; [right | right |]; assumption.
Qed.

Lemma length_flat_map_const {X Y : Type} : forall (f : Y -> list X) (l : list Y) (n : nat),
  (forall a, In a l -> length (f a) = n) -> length (flat_map f l) = length l * n.
Proof.
  induction l as [| a l IH]; intros n H; simpl; [reflexivity |].
  rewrite app_length, (H a (or_introl eq_refl)), (IH n); [reflexivity |].
  intros b Hb. apply H. right. exact Hb.
Qed.

(* ================================================================= *)
(* The retention experiment.                                          *)
(* ================================================================= *)

Section Retention.

Variable X A : Type.
Variable F : X -> X.
Variable q : X -> A.
Variable q0 : A.

(* The operation is a reset: every state is sent to one representing q0. *)
Hypothesis reset : forall x, q (F x) = q0.

Fixpoint iter (t : nat) (x : X) : X :=
  match t with 0 => x | S t' => F (iter t' x) end.

Lemma iter_pos_q0 : forall t x, 1 <= t -> q (iter t x) = q0.
Proof. intros [| t] x H; [lia | simpl; apply reset]. Qed.

(* Representatives: x0 for q0, and the others. *)
Variable x0 : X.
Variable others : list X.
Hypothesis x0_q0 : q x0 = q0.
Hypothesis others_not_q0 : forall r, In r others -> q r <> q0.
Hypothesis others_distinct : NoDup (map q others).

Definition reps : list X := x0 :: others.

(* The horizon. *)
Variable T : nat.

(* The states encountered in fewer than T applications. *)
Definition inD (z : X) : Prop :=
  exists r t, In r reps /\ t < T /\ z = iter t r.

(* Retention: F is injective on that set. *)
Hypothesis retain : forall x y, inD x -> inD y -> F x = F y -> x = y.

(* Cancellation of k common applications along two trajectories. *)
Lemma cancel : forall k s t r r',
  In r reps -> In r' reps -> s + k <= T -> t + k <= T ->
  iter (s + k) r = iter (t + k) r' -> iter s r = iter t r'.
Proof.
  induction k as [| k IH]; intros s t r r' Hr Hr' Hs Ht Heq.
  - rewrite !Nat.add_0_r in Heq. exact Heq.
  - apply (IH s t r r' Hr Hr'); try lia.
    replace (s + S k) with (S (s + k)) in Heq by lia.
    replace (t + S k) with (S (t + k)) in Heq by lia.
    simpl in Heq.
    apply retain; [| | exact Heq].
    + exists r, (s + k). split; [exact Hr | split; [lia | reflexivity]].
    + exists r', (t + k). split; [exact Hr' | split; [lia | reflexivity]].
Qed.

(* Trajectory nodes of the other representatives coincide only trivially. *)
Lemma nodes_separate : forall s t r r',
  In r others -> In r' others -> s <= T -> t <= T ->
  iter s r = iter t r' -> s = t /\ r = r'.
Proof.
  intros s t r r' Hr Hr' Hs Ht Heq.
  assert (Hr1 : In r reps) by (right; exact Hr).
  assert (Hr1' : In r' reps) by (right; exact Hr').
  destruct (le_lt_dec s t) as [Hle | Hlt].
  - assert (Hc : iter 0 r = iter (t - s) r').
    { apply (cancel s 0 (t - s) r r' Hr1 Hr1'); try lia.
      replace (0 + s) with s by lia. replace (t - s + s) with t by lia. exact Heq. }
    simpl in Hc.
    destruct (Nat.eq_dec s t) as [E | NE].
    + subst t. replace (s - s) with 0 in Hc by lia. simpl in Hc. auto.
    + exfalso. apply (others_not_q0 r Hr). rewrite Hc. apply iter_pos_q0. lia.
  - exfalso.
    assert (Hc : iter (s - t) r = iter 0 r').
    { apply (cancel t (s - t) 0 r r' Hr1 Hr1'); try lia.
      replace (s - t + t) with s by lia. replace (0 + t) with t by lia. exact Heq. }
    simpl in Hc.
    apply (others_not_q0 r' Hr'). rewrite <- Hc. apply iter_pos_q0. lia.
Qed.

(* The trajectory of a representative through the horizon: T+1 nodes. *)
Definition traj (r : X) : list X := map (fun t => iter t r) (seq 0 (S T)).

Lemma in_traj : forall z r, In z (traj r) <-> exists t, t <= T /\ z = iter t r.
Proof.
  intros z r. unfold traj. rewrite in_map_iff. split.
  - intros [t [Hz Ht]]. apply in_seq in Ht. exists t. split; [lia | auto].
  - intros [t [Ht Hz]]. exists t. split; [auto | apply in_seq; lia].
Qed.

Lemma traj_length : forall r, length (traj r) = S T.
Proof. intro r. unfold traj. rewrite map_length, seq_length. reflexivity. Qed.

Lemma traj_nodup : forall r, In r others -> NoDup (traj r).
Proof.
  intros r Hr. unfold traj. apply nodup_map_of_inj_on; [| apply seq_NoDup].
  intros a b Ha Hb E. apply in_seq in Ha. apply in_seq in Hb.
  assert (H := nodes_separate a b r r Hr Hr ltac:(lia) ltac:(lia) E).
  destruct H as [Hab _]. exact Hab.
Qed.

Lemma traj_disjoint : forall r r', In r others -> In r' others -> r <> r' ->
  forall z, In z (traj r) -> ~ In z (traj r').
Proof.
  intros r r' Hr Hr' Hne z Hz Hz'.
  apply in_traj in Hz. apply in_traj in Hz'.
  destruct Hz as [s [Hs ->]]. destruct Hz' as [t [Ht E]].
  destruct (nodes_separate s t r r' Hr Hr' Hs Ht E) as [_ Hrr']. exact (Hne Hrr').
Qed.

(* The nodes of all the other representatives' trajectories. *)
Definition nodes : list X := flat_map traj others.

Lemma others_nodup : NoDup others.
Proof.
  generalize others_distinct. clear. induction others as [| r l IH]; intro H; [constructor |].
  simpl in H. inversion H as [| ? ? Hr Hl]; subst. constructor; [| exact (IH Hl)].
  intro Hin. apply Hr. apply in_map. exact Hin.
Qed.

Lemma nodes_nodup : NoDup nodes.
Proof.
  apply nodup_flat_map; [exact others_nodup | exact traj_nodup |].
  intros a b Ha Hb Hab z Hz. apply (traj_disjoint a b Ha Hb Hab z Hz).
Qed.

Lemma nodes_length : length nodes = length others * S T.
Proof. apply length_flat_map_const. intros r _. apply traj_length. Qed.

(* The end of the q0 representative's own trajectory is a further state. *)
Definition extra : X := iter T x0.

Lemma extra_not_node : ~ In extra nodes.
Proof.
  unfold nodes. rewrite in_flat_map. intros [r [Hr Hz]].
  apply in_traj in Hz. destruct Hz as [t [Ht E]]. unfold extra in E.
  destruct t as [| t].
  - (* iter T x0 = r: q r would be q0 *)
    apply (others_not_q0 r Hr). simpl in E. rewrite <- E.
    destruct T as [| T']; [exact x0_q0 | apply iter_pos_q0; lia].
  - (* cancel S t applications: iter (T - S t) x0 = r *)
    assert (Hx0 : In x0 reps) by (left; reflexivity).
    assert (Hr1 : In r reps) by (right; exact Hr).
    assert (Hc : iter (T - S t) x0 = iter 0 r).
    { apply (cancel (S t) (T - S t) 0 x0 r Hx0 Hr1); try lia.
      replace (T - S t + S t) with T by lia. replace (0 + S t) with (S t) by lia. exact E. }
    simpl in Hc.
    apply (others_not_q0 r Hr). rewrite <- Hc.
    destruct (Nat.eq_dec T (S t)) as [ET | NET].
    + replace (T - S t) with 0 by lia. exact x0_q0.
    + apply iter_pos_q0. lia.
Qed.

(* Finiteness of the implementation. *)
Variable all : list X.
Hypothesis all_nodup : NoDup all.
Hypothesis all_complete : forall x, In x all.

Theorem retention_bound : 1 + (S T) * length others <= length all.
Proof.
  assert (Hnd : NoDup (extra :: nodes)) by (constructor; [exact extra_not_node | exact nodes_nodup]).
  assert (Hlen := NoDup_incl_length Hnd (fun z _ => all_complete z)).
  simpl in Hlen. rewrite nodes_length in Hlen. lia.
Qed.

(* Equivalently: the number of injectively retained repetitions is bounded. *)
Corollary retention_horizon : length others >= 1 -> T <= (length all - 1) / length others - 1 \/ T = 0.
Proof.
  intro Hn. pose proof retention_bound as Hb.
  destruct T as [| T']; [right; reflexivity | left].
  assert (S (S T') * length others <= length all - 1) by lia.
  assert (Hdiv : S (S T') <= (length all - 1) / length others).
  { apply Nat.div_le_lower_bound; [lia |]. rewrite Nat.mul_comm. exact H. }
  lia.
Qed.

End Retention.

Print Assumptions retention_bound.
Print Assumptions retention_horizon.
