(* SCOPE NOTE: standalone proof scope. A short check written beside the book: it states its own
   machine, prices and conditions as hypotheses and uses only the Coq standard library, so it
   does not import the foundation chain. *)
(* Chapter twenty-one, how much room keeping takes: an operation sends every state to a resting value and
   leaves resting starts alone; N distinct starts, of which some rest already; the operation repeated T
   times keeps apart every two states the runs pass through before the T-th repetition. Then any list
   of every state, without repeats, has at least N + T times (the starts not resting) members. *)
From Coq Require Import List Arith Lia FinFun.
Import ListNotations.

Section Room.
  Variable St : Type.
  Hypothesis eq_dec : forall a b : St, {a = b} + {a <> b}.
  Variable F : St -> St.
  Variable rest : St -> bool.
  Hypothesis F_rests : forall x, rest (F x) = true.
  Variable starts : list St.
  Hypothesis starts_nodup : NoDup starts.
  Hypothesis resting_fixed : forall s, In s starts -> rest s = true -> F s = s.
  Variable T : nat.

  Fixpoint iter (k : nat) (x : St) : St := match k with 0 => x | S j => F (iter j x) end.

  (* the promise: two states reached from starts in fewer than T repetitions, landing together, are one *)
  Hypothesis promise : forall s s' i j, In s starts -> In s' starts -> i < T -> j < T ->
      F (iter i s) = F (iter j s') -> iter i s = iter j s'.

  Lemma iter_rest : forall k x, 0 < k -> rest (iter k x) = true.
  Proof. intros [|k] x H; [lia | simpl; apply F_rests]. Qed.

  Lemma iter_fixed : forall k r, In r starts -> rest r = true -> iter k r = r.
  Proof. induction k; intros r Hr Rr; simpl; [reflexivity | rewrite IHk; auto]. Qed.

  (* walk back: equal states at positions i <= j come from s and iter (j - i) s' *)
  Lemma walk_back : forall i j s s', In s starts -> In s' starts -> i <= j -> j <= T ->
      iter i s = iter j s' -> s = iter (j - i) s'.
  Proof.
    induction i as [|i IH]; intros j s s' Hs Hs' Hij HjT E.
    - simpl in E. rewrite Nat.sub_0_r. exact E.
    - destruct j as [|j]; [lia|].
      simpl in E. apply promise in E; try assumption; try lia.
      replace (S j - S i) with (j - i) by lia. apply IH; auto; lia.
  Qed.

  (* positions: (s, k) for k = 0..T on every start that isn't resting; (r, 0) for every resting start *)
  Definition block (s : St) : list (St * nat) :=
    if rest s then [(s, 0)] else map (fun k => (s, k)) (seq 0 (S T)).

  Definition positions : list (St * nat) := flat_map block starts.

  Lemma in_positions : forall s k, In (s, k) positions <->
      In s starts /\ ((rest s = true /\ k = 0) \/ (rest s = false /\ k <= T)).
  Proof.
    intros s k. unfold positions. rewrite in_flat_map. unfold block. split.
    - intros [s0 [Hs0 Hin]]. destruct (rest s0) eqn:R0.
      + destruct Hin as [E | []]. inversion E; subst. auto.
      + apply in_map_iff in Hin as [k0 [E Hk]]. inversion E; subst. apply in_seq in Hk.
        split; [auto | right; split; [auto | lia]].
    - intros [Hs [[R K] | [R K]]]; exists s; split; auto; rewrite R.
      + subst. left. reflexivity.
      + apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia].
  Qed.

  Lemma nodup_app : forall (A : Type) (l1 l2 : list A), NoDup l1 -> NoDup l2 ->
      (forall x, In x l1 -> In x l2 -> False) -> NoDup (l1 ++ l2).
  Proof.
    induction l1 as [|a l1 IH]; intros l2 H1 H2 D; simpl; [exact H2|].
    inversion H1; subst. constructor.
    - intro Hin. apply in_app_or in Hin as [Hin | Hin]; [contradiction | apply (D a); [left|]; auto].
    - apply IH; auto. intros x Hx Hy. apply (D x); [right|]; auto.
  Qed.

  Lemma in_block_fst : forall s p, In p (block s) -> fst p = s.
  Proof.
    intros s [x k] H. unfold block in H. destruct (rest s).
    - destruct H as [E | []]. inversion E; reflexivity.
    - apply in_map_iff in H as [? [E _]]. inversion E; reflexivity.
  Qed.

  Lemma block_nodup : forall s, NoDup (block s).
  Proof.
    intro s. unfold block. destruct (rest s).
    - constructor; [simpl; tauto | constructor].
    - apply FinFun.Injective_map_NoDup; [intros a b E; inversion E; auto | apply seq_NoDup].
  Qed.

  Lemma flat_nodup : forall l, NoDup l -> NoDup (flat_map block l).
  Proof.
    induction l as [|s l IH]; intro H; simpl; [constructor|].
    inversion H; subst. apply nodup_app; [apply block_nodup | apply IH; auto|].
    intros p Hx Hy. apply in_flat_map in Hy as [s' [Hs' Hy']].
    pose proof (in_block_fst _ _ Hx). pose proof (in_block_fst _ _ Hy'). congruence.
  Qed.

  Lemma positions_nodup : NoDup positions.
  Proof. exact (flat_nodup starts starts_nodup). Qed.

  Lemma point_injective : forall p q, In p positions -> In q positions ->
      iter (snd p) (fst p) = iter (snd q) (fst q) -> p = q.
  Proof.
    (* one side of the argument, with the first position no later than the second *)
    assert (Side : forall s k s' k', In s starts -> In s' starts ->
              ((rest s = true /\ k = 0) \/ (rest s = false /\ k <= T)) ->
              ((rest s' = true /\ k' = 0) \/ (rest s' = false /\ k' <= T)) ->
              k <= k' -> iter k s = iter k' s' -> (s, k) = (s', k')).
    { intros s k s' k' Hs Hs' Ps Ps' Hkk E.
      destruct Ps' as [[R' K'] | [R' K']].
      - subst k'. assert (k = 0) by lia. subst k. simpl in E. subst s'. reflexivity.
      - destruct Ps as [[R K] | [R K]].
        + (* s rests: it equals itself at position k', walk both back k' steps *)
          subst k. simpl in E. rewrite <- (iter_fixed k' s Hs R) in E.
          pose proof (walk_back k' k' s s' Hs Hs' (le_n _) K' E) as B.
          rewrite Nat.sub_diag in B. simpl in B. subst s'. congruence.
        + pose proof (walk_back k k' s s' Hs Hs' Hkk K' E) as B.
          destruct (k' - k) as [|d] eqn:D.
          * simpl in B. subst s'. f_equal. lia.
          * exfalso. rewrite B in R. rewrite iter_rest in R by lia. discriminate. }
    intros [s k] [s' k'] Hp Hq E. simpl in E.
    apply in_positions in Hp as [Hs Ps]. apply in_positions in Hq as [Hs' Ps'].
    destruct (le_ge_dec k k') as [L | L].
    - apply Side; auto.
    - symmetry. apply Side; auto.
  Qed.

  Lemma length_flat : forall l : list St, length (flat_map block l) = length l + T * length (filter (fun s => negb (rest s)) l).
  Proof.
    induction l as [|s l IH]; simpl; [lia|].
    rewrite app_length, IH. unfold block. destruct (rest s); simpl.
    - lia.
    - rewrite map_length, seq_length. lia.
  Qed.

  Lemma length_positions : length positions = length starts + T * length (filter (fun s => negb (rest s)) starts).
  Proof. exact (length_flat starts). Qed.

  Lemma nodup_map_on : forall (A B : Type) (g : A -> B) (l : list A), NoDup l ->
      (forall x y, In x l -> In y l -> g x = g y -> x = y) -> NoDup (map g l).
  Proof.
    induction l as [|a l IH]; intros H Inj; simpl; [constructor|].
    inversion H; subst. constructor.
    - intro Hin. apply in_map_iff in Hin as [y [E Hy]].
      assert (a = y) by (apply Inj; [left; reflexivity | right; exact Hy | symmetry; exact E]).
      subst. contradiction.
    - apply IH; auto. intros x y Hx Hy E. apply Inj; [right | right |]; auto.
  Qed.

  Theorem room_needed : forall all : list St, NoDup all -> (forall x, In x all) ->
      length starts + T * length (filter (fun s => negb (rest s)) starts) <= length all.
  Proof.
    intros all Hall Hin. rewrite <- length_positions.
    rewrite <- (map_length (fun p => iter (snd p) (fst p)) positions).
    apply NoDup_incl_length; [|intros x _; apply Hin].
    apply nodup_map_on; [apply positions_nodup|].
    intros p q Hp Hq E. apply point_injective; assumption.
  Qed.
End Room.

Print Assumptions room_needed.
