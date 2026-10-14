(** HeatOrRoom.v: the count under the three currencies.

    The toll chapter of the monograph leads with one sentence: anything a
    machine keeps and can't take back is paid for in heat, room or time.
    This file checks the counting that sentence rests on, the proposition
    the book calls Heat or room. No heat is mentioned here: pricing a merge
    is a separate premise. What is counted is states.

    (1) The dichotomy, on any state space [Section Dichotomy]. Take a
        reading P that a move F never turns off, and a state s at which F
        turns it from no to yes. If F never merges (is injective), then the
        iterates of s are pairwise distinct
        ([permanent_flip_iterates_distinct]), so no finite duplicate-free
        list contains them all ([permanent_flip_no_finite_list]). Either the
        move merges, or it needs a fresh state every time.

    (1') The run form [Section RunForm], the same count for every step of
        every computation that keeps a record. Take any deterministic step f,
        a run x0, f x0, f (f x0), ... and a step r at which a reading that f
        never turns off goes from no to yes. If no two states of the run's
        first n steps merge under f, the run visits a fresh state at every one
        of those steps ([run_merges_or_fresh]); so on M states a run that keeps
        a record and never merges has fewer than M steps
        ([run_bounded_by_room]). Time is paid out of room.

    (2) The retention bound [Section Retention]. A finite implementation of
        a reset, F : X -> X, with an abstraction q : X -> A sending every
        F-image to the fixed abstract state q0, and representatives x0 for
        q0 and a list of others for pairwise distinct abstract states
        different from q0. Retention: F is injective on the states reached
        from the representatives in fewer than T applications. Then
        |X| >= 1 + (T+1) * (number of others) ([retention_bound]), so a
        bounded memory keeps the history of at most (|X|-1)/(N-1) resets
        ([retention_horizon]). A bounded memory delays the merge and does
        not avoid it.

    (3) The bound is exact [Section Tightness]. One fixed chair Z and, for
        each of n others, a path of T+1 chairs Node i 0, ..., Node i T, with
        F walking the path and sending its last chair to Z. The set has
        exactly 1 + (T+1) * n states ([tight_length], [tight_nodup]), is
        closed under F ([tight_closed]), satisfies the reset and
        representative hypotheses of (2) ([tight_reset],
        [tight_others_not_q0], [tight_others_distinct]), retains through T
        repetitions ([tight_retain]), and merges on the next
        ([tight_merges_next]).

    The fibre form of the bound, M >= N + T (N - L) for an operation with L
    fixed places, is the same count run inside each fibre; the monograph
    states it on the page and this file does not repeat it.

    Dependencies: the standard library only. No axioms, no Admitted. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   counts the states of an abstract move on any type and imports only the
   standard library. It is the count the monograph's Heat or room proposition
   rests on. The finite-machine toll it sits under is PermanentCertification.v,
   and the small machine's record-layer toll is in ThieleComplete.v. *)

From Coq Require Import List Arith Lia Bool.
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


(* ================================================================= *)
(* Iteration of a move.                                               *)
(* ================================================================= *)

Fixpoint iterF {X : Type} (F : X -> X) (t : nat) (x : X) : X :=
  match t with 0 => x | S t' => F (iterF F t' x) end.

Lemma iterF_add {X : Type} (F : X -> X) : forall a b x,
  iterF F (a + b) x = iterF F a (iterF F b x).
Proof. induction a as [| a IH]; intros b x; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(* ================================================================= *)
(* (1) The dichotomy: merge, or a fresh state every time.             *)
(* ================================================================= *)

Section Dichotomy.

Variable X : Type.
Variable F : X -> X.
Variable P : X -> bool.

(* The reading is permanent under the move. *)
Hypothesis permanent : forall x, P x = true -> P (F x) = true.
(* The move never merges. *)
Hypothesis injective : forall x y, F x = F y -> x = y.

(* The raising state. *)
Variable s : X.
Hypothesis s_no : P s = false.
Hypothesis s_yes : P (F s) = true.

Lemma iter_pos_yes : forall t, 1 <= t -> P (iterF F t s) = true.
Proof.
  induction t as [| t IH]; intro H; [lia |].
  simpl. destruct t as [| t]; [exact s_yes |].
  apply permanent. apply IH. lia.
Qed.

Lemma cancel_iter : forall k a b,
  iterF F (k + a) s = iterF F (k + b) s -> iterF F a s = iterF F b s.
Proof.
  induction k as [| k IH]; intros a b H; [exact H |].
  apply IH. simpl in H. apply injective. exact H.
Qed.

Theorem permanent_flip_iterates_distinct : forall j k,
  iterF F j s = iterF F k s -> j = k.
Proof.
  intros j k H. destruct (le_lt_dec j k) as [Hle | Hlt].
  - destruct (Nat.eq_dec j k) as [E | NE]; [exact E |]. exfalso.
    assert (Hc : iterF F 0 s = iterF F (k - j) s).
    { apply (cancel_iter j 0 (k - j)). rewrite Nat.add_0_r.
      replace (j + (k - j)) with k by lia. exact H. }
    simpl in Hc.
    assert (Hp : P s = true) by (rewrite Hc; apply iter_pos_yes; lia).
    rewrite s_no in Hp. discriminate Hp.
  - exfalso.
    assert (Hc : iterF F (j - k) s = iterF F 0 s).
    { apply (cancel_iter k (j - k) 0). replace (k + (j - k)) with j by lia.
      rewrite Nat.add_0_r. exact H. }
    simpl in Hc.
    assert (Hp : P s = true) by (rewrite <- Hc; apply iter_pos_yes; lia).
    rewrite s_no in Hp. discriminate Hp.
Qed.

(* So the run visits a new state every time: no finite list holds it. *)
Theorem permanent_flip_no_finite_list :
  forall all : list X, NoDup all -> (forall x, In x all) -> False.
Proof.
  intros all Hnd Hall.
  set (l := map (fun t => iterF F t s) (seq 0 (S (length all)))).
  assert (Hl : NoDup l).
  { unfold l. apply nodup_map_of_inj_on; [| apply seq_NoDup].
    intros a b _ _ E. apply permanent_flip_iterates_distinct. exact E. }
  assert (Hlen := NoDup_incl_length Hl (fun z _ => Hall z)).
  unfold l in Hlen. rewrite map_length, seq_length in Hlen. lia.
Qed.

End Dichotomy.

(* ================================================================= *)
(* (1') The run form: every step of every computation that keeps a    *)
(*      record.                                                        *)
(* ================================================================= *)

Section RunForm.

Variable X : Type.
Variable f : X -> X.
Variable P : X -> bool.
(* The reading is permanent under the step. *)
Hypothesis permanent : forall x, P x = true -> P (f x) = true.

(* A run from x0, and a step r at which the reading goes from no to yes. *)
Variable x0 : X.
Variable r : nat.
Hypothesis r_no : P (iterF f r x0) = false.
Hypothesis r_yes : P (iterF f (S r) x0) = true.

Lemma run_yes_after : forall t, S r <= t -> P (iterF f t x0) = true.
Proof.
  induction t as [| t IH]; intro H; [lia |].
  destruct (Nat.eq_dec t r) as [-> | NE]; [exact r_yes |].
  simpl. apply permanent. apply IH. lia.
Qed.

Lemma run_no_before : forall t, t <= r -> P (iterF f t x0) = false.
Proof.
  intros t Ht. destruct (P (iterF f t x0)) eqn:E; [| reflexivity].
  exfalso.
  assert (Hr : P (iterF f r x0) = true).
  { replace r with ((r - t) + t) by lia. rewrite iterF_add.
    generalize (r - t). intro k. induction k as [| k IH]; [exact E | simpl; apply permanent; exact IH]. }
  rewrite r_no in Hr. discriminate Hr.
Qed.

(* Merging among the run's own states, within its first n steps. *)
Definition run_merges (n : nat) : Prop :=
  exists i j, i <= n /\ j <= n /\ i <> j /\ f (iterF f i x0) = f (iterF f j x0).

(* If the first n steps of the run never merge, cancellation works. *)
Lemma run_cancel : forall n k a b, ~ run_merges n ->
  k + a <= n -> k + b <= n ->
  iterF f (k + a) x0 = iterF f (k + b) x0 -> iterF f a x0 = iterF f b x0.
Proof.
  intros n k. induction k as [| k IH]; intros a b Hnm Ha Hb H; [exact H |].
  apply (IH a b Hnm); try lia.
  simpl in H.
  destruct (Nat.eq_dec (k + a) (k + b)) as [E | NE].
  - rewrite E. reflexivity.
  - exfalso. apply Hnm. exists (k + a), (k + b). repeat split; try lia. exact H.
Qed.

(* A run that keeps a record and never merges never repeats a state. *)
Theorem run_merges_or_fresh : forall n, ~ run_merges n ->
  forall i j, i <= n -> j <= n -> iterF f i x0 = iterF f j x0 -> i = j.
Proof.
  intros n Hnm i j Hi Hj H. destruct (le_lt_dec i j) as [Hle | Hlt].
  - destruct (Nat.eq_dec i j) as [E | NE]; [exact E |]. exfalso.
    (* cancel i steps: x0 = x_(j-i), with j - i >= 1 *)
    assert (Hc : iterF f 0 x0 = iterF f (j - i) x0).
    { apply (run_cancel n i 0 (j - i) Hnm); try lia.
      rewrite Nat.add_0_r. replace (i + (j - i)) with j by lia. exact H. }
    simpl in Hc.
    (* the run is periodic with period d = j - i from the start *)
    assert (Hper : forall t, iterF f t x0 = iterF f (t + (j - i)) x0).
    { intro t. rewrite iterF_add. rewrite <- Hc. reflexivity. }
    set (d := j - i).
    assert (Hd : 1 <= d) by lia.
    (* x_(S r) = x_(S r - d) if S r >= d, else x_(S r) = x_(S r + d) and ... use
       the no-before-r fact at index (S r) mod d reached by peeling periods *)
    assert (Hpeel : forall m, iterF f (S r) x0 = iterF f (S r + m * d) x0).
    { induction m as [| m IHm]; [rewrite Nat.add_0_r; reflexivity |].
      rewrite IHm. replace (S r + S m * d) with ((S r + m * d) + d) by lia. apply Hper. }
    (* every index equals its residue modulo the period *)
    assert (Hdown : forall t, d <= t -> iterF f t x0 = iterF f (t - d) x0).
    { intros t Ht. replace t with ((t - d) + d) at 1 by lia. symmetry. apply Hper. }
    assert (Hres : forall t, iterF f t x0 = iterF f (t mod d) x0).
    { intro t. induction t as [t IHt] using (well_founded_induction lt_wf).
      destruct (le_lt_dec d t) as [Hle' | Hlt'].
      - rewrite (Hdown t Hle'). rewrite (IHt (t - d)) by lia.
        f_equal. replace t with ((t - d) + 1 * d) at 2 by lia. rewrite Nat.Div0.mod_add. reflexivity.
      - rewrite Nat.mod_small by lia. reflexivity. }
    assert (Hyes : P (iterF f (S r) x0) = true) by exact r_yes.
    rewrite Hres in Hyes.
    assert (Hno : P (iterF f (S r mod d) x0) = false).
    { apply run_no_before.
      assert (S r mod d < d) by (apply Nat.mod_upper_bound; lia).
      (* if d <= S r the residue is below the raise; if d > S r, x0 = x_d
         with x_d already raised, which permanence forbids *)
      destruct (le_lt_dec d (S r)) as [Hle2 | Hlt2]; [lia |].
      rewrite Nat.mod_small by lia.
      exfalso.
      assert (Hdy : P (iterF f (j - i) x0) = true) by (apply run_yes_after; lia).
      rewrite <- Hc in Hdy. simpl in Hdy.
      assert (Hz0 : P (iterF f 0 x0) = false) by (apply run_no_before; lia).
      simpl in Hz0. rewrite Hz0 in Hdy. discriminate Hdy. }
    rewrite Hno in Hyes. discriminate Hyes.
  - exfalso.
    assert (Hc : iterF f (i - j) x0 = iterF f 0 x0).
    { apply (run_cancel n j (i - j) 0 Hnm); try lia.
      replace (j + (i - j)) with i by lia. rewrite Nat.add_0_r. exact H. }
    simpl in Hc. symmetry in Hc.
    set (d := i - j) in *. assert (Hd : 1 <= d) by lia.
    assert (Hper : forall t, iterF f t x0 = iterF f (t + d) x0).
    { intro t. rewrite iterF_add. rewrite <- Hc. reflexivity. }
    assert (Hdown : forall t, d <= t -> iterF f t x0 = iterF f (t - d) x0).
    { intros t Ht. replace t with ((t - d) + d) at 1 by lia. symmetry. apply Hper. }
    assert (Hres : forall t, iterF f t x0 = iterF f (t mod d) x0).
    { intro t. induction t as [t IHt] using (well_founded_induction lt_wf).
      destruct (le_lt_dec d t) as [Hle' | Hlt'].
      - rewrite (Hdown t Hle'). rewrite (IHt (t - d)) by lia.
        f_equal. replace t with ((t - d) + 1 * d) at 2 by lia. rewrite Nat.Div0.mod_add. reflexivity.
      - rewrite Nat.mod_small by lia. reflexivity. }
    assert (Hyes : P (iterF f (S r) x0) = true) by exact r_yes.
    rewrite Hres in Hyes.
    assert (Hno : P (iterF f (S r mod d) x0) = false).
    { apply run_no_before.
      assert (S r mod d < d) by (apply Nat.mod_upper_bound; lia).
      destruct (le_lt_dec d (S r)) as [Hle2 | Hlt2]; [lia |].
      rewrite Nat.mod_small by lia. exfalso.
      assert (Hdy : P (iterF f d x0) = true) by (apply run_yes_after; lia).
      rewrite <- Hc in Hdy. simpl in Hdy.
      assert (Hz0 : P (iterF f 0 x0) = false) by (apply run_no_before; lia).
      simpl in Hz0. rewrite Hz0 in Hdy. discriminate Hdy. }
    rewrite Hno in Hyes. discriminate Hyes.
Qed.

(* So on M states a run that keeps a record and never merges has at most
   M - 1 steps: time is paid out of room. *)
Theorem run_bounded_by_room : forall (all : list X), NoDup all -> (forall x, In x all) ->
  forall n, ~ run_merges n -> n < length all.
Proof.
  intros all Hnd Hall n Hnm.
  set (l := map (fun t => iterF f t x0) (seq 0 (S n))).
  assert (Hl : NoDup l).
  { unfold l. apply nodup_map_of_inj_on; [| apply seq_NoDup].
    intros a b Ha Hb E. apply in_seq in Ha. apply in_seq in Hb.
    apply (run_merges_or_fresh n Hnm); [lia | lia | exact E]. }
  assert (Hlen := NoDup_incl_length Hl (fun z _ => Hall z)).
  unfold l in Hlen. rewrite map_length, seq_length in Hlen. lia.
Qed.

End RunForm.

(* ================================================================= *)
(* (2) The retention bound.                                           *)
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

(* ================================================================= *)
(* (3) The bound is exact.                                            *)
(* ================================================================= *)

Section Tightness.

(* n other representatives, horizon T. *)
Variable n T : nat.

Inductive St : Type := Z | Node (i t : nat).

(* F walks each path and sends its last chair to Z; Z stays. *)
Definition Ft (x : St) : St :=
  match x with
  | Z => Z
  | Node i t => if t <? T then Node i (S t) else Z
  end.

(* The abstraction: the first chair of path i represents i; all else q0. *)
Definition qt (x : St) : option nat :=
  match x with Z => None | Node i t => if t =? 0 then Some i else None end.

Definition others_t : list St := map (fun i => Node i 0) (seq 0 n).
Definition path (i : nat) : list St := map (fun t => Node i t) (seq 0 (S T)).
Definition all_t : list St := Z :: flat_map path (seq 0 n).

Lemma tight_reset : forall x, qt (Ft x) = None.
Proof.
  intros [| i t]; simpl; [reflexivity |].
  destruct (t <? T); simpl; reflexivity.
Qed.

Lemma tight_x0_q0 : qt Z = None.
Proof. reflexivity. Qed.

Lemma tight_others_not_q0 : forall r, In r others_t -> qt r <> None.
Proof.
  intros r Hr. unfold others_t in Hr. apply in_map_iff in Hr.
  destruct Hr as [i [<- _]]. simpl. discriminate.
Qed.

Lemma tight_others_distinct : NoDup (map qt others_t).
Proof.
  unfold others_t. rewrite map_map. simpl.
  apply nodup_map_of_inj_on; [| apply seq_NoDup].
  intros a b _ _ E. injection E. auto.
Qed.

Lemma tight_length : length all_t = 1 + S T * n.
Proof.
  unfold all_t. simpl. f_equal.
  rewrite (length_flat_map_const path (seq 0 n) (S T)).
  - rewrite seq_length. lia.
  - intros i _. unfold path. rewrite map_length, seq_length. reflexivity.
Qed.

Lemma tight_length_others : length others_t = n.
Proof. unfold others_t. rewrite map_length, seq_length. reflexivity. Qed.

Lemma in_path : forall z i, In z (path i) <-> exists t, t <= T /\ z = Node i t.
Proof.
  intros z i. unfold path. rewrite in_map_iff. split.
  - intros [t [<- Ht]]. apply in_seq in Ht. exists t. split; [lia | reflexivity].
  - intros [t [Ht ->]]. exists t. split; [reflexivity | apply in_seq; lia].
Qed.

Lemma tight_nodup : NoDup all_t.
Proof.
  unfold all_t. constructor.
  - rewrite in_flat_map. intros [i [_ Hz]]. apply in_path in Hz.
    destruct Hz as [t [_ E]]. discriminate E.
  - apply nodup_flat_map; [apply seq_NoDup | |].
    + intros i _. unfold path. apply nodup_map_of_inj_on; [| apply seq_NoDup].
      intros a b _ _ E. injection E. auto.
    + intros a b _ _ Hab z Hz Hz'. apply in_path in Hz. apply in_path in Hz'.
      destruct Hz as [t [_ ->]]. destruct Hz' as [t' [_ E]].
      injection E. intros _ Eab. exact (Hab Eab).
Qed.

Lemma tight_closed : forall x, In x all_t -> In (Ft x) all_t.
Proof.
  intros x Hx. unfold all_t in *. destruct Hx as [<- | Hx]; [left; reflexivity |].
  rewrite in_flat_map in Hx. destruct Hx as [i [Hi Hz]]. apply in_path in Hz.
  destruct Hz as [t [Ht ->]]. simpl.
  destruct (t <? T) eqn:E.
  - right. rewrite in_flat_map. exists i. split; [exact Hi |].
    apply in_path. exists (S t). apply Nat.ltb_lt in E. split; [lia | reflexivity].
  - left. reflexivity.
Qed.

Lemma tight_reps_in : In Z all_t /\ (forall r, In r others_t -> In r all_t).
Proof.
  split; [left; reflexivity |].
  intros r Hr. unfold others_t in Hr. apply in_map_iff in Hr.
  destruct Hr as [i [<- Hi]]. right. rewrite in_flat_map. exists i. split; [exact Hi |].
  apply in_path. exists 0. split; [lia | reflexivity].
Qed.

Lemma iter_node : forall t i, t <= T -> iterF Ft t (Node i 0) = Node i t.
Proof.
  induction t as [| t IH]; intros i Ht; [reflexivity |].
  simpl. rewrite IH by lia. simpl.
  destruct (t <? T) eqn:E; [reflexivity |].
  apply Nat.ltb_ge in E. lia.
Qed.

Lemma iter_Z : forall t, iterF Ft t Z = Z.
Proof. induction t as [| t IH]; [reflexivity | simpl; rewrite IH; reflexivity]. Qed.

(* Retention: F is injective on the states reached in fewer than T steps. *)
Definition reached (z : St) : Prop :=
  exists r t, In r (Z :: others_t) /\ t < T /\ z = iterF Ft t r.

Lemma reached_shape : forall z, reached z ->
  z = Z \/ exists i t, t < T /\ z = Node i t.
Proof.
  intros z [r [t [Hr [Ht ->]]]]. destruct Hr as [<- | Hr].
  - left. apply iter_Z.
  - right. unfold others_t in Hr. apply in_map_iff in Hr. destruct Hr as [i [<- _]].
    exists i, t. split; [exact Ht | apply iter_node; lia].
Qed.

Theorem tight_retain : forall x y, reached x -> reached y -> Ft x = Ft y -> x = y.
Proof.
  intros x y Hx Hy E.
  destruct (reached_shape x Hx) as [-> | [i [t [Ht ->]]]];
  destruct (reached_shape y Hy) as [-> | [i' [t' [Ht' ->]]]]; simpl in E.
  - reflexivity.
  - apply Nat.ltb_lt in Ht'. rewrite Ht' in E. discriminate E.
  - apply Nat.ltb_lt in Ht. rewrite Ht in E. discriminate E.
  - apply Nat.ltb_lt in Ht. apply Nat.ltb_lt in Ht'. rewrite Ht, Ht' in E.
    injection E. intros -> ->. reflexivity.
Qed.

(* And on the next repetition the last chair of a path lands on Z. *)
Theorem tight_merges_next : 1 <= n ->
  iterF Ft T (Node 0 0) <> iterF Ft T Z /\
  Ft (iterF Ft T (Node 0 0)) = Ft (iterF Ft T Z).
Proof.
  intro Hn. rewrite iter_node by lia. rewrite iter_Z. split; [discriminate |].
  simpl. rewrite Nat.ltb_irrefl. reflexivity.
Qed.

(* The lower bound of (2) is met with equality. *)
Theorem tight_exact : length all_t = 1 + S T * length others_t.
Proof. rewrite tight_length_others. apply tight_length. Qed.

End Tightness.

Print Assumptions permanent_flip_iterates_distinct.
Print Assumptions permanent_flip_no_finite_list.
Print Assumptions run_merges_or_fresh.
Print Assumptions run_bounded_by_room.
Print Assumptions retention_bound.
Print Assumptions retention_horizon.
Print Assumptions tight_retain.
Print Assumptions tight_merges_next.
Print Assumptions tight_exact.
