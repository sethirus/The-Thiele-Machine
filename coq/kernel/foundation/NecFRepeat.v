(** NecFRepeat: a record that goes up and stays up along a repeated move is
    raised by a merge of two states the run itself visits.

    - Iterate any map f from a start s0 on a finite machine. If the flag is
      down at s0 and up at every step from some point on, then f sends two
      different states of that very orbit to one state
      ([nec_f_orbit_merges_visited]). The map can be one move repeated
      ([nec_f_repeat_merges_visited]), or the step of a closed machine that
      picks its next move from its own state ([nec_f_closed_merges_visited]).
    - Moves picked from outside give no such merge: two states, a swap and a
      move that does nothing; the swap once and then the idle move forever
      raises the flag for good and neither move merges anything
      ([nec_f_outside_moves_no_merge]).
    - A word of moves repeated forever: if the flag is down at the start and
      up at every repetition from some point on, some letter of the word
      merges two states the run visits at that letter's place in the pattern,
      in two different repetitions ([nec_f_word_merges_visited]).
    - No permanence premise is used: "up from some point on" along the run is
      all the argument needs. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From Kernel Require Import PermanentCertification.

Section Orbit.

Variable X : Type.
Variable eq_dec : forall a b : X, {a = b} + {a <> b}.
Variable cert : X -> bool.

(** The orbit of a map: the start, then the map applied n times. *)
Definition nec_f_orbit (f : X -> X) (n : nat) (s0 : X) : X := Nat.iter n f s0.

Lemma nec_f_orbit_add : forall f m n s0,
  nec_f_orbit f (m + n) s0 = nec_f_orbit f m (nec_f_orbit f n s0).
Proof.
  intros f m n s0. unfold nec_f_orbit. induction m as [| m IH]; [reflexivity |].
  simpl. rewrite IH. reflexivity.
Qed.

(** Searching a bounded range of a sequence for a target is decidable. *)
Lemma nec_f_bounded_search : forall (g : nat -> X) (t : X) n,
  (exists p, p <= n /\ g p = t) \/ (forall p, p <= n -> g p <> t).
Proof.
  intros g t n. induction n as [| n IH].
  - destruct (eq_dec (g 0) t) as [E | N].
    + left. exists 0. split; [lia | exact E].
    + right. intros p Hp. replace p with 0 by lia. exact N.
  - destruct IH as [[p [Hp E]] | Hno].
    + left. exists p. split; [lia | exact E].
    + destruct (eq_dec (g (S n)) t) as [E | N].
      * left. exists (S n). split; [lia | exact E].
      * right. intros p Hp. destruct (Nat.eq_dec p (S n)) as [-> | Hne]; [exact N |].
        apply Hno. lia.
Qed.

(** The first n + 1 states of the orbit, newest first. *)
Fixpoint nec_f_prefix (f : X -> X) (n : nat) (s0 : X) : list X :=
  match n with
  | 0 => [s0]
  | S k => nec_f_orbit f (S k) s0 :: nec_f_prefix f k s0
  end.

Lemma nec_f_prefix_length : forall f n s0, length (nec_f_prefix f n s0) = S n.
Proof. intros f n s0. induction n as [| n IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma nec_f_prefix_in : forall f n s0 t,
  In t (nec_f_prefix f n s0) -> exists p, p <= n /\ nec_f_orbit f p s0 = t.
Proof.
  intros f n s0 t. induction n as [| n IH]; simpl; intro H.
  - destruct H as [<- | []]. exists 0. split; [lia | reflexivity].
  - destruct H as [<- | H].
    + exists (S n). split; [lia | reflexivity].
    + destruct (IH H) as [p [Hp E]]. exists p. split; [lia | exact E].
Qed.

(** Either two of the first n + 1 states coincide, or they are all different. *)
Lemma nec_f_dup_or_nodup : forall f n s0,
  (exists p q, p < q <= n /\ nec_f_orbit f p s0 = nec_f_orbit f q s0) \/
  NoDup (nec_f_prefix f n s0).
Proof.
  intros f n s0. induction n as [| n IH].
  - right. constructor; [intros [] | constructor].
  - destruct IH as [[p [q [Hpq He]]] | Hnd].
    + left. exists p, q. split; [lia | exact He].
    + destruct (nec_f_bounded_search (fun p => nec_f_orbit f p s0) (nec_f_orbit f (S n) s0) n)
        as [[p [Hp E]] | Hno].
      * left. exists p, (S n). split; [lia | exact E].
      * right. simpl. constructor; [| exact Hnd].
        intro Hin. destruct (nec_f_prefix_in f n s0 _ Hin) as [p [Hp E]].
        exact (Hno p Hp E).
Qed.

(** On a finite machine some state of the orbit comes back. *)
Lemma nec_f_orbit_repeats : forall f (all : list X) s0,
  @finite_states X all ->
  exists p q, p < q /\ nec_f_orbit f p s0 = nec_f_orbit f q s0.
Proof.
  intros f all s0 [_ Hall].
  destruct (nec_f_dup_or_nodup f (length all) s0) as [[p [q [Hpq He]]] | Hnd].
  - exists p, q. split; [lia | exact He].
  - exfalso. assert (Hle : length (nec_f_prefix f (length all) s0) <= length all).
    { apply NoDup_incl_length; [exact Hnd | intros t _; apply Hall]. }
    rewrite nec_f_prefix_length in Hle. lia.
Qed.

(** If the start comes back after d > 0 steps, it comes back after every
    multiple of d. *)
Lemma nec_f_orbit_periodic : forall f s0 d k,
  nec_f_orbit f d s0 = s0 -> nec_f_orbit f (k * d) s0 = s0.
Proof.
  intros f s0 d k Hd. induction k as [| k IH]; [reflexivity |].
  replace (S k * d) with (k * d + d) by lia.
  rewrite nec_f_orbit_add, Hd, IH. reflexivity.
Qed.

(** A start whose flag is down cannot come back to a run whose flag is up
    from some point on. *)
Lemma nec_f_start_never_returns : forall f s0 N d,
  cert s0 = false ->
  (forall n, N <= n -> cert (nec_f_orbit f n s0) = true) ->
  0 < d -> nec_f_orbit f d s0 <> s0.
Proof.
  intros f s0 N d H0 Hup Hd Hret.
  pose proof (Hup (N * d)) as H. rewrite nec_f_orbit_periodic in H by exact Hret.
  rewrite H0 in H. assert (N <= N * d) by nia. discriminate H. exact H1.
Qed.

(** Walking a coincidence back towards the start finds the merge: the start
    itself can't come back, so somewhere two different states land together. *)
Lemma nec_f_walk_back : forall f s0 N p q,
  cert s0 = false ->
  (forall n, N <= n -> cert (nec_f_orbit f n s0) = true) ->
  p < q -> nec_f_orbit f p s0 = nec_f_orbit f q s0 ->
  exists m n, m < q /\ n < q /\ nec_f_orbit f m s0 <> nec_f_orbit f n s0 /\
              f (nec_f_orbit f m s0) = f (nec_f_orbit f n s0).
Proof.
  intros f s0 N p. induction p as [| p IH]; intros q H0 Hup Hpq E.
  - exfalso. apply (nec_f_start_never_returns f s0 N q H0 Hup); [lia |].
    symmetry. exact E.
  - destruct q as [| q]; [lia |].
    destruct (eq_dec (nec_f_orbit f p s0) (nec_f_orbit f q s0)) as [Eq | Ne].
    + destruct (IH q H0 Hup ltac:(lia) Eq) as [m [n [Hm [Hn Hmn]]]].
      exists m, n. split; [lia | split; [lia | exact Hmn]].
    + exists p, q. split; [lia | split; [lia | split; [exact Ne | exact E]]].
Qed.

(** The main fact: the map merges two different states of the orbit. *)
Theorem nec_f_orbit_merges_visited : forall f (all : list X) s0 N,
  @finite_states X all ->
  cert s0 = false ->
  (forall n, N <= n -> cert (nec_f_orbit f n s0) = true) ->
  exists m n, nec_f_orbit f m s0 <> nec_f_orbit f n s0 /\
              f (nec_f_orbit f m s0) = f (nec_f_orbit f n s0).
Proof.
  intros f all s0 N Hfin H0 Hup.
  destruct (nec_f_orbit_repeats f all s0 Hfin) as [p [q [Hpq He]]].
  destruct (nec_f_walk_back f s0 N p q H0 Hup Hpq He) as [m [n [_ [_ Hmn]]]].
  exists m, n. exact Hmn.
Qed.

End Orbit.

Arguments nec_f_orbit {X} f n s0.

(** * One move repeated, and a closed machine *)

Section Moves.

Variables (X I : Type).
Variable eq_dec : forall a b : X, {a = b} + {a <> b}.
Variable step : X -> I -> X.
Variable cert : X -> bool.

(** One move i, repeated from s0. *)
Theorem nec_f_repeat_merges_visited : forall (all : list X) i s0 N,
  @finite_states X all ->
  cert s0 = false ->
  (forall n, N <= n -> cert (nec_f_orbit (fun s => step s i) n s0) = true) ->
  exists m n,
    nec_f_orbit (fun s => step s i) m s0 <> nec_f_orbit (fun s => step s i) n s0 /\
    step (nec_f_orbit (fun s => step s i) m s0) i = step (nec_f_orbit (fun s => step s i) n s0) i.
Proof.
  intros all i s0 N Hfin H0 Hup.
  exact (nec_f_orbit_merges_visited X eq_dec cert (fun s => step s i) all s0 N Hfin H0 Hup).
Qed.

(** A closed machine: the next move is picked from the state. *)
Theorem nec_f_closed_merges_visited : forall (all : list X) (pick : X -> I) s0 N,
  @finite_states X all ->
  cert s0 = false ->
  (forall n, N <= n -> cert (nec_f_orbit (fun s => step s (pick s)) n s0) = true) ->
  exists m n,
    let a := nec_f_orbit (fun s => step s (pick s)) m s0 in
    let b := nec_f_orbit (fun s => step s (pick s)) n s0 in
    a <> b /\ step a (pick a) = step b (pick b).
Proof.
  intros all pick s0 N Hfin H0 Hup.
  exact (nec_f_orbit_merges_visited X eq_dec cert (fun s => step s (pick s)) all s0 N Hfin H0 Hup).
Qed.

(** * A word of moves, repeated *)

Definition nec_f_run (w : list I) (s : X) : X := fold_left step w s.

Lemma nec_f_run_app : forall u v s, nec_f_run (u ++ v) s = nec_f_run v (nec_f_run u s).
Proof. intros u v s. unfold nec_f_run. apply fold_left_app. Qed.

(** n repetitions of the word. *)
Fixpoint nec_f_reps (w : list I) (n : nat) : list I :=
  match n with 0 => [] | S k => nec_f_reps w k ++ w end.

Lemma nec_f_reps_orbit : forall w n s0,
  nec_f_run (nec_f_reps w n) s0 = nec_f_orbit (nec_f_run w) n s0.
Proof.
  intros w n s0. induction n as [| n IH]; [reflexivity |].
  simpl. rewrite nec_f_run_app, IH. reflexivity.
Qed.

(** If a word sends two different states to one, its first letter where the
    two paths meet merges two different states. *)
Lemma nec_f_word_first_meet : forall w a b,
  a <> b -> nec_f_run w a = nec_f_run w b ->
  exists u c v, w = u ++ c :: v /\
    nec_f_run u a <> nec_f_run u b /\
    step (nec_f_run u a) c = step (nec_f_run u b) c.
Proof.
  intros w. induction w as [| c w IH]; intros a b Hne E.
  - exfalso. exact (Hne E).
  - destruct (eq_dec (step a c) (step b c)) as [Ec | Nc].
    + exists [], c, w. split; [reflexivity | split; [exact Hne | exact Ec]].
    + destruct (IH (step a c) (step b c) Nc E) as [u [c' [v [Hw [Hu Hc]]]]].
      exists (c :: u), c', v. split; [simpl; rewrite Hw; reflexivity | split; [exact Hu | exact Hc]].
Qed.

Theorem nec_f_word_merges_visited : forall (all : list X) w s0 N,
  @finite_states X all ->
  cert s0 = false ->
  (forall n, N <= n -> cert (nec_f_run (nec_f_reps w n) s0) = true) ->
  exists m n u c v,
    w = u ++ c :: v /\
    nec_f_run (nec_f_reps w m ++ u) s0 <> nec_f_run (nec_f_reps w n ++ u) s0 /\
    step (nec_f_run (nec_f_reps w m ++ u) s0) c = step (nec_f_run (nec_f_reps w n ++ u) s0) c.
Proof.
  intros all w s0 N Hfin H0 Hup.
  assert (Hup' : forall n, N <= n -> cert (nec_f_orbit (nec_f_run w) n s0) = true).
  { intros n Hn. rewrite <- nec_f_reps_orbit. exact (Hup n Hn). }
  destruct (nec_f_orbit_merges_visited X eq_dec cert (nec_f_run w) all s0 N Hfin H0 Hup')
    as [m [n [Hne E]]].
  destruct (nec_f_word_first_meet w _ _ Hne E) as [u [c [v [Hw [Hu Hc]]]]].
  exists m, n, u, c, v. rewrite !nec_f_run_app, !nec_f_reps_orbit.
  split; [exact Hw | split; [exact Hu | exact Hc]].
Qed.

End Moves.

(** * Moves picked from outside: no merge is forced *)

(** Two states, false reading no and true reading yes; move true swaps,
    move false does nothing. *)
Definition nec_f_out_step (s : bool) (m : bool) : bool := if m then negb s else s.

Theorem nec_f_outside_moves_no_merge :
  (forall n, nec_f_run bool bool nec_f_out_step (true :: repeat false n) false = true) /\
  (forall m a b, nec_f_out_step a m = nec_f_out_step b m -> a = b).
Proof.
  split.
  - intro n. unfold nec_f_run. simpl. induction n as [| n IH]; [reflexivity |].
    simpl. exact IH.
  - intros [] [] []; simpl; congruence.
Qed.

Print Assumptions nec_f_orbit_merges_visited.
Print Assumptions nec_f_repeat_merges_visited.
Print Assumptions nec_f_closed_merges_visited.
Print Assumptions nec_f_word_merges_visited.
Print Assumptions nec_f_outside_moves_no_merge.
