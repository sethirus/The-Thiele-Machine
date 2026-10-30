(* Chapter twenty-two: two machines side by side; a run with branching steps; listing what a reading that
   never turns off accepts. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.

(* ---------- Bolting two together ---------- *)
Section Pair.
  Variables SA SB MA MB : Type.
  Variable stepA : SA -> MA -> SA.
  Variable stepB : SB -> MB -> SB.
  Variable costA : MA -> nat.
  Variable costB : MB -> nat.
  Variable rA : SA -> bool.
  Variable rB : SB -> bool.
  Hypothesis A_never_falls : forall s m, rA s = true -> rA (stepA s m) = true.
  Hypothesis B_never_falls : forall s m, rB s = true -> rB (stepB s m) = true.
  Hypothesis A_toll : forall s m, rA s = false -> rA (stepA s m) = true -> 1 <= costA m.
  Hypothesis B_toll : forall s m, rB s = false -> rB (stepB s m) = true -> 1 <= costB m.

  Definition pmove := (MA + MB)%type.
  Definition pstep (p : SA * SB) (m : pmove) : SA * SB :=
    match m with inl a => (stepA (fst p) a, snd p) | inr b => (fst p, stepB (snd p) b) end.
  Definition pcost (m : pmove) := match m with inl a => costA a | inr b => costB b end.
  Definition either (p : SA * SB) := rA (fst p) || rB (snd p).
  Definition both (p : SA * SB) := rA (fst p) && rB (snd p).

  Theorem either_keeps_toll : forall p m,
      (either p = true -> either (pstep p m) = true) /\
      (either p = false -> either (pstep p m) = true -> 1 <= pcost m).
  Proof.
    intros [x y] [a|b]; unfold either; simpl; split; intro H.
    - apply orb_true_iff in H as [H|H]; apply orb_true_iff; [left; apply A_never_falls | right]; auto.
    - apply orb_false_iff in H as [H1 H2]. intro H'. rewrite H2, orb_false_r in H'. apply (A_toll x); auto.
    - apply orb_true_iff in H as [H|H]; apply orb_true_iff; [left | right; apply B_never_falls]; auto.
    - apply orb_false_iff in H as [H1 H2]. intro H'. rewrite H1 in H'. simpl in H'. apply (B_toll y); auto.
  Qed.

  Theorem both_keeps_toll : forall p m,
      (both p = true -> both (pstep p m) = true) /\
      (both p = false -> both (pstep p m) = true -> 1 <= pcost m).
  Proof.
    intros [x y] [a|b]; unfold both; simpl; split; intro H.
    - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split; [apply A_never_falls|]; auto.
    - intro H'. apply andb_true_iff in H' as [H1 H2]. destruct (rA x) eqn:Rx.
      + rewrite H2 in H. simpl in H. discriminate.
      + apply (A_toll x); auto.
    - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split; [|apply B_never_falls]; auto.
    - intro H'. apply andb_true_iff in H' as [H1 H2]. destruct (rB y) eqn:Ry.
      + rewrite H1 in H. simpl in H. discriminate.
      + apply (B_toll y); auto.
  Qed.

  Fixpoint prun (p : SA * SB) (ms : list pmove) := match ms with [] => p | m :: r => prun (pstep p m) r end.
  Fixpoint ptotal (ms : list pmove) := match ms with [] => 0 | m :: r => pcost m + ptotal r end.
  Fixpoint acost (ms : list pmove) := match ms with [] => 0 | inl a :: r => costA a + acost r | inr _ :: r => acost r end.
  Fixpoint bcost (ms : list pmove) := match ms with [] => 0 | inr b :: r => costB b + bcost r | inl _ :: r => bcost r end.

  Lemma total_split : forall ms, ptotal ms = acost ms + bcost ms.
  Proof. induction ms as [|[a|b] r IH]; simpl; lia. Qed.

  Lemma a_part_pays : forall ms p, rA (fst p) = false -> rA (fst (prun p ms)) = true -> 1 <= acost ms.
  Proof.
    induction ms as [|[a|b] r IH]; intros [x y] H1 H2; simpl in *; [congruence| |].
    - destruct (rA (stepA x a)) eqn:R.
      + pose proof (A_toll x a H1 R). lia.
      + specialize (IH (stepA x a, y) R H2). lia.
    - exact (IH (x, stepB y b) H1 H2).
  Qed.
  Lemma b_part_pays : forall ms p, rB (snd p) = false -> rB (snd (prun p ms)) = true -> 1 <= bcost ms.
  Proof.
    induction ms as [|[a|b] r IH]; intros [x y] H1 H2; simpl in *; [congruence| |].
    - exact (IH (stepA x a, y) H1 H2).
    - destruct (rB (stepB y b)) eqn:R.
      + pose proof (B_toll y b H1 R). lia.
      + specialize (IH (x, stepB y b) R H2). lia.
  Qed.

  Theorem both_from_clean_costs_two : forall ms p, rA (fst p) = false -> rB (snd p) = false ->
      both (prun p ms) = true -> 2 <= ptotal ms.
  Proof.
    intros ms p HA HB H. unfold both in H. apply andb_true_iff in H as [H1 H2].
    rewrite total_split. pose proof (a_part_pays ms p HA H1). pose proof (b_part_pays ms p HB H2). lia.
  Qed.
End Pair.

(* "the first is up and the second is down" can come down *)
Example first_not_second_falls :
  let r := fun p : bool * bool => fst p && negb (snd p) in r (true, false) = true /\ r (true, true) = false.
Proof. split; reflexivity. Qed.

(* ---------- Steps that branch: one run, after the raise ---------- *)
Section BranchingRun.
  Variable X : Type.
  Hypothesis eq_dec : forall a b : X, {a = b} + {a <> b}.
  Variable x : nat -> X.                 (* the run: the state at each time, however its choices fell *)
  Variable read : X -> bool.
  Variable k : nat.                      (* the reading goes up on the step into time k *)
  Hypothesis Hk : 1 <= k.
  Hypothesis before : read (x (k - 1)) = false.
  Hypothesis after : forall n, k <= n -> read (x n) = true.

  Theorem repeat_after_raise_merges : forall i j, k <= i -> i < j -> x i = x j ->
      exists p q, x p <> x q /\ x (S p) = x (S q).
  Proof.
    intros i j Hi Hij E.
    set (D := i - (k - 1)).
    (* walking back d steps from i and j; at d = D the earlier state reads no and the later reads yes *)
    assert (Walk : forall n d, D - d = n -> d <= D -> x (i - d) = x (j - d) ->
              exists p q, x p <> x q /\ x (S p) = x (S q)).
    { induction n as [|n IH]; intros d Hn Hd Ed.
      - exfalso. assert (d = D) by lia. subst d. unfold D in Ed.
        replace (i - (i - (k - 1))) with (k - 1) in Ed by lia.
        assert (read (x (k - 1)) = read (x (j - (i - (k - 1))))) by (rewrite Ed; reflexivity).
        rewrite before, after in H by lia. discriminate.
      - destruct (eq_dec (x (i - S d)) (x (j - S d))) as [Eq | Ne].
        + apply (IH (S d)); [lia | lia | exact Eq].
        + exists (i - S d), (j - S d). split; [exact Ne|].
          replace (S (i - S d)) with (i - d) by lia. replace (S (j - S d)) with (j - d) by lia. exact Ed. }
    apply (Walk D 0); [lia | lia | rewrite !Nat.sub_0_r; exact E].
  Qed.
End BranchingRun.

(* ---------- Listing what a reading that never turns off accepts ---------- *)
Section Listing.
  Variable reads_yes : nat -> nat -> bool.    (* input, steps run -> the reading after that many steps *)
  Hypothesis never_off : forall x n, reads_yes x n = true -> reads_yes x (S n) = true.

  Lemma stays_on : forall x n m, n <= m -> reads_yes x n = true -> reads_yes x m = true.
  Proof. intros x n m H. induction H; auto. Qed.

  Definition accepted (x : nat) := exists n, reads_yes x n = true.
  (* round m: run every input below m for m steps, taking turns, and write down the ones reading yes *)
  Definition listed (m : nat) : list nat := filter (fun x => reads_yes x m) (seq 0 m).

  Theorem listing_lists_exactly_the_accepted : forall x, accepted x <-> exists m, In x (listed m).
  Proof.
    intro x. unfold accepted, listed. split.
    - intros [n Hn]. exists (S (max n x)). apply filter_In. split.
      + apply in_seq. lia.
      + apply (stays_on x n); [lia | exact Hn].
    - intros [m Hm]. apply filter_In in Hm as [_ Hm]. exists m. exact Hm.
  Qed.
End Listing.

(* a reading that falls: yes while program n runs, no for good once it stops; it reads yes for good
   exactly on the programs that never stop *)
Definition falls (stop_time : option nat) (step : nat) : bool :=
  match stop_time with None => true | Some t => Nat.ltb step t end.
Lemma falls_yes_forever_iff_never_stops : forall st,
    (forall n, falls st n = true) <-> st = None.
Proof.
  intros [t|]; simpl; split; intro H; try reflexivity; try discriminate.
  specialize (H t). rewrite Nat.ltb_irrefl in H. discriminate.
Qed.

Print Assumptions either_keeps_toll.
Print Assumptions both_keeps_toll.
Print Assumptions both_from_clean_costs_two.
Print Assumptions repeat_after_raise_merges.
Print Assumptions listing_lists_exactly_the_accepted.

(* ---------- Turing's model lets a table rub out a mark, or print it, with no check ---------- *)
Section TuringMarks.
  Variables Q Sym : Type.
  Inductive dir := L | R.
  Definition table := Q -> Sym -> Q * Sym * dir.
  (* change one entry to write any symbol you like: still a table of the model *)
  Definition set_entry (t : table) (q : Q) (s w : Sym) (eq_q : forall a b : Q, {a = b} + {a <> b})
    (eq_s : forall a b : Sym, {a = b} + {a <> b}) : table :=
    fun q' s' => if eq_q q q' then if eq_s s s' then let '(q2, _, d) := t q' s' in (q2, w, d) else t q' s' else t q' s'.
  Theorem any_mark_can_be_written : forall eq_q eq_s (t : table) q s w,
      let '(_, w', _) := set_entry t q s w eq_q eq_s q s in w' = w.
  Proof.
    intros eq_q eq_s t q s w. unfold set_entry.
    destruct (eq_q q q) as [_|N]; [|congruence]. destruct (eq_s s s) as [_|N]; [|congruence].
    destruct (t q s) as [[q2 w0] d]. reflexivity.
  Qed.
End TuringMarks.
Print Assumptions any_mark_can_be_written.
