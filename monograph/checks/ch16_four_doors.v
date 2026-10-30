(* The four doors, under two conditions: the guard sees only the boxes (its glance can't tell
   the passing value from the failing one), and every box only ever goes up.
   Rounds: write the passing value, check, ask; write the failing value, ask.
   If no ask is ever wrong, twice the unlocked rounds is at most the number of boxes plus one. *)
From Coq Require Import List Bool Lia Arith.
Import ListNotations.

(* boxes: a list of bits; c <= d when every box up in c is up in d *)
Fixpoint le (c d : list bool) : Prop :=
  match c, d with
  | [], [] => True
  | x :: c', y :: d' => (x = true -> y = true) /\ le c' d'
  | _, _ => False
  end.

Fixpoint count (c : list bool) : nat :=
  match c with [] => 0 | x :: c' => (if x then 1 else 0) + count c' end.

Lemma le_refl : forall c, le c c.
Proof. induction c; simpl; auto. Qed.

Lemma le_trans : forall a b c, le a b -> le b c -> le a c.
Proof.
  induction a as [|x a IH]; destruct b as [|y b]; destruct c as [|z c]; simpl; try tauto.
  intros [H1 H2] [H3 H4]. split; eauto.
Qed.

Lemma le_length : forall c d, le c d -> length c = length d.
Proof.
  induction c as [|x c IH]; destruct d as [|y d]; simpl; try tauto.
  intros [_ H]. f_equal. auto.
Qed.

Lemma le_count : forall c d, le c d -> count c <= count d.
Proof.
  induction c as [|x c IH]; destruct d as [|y d]; simpl; try tauto; try lia.
  intros [H1 H2]. specialize (IH d H2).
  destruct x, y; try lia; try (specialize (H1 eq_refl); discriminate).
Qed.

(* if c <= d and they differ, d has strictly more boxes up *)
Lemma le_count_strict : forall c d, le c d -> c <> d -> count c < count d.
Proof.
  induction c as [|x c IH]; destruct d as [|y d]; simpl; try tauto.
  intros [H1 H2] Hne.
  destruct (list_eq_dec bool_dec c d) as [E | Ne].
  - subst. destruct x, y; try (exfalso; apply Hne; reflexivity);
      try (specialize (H1 eq_refl); discriminate); lia.
  - specialize (IH d H2 Ne).
    destruct x, y; try lia; try (specialize (H1 eq_refl); discriminate).
Qed.

Lemma count_le_length : forall c, count c <= length c.
Proof. induction c as [|x c IH]; simpl; [lia | destruct x; lia]. Qed.

Section Doors.
  Variable guard : list bool -> bool.             (* sees only the boxes *)
  Variables write_good check write_bad : list bool -> list bool.
  Hypothesis up_wg : forall c, le c (write_good c).
  Hypothesis up_ck : forall c, le c (check c).
  Hypothesis up_wb : forall c, le c (write_bad c).

  Definition after_check c := check (write_good c).
  Definition after_round c := write_bad (after_check c).

  (* n rounds from c: (unlocked rounds, some ask wrong, final boxes) *)
  Fixpoint run (n : nat) (c : list bool) : nat * bool * list bool :=
    match n with
    | 0 => (0, false, c)
    | S n' =>
        let c1 := after_check c in
        let c2 := write_bad c1 in
        let '(u, w, f) := run n' c2 in
        ((if guard c1 then 1 else 0) + u, guard c2 || w, f)
    end.

  Lemma run_le : forall n c, le c (snd (run n c)).
  Proof.
    induction n as [|n IH]; intro c; simpl; [apply le_refl|].
    destruct (run n (write_bad (after_check c))) as [[u w] f] eqn:R. simpl.
    specialize (IH (write_bad (after_check c))). rewrite R in IH. simpl in IH.
    eapply le_trans; [|exact IH].
    eapply le_trans; [apply up_wg|]. eapply le_trans; [apply up_ck|]. apply up_wb.
  Qed.

  (* the invariant: with no wrong ask, 2u <= boxes raised + [guard was up at the start] *)
  Lemma rounds_bound : forall n c u f,
      run n c = (u, false, f) ->
      2 * u <= count f - count c + (if guard c then 1 else 0) /\ count c <= count f.
  Proof.
    induction n as [|n IH]; intros c u f H; simpl in H.
    - inversion H; subst. destruct (guard f); lia.
    - set (c1 := after_check c) in *. set (c2 := write_bad c1) in *.
      destruct (run n c2) as [[u' w'] f'] eqn:R.
      inversion H as [[Hu Hw Hf]]. subst f'.
      apply orb_false_iff in Hw as [G2 W]. subst w'.
      destruct (IH c2 u' f R) as [IHb IHle]. rewrite G2 in IHb.
      assert (L1 : le c c1) by (unfold c1, after_check; eapply le_trans; [apply up_wg | apply up_ck]).
      assert (L2 : le c1 c2) by (unfold c2; apply up_wb).
      pose proof (le_count _ _ L1) as K1. pose proof (le_count _ _ L2) as K2.
      destruct (guard c1) eqn:G1.
      + (* an unlocked round: c1 differs from c2, and from c unless the guard was already up *)
        assert (N12 : c1 <> c2) by (intro E; rewrite E in G1; congruence).
        pose proof (le_count_strict _ _ L2 N12) as S12.
        destruct (guard c) eqn:G0.
        * split; lia.
        * assert (N01 : c <> c1) by (intro E; rewrite <- E in G1; congruence).
          pose proof (le_count_strict _ _ L1 N01) as S01. split; lia.
      + destruct (guard c); split; lia.
  Qed.

  Theorem four_doors_budget : forall n c u f,
      run n c = (u, false, f) -> 2 * u <= length c + 1.
  Proof.
    intros n c u f H.
    destruct (rounds_bound n c u f H) as [B _].
    pose proof (run_le n c) as L. rewrite H in L. simpl in L.
    pose proof (le_length _ _ L) as Len. pose proof (count_le_length f) as Cf.
    destruct (guard c); lia.
  Qed.
End Doors.


(* The conditions can all hold and the bound is reached: machines with only rising boxes, no wrong
   answer, and exactly the most unlocked rounds the theorem allows. *)
Definition set_at (i : nat) (c : list bool) : list bool :=
  firstn i c ++ (match skipn i c with [] => [] | _ :: r => true :: r end).

(* one box: the guard is up while the box is down; the failing write raises it *)
Definition g1 (c : list bool) := match c with [false] => true | _ => false end.
Example one_box_reaches_bound : run g1 (fun c => c) (fun c => c) (set_at 0) 3 [false] = (1, false, [true]).
Proof. reflexivity. Qed.

(* three boxes: the guard is up at zero and at two boxes up. Round one unlocks at the start; the failing
   write raises a box (locked). Round two's check raises a box (unlocked); its failing write raises the
   last box (locked). Two unlocked rounds, never wrong, and 2 * 2 <= 3 + 1. *)
Definition g3 (c : list bool) := Nat.eqb (count c) 0 || Nat.eqb (count c) 2.
Definition raise_next (c : list bool) := match c with
  | [false; false; false] => [true; false; false]
  | [true; false; false] => [true; true; false]
  | [true; true; false] => [true; true; true]
  | _ => c end.
Definition check3 (c : list bool) := if Nat.eqb (count c) 1 then raise_next c else c.
Example three_boxes_reach_bound :
  run g3 (fun c => c) check3 (fun c => if g3 c then raise_next c else c) 4 [false; false; false]
  = (2, false, [true; true; true]).
Proof. reflexivity. Qed.

(* Condition two is doing work: one box that a write can take back down unlocks every round, honestly. *)
Definition toggle_check (c : list bool) := [true].
Definition toggle_clear (c : list bool) := [false].
Definition toggle_guard (c : list bool) := match c with [true] => true | _ => false end.

Fixpoint toggle_run (n : nat) (c : list bool) : nat * bool :=
  match n with
  | 0 => (0, false)
  | S n' => let c1 := toggle_check c in let c2 := toggle_clear c1 in
            let '(u, w) := toggle_run n' c2 in
            ((if toggle_guard c1 then 1 else 0) + u, toggle_guard c2 || w)
  end.

Example toggle_unlocks_every_round : toggle_run 10 [false] = (10, false).
Proof. reflexivity. Qed.

(* ---------- The second door is sound: fresh editions never give a wrong answer ---------- *)
Section FreshEditions.
  Variable P : nat -> bool.                   (* the checked property *)
  Inductive op := Write (a : nat) | Check | Ask.
  Record mstate := { data : nat; edition : nat; boxes : list nat }.
  Definition start := {| data := 0; edition := 0; boxes := [] |}.
  Definition stepm (m : mstate) (o : op) : mstate :=
    match o with
    | Write a => {| data := a; edition := S (edition m); boxes := boxes m |}
    | Check => if P (data m) then {| data := data m; edition := edition m; boxes := edition m :: boxes m |} else m
    | Ask => m
    end.
  Definition fires (m : mstate) := existsb (Nat.eqb (edition m)) (boxes m).
  Fixpoint runm (m : mstate) (prog : list op) : mstate :=
    match prog with [] => m | o :: r => runm (stepm m o) r end.
  Definition inv (m : mstate) := (forall e, In e (boxes m) -> e <= edition m) /\
                                 (In (edition m) (boxes m) -> P (data m) = true).
  Lemma inv_start : inv start. Proof. split; simpl; tauto. Qed.
  Lemma inv_step : forall m o, inv m -> inv (stepm m o).
  Proof.
    intros m o H. destruct o as [a| |]; simpl.
    - destruct H as [B C]. split; simpl.
      + intros e He. specialize (B e He). lia.
      + intro Hin. specialize (B _ Hin). lia.
    - destruct (P (data m)) eqn:Pm.
      + destruct H as [B C]. split; simpl.
        * intros e [He | He]; [lia | apply B; exact He].
        * intros _. exact Pm.
      + exact H.
    - exact H.
  Qed.
  Lemma inv_run : forall prog m, inv m -> inv (runm m prog).
  Proof. induction prog; intros; simpl; auto using inv_step. Qed.
  Theorem fresh_editions_never_wrong : forall prog,
      fires (runm start prog) = true -> P (data (runm start prog)) = true.
  Proof.
    intros prog F. destruct (inv_run prog start inv_start) as [_ C]. apply C.
    unfold fires in F. apply existsb_exists in F as [e [He Ee]].
    apply Nat.eqb_eq in Ee. subst e. exact He.
  Qed.
End FreshEditions.

(* ---------- The first door: editions that wrap around, four moves to a wrong answer ---------- *)
Definition even (x : nat) := Nat.even x.
Definition wstep (m : nat * nat * list nat) (o : op) : nat * nat * list nat :=
  let '(x, v, bs) := m in
  match o with
  | Write a => (a, (S v) mod 2, bs)
  | Check => if even x then (x, v, v :: bs) else (x, v, bs)
  | Ask => (x, v, bs)
  end.
Fixpoint wrun m prog := match prog with [] => m | o :: r => wrun (wstep m o) r end.
Example wrap_four_moves_wrong :
  let '(x, v, bs) := wrun (0, 0, []) [Check; Write 1; Write 3; Ask] in
  existsb (Nat.eqb v) bs = true /\ even x = false.
Proof. vm_compute. split; reflexivity. Qed.

(* ---------- The third door merges twice: at the passing check and at the wipe ---------- *)
Definition t_check (s : bool * bool) := if fst s then (fst s, true) else s.   (* data true passes *)
Definition t_flip_write (s : bool * bool) := (negb (fst s), false).
Example toggle_check_merges : t_check (true, false) = t_check (true, true) /\ (true, false) <> (true, true).
Proof. split; [reflexivity | discriminate]. Qed.
Example toggle_wipe_merges : t_flip_write (false, false) = t_flip_write (false, true) /\ (false, false) <> (false, true).
Proof. split; [reflexivity | discriminate]. Qed.
Lemma flip_alone_one_to_one : forall a b : bool, negb a = negb b -> a = b.
Proof. destruct a, b; simpl; congruence. Qed.

(* ---------- The fourth door's room: keeping every checked value unlocked at once ---------- *)
Section ValueRoom.
  Variable M K : Type.
  Variable mem : (K -> bool) -> M.            (* memory after a set of checked values *)
  Variable guard : M -> K -> bool.            (* reads the memory and the value *)
  Hypothesis unlocks_exactly : forall s k, guard (mem s) k = s k.
  Theorem distinct_sets_distinct_memory : forall s t, mem s = mem t -> forall k, s k = t k.
  Proof. intros s t E k. rewrite <- (unlocks_exactly s k), <- (unlocks_exactly t k), E. reflexivity. Qed.
End ValueRoom.

Print Assumptions fresh_editions_never_wrong.
Print Assumptions distinct_sets_distinct_memory.

Print Assumptions four_doors_budget.
