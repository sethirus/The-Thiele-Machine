(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file is the noisy
   form of the chairs theorem, stated on a finite Markov kernel over the rationals with no
   dependence on the certification-system kernel. Both directions of the noisy dichotomy:
   a kernel that can raise a permanent reading (a closed set reachable from outside) does not
   preserve the uniform spread, and strictly raises the collision weight of the uniform spread in
   one step; a kernel that preserves the uniform spread never raises the collision weight of any
   spread. Collision weight: the sum of the squared probabilities, least for the uniform spread.
   The Shannon form of the strict drop is in GibbsGap.v. *)
Require Import QArith List Lia.
Import ListNotations.
Local Open Scope Q_scope.

Definition Qsum (l : list Q) : Q := fold_right Qplus 0 l.


Lemma Qsum_map_plus : forall {A} (f g : A -> Q) l,
  Qsum (map (fun x => f x + g x) l) == Qsum (map f l) + Qsum (map g l).
Proof. induction l; simpl. ring. rewrite IHl. ring. Qed.

Lemma Qsum_map_ext : forall {A} (f g : A -> Q) l, (forall x, In x l -> f x == g x) ->
  Qsum (map f l) == Qsum (map g l).
Proof. induction l; simpl; intros. reflexivity. rewrite (H a) by auto. rewrite IHl by auto. reflexivity. Qed.

Lemma Qsum_swap : forall {A B} (f : A -> B -> Q) la lb,
  Qsum (map (fun a => Qsum (map (fun b => f a b) lb)) la)
  == Qsum (map (fun b => Qsum (map (fun a => f a b) la)) lb).
Proof.
  induction la; intros; simpl.
  - induction lb; simpl. reflexivity. rewrite <- IHlb. ring.
  - rewrite IHla. rewrite <- Qsum_map_plus. apply Qsum_map_ext. intros. simpl. reflexivity.
Qed.

Lemma Qsum_nonneg : forall l, (forall x, In x l -> 0 <= x) -> 0 <= Qsum l.
Proof.
  induction l; simpl; intros. apply Qle_refl.
  assert (0 <= a) by auto. assert (0 <= Qsum l) by auto.
  setoid_replace 0 with (0 + 0) by ring. apply Qplus_le_compat; auto.
Qed.

Lemma Qsum_zero_each : forall l, (forall x, In x l -> 0 <= x) -> Qsum l == 0 ->
  forall x, In x l -> x == 0.
Proof.
  induction l; simpl; intros H Hs x Hx. contradiction.
  assert (Ha : 0 <= a) by auto. assert (Hl : 0 <= Qsum l) by (apply Qsum_nonneg; auto).
  destruct Hx as [-> | Hx].
  - apply Qle_antisym; auto. setoid_replace x with (x + Qsum l - Qsum l) by ring.
    rewrite Hs. setoid_replace (0 - Qsum l) with (- Qsum l) by ring.
    apply Qopp_le_compat in Hl. setoid_replace (- 0) with 0 in Hl by ring. auto.
  - apply IHl; auto. apply Qle_antisym; auto.
    setoid_replace (Qsum l) with (a + Qsum l - a) by ring. rewrite Hs.
    setoid_replace (0 - a) with (- a) by ring.
    apply Qopp_le_compat in Ha. setoid_replace (- 0) with 0 in Ha by ring. auto.
Qed.

Lemma Qsum_map_zero : forall {A} (l : list A), Qsum (map (fun _ => 0) l) == 0.
Proof. induction l; simpl. reflexivity. rewrite IHl. ring. Qed.

Lemma Qsum_map_scale : forall {A} (k : Q) (f : A -> Q) l,
  Qsum (map (fun x => k * f x) l) == k * Qsum (map f l).
Proof. induction l; simpl. ring. rewrite IHl. ring. Qed.

Lemma len_cons : forall {A} (a : A) l, inject_Z (Z.of_nat (length (a :: l))) == inject_Z (Z.of_nat (length l)) + 1.
Proof. intros. simpl length. rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite inject_Z_plus. reflexivity. Qed.

Lemma Qsum_pos_of_member : forall l, (forall x, In x l -> 0 <= x) -> (exists x, In x l /\ 0 < x) -> 0 < Qsum l.
Proof.
  induction l; simpl; intros Hn [x [Hx Hp]]. contradiction.
  destruct Hx as [-> | Hx].
  - assert (0 <= Qsum l) by (apply Qsum_nonneg; auto). setoid_replace 0 with (0+0) by ring. apply Qplus_lt_le_compat; auto.
  - assert (0 < Qsum l) by (apply IHl; auto; exists x; auto). assert (0 <= a) by auto.
    setoid_replace 0 with (0+0) by ring. setoid_replace (a + Qsum l) with (Qsum l + a) by ring.
    apply Qplus_lt_le_compat; auto.
Qed.

Lemma Qsq_nonneg : forall x, 0 <= x * x.
Proof. intro x. destruct (Qlt_le_dec x 0).
  - setoid_replace (x*x) with ((-x)*(-x)) by ring. apply Qlt_le_weak in q. apply Qopp_le_compat in q.
    setoid_replace (-0) with 0 in q by ring. apply Qmult_le_0_compat; auto.
  - apply Qmult_le_0_compat; auto. Qed.

Lemma Qsq_pos : forall x, ~ x == 0 -> 0 < x * x.
Proof. intros x Hx. destruct (Qlt_le_dec x 0).
  - setoid_replace (x*x) with ((-x)*(-x)) by ring. apply Qopp_lt_compat in q.
    setoid_replace (-0) with 0 in q by ring. apply Qmult_lt_0_compat; auto.
  - destruct (Qle_lt_or_eq _ _ q). apply Qmult_lt_0_compat; auto. exfalso. apply Hx. symmetry. auto. Qed.

Lemma Qsum_le : forall {A} (f g : A -> Q) l, (forall x, In x l -> f x <= g x) -> Qsum (map f l) <= Qsum (map g l).
Proof. induction l; simpl; intros. apply Qle_refl. apply Qplus_le_compat; auto. Qed.

(* ---- No entry from outside under a uniform-preserving kernel ---- *)
Section Noisy.
Variable n : nat.
Variable P : nat -> nat -> Q.
Variable Y : nat -> bool.
Definition idx := seq 0 n.
Definition ind (b : bool) : Q := if b then 1 else 0.
Hypothesis nonneg : forall i j, 0 <= P i j.
Hypothesis col_stoch : forall j, In j idx -> Qsum (map (fun i => P i j) idx) == 1.
Hypothesis closed : forall i, In i idx -> Y i = true -> Qsum (map (fun j => ind (Y j) * P i j) idx) == 1.

(* mass flowing into Y from row i *)
Definition into (i : nat) := Qsum (map (fun j => ind (Y j) * P i j) idx).
Definition sizeY := Qsum (map (fun j => ind (Y j)) idx).

Lemma total_into : Qsum (map into idx) == sizeY.
Proof.
  unfold into, sizeY. rewrite Qsum_swap. apply Qsum_map_ext. intros j Hj.
  destruct (Y j) eqn:E; unfold ind.
  - transitivity (Qsum (map (fun i => P i j) idx)).
    + apply Qsum_map_ext. intros. ring.
    + apply col_stoch; auto.
  - transitivity (Qsum (map (fun _ : nat => 0) idx)).
    + apply Qsum_map_ext. intros. ring.
    + apply Qsum_map_zero.
Qed.

Lemma split_rows : Qsum (map into idx) ==
  Qsum (map (fun i => ind (Y i) * into i) idx) + Qsum (map (fun i => ind (negb (Y i)) * into i) idx).
Proof.
  rewrite <- Qsum_map_plus. apply Qsum_map_ext. intros i _. destruct (Y i); unfold ind; simpl; ring.
Qed.

Lemma inside_rows : Qsum (map (fun i => ind (Y i) * into i) idx) == sizeY.
Proof.
  unfold sizeY. apply Qsum_map_ext. intros i Hi. destruct (Y i) eqn:E; unfold ind.
  - rewrite (closed i Hi E). ring.
  - ring.
Qed.

Lemma into_nonneg : forall i, 0 <= into i.
Proof. intro i. unfold into. apply Qsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as [j [<- _]].
  destruct (Y j); unfold ind. setoid_replace (1 * P i j) with (P i j) by ring. auto. setoid_replace (0 * P i j) with 0 by ring. apply Qle_refl. Qed.

Theorem no_entry_from_outside : forall i, In i idx -> Y i = false -> into i == 0.
Proof.
  intros i Hi Hf.
  assert (Hout : Qsum (map (fun i => ind (negb (Y i)) * into i) idx) == 0).
  { assert (H1 := total_into). rewrite split_rows in H1. rewrite inside_rows in H1.
    setoid_replace (Qsum (map (fun i => ind (negb (Y i)) * into i) idx))
      with (sizeY + Qsum (map (fun i => ind (negb (Y i)) * into i) idx) - sizeY) by ring.
    rewrite H1. ring. }
  assert (Hterm : ind (negb (Y i)) * into i == 0).
  { apply (Qsum_zero_each (map (fun i => ind (negb (Y i)) * into i) idx)); auto.
    - intros x Hx. apply in_map_iff in Hx. destruct Hx as [k [<- _]]. destruct (Y k); unfold ind; simpl.
      setoid_replace (0 * into k) with 0 by ring. apply Qle_refl.
      setoid_replace (1 * into k) with (into k) by ring. apply into_nonneg.
    - apply in_map_iff. exists i. auto. }
  rewrite Hf in Hterm. unfold ind in Hterm. simpl in Hterm.
  setoid_replace (into i) with (1 * into i) by ring. auto.
Qed.

Theorem noisy_chairs : forall i j, In i idx -> In j idx -> Y i = false -> Y j = true -> P i j == 0.
Proof.
  intros i j Hi Hj Hf Ht.
  assert (H0 := no_entry_from_outside i Hi Hf). unfold into in H0.
  assert (ind (Y j) * P i j == 0).
  { apply (Qsum_zero_each (map (fun j => ind (Y j) * P i j) idx)); auto.
    - intros x Hx. apply in_map_iff in Hx. destruct Hx as [k [<- _]]. destruct (Y k); unfold ind.
      setoid_replace (1 * P i k) with (P i k) by ring. auto.
      setoid_replace (0 * P i k) with 0 by ring. apply Qle_refl.
    - apply in_map_iff. exists j. auto. }
  rewrite Ht in H. unfold ind in H. setoid_replace (P i j) with (1 * P i j) by ring. auto.
Qed.
End Noisy.

(* ---- A raise forces some column sum off 1 ---- *)
Section Raise.
Variable n : nat.
Variable P : nat -> nat -> Q.
Variable Y : nat -> bool.
Hypothesis nonneg : forall i j, 0 <= P i j.
Hypothesis row_stoch : forall i, In i (idx n) -> Qsum (map (fun j => P i j) (idx n)) == 1.
Hypothesis closed : forall i, In i (idx n) -> Y i = true -> Qsum (map (fun j => ind (Y j) * P i j) (idx n)) == 1.
Definition colsum (j : nat) : Q := Qsum (map (fun i => P i j) (idx n)).

Lemma colsums_total : Qsum (map colsum (idx n)) == inject_Z (Z.of_nat n).
Proof.
  unfold colsum. rewrite Qsum_swap.
  transitivity (Qsum (map (fun _ : nat => 1) (idx n))).
  - apply Qsum_map_ext. intros i Hi. apply row_stoch. auto.
  - assert (E : forall l : list nat, Qsum (map (fun _ : nat => 1) l) == inject_Z (Z.of_nat (length l))).
    { induction l. reflexivity. simpl map. simpl Qsum. rewrite IHl. simpl length. rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite inject_Z_plus. ring. }
    rewrite E. unfold idx. rewrite seq_length. reflexivity.
Qed.

Theorem raise_breaks_uniform : forall i j, In i (idx n) -> In j (idx n) -> Y i = false -> Y j = true -> 0 < P i j ->
  exists j', In j' (idx n) /\ ~ colsum j' == 1.
Proof.
  intros i j Hi Hj Hf Ht Hpos.
  destruct (existsb (fun j' => negb (Qeq_bool (colsum j') 1)) (idx n)) eqn:E.
  - apply existsb_exists in E. destruct E as [j' [Hj' Hb]].
    exists j'. split; auto. intro Heq. apply Qeq_bool_iff in Heq. rewrite Heq in Hb. discriminate.
  - exfalso.
    assert (Hcol : forall j', In j' (idx n) -> Qsum (map (fun i => P i j') (idx n)) == 1).
    { intros j' Hj'. apply Qeq_bool_iff.
      destruct (Qeq_bool (colsum j') 1) eqn:E2; auto.
      assert (existsb (fun j' => negb (Qeq_bool (colsum j') 1)) (idx n) = true).
      { apply existsb_exists. exists j'. split; auto. rewrite E2. reflexivity. }
      congruence. }
    pose proof (noisy_chairs n P Y nonneg Hcol closed i j Hi Hj Hf Ht) as H0.
    rewrite H0 in Hpos. apply (Qlt_irrefl 0). auto.
Qed.
End Raise.

(* ---- Strict concentration of the uniform spread when a column sum is off 1 ---- *)
Section Conc.
Variable c : list Q.                 (* the column sums *)
Let N := inject_Z (Z.of_nat (length c)).
Hypothesis total : Qsum c == N.      (* rows sum to 1 *)

(* sum (c_j - 1)^2 = sum c_j^2 - 2 sum c_j + N = sum c_j^2 - N *)
Lemma expand : Qsum (map (fun x => (x - 1) * (x - 1)) c) == Qsum (map (fun x => x * x) c) - N.
Proof.
  assert (E : forall l, Qsum (map (fun x => (x - 1) * (x - 1)) l)
     == Qsum (map (fun x => x * x) l) - 2 * Qsum l + inject_Z (Z.of_nat (length l))).
  { induction l. simpl. ring. rewrite len_cons. simpl. rewrite IHl. ring. }
  rewrite E. rewrite total. unfold N. ring.
Qed.

Theorem raise_concentrates : (exists x, In x c /\ ~ x == 1) ->
  N < Qsum (map (fun x => x * x) c).
Proof.
  intros [x [Hx Hne]].
  assert (Hpos : 0 < Qsum (map (fun x => (x - 1) * (x - 1)) c)).
  { apply Qsum_pos_of_member.
    - intros y Hy. apply in_map_iff in Hy. destruct Hy as [z [<- _]]. apply Qsq_nonneg.
    - exists ((x - 1) * (x - 1)). split. apply in_map_iff. exists x. auto.
      apply Qsq_pos. intro H. apply Hne. setoid_replace x with ((x - 1) + 1) by ring. rewrite H. ring. }
  rewrite expand in Hpos.
  setoid_replace N with (N + 0) by ring.
  setoid_replace (Qsum (map (fun x => x * x) c)) with (N + (Qsum (map (fun x => x * x) c) - N)) by ring.
  apply Qplus_lt_r. auto.
Qed.

(* and the uniform spread is exactly the collision floor: all columns 1 gives sum = N *)
Theorem uniform_floor : (forall x, In x c -> x == 1) -> Qsum (map (fun x => x * x) c) == N.
Proof.
  intro H.
  assert (E : forall l, (forall x, In x l -> x == 1) -> Qsum (map (fun x => x * x) l) == inject_Z (Z.of_nat (length l))).
  { induction l; intros Hl. simpl. reflexivity.
    rewrite len_cons. simpl. rewrite (Hl a) by (simpl; auto). rewrite IHl by (intros; apply Hl; simpl; auto). ring. }
  apply E. auto.
Qed.
End Conc.

(* ---- The converse: a uniform-preserving kernel never concentrates any spread ---- *)
Section NoConc.
Variable n : nat.
Variable P : nat -> nat -> Q.
Variable q : nat -> Q.
Hypothesis nonneg : forall i j, 0 <= P i j.
Hypothesis row_stoch : forall i, In i (idx n) -> Qsum (map (fun j => P i j) (idx n)) == 1.
Hypothesis col_stoch : forall j, In j (idx n) -> Qsum (map (fun i => P i j) (idx n)) == 1.

Definition push (j : nat) : Q := Qsum (map (fun i => q i * P i j) (idx n)).

(* weighted variance identity: sum_i P_ij (q_i - m)^2 = sum_i P_ij q_i^2 - m^2 when m = push j and column j sums to 1 *)
Lemma variance_identity : forall j, In j (idx n) ->
  Qsum (map (fun i => P i j * ((q i - push j) * (q i - push j))) (idx n))
  == Qsum (map (fun i => P i j * (q i * q i)) (idx n)) - push j * push j.
Proof.
  intros j Hj.
  transitivity (Qsum (map (fun i => P i j * (q i * q i) + ((-2 * push j) * (q i * P i j) + (push j * push j) * P i j)) (idx n))).
  { apply Qsum_map_ext. intros. ring. }
  rewrite Qsum_map_plus. rewrite Qsum_map_plus. rewrite Qsum_map_scale. rewrite Qsum_map_scale.
  fold (push j). rewrite (col_stoch j Hj). ring.
Qed.

Lemma column_jensen : forall j, In j (idx n) ->
  push j * push j <= Qsum (map (fun i => P i j * (q i * q i)) (idx n)).
Proof.
  intros j Hj.
  assert (0 <= Qsum (map (fun i => P i j * ((q i - push j) * (q i - push j))) (idx n))).
  { apply Qsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as [i [<- _]].
    apply Qmult_le_0_compat. apply nonneg. apply Qsq_nonneg. }
  rewrite variance_identity in H by auto.
  setoid_replace (push j * push j) with (push j * push j + 0) by ring.
  setoid_replace (Qsum (map (fun i => P i j * (q i * q i)) (idx n)))
    with (push j * push j + (Qsum (map (fun i => P i j * (q i * q i)) (idx n)) - push j * push j)) by ring.
  apply Qplus_le_r. auto.
Qed.

Theorem no_merge_no_concentration :
  Qsum (map (fun j => push j * push j) (idx n)) <= Qsum (map (fun i => q i * q i) (idx n)).
Proof.
  apply Qle_trans with (y := Qsum (map (fun j => Qsum (map (fun i => P i j * (q i * q i)) (idx n))) (idx n))).
  - apply Qsum_le. intros j Hj. apply column_jensen. auto.
  - rewrite Qsum_swap.
    apply Qle_lteq. right.
    apply Qsum_map_ext. intros i Hi.
    transitivity (Qsum (map (fun j => (q i * q i) * P i j) (idx n))).
    { apply Qsum_map_ext. intros. ring. }
    rewrite Qsum_map_scale. rewrite (row_stoch i Hi). ring.
Qed.
End NoConc.

(* ---- The chain in one statement ---- *)
Section Chain.
Variable n : nat.
Variable P : nat -> nat -> Q.
Variable Y : nat -> bool.
Hypothesis nonneg : forall i j, 0 <= P i j.
Hypothesis row_stoch : forall i, In i (idx n) -> Qsum (map (fun j => P i j) (idx n)) == 1.
Hypothesis closed : forall i, In i (idx n) -> Y i = true ->
  Qsum (map (fun j => ind (Y j) * P i j) (idx n)) == 1.

Let c := map (colsum n P) (idx n).   (* N times the spread after one step from uniform *)

Theorem raise_concentrates_uniform :
  forall i j, In i (idx n) -> In j (idx n) -> Y i = false -> Y j = true -> 0 < P i j ->
  inject_Z (Z.of_nat n) < Qsum (map (fun x => x * x) c).
Proof.
  intros i j Hi Hj Hf Ht Hpos.
  assert (Htot : Qsum c == inject_Z (Z.of_nat (length c))).
  { unfold c. rewrite map_length. unfold idx. rewrite seq_length.
    apply (colsums_total n P row_stoch). }
  assert (Hlen : inject_Z (Z.of_nat n) == inject_Z (Z.of_nat (length c))).
  { unfold c. rewrite map_length. unfold idx. rewrite seq_length. reflexivity. }
  rewrite Hlen.
  apply (raise_concentrates c Htot).
  destruct (raise_breaks_uniform n P Y nonneg closed i j Hi Hj Hf Ht Hpos) as [j' [Hj' Hne]].
  exists (colsum n P j'). split; auto. apply in_map_iff. exists j'. auto.
Qed.
End Chain.
