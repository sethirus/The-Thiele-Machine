(** AxLatch2: two records are one record on a product axis, and a chain of
    k + 1 values needs exactly k bits.

    Results (closed):

      product_pair_is_two_latches   the book's statement that two permanent
                                    records are two latches, each of whose
                                    events may read the other, is the axis
                                    decomposition over the product of two
                                    two-point orders.
      chain_bits_tight              a chain of k + 1 distinct bit vectors of
                                    length k exists, so the bound
                                    [chain_needs_bits_holds] (at most k + 1)
                                    is attained for every k. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import StructuralCore StructuralCoreCover StructuralCoreAnyBase
  StructuralRecordAxis GrowingRecordCore GrowingRecord.
From Kernel Require Import AxCore AxMerge AxLatch.

(** * The product of two orders *)

Definition prod_pre {A B : Type} (P : BPre A) (Q : BPre B) : BPre (A * B).
Proof.
  refine {| bp_leb := fun x y => andb (bp_leb A P (fst x) (fst y))
                                     (bp_leb B Q (snd x) (snd y)) |}.
  - intros [a b]. simpl. rewrite !bp_refl. reflexivity.
  - intros [a b] [a' b'] [a'' b''] H1 H2. simpl in *.
    apply andb_true_iff in H1 as [H1 H1']. apply andb_true_iff in H2 as [H2 H2'].
    rewrite (bp_trans A P _ _ _ H1 H2), (bp_trans B Q _ _ _ H1' H2'). reflexivity.
Defined.

(** * Two records are one record on the product axis *)

Theorem product_pair_is_two_latches : record_pair_is_two_latches.
Proof.
  intros M B C c1 c2 [[f Hf] [_ [_ [Hp1 Hp2]]]].
  set (rec := fun m => (c1 m, c2 m)).
  set (P2 := prod_pre two_pre two_pre).
  assert (Hg : ax_rgrows P2 rec).
  { intro m. unfold bp_le, rec. simpl.
    destruct (c1 m) eqn:E1, (c2 m) eqn:E2; simpl;
      try reflexivity;
      first [rewrite (Hp1 m E1); reflexivity | rewrite (Hp2 m E2); reflexivity |
             rewrite ?(Hp1 m E1), ?(Hp2 m E2); reflexivity]. }
  assert (Hd : ax_rdriven C rec).
  { exists (fun b x => f b (fst x) (snd x)). intro m. unfold rec.
    simpl. rewrite <- (Hf m). reflexivity. }
  destruct (ax_decompose M B C _ P2 rec Hg Hd) as [h Hh].
  exists (fun b r2 => h (true, false) b (false, r2)),
         (fun b r1 => h (false, true) b (r1, false)).
  intro m. pose proof (Hh m (true, false)) as H1. pose proof (Hh m (false, true)) as H2.
  unfold rec in H1, H2. simpl in H1, H2.
  split.
  - destruct (c1 m) eqn:E1.
    + rewrite (Hp1 m E1). reflexivity.
    + simpl in H1 |- *. rewrite andb_true_r in H1. exact H1.
  - destruct (c2 m) eqn:E2.
    + rewrite (Hp2 m E2). reflexivity.
    + simpl in H2 |- *. exact H2.
Qed.

(** * A chain of k + 1 values needs, and is carried by, k bits *)

Definition chain_vec (k j : nat) : list bool := repeat true j ++ repeat false (k - j).

Lemma nth_repeat_false : forall m n, nth n (repeat false m) false = false.
Proof.
  induction m as [| m IH]; intro n; simpl; [destruct n; reflexivity |].
  destruct n; [reflexivity | apply IH].
Qed.

Lemma chain_vec_nth : forall j m n, nth n (repeat true j ++ repeat false m) false = true <-> n < j.
Proof.
  induction j as [| j IH]; intros m n; simpl.
  - rewrite nth_repeat_false. split; intro H; [discriminate | lia].
  - destruct n; simpl.
    + split; [intros _; lia | intros _; reflexivity].
    + rewrite IH. lia.
Qed.

Lemma chain_vec_length : forall k j, j <= k -> length (chain_vec k j) = k.
Proof.
  intros k j H. unfold chain_vec. rewrite app_length, !repeat_length. lia.
Qed.

Lemma chain_vec_le : forall k j, j < k -> bits_le (chain_vec k j) (chain_vec k (S j)).
Proof.
  intros k j H. split.
  - rewrite !chain_vec_length; lia.
  - intro n. unfold chain_vec. rewrite !chain_vec_nth. lia.
Qed.

Lemma chain_vec_inj : forall k j j', j <= k -> j' <= k ->
  chain_vec k j = chain_vec k j' -> j = j'.
Proof.
  intros k j j' Hj Hj' H. unfold chain_vec in H.
  destruct (Nat.lt_trichotomy j j') as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - exfalso. assert (Hn : nth j (repeat true j' ++ repeat false (k - j')) false = true)
      by (apply chain_vec_nth; lia).
    rewrite <- H in Hn. apply chain_vec_nth in Hn. lia.
  - exfalso. assert (Hn : nth j' (repeat true j ++ repeat false (k - j)) false = true)
      by (apply chain_vec_nth; lia).
    rewrite H in Hn. apply chain_vec_nth in Hn. lia.
Qed.

Lemma chain_seq_chain : forall k n j, j + n <= S k ->
  bits_chain (map (chain_vec k) (seq j n)).
Proof.
  intros k n. induction n as [| n IH]; intros j Hj; simpl; [exact I |].
  destruct n as [| n]; [exact I |].
  simpl in IH |- *. split.
  - apply chain_vec_le. lia.
  - apply (IH (S j)). lia.
Qed.

Theorem chain_bits_tight : forall k,
  exists vs : list (list bool),
    Forall (fun v => length v = k) vs /\ bits_chain vs /\ NoDup vs /\ length vs = S k.
Proof.
  intro k. exists (map (chain_vec k) (seq 0 (S k))). split; [| split; [| split]].
  - apply Forall_forall. intros v Hv. apply in_map_iff in Hv as [j [<- Hj]].
    apply in_seq in Hj. apply chain_vec_length. lia.
  - apply chain_seq_chain. lia.
  - apply ax_NoDup_map_inj.
    + intros x y Hx Hy Hxy. apply in_seq in Hx. apply in_seq in Hy.
      apply (chain_vec_inj k x y); [lia | lia | exact Hxy].
    + apply seq_NoDup.
  - rewrite map_length, seq_length. reflexivity.
Qed.

(** The count is exact: at most k + 1 values, and k + 1 are attained. *)
Corollary chain_bits_exact : forall k,
  (forall vs, Forall (fun v => length v = k) vs -> bits_chain vs -> NoDup vs ->
     length vs <= S k) /\
  exists vs, Forall (fun v => length v = k) vs /\ bits_chain vs /\ NoDup vs /\
             length vs = S k.
Proof.
  intro k. split.
  - intros vs H1 H2 H3. exact (chain_needs_bits_holds k vs H1 H2 H3).
  - apply chain_bits_tight.
Qed.

Print Assumptions product_pair_is_two_latches.
Print Assumptions chain_bits_tight.
Print Assumptions chain_bits_exact.
