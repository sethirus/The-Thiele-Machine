(** Scan invariant and the last-occurrence list selected by the real scanner.
    These are bounded data-correctness lemmas connected to actual update maps.
    They do not assert whole-loop scheduling, retirement, or uniqueness. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart NormalizationSteps.
From Coq Require Import List Bool Arith Lia String.
Import ListNotations.
Open Scope string_scope.

Definition coupling_pair := (word 32 * word 32)%type.
Definition coupling_pair_eq_dec : forall x y : coupling_pair, {x=y}+{x<>y}.
Proof. decide equality; apply weq. Defined.
Definition coupling_pair_eqb (x y : coupling_pair) :=
 andb (word_eqb (fst x) (fst y)) (word_eqb (snd x) (snd y)).
Definition table_pair (src dst : PairTable) (k : nat) : coupling_pair :=
 (src (pair_index (natToWord 5 k)), dst (pair_index (natToWord 5 k))).
Definition table_slice src dst lo count := map (table_pair src dst) (seq lo count).
Definition scan_seen src dst i lo count :=
 existsb (fun k => scan_match (natToWord 5 i) (natToWord 5 k) src dst)
 (seq lo count).

Lemma coupling_pair_eqb_true : forall x y, coupling_pair_eqb x y = true <-> x=y.
Proof.
 intros [a b] [c d]. unfold coupling_pair_eqb, word_eqb; simpl.
 destruct (weq a c); destruct (weq b d); subst; simpl; split; intros; try congruence.
Qed.
Lemma scan_match_pair : forall src dst i k,
 scan_match (natToWord 5 i) (natToWord 5 k) src dst =
 coupling_pair_eqb (table_pair src dst i) (table_pair src dst k).
Proof. reflexivity. Qed.
Lemma scan_seen_empty : forall src dst i lo, scan_seen src dst i lo 0 = false.
Proof. reflexivity. Qed.
Lemma scan_seen_extend : forall src dst i lo count,
 scan_seen src dst i lo (S count) =
 orb (scan_seen src dst i lo count)
     (scan_match (natToWord 5 i) (natToWord 5 (lo+count)) src dst).
Proof.
 intros. unfold scan_seen. rewrite seq_S, existsb_app. simpl.
 rewrite orb_false_r. reflexivity.
Qed.
Lemma scan_seen_iff : forall src dst i lo count,
 scan_seen src dst i lo count = true <->
 exists k, (lo <= k < lo+count)%nat /\ table_pair src dst i = table_pair src dst k.
Proof.
 intros. unfold scan_seen. rewrite existsb_exists. split.
 - intros [k [Hk Hmatch]]. exists k. rewrite in_seq in Hk.
   split; [exact Hk|]. rewrite scan_match_pair in Hmatch.
   apply coupling_pair_eqb_true; exact Hmatch.
 - intros [k [Hk Heq]]. exists k. split; [apply in_seq; exact Hk|].
   rewrite scan_match_pair. apply coupling_pair_eqb_true; exact Heq.
Qed.
Lemma scan_seen_slice : forall src dst i lo count,
 scan_seen src dst i lo count = true <->
 In (table_pair src dst i) (table_slice src dst lo count).
Proof.
 intros. rewrite scan_seen_iff. unfold table_slice. rewrite in_map_iff.
 split; intros [k [H1 H2]]; exists k; split.
 - symmetry; exact H2.
 - apply in_seq; exact H1.
 - apply in_seq; exact H2.
 - symmetry; exact H1.
Qed.

Lemma bounded_word_ltb : forall j e, (j<32)%nat -> (e<32)%nat ->
 word_ltb (natToWord 5 j) (natToWord 5 e) = Nat.ltb j e.
Proof.
 intros j e Hj He. unfold word_ltb.
 destruct (wlt_dec (natToWord 5 j) (natToWord 5 e)) as [Hlt|Hnlt].
 - apply wordToNat_lt1 in Hlt.
   rewrite !wordToNat_natToWord_2 in Hlt by assumption.
   symmetry. apply Nat.ltb_lt; exact Hlt.
 - symmetry. apply Nat.ltb_ge. apply Nat.nlt_ge. intro Hlt. apply Hnlt.
   apply wordToNat_lt2. rewrite !wordToNat_natToWord_2 by assumption. exact Hlt.
Qed.

(** The invariant counts exactly the candidates already visited. The write
    equation is for the actual scan action's update map, unioned with old
    registers. The final scan at j=e changes phase without reading a new pair
    into the duplicate flag. *)
Theorem normalization_scan_extends_seen : forall old src dst i lo count e,
 (lo+count < e)%nat -> (e<=16)%nat ->
 M.find "mc_duplicate"
 (M.union (normalization_scan_updates (natToWord 5 i)
   (natToWord 5 (lo+count)) (natToWord 5 e)
   (scan_seen src dst i lo count) src dst) old) =
 Some (regbool (scan_seen src dst i lo (S count))).
Proof.
 intros old src dst i lo count e Hrange He.
 rewrite M.find_union. unfold normalization_scan_updates.
 rewrite M.find_add_1 by reflexivity.
 rewrite bounded_word_ltb by lia.
 rewrite (proj2 (Nat.ltb_lt _ _) Hrange). simpl.
 rewrite scan_seen_extend. reflexivity.
Qed.
Theorem normalization_scan_terminal_seen : forall old src dst i lo count e,
 (lo+count=e)%nat -> (e<=16)%nat ->
 M.find "mc_duplicate"
 (M.union (normalization_scan_updates (natToWord 5 i)
   (natToWord 5 e) (natToWord 5 e)
   (scan_seen src dst i lo count) src dst) old) =
 Some (regbool (scan_seen src dst i lo count)).
Proof.
 intros. rewrite M.find_union. unfold normalization_scan_updates.
 rewrite M.find_add_1 by reflexivity.
 rewrite bounded_word_ltb by lia. rewrite Nat.ltb_irrefl, andb_false_l, orb_false_r.
 reflexivity.
Qed.
Theorem normalization_scan_terminal_phase : forall old src dst i e dup,
 (e<=16)%nat ->
 M.find "mc_phase"
 (M.union (normalization_scan_updates (natToWord 5 i)
   (natToWord 5 e) (natToWord 5 e) dup src dst) old) =
 Some (reg4 (natToWord 4 9)).
Proof.
 intros. rewrite M.find_union. unfold normalization_scan_updates.
 repeat rewrite M.find_add_2 by discriminate.
 rewrite M.find_add_1 by reflexivity.
 rewrite bounded_word_ltb by lia. rewrite Nat.ltb_irrefl. reflexivity.
Qed.

Definition retained_indices src dst lo count endpoint :=
 filter (fun i => negb (scan_seen src dst i (S i) (endpoint-S i))) (seq lo count).
Definition retained_pairs src dst lo count :=
 map (table_pair src dst) (retained_indices src dst lo count (lo+count)).

(** Coq's nodup keeps the last occurrence. Thus the scanner's omit-when-a-
    later-match-exists decision selects exactly that list, in original order.
    Connecting the successive emitted prefix to this list remains a separate
    whole-loop invariant. *)
Theorem normalization_retained_pairs_nodup : forall src dst lo count,
 retained_pairs src dst lo count =
 nodup coupling_pair_eq_dec (table_slice src dst lo count).
Proof.
 intros src dst lo count. revert lo. induction count as [|count IH]; intro lo.
 - reflexivity.
 - unfold retained_pairs, retained_indices, table_slice in *. simpl seq.
   simpl filter. simpl map. simpl nodup.
   replace (lo + S count - S lo)%nat with count by lia.
   replace (lo + S count)%nat with (S lo + count)%nat by lia.
   specialize (IH (S lo)). simpl Nat.add in IH. simpl Nat.sub in IH.
   destruct (scan_seen src dst lo (S lo) count) eqn:Hseen; simpl.
   + apply scan_seen_slice in Hseen. unfold table_slice in Hseen.
     destruct (in_dec coupling_pair_eq_dec (table_pair src dst lo)
       (map (table_pair src dst) (seq (S lo) count))); [apply IH|contradiction].
   + destruct (in_dec coupling_pair_eq_dec (table_pair src dst lo)
       (map (table_pair src dst) (seq (S lo) count))) as [Hin|Hnot].
     * exfalso. apply (proj2 (scan_seen_slice src dst lo (S lo) count)) in Hin.
       congruence.
     * f_equal. apply IH.
Qed.
Corollary normalization_retained_pairs_nodup_property : forall src dst lo count,
 NoDup (retained_pairs src dst lo count).
Proof. intros. rewrite normalization_retained_pairs_nodup. apply NoDup_nodup. Qed.
Corollary normalization_retained_pairs_membership : forall src dst lo count p,
 In p (retained_pairs src dst lo count) <-> In p (table_slice src dst lo count).
Proof. intros. rewrite normalization_retained_pairs_nodup. apply nodup_In. Qed.

Lemma scan_seen_agrees : forall src dst src' dst' i lo count,
 table_pair src dst i = table_pair src' dst' i ->
 (forall k, (lo<=k<lo+count)%nat -> table_pair src dst k = table_pair src' dst' k) ->
 scan_seen src dst i lo count = scan_seen src' dst' i lo count.
Proof.
 intros src dst src' dst' i lo count Hi. induction count as [|count IH]; intro Hrange.
 - reflexivity.
 - rewrite !scan_seen_extend. rewrite IH by (intros; apply Hrange; lia).
   rewrite !scan_match_pair, Hi, Hrange by lia. reflexivity.
Qed.

Definition emitted_table (table : PairTable) i out (dup : bool) :=
 if dup then table else put_vector table (pair_index (natToWord 5 out))
    (table (pair_index (natToWord 5 i))).
Lemma emitted_table_is_actual_src_update : forall old src dst i out e dup,
 M.find "coupling_pair_src_table"
 (M.union (normalization_emit_updates (natToWord 5 i) (natToWord 5 e)
   (natToWord 5 out) dup src dst) old) =
 Some (regpairs (emitted_table src i out dup)).
Proof.
 intros. rewrite M.find_union. unfold normalization_emit_updates.
 rewrite M.find_add_1 by reflexivity. reflexivity.
Qed.
Lemma emitted_table_is_actual_dst_update : forall old src dst i out e dup,
 M.find "coupling_pair_dst_table"
 (M.union (normalization_emit_updates (natToWord 5 i) (natToWord 5 e)
   (natToWord 5 out) dup src dst) old) =
 Some (regpairs (emitted_table dst i out dup)).
Proof.
 intros. rewrite M.find_union. unfold normalization_emit_updates.
 rewrite M.find_add_2 by discriminate. rewrite M.find_add_1 by reflexivity.
 reflexivity.
Qed.
Lemma table_pair_after_emit_unread : forall src dst i out dup k,
 (out<=i<k)%nat -> (k<16)%nat ->
 table_pair (emitted_table src i out dup) (emitted_table dst i out dup) k =
 table_pair src dst k.
Proof.
 intros. unfold table_pair, emitted_table.
 rewrite !normalization_emit_preserves_unread_suffix by lia. reflexivity.
Qed.
Theorem normalization_emit_preserves_future_scan : forall src dst i out dup candidate lo count,
 (out<=i<candidate)%nat -> (candidate<16)%nat -> (i<lo)%nat -> (lo+count<=16)%nat ->
 scan_seen (emitted_table src i out dup) (emitted_table dst i out dup) candidate lo count =
 scan_seen src dst candidate lo count.
Proof.
 intros. apply scan_seen_agrees.
 - apply table_pair_after_emit_unread; lia.
 - intros. apply table_pair_after_emit_unread; lia.
Qed.

Theorem normalization_scan_advances_pointer : forall old src dst i lo count e,
 (lo+count<=16)%nat ->
 M.find "mc_j"
 (M.union (normalization_scan_updates (natToWord 5 i)
   (natToWord 5 (lo+count)) (natToWord 5 e)
   (scan_seen src dst i lo count) src dst) old) =
 Some (reg5 (natToWord 5 (lo+S count))).
Proof.
 intros. rewrite M.find_union. unfold normalization_scan_updates.
 rewrite M.find_add_2 by discriminate. rewrite M.find_add_1 by reflexivity.
 rewrite <- natToWord_plus. replace (lo+count+1)%nat with (lo+S count)%nat by lia.
 reflexivity.
Qed.
Theorem normalization_scan_continues_phase : forall old src dst i j e dup,
 (j<e)%nat -> (e<=16)%nat ->
 M.find "mc_phase"
 (M.union (normalization_scan_updates (natToWord 5 i)
   (natToWord 5 j) (natToWord 5 e) dup src dst) old) =
 Some (reg4 (natToWord 4 8)).
Proof.
 intros. rewrite M.find_union. unfold normalization_scan_updates.
 repeat rewrite M.find_add_2 by discriminate.
 rewrite M.find_add_1 by reflexivity.
 rewrite bounded_word_ltb by lia. rewrite (proj2 (Nat.ltb_lt _ _) H). reflexivity.
Qed.

(** At the terminal scan, the emit rule's duplicate flag selects precisely
    the head contribution in the nodup recurrence. This relates its boolean
    choice to list content without assuming that the whole loop has run. *)
Theorem normalization_terminal_emit_selection : forall src dst i count,
 List.app (if scan_seen src dst i (S i) count then nil else cons (table_pair src dst i) nil)
 (nodup coupling_pair_eq_dec (table_slice src dst (S i) count)) =
 nodup coupling_pair_eq_dec (table_slice src dst i (S count)).
Proof.
 intros src dst i count. unfold table_slice at 2. simpl seq. simpl map. simpl nodup.
 destruct (scan_seen src dst i (S i) count) eqn:Hseen; simpl.
 - apply scan_seen_slice in Hseen. unfold table_slice in Hseen.
   destruct (in_dec coupling_pair_eq_dec (table_pair src dst i)
     (map (table_pair src dst) (seq (S i) count))); [reflexivity|contradiction].
 - destruct (in_dec coupling_pair_eq_dec (table_pair src dst i)
     (map (table_pair src dst) (seq (S i) count))) as [Hin|Hnot]; [|reflexivity].
   apply (proj2 (scan_seen_slice src dst i (S i) count)) in Hin. congruence.
Qed.
