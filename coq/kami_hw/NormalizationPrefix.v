(** Emitted-prefix and unread-suffix invariant for the actual emit update.
    Every preservation theorem uses [emitted_table], whose register-map
    equations are proved in NormalizationLoop. Scheduling the scan and emit
    actions into the full physical normalization loop remains separate. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart
  NormalizationSteps NormalizationLoop.
From Coq Require Import List Bool Arith Lia String.
Import ListNotations.
Open Scope string_scope.

Definition selected_prefix src dst b i e :=
 map (table_pair src dst) (retained_indices src dst b (i-b) e).
Definition next_output (out : nat) (dup : bool) := if dup then out else S out.

Definition normalization_prefix_invariant rawsrc rawdst src dst b i out e :=
 (b <= out <= i /\ i <= e /\ e <= 16)%nat /\
 table_slice src dst b (out-b) = selected_prefix rawsrc rawdst b i e /\
 (forall k, (i<=k<e)%nat -> table_pair src dst k = table_pair rawsrc rawdst k).

Lemma selected_prefix_start : forall src dst b e,
 selected_prefix src dst b b e = nil.
Proof. intros. unfold selected_prefix. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma selected_prefix_succ : forall src dst b i e,
 (b<=i)%nat ->
 selected_prefix src dst b (S i) e =
 List.app (selected_prefix src dst b i e)
   (if scan_seen src dst i (S i) (e-S i)
    then nil else cons (table_pair src dst i) nil).
Proof.
 intros src dst b i e Hbi. unfold selected_prefix, retained_indices.
 replace (S i-b)%nat with (S (i-b)) by lia.
 rewrite seq_S, filter_app, map_app.
 replace (b+(i-b))%nat with i by lia. simpl.
 destruct (scan_seen src dst i (S i) (e-S i)); reflexivity.
Qed.

Lemma table_slice_succ : forall src dst b count,
 table_slice src dst b (S count) =
 List.app (table_slice src dst b count) (cons (table_pair src dst (b+count)) nil).
Proof. intros. unfold table_slice. rewrite seq_S, map_app. reflexivity. Qed.

Lemma table_pair_after_emit_other : forall src dst i out dup k,
 (out<16)%nat -> (k<16)%nat -> k<>out ->
 table_pair (emitted_table src i out dup) (emitted_table dst i out dup) k =
 table_pair src dst k.
Proof.
 intros. unfold table_pair, emitted_table.
 rewrite !normalization_emit_preserves_other_pair by assumption. reflexivity.
Qed.

Lemma table_pair_after_emit_target : forall src dst i out,
 table_pair (emitted_table src i out false) (emitted_table dst i out false) out =
 table_pair src dst i.
Proof.
 intros. unfold table_pair, emitted_table, put_vector.
 destruct (weq (pair_index (natToWord 5 out)) (pair_index (natToWord 5 out)));
 [reflexivity|contradiction].
Qed.

Lemma table_slice_emit_prefix : forall src dst b i out dup,
 (b<=out)%nat -> (out<16)%nat ->
 table_slice (emitted_table src i out dup) (emitted_table dst i out dup) b (out-b) =
 table_slice src dst b (out-b).
Proof.
 intros src dst b i out dup Hbo Ho. unfold table_slice. apply map_ext_in.
 intros k Hk. apply in_seq in Hk. apply table_pair_after_emit_other; lia.
Qed.

Theorem normalization_prefix_established : forall src dst b e,
 (b<=e<=16)%nat ->
 normalization_prefix_invariant src dst src dst b b b e.
Proof.
 intros src dst b e Hb. unfold normalization_prefix_invariant.
 split; [lia|]. split; [rewrite selected_prefix_start, Nat.sub_diag; reflexivity|].
 intros; reflexivity.
Qed.

Lemma normalization_prefix_scan_agrees : forall rawsrc rawdst src dst b i out e,
 normalization_prefix_invariant rawsrc rawdst src dst b i out e -> (i<e)%nat ->
 scan_seen src dst i (S i) (e-S i) =
 scan_seen rawsrc rawdst i (S i) (e-S i).
Proof.
 intros rawsrc rawdst src dst b i out e [Hb [Hp Hs]] Hi.
 apply scan_seen_agrees; [apply Hs; lia|]. intros; apply Hs; lia.
Qed.

Theorem normalization_prefix_preserved : forall rawsrc rawdst src dst b i out e,
 normalization_prefix_invariant rawsrc rawdst src dst b i out e -> (i<e)%nat ->
 let dup := scan_seen src dst i (S i) (e-S i) in
 normalization_prefix_invariant rawsrc rawdst
   (emitted_table src i out dup) (emitted_table dst i out dup)
   b (S i) (next_output out dup) e.
Proof.
 intros rawsrc rawdst src dst b i out e Hinv Hi.
 pose proof (normalization_prefix_scan_agrees _ _ _ _ _ _ _ _ Hinv Hi) as Hdup.
 destruct Hinv as [Hb [Hp Hs]]. cbv zeta.
 unfold normalization_prefix_invariant. split.
 - unfold next_output. destruct (scan_seen src dst i (S i) (e-S i)); lia.
 - split.
   + rewrite selected_prefix_succ by lia. rewrite <- Hdup.
     destruct (scan_seen src dst i (S i) (e-S i)) eqn:Hd.
     * unfold next_output. rewrite app_nil_r. exact Hp.
     * unfold next_output. replace (S out-b)%nat with (S (out-b)) by lia.
       rewrite table_slice_succ, table_slice_emit_prefix by lia.
       replace (b+(out-b))%nat with out by lia.
       rewrite table_pair_after_emit_target, Hp, Hs by lia. reflexivity.
   + intros k Hk. rewrite table_pair_after_emit_unread by lia. apply Hs; lia.
Qed.

(** This is the preservation statement at the actual register-map boundary.
    The source/destination writes are those of [normalization_emit_updates],
    not an independent list-normalization implementation. *)
Theorem normalization_actual_emit_preserves_prefix : forall old rawsrc rawdst src dst b i out e,
 normalization_prefix_invariant rawsrc rawdst src dst b i out e -> (i<e)%nat ->
 let dup := scan_seen src dst i (S i) (e-S i) in
 let updates := normalization_emit_updates (natToWord 5 i) (natToWord 5 e)
   (natToWord 5 out) dup src dst in
 exists src' dst',
 M.find "coupling_pair_src_table" (M.union updates old) = Some (regpairs src') /\
 M.find "coupling_pair_dst_table" (M.union updates old) = Some (regpairs dst') /\
 normalization_prefix_invariant rawsrc rawdst src' dst'
   b (S i) (next_output out dup) e.
Proof.
 intros old rawsrc rawdst src dst b i out e Hinv Hi. cbv zeta.
 eexists; eexists. split; [apply emitted_table_is_actual_src_update|].
 split; [apply emitted_table_is_actual_dst_update|].
 apply normalization_prefix_preserved; assumption.
Qed.

Theorem normalization_prefix_terminal_nodup : forall rawsrc rawdst src dst b out e,
 normalization_prefix_invariant rawsrc rawdst src dst b e out e ->
 table_slice src dst b (out-b) =
 nodup coupling_pair_eq_dec (table_slice rawsrc rawdst b (e-b)).
Proof.
 intros rawsrc rawdst src dst b out e [Hb [Hp Hs]]. rewrite Hp.
 unfold selected_prefix.
 pose proof (normalization_retained_pairs_nodup rawsrc rawdst b (e-b)) as Hn.
 unfold retained_pairs in Hn. replace (b+(e-b))%nat with e in Hn by lia.
 exact Hn.
Qed.

Corollary normalization_prefix_terminal_nodup_property : forall rawsrc rawdst src dst b out e,
 normalization_prefix_invariant rawsrc rawdst src dst b e out e ->
 NoDup (table_slice src dst b (out-b)).
Proof.
 intros. rewrite (normalization_prefix_terminal_nodup _ _ _ _ _ _ _ H).
 apply NoDup_nodup.
Qed.

Lemma normalization_emit_output_nat : forall out dup,
 emit_next (natToWord 5 out) dup = natToWord 5 (next_output out dup).
Proof.
 intros out dup. unfold emit_next, next_output. destruct dup; [reflexivity|].
 rewrite <- natToWord_plus. replace (out+1)%nat with (S out) by lia. reflexivity.
Qed.

Theorem normalization_actual_emit_output_pointer : forall old src dst i out e dup,
 M.find "mc_norm_ptr"
 (M.union (normalization_emit_updates (natToWord 5 i) (natToWord 5 e)
   (natToWord 5 out) dup src dst) old) =
 Some (reg5 (natToWord 5 (next_output out dup))).
Proof.
 intros. rewrite M.find_union. unfold normalization_emit_updates.
 repeat rewrite M.find_add_2 by discriminate.
 rewrite M.find_add_1 by reflexivity. rewrite normalization_emit_output_nat.
 reflexivity.
Qed.

Theorem normalization_actual_emit_candidate_pointer : forall old src dst i out e dup,
 M.find "mc_i"
 (M.union (normalization_emit_updates (natToWord 5 i) (natToWord 5 e)
   (natToWord 5 out) dup src dst) old) =
 Some (reg5 (natToWord 5 (S i))).
Proof.
 intros. rewrite M.find_union. unfold normalization_emit_updates.
 repeat rewrite M.find_add_2 by discriminate.
 rewrite M.find_add_1 by reflexivity. rewrite <- natToWord_plus.
 replace (i+1)%nat with (S i) by lia. reflexivity.
Qed.

Theorem normalization_actual_emit_terminal_end : forall old src dst i out dup,
 M.find "mc_write_ptr"
 (M.union (normalization_emit_updates (natToWord 5 i) (natToWord 5 (S i))
   (natToWord 5 out) dup src dst) old) =
 Some (reg5 (natToWord 5 (next_output out dup))).
Proof.
 intros. rewrite M.find_union. unfold normalization_emit_updates.
 repeat rewrite M.find_add_2 by discriminate.
 rewrite M.find_add_1 by reflexivity. rewrite <- natToWord_plus.
 replace (i+1)%nat with (S i) by lia. unfold word_eqb.
 destruct (weq (natToWord 5 (S i)) (natToWord 5 (S i))); [|contradiction].
 rewrite normalization_emit_output_nat. reflexivity.
Qed.

Corollary normalization_prefix_output_in_range : forall rawsrc rawdst src dst b i out e,
 normalization_prefix_invariant rawsrc rawdst src dst b i out e -> (i<e)%nat ->
 forall dup, wordToNat (natToWord 5 (next_output out dup)) = next_output out dup.
Proof.
 intros rawsrc rawdst src dst b i out e [Hb Hrest] Hi dup.
 apply wordToNat_natToWord_2. change (next_output out dup<32)%nat.
 unfold next_output. destruct dup; lia.
Qed.
