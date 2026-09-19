(** Selected finite executions of the actual outer normalization loop.
    This is an existence schedule, not a fairness or dispatch-refinement claim. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart
 NormalizationSteps NormalizationLoop NormalizationExecution NormalizationPrefix
 NormalizationScanExecution.
From Coq Require Import List String Bool Arith Lia.
Import ListNotations.
Open Scope string_scope.

Definition outer_footprint := ["mc_duplicate"; "mc_j"; "mc_phase";
 "mc_i"; "mc_norm_ptr"; "mc_write_ptr";
 "coupling_pair_src_table"; "coupling_pair_dst_table"].
Definition outer_frame (old new : RegsT) := forall key,
 ~ In key outer_footprint -> M.find key new = M.find key old.
Definition outer_emitted old src dst i out e :=
 M.union (normalization_emit_updates (natToWord 5 i) (natToWord 5 e)
 (natToWord 5 out) (scan_seen src dst i (S i) (e-S i)) src dst)
 (scan_complete_state src dst i (S i) e false old).

Lemma outer_emitted_frame : forall old src dst i out e,
 outer_frame old (outer_emitted old src dst i out e).
Proof.
 intros old src dst i out e key Hkey. unfold outer_emitted.
 rewrite normalization_emit_frame.
 - apply normalization_scan_complete_frame. unfold outer_footprint in Hkey.
   simpl in *; intuition.
 - unfold outer_footprint in Hkey. simpl in *; intuition.
Qed.

Lemma outer_emit_execution : forall old src dst i out e,
 (i<e)%nat -> (e<=16)%nat ->
 scan_registers old i (S i) e false src dst ->
 M.find "mc_norm_ptr" old = Some (reg5 (natToWord 5 out)) ->
 exists labels, Multistep thieleCore old (outer_emitted old src dst i out e) labels /\
 List.length labels = (e-i+1)%nat.
Proof.
 intros old src dst i out e Hi He Hr Ho.
 exists (normalization_label "mc_normalize_emit" ::
 repeat scan_rule_label (S (e-S i))). split.
 2: { simpl; rewrite repeat_length; lia. }
 unfold outer_emitted. eapply normalization_step_extends_execution.
 - apply normalization_scan_complete_execution; [lia|assumption|exact Hr].
 - apply normalization_emit_actual_substep.
   + apply normalization_scan_complete_phase; assumption.
   + rewrite normalization_scan_complete_frame by (simpl; intuition discriminate).
     destruct Hr; assumption.
   + rewrite normalization_scan_complete_frame by (simpl; intuition discriminate).
     destruct Hr; assumption.
   + rewrite normalization_scan_complete_frame by (simpl; intuition discriminate). exact Ho.
   + rewrite normalization_scan_complete_duplicate by assumption. reflexivity.
   + rewrite normalization_scan_complete_frame by (simpl; intuition discriminate).
     destruct Hr; assumption.
   + rewrite normalization_scan_complete_frame by (simpl; intuition discriminate).
     destruct Hr; assumption.
Qed.

Lemma bounded_word_eqb : forall a b, (a<32)%nat -> (b<32)%nat ->
 word_eqb (natToWord 5 a) (natToWord 5 b) = Nat.eqb a b.
Proof.
 intros a b Ha Hb. unfold word_eqb. destruct (weq _ _) as [H|H].
 - apply (f_equal (@wordToNat 5)) in H. rewrite !wordToNat_natToWord_2 in H by assumption.
   subst; symmetry; apply Nat.eqb_refl.
 - symmetry; apply Nat.eqb_neq. intro E; subst; contradiction.
Qed.

Ltac emit_read := unfold outer_emitted; rewrite M.find_union;
 unfold normalization_emit_updates; repeat rewrite M.find_add_2 by discriminate;
 rewrite M.find_add_1 by reflexivity.

Lemma outer_emitted_phase : forall old src dst i out e,
 (i<e)%nat -> (e<=16)%nat ->
 M.find "mc_phase" (outer_emitted old src dst i out e) =
 Some (reg4 (natToWord 4 (if Nat.eqb (S i) e then 11 else 8))).
Proof.
 intros. emit_read. rewrite <- natToWord_plus.
 replace (i+1)%nat with (S i) by lia. rewrite bounded_word_eqb by lia.
 destruct (Nat.eqb (S i) e); reflexivity.
Qed.
Lemma outer_emitted_end : forall old src dst i out e,
 (i<e)%nat -> (e<=16)%nat ->
 M.find "mc_write_ptr" (outer_emitted old src dst i out e) =
 Some (reg5 (natToWord 5 (if Nat.eqb (S i) e then
 next_output out (scan_seen src dst i (S i) (e-S i)) else e))).
Proof.
 intros. emit_read. rewrite <- natToWord_plus.
 replace (i+1)%nat with (S i) by lia. rewrite bounded_word_eqb by lia.
 rewrite normalization_emit_output_nat. destruct (Nat.eqb (S i) e); reflexivity.
Qed.
Lemma outer_emitted_scan_registers : forall old src dst i out e,
 (S i<e)%nat -> (e<=16)%nat ->
 scan_registers (outer_emitted old src dst i out e) (S i) (S (S i)) e false
 (emitted_table src i out (scan_seen src dst i (S i) (e-S i)))
 (emitted_table dst i out (scan_seen src dst i (S i) (e-S i))).
Proof.
 intros. constructor.
 - rewrite outer_emitted_phase by lia. rewrite (proj2 (Nat.eqb_neq (S i) e) ltac:(lia)); reflexivity.
 - apply normalization_actual_emit_candidate_pointer.
 - emit_read. rewrite <- !natToWord_plus.
   replace (i+1+1)%nat with (S (S i)) by lia. reflexivity.
 - rewrite outer_emitted_end by lia. rewrite (proj2 (Nat.eqb_neq (S i) e) ltac:(lia)); reflexivity.
 - emit_read. reflexivity.
 - apply emitted_table_is_actual_src_update.
 - apply emitted_table_is_actual_dst_update.
Qed.

Lemma normalization_multistep_trans : forall a b c xs ys,
 Multistep thieleCore a b xs -> Multistep thieleCore b c ys ->
 Multistep thieleCore a c (List.app ys xs).
Proof.
 intros a b c xs ys H1 H2. induction H2 as [o1 o2 E|o a0 n Hmulti IH u l Hstep].
 - subst; exact H1.
 - simpl. eapply Multi; [apply IH; exact H1|eassumption].
Qed.

Fixpoint outer_firings (n : nat) : nat :=
 match n with O => O | S k => (S k + 1 + outer_firings k)%nat end.

Theorem normalization_outer_execution : forall remaining old rawsrc rawdst src dst b i out e,
 (e-i=remaining)%nat -> (i<e)%nat ->
 normalization_prefix_invariant rawsrc rawdst src dst b i out e ->
 scan_registers old i (S i) e false src dst ->
 M.find "mc_norm_ptr" old = Some (reg5 (natToWord 5 out)) ->
 exists final labels src' dst' out',
 Multistep thieleCore old final labels /\
 normalization_prefix_invariant rawsrc rawdst src' dst' b e out' e /\
 M.find "mc_phase" final = Some (reg4 (natToWord 4 11)) /\
 M.find "mc_write_ptr" final = Some (reg5 (natToWord 5 out')) /\
 M.find "coupling_pair_src_table" final = Some (regpairs src') /\
 M.find "coupling_pair_dst_table" final = Some (regpairs dst') /\ outer_frame old final /\
 List.length labels = outer_firings remaining.
Proof.
 induction remaining as [|n IH]; intros old rawsrc rawdst src dst b i out e Hn Hi Hinv Hr Ho.
 - lia.
 - pose proof Hinv as Hb. destruct Hb as [Hb _].
   destruct (outer_emit_execution old src dst i out e Hi ltac:(lia) Hr Ho) as [ls [Hex Hlen]].
   pose (dup := scan_seen src dst i (S i) (e-S i)).
   pose (src1 := emitted_table src i out dup).
   pose (dst1 := emitted_table dst i out dup).
   pose (out1 := next_output out dup).
   assert (Hinv1 : normalization_prefix_invariant rawsrc rawdst src1 dst1 b (S i) out1 e).
   { apply normalization_prefix_preserved; assumption. }
   destruct (Nat.eq_dec (S i) e) as [Heq|Hneq].
   + exists (outer_emitted old src dst i out e), ls, src1, dst1, out1.
     split; [exact Hex|]. split; [rewrite Heq in Hinv1; exact Hinv1|].
     split; [rewrite outer_emitted_phase by lia; rewrite Heq, Nat.eqb_refl; reflexivity|].
     split; [rewrite outer_emitted_end by lia; rewrite (proj2 (Nat.eqb_eq _ _) Heq); reflexivity|].
     split; [apply emitted_table_is_actual_src_update|].
     split; [apply emitted_table_is_actual_dst_update|].
     split; [apply outer_emitted_frame|].
     assert (n=0)%nat by lia. subst n. simpl. rewrite Hlen; lia.
   + destruct (IH (outer_emitted old src dst i out e) rawsrc rawdst src1 dst1 b
       (S i) out1 e ltac:(lia) ltac:(lia) Hinv1
       (outer_emitted_scan_registers old src dst i out e ltac:(lia) ltac:(lia))
       (normalization_actual_emit_output_pointer _ _ _ _ _ _ _))
       as [final [labels [src' [dst' [out' [Hrun [Hinv' [Hphase [Hend [Hsrc [Hdst [Hframe Hlength]]]]]]]]]]]].
     exists final, (List.app labels ls), src', dst', out'.
     split; [eapply normalization_multistep_trans; eassumption|].
     split; [exact Hinv'|]. split; [exact Hphase|]. split; [exact Hend|].
     split; [exact Hsrc|]. split; [exact Hdst|].
     split.
     * intros key Hkey. rewrite Hframe by exact Hkey. apply outer_emitted_frame; exact Hkey.
     * rewrite app_length, Hlength, Hlen. simpl; lia.
Qed.

Definition normalization_started old b e :=
 M.union (normalization_start_updates (natToWord 5 b) (natToWord 5 e)) old.
Lemma normalization_started_frame : forall old b e key,
 ~ In key ["mc_i"; "mc_j"; "mc_norm_ptr"; "mc_duplicate"; "mc_phase"] ->
 M.find key (normalization_started old b e) = M.find key old.
Proof.
 intros. unfold normalization_started. rewrite M.find_union.
 unfold normalization_start_updates.
 repeat rewrite M.find_add_2 by (simpl in H; intuition).
 rewrite M.find_empty; reflexivity.
Qed.
Lemma normalization_started_reads : forall old src dst b e,
 (b<e)%nat -> (e<=16)%nat ->
 M.find "mc_write_ptr" old = Some (reg5 (natToWord 5 e)) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 scan_registers (normalization_started old b e) b (S b) e false src dst /\
 M.find "mc_norm_ptr" (normalization_started old b e) = Some (reg5 (natToWord 5 b)).
Proof.
 intros old src dst b e Hb He Hend Hsrc Hdst.
 assert (Hneq : natToWord 5 b <> natToWord 5 e).
 { intro H. apply (f_equal (@wordToNat 5)) in H.
   rewrite !wordToNat_natToWord_2 in H by (simpl; lia). lia. }
 split.
 - constructor.
   + unfold normalization_started. rewrite M.find_union. unfold normalization_start_updates.
     repeat rewrite M.find_add_2 by discriminate. rewrite M.find_add_1 by reflexivity.
     destruct (weq _ _); [contradiction|reflexivity].
   + unfold normalization_started. rewrite M.find_union. unfold normalization_start_updates.
     rewrite M.find_add_1 by reflexivity. reflexivity.
   + unfold normalization_started. rewrite M.find_union. unfold normalization_start_updates.
     rewrite M.find_add_2 by discriminate. rewrite M.find_add_1 by reflexivity.
     rewrite <- natToWord_plus. replace (b+1)%nat with (S b) by lia. reflexivity.
   + rewrite normalization_started_frame by (simpl; intuition discriminate); assumption.
   + unfold normalization_started. rewrite M.find_union. unfold normalization_start_updates.
     repeat rewrite M.find_add_2 by discriminate. rewrite M.find_add_1 by reflexivity. reflexivity.
   + rewrite normalization_started_frame by (simpl; intuition discriminate); assumption.
   + rewrite normalization_started_frame by (simpl; intuition discriminate); assumption.
 - unfold normalization_started. rewrite M.find_union. unfold normalization_start_updates.
   repeat rewrite M.find_add_2 by discriminate. rewrite M.find_add_1 by reflexivity. reflexivity.
Qed.

(** The concrete descriptor tables and allocator pointers are specified by the
    actual six-write commit map. The list result is ordered Coq nodup. *)
Theorem normalization_nonempty_retirement : forall old src dst b e d bases counts valid,
 (b<e)%nat -> (e<=16)%nat ->
 M.find "mc_phase" old = Some (reg4 (natToWord 4 5)) ->
 M.find "mc_write_base" old = Some (reg5 (natToWord 5 b)) ->
 M.find "mc_write_ptr" old = Some (reg5 (natToWord 5 e)) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 M.find "coupling_desc_next_id" old = Some (reg5 d) ->
 M.find "coupling_desc_base_table" old = Some (regbases bases) ->
 M.find "coupling_desc_count_table" old = Some (regcounts counts) ->
 M.find "coupling_desc_valid_table" old = Some (regvalid valid) ->
 exists precommit labels src' dst' out,
 (b<=out<=e)%nat /\
 Multistep thieleCore old
 (M.union (normalization_commit_updates (natToWord 5 b) (natToWord 5 out)
    d bases counts valid) precommit) labels /\
 M.find "mc_phase"
 (M.union (normalization_commit_updates (natToWord 5 b) (natToWord 5 out)
    d bases counts valid) precommit) = Some (reg4 (natToWord 4 0)) /\
 M.find "coupling_pair_src_table" precommit = Some (regpairs src') /\
 M.find "coupling_pair_dst_table" precommit = Some (regpairs dst') /\
 table_slice src' dst' b (out-b) =
 nodup coupling_pair_eq_dec (table_slice src dst b (e-b)) /\
 outer_frame old precommit /\
 List.length labels = (2 + outer_firings (e-b))%nat.
Proof.
 intros old src dst b e d bases counts valid Hb He Hp Hbase Hend Hsrc Hdst Hd Hbs Hcs Hv.
 destruct (normalization_started_reads old src dst b e Hb He Hend Hsrc Hdst) as [Hr Ho].
 assert (Hinv : normalization_prefix_invariant src dst src dst b b b e).
 { split; [lia|]. split.
   - rewrite Nat.sub_diag, selected_prefix_start. reflexivity.
   - intros; reflexivity. }
 destruct (normalization_outer_execution (e-b) (normalization_started old b e)
 src dst src dst b b b e eq_refl Hb Hinv Hr Ho)
 as [pre [ls [src' [dst' [out [Hrun [Hinv' [Hphase [Hend' [Hsrc' [Hdst' [Hframe Hlength]]]]]]]]]]]].
 assert (Hframe0 : outer_frame old pre).
 { intros key Hkey. rewrite Hframe by assumption.
   apply normalization_started_frame. unfold outer_footprint in Hkey; simpl in *; intuition. }
 exists pre, (normalization_label "mc_commit" ::
 List.app ls [normalization_label "mc_normalize_start"]), src', dst', out.
 split; [destruct Hinv' as [Hbound _]; lia|].
 split.
 - eapply normalization_step_extends_execution.
   + eapply normalization_multistep_trans; [|exact Hrun].
     apply normalization_substep_execution. apply normalization_start_actual_substep; assumption.
   + apply normalization_commit_actual_substep; try assumption;
     rewrite Hframe0 by (unfold outer_footprint; simpl; intuition discriminate); assumption.
 - split; [apply normalization_commit_phase_zero|].
   split; [exact Hsrc'|]. split; [exact Hdst'|].
   split; [apply normalization_prefix_terminal_nodup; exact Hinv'|].
   split; [exact Hframe0|]. simpl. rewrite app_length, Hlength. simpl; lia.
Qed.

Theorem normalization_commit_pair_tables : forall pre b out d bases counts valid,
 M.find "coupling_pair_src_table"
 (M.union (normalization_commit_updates b out d bases counts valid) pre) =
 M.find "coupling_pair_src_table" pre /\
 M.find "coupling_pair_dst_table"
 (M.union (normalization_commit_updates b out d bases counts valid) pre) =
 M.find "coupling_pair_dst_table" pre.
Proof.
 intros; split; apply normalization_commit_frame; simpl; intuition discriminate.
Qed.

Theorem normalization_retirement : forall old src dst b e d bases counts valid,
 (b<=e)%nat -> (e<=16)%nat ->
 M.find "mc_phase" old = Some (reg4 (natToWord 4 5)) ->
 M.find "mc_write_base" old = Some (reg5 (natToWord 5 b)) ->
 M.find "mc_write_ptr" old = Some (reg5 (natToWord 5 e)) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 M.find "coupling_desc_next_id" old = Some (reg5 d) ->
 M.find "coupling_desc_base_table" old = Some (regbases bases) ->
 M.find "coupling_desc_count_table" old = Some (regcounts counts) ->
 M.find "coupling_desc_valid_table" old = Some (regvalid valid) ->
 exists precommit labels src' dst' out,
 (b<=out<=e)%nat /\
 Multistep thieleCore old
 (M.union (normalization_commit_updates (natToWord 5 b) (natToWord 5 out)
    d bases counts valid) precommit) labels /\
 M.find "mc_phase"
 (M.union (normalization_commit_updates (natToWord 5 b) (natToWord 5 out)
    d bases counts valid) precommit) = Some (reg4 (natToWord 4 0)) /\
 M.find "coupling_pair_src_table" precommit = Some (regpairs src') /\
 M.find "coupling_pair_dst_table" precommit = Some (regpairs dst') /\
 table_slice src' dst' b (out-b) =
 nodup coupling_pair_eq_dec (table_slice src dst b (e-b)) /\
 outer_frame old precommit /\
 List.length labels = (2 + outer_firings (e-b))%nat.
Proof.
 intros old src dst b e d bases counts valid Hb He Hp Hbase Hend Hsrc Hdst Hd Hbs Hcs Hv.
 destruct (Nat.eq_dec b e) as [E|E].
 - subst e. exists (normalization_started old b b),
   [normalization_label "mc_commit"; normalization_label "mc_normalize_start"], src, dst, b.
   split; [lia|]. split; [apply normalization_empty_execution; assumption|].
   split; [apply normalization_commit_phase_zero|].
   split; [rewrite normalization_started_frame by (simpl; intuition discriminate); assumption|].
   split; [rewrite normalization_started_frame by (simpl; intuition discriminate); assumption|].
   split; [rewrite Nat.sub_diag; reflexivity|].
   split.
   + intros key Hkey; apply normalization_started_frame.
     unfold outer_footprint in Hkey; simpl in *; intuition.
   + rewrite Nat.sub_diag; reflexivity.
 - apply normalization_nonempty_retirement; try assumption; lia.
Qed.

Lemma normalization_committed_descriptor : forall pre b out d bases counts valid,
 let final := M.union (normalization_commit_updates b out d bases counts valid) pre in
 M.find "coupling_desc_base_table" final =
   Some (regbases (put_vector bases (pair_index d) (pair_index b))) /\
 M.find "coupling_desc_count_table" final =
   Some (regcounts (put_vector counts (pair_index d) (wminus out b))) /\
 M.find "coupling_desc_valid_table" final =
   Some (regvalid (put_vector valid (pair_index d) true)) /\
 M.find "coupling_desc_next_id" final = Some (reg5 (wplus d (natToWord 5 1))) /\
 M.find "coupling_pair_next_id" final = Some (reg5 out).
Proof.
 intros pre b out d bases counts valid; cbv zeta. repeat split; try reflexivity; rewrite M.find_union;
 unfold normalization_commit_updates;
 repeat rewrite M.find_add_2 by discriminate;
 rewrite M.find_add_1 by reflexivity; reflexivity.
Qed.

Lemma normalization_committed_frame : forall pre old b out d bases counts valid,
 outer_frame old pre -> forall key,
 ~ In key (List.app outer_footprint ["coupling_desc_base_table";
 "coupling_desc_count_table"; "coupling_desc_valid_table";
 "coupling_desc_next_id"; "coupling_pair_next_id"]) ->
 M.find key (M.union (normalization_commit_updates b out d bases counts valid) pre) =
 M.find key old.
Proof.
 intros pre old b out d bases counts valid Hframe key Hkey.
 rewrite normalization_commit_frame.
 - apply Hframe. intro Hin; apply Hkey; apply in_or_app; auto.
 - unfold outer_footprint in Hkey. simpl in *; intuition.
Qed.

Lemma normalization_descriptor_count_nat : forall b out,
 (b<=out)%nat ->
 wminus (natToWord 5 out) (natToWord 5 b) = natToWord 5 (out-b).
Proof.
 intros b out Hbo.
 replace out with ((out-b)+b)%nat at 1 by lia.
 rewrite natToWord_plus, wminus_def, <- wplus_assoc, wminus_inv.
 rewrite wplus_comm, wplus_unit. reflexivity.
Qed.
Lemma normalization_descriptor_count_exact : forall b out,
 (b<=out<=16)%nat ->
 wordToNat (wminus (natToWord 5 out) (natToWord 5 b)) = (out-b)%nat.
Proof.
 intros. rewrite normalization_descriptor_count_nat by lia.
 apply wordToNat_natToWord_2. simpl; lia.
Qed.
Lemma normalization_outer_firing_formula : forall n,
 (2 * outer_firings n = n * (n+3))%nat.
Proof. induction n; simpl; nia. Qed.
Theorem normalization_retirement_firing_bound : forall b e,
 (b<=e<=16)%nat -> (2 + outer_firings (e-b) <= 154)%nat.
Proof.
 intros b e Hb. pose proof (normalization_outer_firing_formula (e-b)). nia.
Qed.
