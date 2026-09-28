(** Prefix preservation for the selected actual normalization execution.
    This strengthens the actual outer-loop induction itself; no prefix frame
    is inferred from the weaker retirement theorem. Scheduling, dispatch,
    descriptor freshness, and external RTL refinement remain separate. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart
 NormalizationSteps NormalizationLoop NormalizationExecution NormalizationPrefix
 NormalizationScanExecution NormalizationRetirement.
From Coq Require Import List String Bool Arith Lia.
Import ListNotations.
Open Scope string_scope.

Definition table_prefix_agrees b src dst rawsrc rawdst :=
 forall k, (k<b)%nat -> table_pair src dst k = table_pair rawsrc rawdst k.

Lemma table_prefix_agrees_refl : forall b src dst,
 table_prefix_agrees b src dst src dst.
Proof. intros b src dst k Hk; reflexivity. Qed.

Lemma normalization_emit_preserves_low_prefix : forall rawsrc rawdst src dst b i out e dup,
 normalization_prefix_invariant rawsrc rawdst src dst b i out e -> (i<e)%nat ->
 table_prefix_agrees b src dst rawsrc rawdst ->
 table_prefix_agrees b (emitted_table src i out dup) (emitted_table dst i out dup)
 rawsrc rawdst.
Proof.
 intros rawsrc rawdst src dst b i out e dup [Hb Hinv] Hi Hprefix k Hk.
 rewrite table_pair_after_emit_other by lia. apply Hprefix; exact Hk.
Qed.

Theorem normalization_outer_execution_with_prefix : forall remaining old rawsrc rawdst src dst b i out e,
 (e-i=remaining)%nat -> (i<e)%nat ->
 normalization_prefix_invariant rawsrc rawdst src dst b i out e ->
 table_prefix_agrees b src dst rawsrc rawdst ->
 scan_registers old i (S i) e false src dst ->
 M.find "mc_norm_ptr" old = Some (reg5 (natToWord 5 out)) ->
 exists final labels src' dst' out',
 Multistep thieleCore old final labels /\
 normalization_prefix_invariant rawsrc rawdst src' dst' b e out' e /\
 M.find "mc_phase" final = Some (reg4 (natToWord 4 11)) /\
 M.find "mc_write_ptr" final = Some (reg5 (natToWord 5 out')) /\
 M.find "coupling_pair_src_table" final = Some (regpairs src') /\
 M.find "coupling_pair_dst_table" final = Some (regpairs dst') /\ outer_frame old final /\
 List.length labels = outer_firings remaining /\
 table_prefix_agrees b src' dst' rawsrc rawdst.
Proof.
 induction remaining as [|n IH]; intros old rawsrc rawdst src dst b i out e Hn Hi Hinv Hprefix Hr Ho.
 - lia.
 - pose proof Hinv as Hb. destruct Hb as [Hb _].
   destruct (outer_emit_execution old src dst i out e Hi ltac:(lia) Hr Ho) as [ls [Hex Hlen]].
   pose (dup := scan_seen src dst i (S i) (e-S i)).
   pose (src1 := emitted_table src i out dup).
   pose (dst1 := emitted_table dst i out dup).
   pose (out1 := next_output out dup).
   assert (Hinv1 : normalization_prefix_invariant rawsrc rawdst src1 dst1 b (S i) out1 e).
   { apply normalization_prefix_preserved; assumption. }
   assert (Hprefix1 : table_prefix_agrees b src1 dst1 rawsrc rawdst).
   { apply normalization_emit_preserves_low_prefix with (e:=e); assumption. }
   destruct (Nat.eq_dec (S i) e) as [Heq|Hneq].
   + exists (outer_emitted old src dst i out e), ls, src1, dst1, out1.
     split; [exact Hex|]. split; [rewrite Heq in Hinv1; exact Hinv1|].
     split; [rewrite outer_emitted_phase by lia; rewrite Heq, Nat.eqb_refl; reflexivity|].
     split; [rewrite outer_emitted_end by lia; rewrite (proj2 (Nat.eqb_eq _ _) Heq); reflexivity|].
     split; [apply emitted_table_is_actual_src_update|].
     split; [apply emitted_table_is_actual_dst_update|].
     split; [apply outer_emitted_frame|].
     split; [assert (n=0)%nat by lia; subst n; simpl; rewrite Hlen; lia|exact Hprefix1].
   + destruct (IH (outer_emitted old src dst i out e) rawsrc rawdst src1 dst1 b
       (S i) out1 e ltac:(lia) ltac:(lia) Hinv1 Hprefix1
       (outer_emitted_scan_registers old src dst i out e ltac:(lia) ltac:(lia))
       (normalization_actual_emit_output_pointer _ _ _ _ _ _ _))
       as [final [labels [src' [dst' [out' [Hrun [Hinv' [Hphase [Hend [Hsrc [Hdst [Hframe [Hlength Hprefix']]]]]]]]]]]]].
     exists final, (List.app labels ls), src', dst', out'.
     split; [eapply normalization_multistep_trans; eassumption|].
     split; [exact Hinv'|]. split; [exact Hphase|]. split; [exact Hend|].
     split; [exact Hsrc|]. split; [exact Hdst|].
     split.
     * intros key Hkey. rewrite Hframe by exact Hkey. apply outer_emitted_frame; exact Hkey.
     * split; [rewrite app_length, Hlength, Hlen; simpl; lia|exact Hprefix'].
Qed.

Theorem normalization_nonempty_retirement_with_prefix : forall old src dst b e d bases counts valid,
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
 List.length labels = (2 + outer_firings (e-b))%nat /\
 table_prefix_agrees b src' dst' src dst.
Proof.
 intros old src dst b e d bases counts valid Hb He Hp Hbase Hend Hsrc Hdst Hd Hbs Hcs Hv.
 destruct (normalization_started_reads old src dst b e Hb He Hend Hsrc Hdst) as [Hr Ho].
 assert (Hinv : normalization_prefix_invariant src dst src dst b b b e).
 { split; [lia|]. split.
   - rewrite Nat.sub_diag, selected_prefix_start. reflexivity.
   - intros; reflexivity. }
 destruct (normalization_outer_execution_with_prefix (e-b) (normalization_started old b e)
 src dst src dst b b b e eq_refl Hb Hinv (table_prefix_agrees_refl b src dst) Hr Ho)
 as [pre [ls [src' [dst' [out [Hrun [Hinv' [Hphase [Hend' [Hsrc' [Hdst' [Hframe [Hlength Hprefix]]]]]]]]]]]]].
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
   split; [exact Hframe0|]. split; [simpl; rewrite app_length, Hlength; simpl; lia|exact Hprefix].
Qed.

Theorem normalization_retirement_with_prefix : forall old src dst b e d bases counts valid,
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
 List.length labels = (2 + outer_firings (e-b))%nat /\
 table_prefix_agrees b src' dst' src dst.
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
   + split; [rewrite Nat.sub_diag; reflexivity|apply table_prefix_agrees_refl].
 - apply normalization_nonempty_retirement_with_prefix; try assumption; lia.
Qed.


(** Payloads of any old interval entirely below the append base retain their
    readouts. Descriptor metadata still needs its own freshness/frame premise. *)
Theorem normalization_prefix_preserves_range_readout : forall b src dst rawsrc rawdst a count,
 table_prefix_agrees b src dst rawsrc rawdst -> (a+count<=b)%nat ->
 table_slice src dst a count = table_slice rawsrc rawdst a count.
Proof.
 intros b src dst rawsrc rawdst a count Hprefix Hrange.
 unfold table_slice. apply map_ext_in. intros k Hk.
 apply in_seq in Hk. apply Hprefix; lia.
Qed.

Theorem normalization_commit_preserves_prefix_reads : forall pre b out d bases counts valid
 src dst rawsrc rawdst bound,
 M.find "coupling_pair_src_table" pre = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" pre = Some (regpairs dst) ->
 table_prefix_agrees bound src dst rawsrc rawdst ->
 let final := M.union (normalization_commit_updates b out d bases counts valid) pre in
 M.find "coupling_pair_src_table" final = Some (regpairs src) /\
 M.find "coupling_pair_dst_table" final = Some (regpairs dst) /\
 forall a count, (a+count<=bound)%nat ->
 table_slice src dst a count = table_slice rawsrc rawdst a count.
Proof.
 intros pre b out d bases counts valid src dst rawsrc rawdst bound Hsrc Hdst Hprefix.
 cbv zeta. destruct (normalization_commit_pair_tables pre b out d bases counts valid) as [Hs Hd].
 rewrite Hs, Hd, Hsrc, Hdst. split; [reflexivity|]. split; [reflexivity|].
 intros; eapply normalization_prefix_preserves_range_readout; eassumption.
Qed.

(** Descriptor slots other than the newly committed slot retain their metadata.
    Freshness of the chosen new slot is a separate allocation obligation. *)
Lemma normalization_commit_other_descriptor : forall bases counts valid d b out slot,
 slot <> pair_index d ->
 put_vector bases (pair_index d) (pair_index b) slot = bases slot /\
 put_vector counts (pair_index d) (wminus out b) slot = counts slot /\
 put_vector valid (pair_index d) true slot = valid slot.
Proof.
 intros. unfold put_vector. destruct (weq slot (pair_index d));
 [contradiction|repeat split; reflexivity].
Qed.

Definition descriptor_pair_readout (src dst : PairTable)
 (bases : word 4 -> word 4) (counts : word 4 -> word 5) (slot : word 4) :=
 table_slice src dst (wordToNat (bases slot)) (wordToNat (counts slot)).

Theorem normalization_commit_old_descriptor_readout : forall src dst rawsrc rawdst
 bases counts d b out bound slot,
 slot <> pair_index d -> table_prefix_agrees bound src dst rawsrc rawdst ->
 (wordToNat (bases slot) + wordToNat (counts slot) <= bound)%nat ->
 descriptor_pair_readout src dst
 (put_vector bases (pair_index d) (pair_index b))
 (put_vector counts (pair_index d) (wminus out b)) slot =
 descriptor_pair_readout rawsrc rawdst bases counts slot.
Proof.
 intros. unfold descriptor_pair_readout, put_vector.
 destruct (weq slot (pair_index d)); [contradiction|].
 eapply normalization_prefix_preserves_range_readout; eassumption.
Qed.
