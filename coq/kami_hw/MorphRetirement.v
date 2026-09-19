(** Composition of the actual MORPH raw-loading and normalization schedules.
    The observation is ordered pair content with the real descriptor update
    map. It does not identify absent hardware labels or region filtering. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart
 NormalizationSteps NormalizationLoop NormalizationExecution NormalizationRetirement NormalizationFrame MorphLoading.
From Coq Require Import List String Arith Lia.
Import ListNotations.
Open Scope string_scope.
Definition raw_memory_pairs (mem : MemoryTable) base count :=
 map (fun k => (mem (mem_index (wplus (wplus base (natToWord 32 1)) (natToWord 32 (2*k)))),
               mem (mem_index (wplus (wplus base (natToWord 32 1)) (natToWord 32 (2*k+1))))))
 (seq 0 count).

Definition morph_precommit_footprint :=
 List.app header_footprint (List.app load_footprint outer_footprint).

Theorem morph_nonempty_retirement : forall old mem base err code count b src dst valid
 d bases counts descvalid,
 (0<count<=16)%nat -> (b+count<=16)%nat ->
 mem (mem_index base) = natToWord 32 count -> morph_fits mem base (natToWord 5 b) = true ->
 M.find "mc_phase" old = Some (reg4 (natToWord 4 1)) ->
 M.find "mem" old = Some (regmem mem) ->
 M.find "mc_mem_base" old = Some (reg32 base) ->
 M.find "coupling_pair_next_id" old = Some (reg5 (natToWord 5 b)) ->
 M.find "err" old = Some (regbool err) ->
 M.find "error_code" old = Some (reg32 code) ->
 M.find "mc_write_base" old = Some (reg5 (natToWord 5 b)) ->
 M.find "mc_write_ptr" old = Some (reg5 (natToWord 5 b)) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 M.find "coupling_pair_valid_table" old = Some (regvalid valid) ->
 M.find "coupling_desc_next_id" old = Some (reg5 d) ->
 M.find "coupling_desc_base_table" old = Some (regbases bases) ->
 M.find "coupling_desc_count_table" old = Some (regcounts counts) ->
 M.find "coupling_desc_valid_table" old = Some (regvalid descvalid) ->
 exists precommit labels src' dst' out,
 (b<=out<=b+count)%nat /\
 Multistep thieleCore old
 (M.union (normalization_commit_updates (natToWord 5 b) (natToWord 5 out)
    d bases counts descvalid) precommit) labels /\
 M.find "mc_phase"
 (M.union (normalization_commit_updates (natToWord 5 b) (natToWord 5 out)
    d bases counts descvalid) precommit) = Some (reg4 (natToWord 4 0)) /\
 M.find "coupling_pair_src_table" precommit = Some (regpairs src') /\
 M.find "coupling_pair_dst_table" precommit = Some (regpairs dst') /\
 table_slice src' dst' b (out-b) = nodup coupling_pair_eq_dec (raw_memory_pairs mem base count) /\
 List.length labels = (count+3+outer_firings count)%nat /\
 (forall key, ~ In key morph_precommit_footprint -> M.find key precommit = M.find key old) /\
 table_prefix_agrees b src' dst' src dst.
Proof.
 intros old mem base err code count b src dst valid d bases counts descvalid
 Hcount Hspace Hraw Hfit Hp Hm Hb Hnext He Hcode Hbase Hout Hsrc Hdst Hv Hd Hbs Hcs Hvs.
 destruct (morph_admitted_loading old mem base (natToWord 5 b) err code count b src dst valid
 Hcount Hspace Hraw Hfit Hp Hm Hb Hnext He Hcode Hout Hsrc Hdst Hv)
 as [loaded [lsrc [ldst [Hload [Hphase [Hend [Hls [Hld [Hrawpairs [Hframe Hloadprefix]]]]]]]]]].
 assert (Lbase : M.find "mc_write_base" loaded = Some (reg5 (natToWord 5 b))).
 { rewrite Hframe; [assumption|unfold header_footprint,load_footprint; simpl; intuition discriminate]. }
 assert (Ld : M.find "coupling_desc_next_id" loaded = Some (reg5 d)).
 { rewrite Hframe; [assumption|unfold header_footprint,load_footprint; simpl; intuition discriminate]. }
 assert (Lbs : M.find "coupling_desc_base_table" loaded = Some (regbases bases)).
 { rewrite Hframe; [assumption|unfold header_footprint,load_footprint; simpl; intuition discriminate]. }
 assert (Lcs : M.find "coupling_desc_count_table" loaded = Some (regcounts counts)).
 { rewrite Hframe; [assumption|unfold header_footprint,load_footprint; simpl; intuition discriminate]. }
 assert (Lvs : M.find "coupling_desc_valid_table" loaded = Some (regvalid descvalid)).
 { rewrite Hframe; [assumption|unfold header_footprint,load_footprint; simpl; intuition discriminate]. }
 destruct (normalization_retirement_with_prefix loaded lsrc ldst b (b+count) d bases counts descvalid
 ltac:(lia) Hspace Hphase Lbase Hend Hls Hld Ld Lbs Lcs Lvs)
 as [pre [labels [src' [dst' [out [Hbound [Hnorm [Hzero [Hs [Ht [Hpairs [Hnormframe [Hlen Hnormprefix]]]]]]]]]]]]].
 exists pre, (List.app labels (List.app (repeat (normalization_label "mc_morph_loop") count)
 [normalization_label "mc_morph_header"])), src', dst', out.
 split; [exact Hbound|]. split; [eapply normalization_multistep_trans; eassumption|].
 split; [exact Hzero|]. split; [exact Hs|]. split; [exact Ht|].
 split.
 - rewrite Hpairs. replace (b+count-b)%nat with count by lia.
   rewrite Hrawpairs; reflexivity.
 - split.
   + rewrite !app_length, repeat_length, Hlen.
     replace (b+count-b)%nat with count by lia. simpl; lia.
   + split.
     * intros key Hkey. rewrite Hnormframe.
       -- apply Hframe. unfold morph_precommit_footprint in Hkey.
          rewrite !in_app_iff in *; intuition.
       -- unfold morph_precommit_footprint in Hkey. rewrite !in_app_iff in Hkey; intuition.
     * intros k Hk. rewrite Hnormprefix by exact Hk. apply Hloadprefix; exact Hk.
Qed.

Theorem morph_nonempty_retirement_firing_bound : forall count,
 (count<=16)%nat -> (count+3+outer_firings count<=171)%nat.
Proof.
 intros. pose proof (normalization_outer_firing_formula count). nia.
Qed.

Theorem morph_retirement : forall old mem base err code count b src dst valid
 d bases counts descvalid,
 (count<=16)%nat -> (b+count<=16)%nat ->
 mem (mem_index base) = natToWord 32 count -> morph_fits mem base (natToWord 5 b) = true ->
 M.find "mc_phase" old = Some (reg4 (natToWord 4 1)) ->
 M.find "mem" old = Some (regmem mem) ->
 M.find "mc_mem_base" old = Some (reg32 base) ->
 M.find "coupling_pair_next_id" old = Some (reg5 (natToWord 5 b)) ->
 M.find "err" old = Some (regbool err) ->
 M.find "error_code" old = Some (reg32 code) ->
 M.find "mc_write_base" old = Some (reg5 (natToWord 5 b)) ->
 M.find "mc_write_ptr" old = Some (reg5 (natToWord 5 b)) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 M.find "coupling_pair_valid_table" old = Some (regvalid valid) ->
 M.find "coupling_desc_next_id" old = Some (reg5 d) ->
 M.find "coupling_desc_base_table" old = Some (regbases bases) ->
 M.find "coupling_desc_count_table" old = Some (regcounts counts) ->
 M.find "coupling_desc_valid_table" old = Some (regvalid descvalid) ->
 exists precommit labels src' dst' out,
 (b<=out<=b+count)%nat /\
 Multistep thieleCore old
 (M.union (normalization_commit_updates (natToWord 5 b) (natToWord 5 out)
    d bases counts descvalid) precommit) labels /\
 M.find "mc_phase"
 (M.union (normalization_commit_updates (natToWord 5 b) (natToWord 5 out)
    d bases counts descvalid) precommit) = Some (reg4 (natToWord 4 0)) /\
 M.find "coupling_pair_src_table" precommit = Some (regpairs src') /\
 M.find "coupling_pair_dst_table" precommit = Some (regpairs dst') /\
 table_slice src' dst' b (out-b) = nodup coupling_pair_eq_dec (raw_memory_pairs mem base count) /\
 List.length labels = (count+3+outer_firings count)%nat /\
 (forall key, ~ In key morph_precommit_footprint -> M.find key precommit = M.find key old) /\
 table_prefix_agrees b src' dst' src dst.
Proof.
 intros old mem base err code count b src dst valid d bases counts descvalid
 Hcount Hspace Hraw Hfit Hp Hm Hb Hnext He Hcode Hbase Hout Hsrc Hdst Hv Hd Hbs Hcs Hvs.
 destruct count as [|count].
 2: { eapply morph_nonempty_retirement; try eassumption; lia. }
 pose (header := M.union (morph_header_updates mem base (natToWord 5 b) err code) old).
 assert (Hphase : M.find "mc_phase" header = Some (reg4 (natToWord 4 5))).
 { apply morph_header_empty; assumption. }
 assert (Lbase : M.find "mc_write_base" header = Some (reg5 (natToWord 5 b))).
 { apply eq_trans with (M.find "mc_write_base" old); [apply morph_header_frame; unfold header_footprint; simpl; intuition discriminate|assumption]. }
 assert (Lend : M.find "mc_write_ptr" header = Some (reg5 (natToWord 5 b))).
 { unfold header; rewrite morph_header_frame by (unfold header_footprint; simpl; intuition discriminate); assumption. }
 assert (Ls : M.find "coupling_pair_src_table" header = Some (regpairs src)).
 { unfold header; rewrite morph_header_frame by (unfold header_footprint; simpl; intuition discriminate); assumption. }
 assert (Lt : M.find "coupling_pair_dst_table" header = Some (regpairs dst)).
 { unfold header; rewrite morph_header_frame by (unfold header_footprint; simpl; intuition discriminate); assumption. }
 assert (Ld : M.find "coupling_desc_next_id" header = Some (reg5 d)).
 { unfold header; rewrite morph_header_frame by (unfold header_footprint; simpl; intuition discriminate); assumption. }
 assert (Lbs : M.find "coupling_desc_base_table" header = Some (regbases bases)).
 { unfold header; rewrite morph_header_frame by (unfold header_footprint; simpl; intuition discriminate); assumption. }
 assert (Lcs : M.find "coupling_desc_count_table" header = Some (regcounts counts)).
 { unfold header; rewrite morph_header_frame by (unfold header_footprint; simpl; intuition discriminate); assumption. }
 assert (Lvs : M.find "coupling_desc_valid_table" header = Some (regvalid descvalid)).
 { unfold header; rewrite morph_header_frame by (unfold header_footprint; simpl; intuition discriminate); assumption. }
 destruct (normalization_retirement_with_prefix header src dst b b d bases counts descvalid
 ltac:(lia) ltac:(lia) Hphase Lbase Lend Ls Lt Ld Lbs Lcs Lvs)
 as [pre [labels [src' [dst' [out [Hbound [Hnorm [Hzero [Hs [Ht [Hpairs [Hnormframe [Hlen Hnormprefix]]]]]]]]]]]]].
 exists pre, (List.app labels [normalization_label "mc_morph_header"]), src', dst', out.
 split; [lia|]. split.
 - eapply normalization_multistep_trans; [|exact Hnorm].
   apply normalization_substep_execution; apply morph_header_actual_substep; assumption.
 - split; [exact Hzero|]. split; [exact Hs|]. split; [exact Ht|].
   split; [rewrite Hpairs, Nat.sub_diag; reflexivity|].
   split; [rewrite app_length, Hlen, Nat.sub_diag; reflexivity|].
   split; [|exact Hnormprefix].
   intros key Hkey. rewrite Hnormframe.
   + apply morph_header_frame. unfold morph_precommit_footprint in Hkey.
     rewrite !in_app_iff in Hkey; intuition.
   + unfold morph_precommit_footprint in Hkey. rewrite !in_app_iff in Hkey; intuition.
Qed.

Theorem morph_retirement_final_frame : forall old pre b out d bases counts valid,
 (forall key, ~ In key morph_precommit_footprint -> M.find key pre = M.find key old) ->
 forall key, ~ In key (List.app morph_precommit_footprint
 ["coupling_desc_base_table"; "coupling_desc_count_table"; "coupling_desc_valid_table";
 "coupling_desc_next_id"; "coupling_pair_next_id"]) ->
 M.find key (M.union (normalization_commit_updates b out d bases counts valid) pre) =
 M.find key old.
Proof.
 intros old pre b out d bases counts valid Hpre key Hkey.
 rewrite normalization_commit_frame.
 - apply Hpre. rewrite in_app_iff in Hkey; intuition.
 - unfold morph_precommit_footprint, header_footprint, load_footprint, outer_footprint in Hkey.
   simpl in *; intuition.
Qed.
