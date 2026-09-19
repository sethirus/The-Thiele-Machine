(** Actual MORPH header and raw-memory loading semantics. There is no region
    membership filter or label decoder in these rules. Software correspondence
    must impose an explicit representation contract for those omissions. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart
 NormalizationSteps NormalizationLoop NormalizationExecution NormalizationRetirement NormalizationFrame.
From Coq Require Import List String Bool Arith Lia.
Import ListNotations.
Open Scope string_scope.
Definition MemoryTable := word 7 -> word 32.
Definition regmem (v : MemoryTable) :=
 existT (fullType type) (SyntaxKind (Vector (Bit 32) 7)) v.
Definition reg32 (v : word 32) := existT (fullType type) (SyntaxKind (Bit 32)) v.
Definition mem_index (w : word 32) := split1 7 25 w.
Definition morph_header_rule := normalization_rule 3.
Definition morph_load_rule := normalization_rule 4.
Definition morph_fits (mem : MemoryTable) (base : word 32) (next : word 5) :=
 andb (negb (word_ltb (evalZeroExtendTrunc 32 (wminus (natToWord 5 16) next))
 (mem (mem_index base))))
 (negb (word_ltb (wrshift (wminus (natToWord 32 127) base) 1)
 (mem (mem_index base)))).
Definition morph_header_updates mem base next err code : UpdatesT :=
 let count := mem (mem_index base) in
 let fits := morph_fits mem base next in
 M.add "err" (regbool (orb err (negb fits)))
 (M.add "error_code" (reg32 (if fits then code else ERR_COUPLING_INVALID))
 (M.add "mc_pair_count" (reg5 (split1 5 27 count))
 (M.add "mc_read_ptr" (reg32 (wplus base (natToWord 32 1)))
 (M.add "mc_i" (reg5 (natToWord 5 0))
 (M.add "mc_phase" (reg4 (if negb fits then natToWord 4 0 else
 if word_eqb count (natToWord 32 0) then natToWord 4 5 else natToWord 4 2))
 (M.empty _)))))).
Definition morph_load_updates (mem : MemoryTable) (readptr : word 32)
 (out i count : word 5) (src dst : PairTable) (valid : word 4 -> bool) : UpdatesT :=
 M.add "coupling_pair_src_table" (regpairs (put_vector src (pair_index out) (mem (mem_index readptr))))
 (M.add "coupling_pair_dst_table" (regpairs (put_vector dst (pair_index out)
 (mem (mem_index (wplus readptr (natToWord 32 1))))))
 (M.add "coupling_pair_valid_table" (regvalid (put_vector valid (pair_index out) true))
 (M.add "mc_read_ptr" (reg32 (wplus readptr (natToWord 32 2)))
 (M.add "mc_write_ptr" (reg5 (wplus out (natToWord 5 1)))
 (M.add "mc_i" (reg5 (wplus i (natToWord 5 1)))
 (M.add "mc_phase" (reg4 (if word_eqb (wplus i (natToWord 5 1)) count
 then natToWord 4 5 else natToWord 4 2)) (M.empty _))))))).
Lemma morph_header_rule_name : attrName morph_header_rule = "mc_morph_header".
Proof. reflexivity. Qed.
Lemma morph_load_rule_name : attrName morph_load_rule = "mc_morph_loop".
Proof. reflexivity. Qed.
Lemma morph_header_rule_in : In morph_header_rule (getRules thieleCore).
Proof. unfold morph_header_rule, normalization_rule; apply nth_In; change (3<12)%nat; lia. Qed.
Lemma morph_load_rule_in : In morph_load_rule (getRules thieleCore).
Proof. unfold morph_load_rule, normalization_rule; apply nth_In; change (4<12)%nat; lia. Qed.
Theorem morph_header_actual_action : forall old mem base next err code,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 1)) ->
 M.find "mem" old = Some (regmem mem) ->
 M.find "mc_mem_base" old = Some (reg32 base) ->
 M.find "coupling_pair_next_id" old = Some (reg5 next) ->
 M.find "err" old = Some (regbool err) ->
 M.find "error_code" old = Some (reg32 code) ->
 SemAction old (attrType morph_header_rule type)
 (morph_header_updates mem base next err code) (M.empty _) WO.
Proof.
 intros old mem base next err code Hp Hm Hb Hn He Hc.
 unfold morph_header_rule, normalization_rule. cbn [nth getRules attrType].
 eapply SemReadReg; [exact Hp|]. apply SemAssertTrue; [reflexivity|].
 eapply SemReadReg; [exact Hm|]. eapply SemReadReg; [exact Hb|].
 eapply SemReadReg; [exact Hn|]. repeat apply SemLet.
 eapply SemReadReg; [exact He|]. eapply SemReadReg; [exact Hc|].
 repeat apply SemLet.
 unfold morph_header_updates, morph_fits, mem_index, word_ltb, word_eqb.
 do 6 (eapply SemWriteReg; [shelve|reflexivity|]). apply SemReturn; reflexivity.
 Unshelve. all: reflexivity.
Qed.
Theorem morph_load_actual_action : forall old mem readptr out i count src dst valid,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 2)) ->
 M.find "mem" old = Some (regmem mem) ->
 M.find "mc_read_ptr" old = Some (reg32 readptr) ->
 M.find "mc_write_ptr" old = Some (reg5 out) ->
 M.find "mc_i" old = Some (reg5 i) ->
 M.find "mc_pair_count" old = Some (reg5 count) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 M.find "coupling_pair_valid_table" old = Some (regvalid valid) ->
 SemAction old (attrType morph_load_rule type)
 (morph_load_updates mem readptr out i count src dst valid) (M.empty _) WO.
Proof.
 intros old mem readptr out i count src dst valid Hp Hm Hr Ho Hi Hc Hs Hd Hv.
 unfold morph_load_rule, normalization_rule. cbn [nth getRules attrType].
 eapply SemReadReg; [exact Hp|]. apply SemAssertTrue; [reflexivity|].
 eapply SemReadReg; [exact Hm|]. eapply SemReadReg; [exact Hr|].
 eapply SemReadReg; [exact Ho|]. eapply SemReadReg; [exact Hi|].
 eapply SemReadReg; [exact Hc|]. eapply SemReadReg; [exact Hs|].
 eapply SemReadReg; [exact Hd|]. eapply SemReadReg; [exact Hv|].
 repeat apply SemLet.
 unfold morph_load_updates, mem_index, pair_index, put_vector, word_eqb.
 do 7 (eapply SemWriteReg; [shelve|reflexivity|]). apply SemReturn; reflexivity.
 Unshelve. all: reflexivity.
Qed.

Theorem morph_header_actual_substep : forall old mem base next err code,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 1)) ->
 M.find "mem" old = Some (regmem mem) ->
 M.find "mc_mem_base" old = Some (reg32 base) ->
 M.find "coupling_pair_next_id" old = Some (reg5 next) ->
 M.find "err" old = Some (regbool err) ->
 M.find "error_code" old = Some (reg32 code) ->
 Substep thieleCore old (morph_header_updates mem base next err code)
 (Rle (Some "mc_morph_header")) (M.empty _).
Proof.
 intros. eapply SingleRule with (a := attrType morph_header_rule).
 - exact morph_header_rule_in.
 - apply morph_header_actual_action; assumption.
Qed.
Record morph_load_registers old mem readptr out i count src dst valid : Prop := {
 load_phase : M.find "mc_phase" old = Some (reg4 (natToWord 4 2));
 load_mem : M.find "mem" old = Some (regmem mem);
 load_read : M.find "mc_read_ptr" old = Some (reg32 readptr);
 load_out : M.find "mc_write_ptr" old = Some (reg5 (natToWord 5 out));
 load_i : M.find "mc_i" old = Some (reg5 (natToWord 5 i));
 load_count : M.find "mc_pair_count" old = Some (reg5 (natToWord 5 count));
 load_src : M.find "coupling_pair_src_table" old = Some (regpairs src);
 load_dst : M.find "coupling_pair_dst_table" old = Some (regpairs dst);
 load_valid : M.find "coupling_pair_valid_table" old = Some (regvalid valid)
}.
Definition morph_loaded_state old mem readptr out i count src dst valid :=
 M.union (morph_load_updates mem readptr (natToWord 5 out) (natToWord 5 i)
 (natToWord 5 count) src dst valid) old.
Definition load_src_next (mem : MemoryTable) readptr out src :=
 put_vector src (pair_index (natToWord 5 out)) (mem (mem_index readptr)).
Definition load_dst_next (mem : MemoryTable) readptr out dst :=
 put_vector dst (pair_index (natToWord 5 out))
 (mem (mem_index (wplus readptr (natToWord 32 1)))).
Definition load_valid_next out valid := put_vector valid (pair_index (natToWord 5 out)) true.
Definition load_footprint := ["coupling_pair_src_table"; "coupling_pair_dst_table";
 "coupling_pair_valid_table"; "mc_read_ptr"; "mc_write_ptr"; "mc_i"; "mc_phase"].
Definition load_frame (old final : RegsT) := forall key, ~ In key load_footprint ->
 M.find key final = M.find key old.
Lemma morph_load_frame : forall old mem readptr out i count src dst valid,
 load_frame old (morph_loaded_state old mem readptr out i count src dst valid).
Proof.
 intros old mem readptr out i count src dst valid key H.
 unfold morph_loaded_state; rewrite M.find_union. unfold morph_load_updates.
 unfold load_footprint in H.
 repeat rewrite M.find_add_2 by (simpl in H; intuition).
 rewrite M.find_empty; reflexivity.
Qed.
Lemma morph_load_execution : forall old mem readptr out i count src dst valid,
 morph_load_registers old mem readptr out i count src dst valid ->
 Multistep thieleCore old (morph_loaded_state old mem readptr out i count src dst valid)
 [normalization_label "mc_morph_loop"].
Proof.
 intros. apply normalization_substep_execution.
 eapply SingleRule with (a := attrType morph_load_rule).
 - exact morph_load_rule_in.
 - apply morph_load_actual_action; destruct H; assumption.
Qed.
Ltac load_read_map := unfold morph_loaded_state; rewrite M.find_union;
 unfold morph_load_updates; repeat rewrite M.find_add_2 by discriminate;
 rewrite M.find_add_1 by reflexivity.
Lemma morph_loaded_phase : forall old mem r out i count src dst valid,
 (i<count<=16)%nat ->
 M.find "mc_phase" (morph_loaded_state old mem r out i count src dst valid) =
 Some (reg4 (natToWord 4 (if Nat.eqb (S i) count then 5 else 2))).
Proof.
 intros. load_read_map. rewrite <- natToWord_plus.
 replace (i+1)%nat with (S i) by lia. rewrite bounded_word_eqb by lia.
 destruct (Nat.eqb (S i) count); reflexivity.
Qed.
Lemma morph_loaded_continues : forall old mem r out i count src dst valid,
 (S i<count<=16)%nat ->
 morph_load_registers old mem r out i count src dst valid ->
 morph_load_registers (morph_loaded_state old mem r out i count src dst valid)
 mem (wplus r (natToWord 32 2)) (S out) (S i) count
 (load_src_next mem r out src) (load_dst_next mem r out dst) (load_valid_next out valid).
Proof.
 intros old mem r out i count src dst valid Hb Hr. constructor.
 - rewrite morph_loaded_phase by lia.
   rewrite (proj2 (Nat.eqb_neq (S i) count) ltac:(lia)); reflexivity.
 - rewrite morph_load_frame by (unfold load_footprint; simpl; intuition discriminate).
   destruct Hr; assumption.
 - load_read_map; reflexivity.
 - load_read_map. rewrite <- natToWord_plus.
   replace (out+1)%nat with (S out) by lia; reflexivity.
 - load_read_map. rewrite <- natToWord_plus.
   replace (i+1)%nat with (S i) by lia; reflexivity.
 - rewrite morph_load_frame by (unfold load_footprint; simpl; intuition discriminate).
   destruct Hr; assumption.
 - load_read_map; reflexivity.
 - load_read_map; reflexivity.
 - load_read_map; reflexivity.
Qed.

Fixpoint loaded_table (mem : MemoryTable) (r : word 32) (out n : nat)
 (table : PairTable) (offset : nat) : PairTable :=
 match n with
 | O => table
 | S k => loaded_table mem (wplus r (natToWord 32 2)) (S out) k
  (put_vector table (pair_index (natToWord 5 out))
    (mem (mem_index (wplus r (natToWord 32 offset))))) offset
 end.
Fixpoint loaded_valid out n (valid : word 4 -> bool) :=
 match n with O => valid | S k => loaded_valid (S out) k (load_valid_next out valid) end.
Lemma load_src_next_zero : forall mem r out src,
 put_vector src (pair_index (natToWord 5 out))
 (mem (mem_index (wplus r (natToWord 32 0)))) = load_src_next mem r out src.
Proof. intros; rewrite wplus_comm, wplus_unit; reflexivity. Qed.

Theorem morph_load_loop_execution : forall n old mem r out i count src dst valid,
 (count-i = n)%nat -> (i<count<=16)%nat ->
 morph_load_registers old mem r out i count src dst valid ->
 exists final,
 Multistep thieleCore old final (repeat (normalization_label "mc_morph_loop") n) /\
 M.find "mc_phase" final = Some (reg4 (natToWord 4 5)) /\
 M.find "mc_write_ptr" final = Some (reg5 (natToWord 5 (out+n))) /\
 M.find "coupling_pair_src_table" final = Some (regpairs (loaded_table mem r out n src 0)) /\
 M.find "coupling_pair_dst_table" final = Some (regpairs (loaded_table mem r out n dst 1)) /\
 M.find "coupling_pair_valid_table" final = Some (regvalid (loaded_valid out n valid)) /\
 load_frame old final.
Proof.
 induction n as [|n IH]; intros old mem r out i count src dst valid Hn Hb Hr.
 - lia.
 - pose (next := morph_loaded_state old mem r out i count src dst valid).
   pose proof (morph_load_execution old mem r out i count src dst valid Hr) as Hex.
   destruct (Nat.eq_dec (S i) count) as [E|E].
   + assert (n=0)%nat by lia; subst n. exists next.
     split; [exact Hex|]. split.
     * unfold next; rewrite morph_loaded_phase by lia; rewrite E, Nat.eqb_refl; reflexivity.
     * split; [unfold next; load_read_map; rewrite <- natToWord_plus; reflexivity|].
       split; [unfold next; load_read_map; cbn [loaded_table]; rewrite load_src_next_zero; reflexivity|].
       split; [unfold next; load_read_map; reflexivity|].
       split; [unfold next; load_read_map; reflexivity|apply morph_load_frame].
   + destruct (IH next mem (wplus r (natToWord 32 2)) (S out) (S i) count
      (load_src_next mem r out src) (load_dst_next mem r out dst) (load_valid_next out valid)
      ltac:(lia) ltac:(lia) (morph_loaded_continues old mem r out i count src dst valid ltac:(lia) Hr))
      as [final [Hrun [Hp [Ho [Hs [Hd [Hv Hf]]]]]]].
     exists final. split.
     * replace (S n) with (n+1)%nat by lia. rewrite repeat_app. simpl.
       eapply normalization_multistep_trans; eassumption.
     * split; [exact Hp|]. split; [replace (out+S n)%nat with (S out+n)%nat by lia; exact Ho|].
       split; [cbn [loaded_table]; rewrite load_src_next_zero; exact Hs|].
       split; [exact Hd|]. split; [exact Hv|].
       intros key Hkey; rewrite Hf by exact Hkey. apply morph_load_frame; exact Hkey.
Qed.

Lemma loaded_table_outside : forall n mem r out table offset k,
 (out+n<=16)%nat -> (k<16)%nat -> ((k<out) \/ (out+n<=k))%nat ->
 loaded_table mem r out n table offset (pair_index (natToWord 5 k)) =
 table (pair_index (natToWord 5 k)).
Proof.
 induction n; intros mem r out table offset k Hb Hk Hout; cbn [loaded_table].
 - reflexivity.
 - rewrite IHn by lia. unfold put_vector.
   destruct (weq (pair_index (natToWord 5 k)) (pair_index (natToWord 5 out))) as [E|E].
   + exfalso. apply (normalization_distinct_pair_indices k out ltac:(lia) ltac:(lia) ltac:(lia)); exact E.
   + reflexivity.
Qed.
Lemma loaded_table_inside : forall n mem r out table offset k,
 (out+n<=16)%nat -> (k<n)%nat ->
 loaded_table mem r out n table offset (pair_index (natToWord 5 (out+k))) =
 mem (mem_index (wplus r (natToWord 32 (2*k+offset)))).
Proof.
 induction n; intros mem r out table offset k Hb Hk; [lia|].
 destruct k as [|k].
 - cbn [loaded_table]. rewrite loaded_table_outside by lia.
   rewrite Nat.add_0_r. unfold put_vector.
   destruct (weq (pair_index (natToWord 5 out)) (pair_index (natToWord 5 out)));
   [replace (2*0+offset)%nat with offset by lia; reflexivity|contradiction].
 - cbn [loaded_table]. replace (out+S k)%nat with (S out+k)%nat by lia.
   rewrite IHn by lia. rewrite <- wplus_assoc, <- natToWord_plus.
   replace (2+(2*k+offset))%nat with (2*S k+offset)%nat by lia. reflexivity.
Qed.

Lemma seq_offset : forall count b,
 seq b count = map (fun k => (b+k)%nat) (seq 0 count).
Proof.
 induction count; intros b; [reflexivity|].
 rewrite !seq_S, map_app, <- IHcount. simpl.
 replace (b+(0+count))%nat with (b+count)%nat by lia. reflexivity.
Qed.

Theorem morph_loaded_raw_pairs : forall mem r b count src dst,
 (b+count<=16)%nat ->
 table_slice (loaded_table mem r b count src 0)
 (loaded_table mem r b count dst 1) b count =
 map (fun k => (mem (mem_index (wplus r (natToWord 32 (2*k)))),
               mem (mem_index (wplus r (natToWord 32 (2*k+1)))))) (seq 0 count).
Proof.
 intros. unfold table_slice. rewrite (seq_offset count b).
 rewrite map_map. apply map_ext_in. intros k Hk. apply in_seq in Hk.
 unfold table_pair. rewrite !loaded_table_inside by lia.
 rewrite Nat.add_0_r; reflexivity.
Qed.

Definition header_footprint := ["err"; "error_code"; "mc_pair_count";
 "mc_read_ptr"; "mc_i"; "mc_phase"].
Lemma morph_header_frame : forall old mem base next err code key,
 ~ In key header_footprint ->
 M.find key (M.union (morph_header_updates mem base next err code) old) = M.find key old.
Proof.
 intros. rewrite M.find_union. unfold morph_header_updates, header_footprint in *.
 repeat rewrite M.find_add_2 by (simpl in H; intuition).
 rewrite M.find_empty; reflexivity.
Qed.
Theorem morph_header_failure : forall old mem base next err code,
 morph_fits mem base next = false ->
 let final := M.union (morph_header_updates mem base next err code) old in
 M.find "err" final = Some (regbool true) /\
 M.find "error_code" final = Some (reg32 ERR_COUPLING_INVALID) /\
 M.find "mc_phase" final = Some (reg4 (natToWord 4 0)).
Proof.
 intros old mem base next err code H; cbv zeta.
 repeat split; rewrite M.find_union; unfold morph_header_updates;
 repeat rewrite M.find_add_2 by discriminate;
 rewrite M.find_add_1 by reflexivity; rewrite H; simpl; try rewrite orb_true_r; reflexivity.
Qed.
Lemma morph_header_admitted_reads : forall old mem base next err code count out src dst valid,
 (0<count<=16)%nat -> mem (mem_index base) = natToWord 32 count ->
 morph_fits mem base next = true ->
 M.find "mem" old = Some (regmem mem) ->
 M.find "mc_write_ptr" old = Some (reg5 (natToWord 5 out)) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 M.find "coupling_pair_valid_table" old = Some (regvalid valid) ->
 morph_load_registers (M.union (morph_header_updates mem base next err code) old)
 mem (wplus base (natToWord 32 1)) out 0 count src dst valid.
Proof.
 intros old mem base next err code count out src dst valid Hcount Hraw Hfit Hm Ho Hs Hd Hv.
 assert (Hzero : word_eqb (natToWord 32 count) (natToWord 32 0) = false).
 { unfold word_eqb. destruct (weq _ _) as [E|E]; [|reflexivity].
   apply (f_equal (@wordToNat 32)) in E.
   rewrite wordToNat_natToWord_2 in E by (eapply pow2_bound_mono with (a:=5); [change (count<32)%nat; lia|lia]). simpl in E; lia. }
 assert (Htrunc : split1 5 27 (natToWord 32 count) = natToWord 5 count).
 { apply wordToNat_inj; rewrite wordToNat_split1.
   rewrite !wordToNat_natToWord_2 by
 (eapply pow2_bound_mono with (a:=5); [change (count<32)%nat; lia|lia]).
   apply Nat.mod_small; simpl; lia. }
 constructor.
 - rewrite M.find_union. unfold morph_header_updates.
   repeat rewrite M.find_add_2 by discriminate. rewrite M.find_add_1 by reflexivity.
   rewrite Hfit, Hraw, Hzero; reflexivity.
 - rewrite morph_header_frame by (unfold header_footprint; simpl; intuition discriminate); assumption.
 - rewrite M.find_union. unfold morph_header_updates.
   repeat rewrite M.find_add_2 by discriminate. rewrite M.find_add_1 by reflexivity; reflexivity.
 - rewrite morph_header_frame by (unfold header_footprint; simpl; intuition discriminate); assumption.
 - rewrite M.find_union. unfold morph_header_updates.
   repeat rewrite M.find_add_2 by discriminate. rewrite M.find_add_1 by reflexivity; reflexivity.
 - rewrite M.find_union. unfold morph_header_updates.
   repeat rewrite M.find_add_2 by discriminate. rewrite M.find_add_1 by reflexivity.
   rewrite Hraw, Htrunc; reflexivity.
 - rewrite morph_header_frame by (unfold header_footprint; simpl; intuition discriminate); assumption.
 - rewrite morph_header_frame by (unfold header_footprint; simpl; intuition discriminate); assumption.
 - rewrite morph_header_frame by (unfold header_footprint; simpl; intuition discriminate); assumption.
Qed.

Theorem morph_admitted_loading : forall old mem base next err code count out src dst valid,
 (0<count<=16)%nat -> (out+count<=16)%nat ->
 mem (mem_index base) = natToWord 32 count -> morph_fits mem base next = true ->
 M.find "mc_phase" old = Some (reg4 (natToWord 4 1)) ->
 M.find "mem" old = Some (regmem mem) ->
 M.find "mc_mem_base" old = Some (reg32 base) ->
 M.find "coupling_pair_next_id" old = Some (reg5 next) ->
 M.find "err" old = Some (regbool err) ->
 M.find "error_code" old = Some (reg32 code) ->
 M.find "mc_write_ptr" old = Some (reg5 (natToWord 5 out)) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 M.find "coupling_pair_valid_table" old = Some (regvalid valid) ->
 exists final src' dst',
 Multistep thieleCore old final
 (List.app (repeat (normalization_label "mc_morph_loop") count)
 [normalization_label "mc_morph_header"]) /\
 M.find "mc_phase" final = Some (reg4 (natToWord 4 5)) /\
 M.find "mc_write_ptr" final = Some (reg5 (natToWord 5 (out+count))) /\
 M.find "coupling_pair_src_table" final = Some (regpairs src') /\
 M.find "coupling_pair_dst_table" final = Some (regpairs dst') /\
 table_slice src' dst' out count =
 map (fun k => (mem (mem_index (wplus (wplus base (natToWord 32 1)) (natToWord 32 (2*k)))),
               mem (mem_index (wplus (wplus base (natToWord 32 1)) (natToWord 32 (2*k+1))))))
 (seq 0 count) /\
 (forall key, ~ In key (List.app header_footprint load_footprint) ->
 M.find key final = M.find key old) /\
 table_prefix_agrees out src' dst' src dst.
Proof.
 intros old mem base next err code count out src dst valid Hcount Hspace Hraw Hfit
 Hp Hm Hb Hn He Hc Ho Hs Hd Hv.
 pose (header := M.union (morph_header_updates mem base next err code) old).
 pose proof (morph_header_admitted_reads old mem base next err code count out src dst valid
 Hcount Hraw Hfit Hm Ho Hs Hd Hv) as Hr.
 destruct (morph_load_loop_execution count header mem (wplus base (natToWord 32 1))
 out 0 count src dst valid ltac:(lia) Hcount Hr)
 as [final [Hrun [Hphase [Hout [Hsrc [Hdst [Hvalid Hframe]]]]]]].
 exists final, (loaded_table mem (wplus base (natToWord 32 1)) out count src 0),
 (loaded_table mem (wplus base (natToWord 32 1)) out count dst 1).
 split.
 - eapply normalization_multistep_trans; [|exact Hrun].
   apply normalization_substep_execution. apply morph_header_actual_substep; assumption.
 - split; [exact Hphase|]. split; [exact Hout|].
   split; [exact Hsrc|]. split; [exact Hdst|].
   split; [apply morph_loaded_raw_pairs; exact Hspace|].
   split.
   + intros key Hkey. rewrite Hframe.
     * apply morph_header_frame. intro Hin; apply Hkey; apply in_or_app; auto.
     * intro Hin; apply Hkey; apply in_or_app; auto.
   + intros k Hk. unfold table_pair.
     rewrite !loaded_table_outside by lia. reflexivity.
Qed.

Theorem morph_header_empty : forall old mem base next err code,
 mem (mem_index base) = natToWord 32 0 -> morph_fits mem base next = true ->
 M.find "mc_phase" (M.union (morph_header_updates mem base next err code) old) =
 Some (reg4 (natToWord 4 5)).
Proof.
 intros. rewrite M.find_union. unfold morph_header_updates.
 repeat rewrite M.find_add_2 by discriminate; rewrite M.find_add_1 by reflexivity.
 rewrite H, H0. unfold word_eqb. destruct (weq _ _); [reflexivity|contradiction].
Qed.

Theorem morph_header_preserves_latched_success_error : forall old mem base next err code,
 morph_fits mem base next = true ->
 M.find "err" (M.union (morph_header_updates mem base next err code) old) = Some (regbool err) /\
 M.find "error_code" (M.union (morph_header_updates mem base next err code) old) = Some (reg32 code).
Proof.
 intros. split; rewrite M.find_union; unfold morph_header_updates;
 repeat rewrite M.find_add_2 by discriminate;
 rewrite M.find_add_1 by reflexivity; rewrite H; simpl; try rewrite orb_false_r; reflexivity.
Qed.
