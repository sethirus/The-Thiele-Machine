(** Actual copy-rule execution for identity COMPOSE and MORPH_TENSOR.
    The copy input ranges must precede the append workspace to preserve reads. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart
 NormalizationSteps NormalizationLoop NormalizationExecution NormalizationRetirement NormalizationFrame MorphLoading.
From Coq Require Import List String Bool Arith Lia.
Import ListNotations.
Open Scope string_scope.
Definition copy_rule := normalization_rule 5.
Definition copy_first (i c1 : word 5) := word_ltb i c1.
Definition copy_done (i j c1 c2 : word 5) :=
 andb (negb (word_ltb i c1)) (negb (word_ltb j c2)).
Definition copy_full (out : word 5) := word_eqb out (natToWord 5 16).
Definition copy_index (i j c1 : word 5) (a1 a2 : word 4) :=
 if copy_first i c1 then wplus a1 (pair_index i) else wplus a2 (pair_index j).
Definition copy_updates (i j c1 c2 out : word 5) (a1 a2 : word 4)
 (src dst : PairTable) (valid : word 4 -> bool) err code : UpdatesT :=
 let done := copy_done i j c1 c2 in
 let full := copy_full out in
 let blocked := orb done full in
 let overflow := andb (negb done) full in
 let idx := copy_index i j c1 a1 a2 in
 M.add "err" (regbool (orb err overflow))
 (M.add "error_code" (reg32 (if overflow then ERR_COUPLING_INVALID else code))
 (M.add "coupling_pair_src_table" (regpairs (if blocked then src else
 put_vector src (pair_index out) (src idx)))
 (M.add "coupling_pair_dst_table" (regpairs (if blocked then dst else
 put_vector dst (pair_index out) (dst idx)))
 (M.add "coupling_pair_valid_table" (regvalid (if blocked then valid else
 put_vector valid (pair_index out) true))
 (M.add "mc_i" (reg5 (if copy_first i c1 then wplus i (natToWord 5 1) else i))
 (M.add "mc_j" (reg5 (if copy_first i c1 then j else wplus j (natToWord 5 1)))
 (M.add "mc_write_ptr" (reg5 (if blocked then out else wplus out (natToWord 5 1)))
 (M.add "mc_phase" (reg4 (if overflow then natToWord 4 0 else
 if done then natToWord 4 5 else natToWord 4 4)) (M.empty _))))))))).
Lemma copy_rule_name : attrName copy_rule = "mc_copy_loop".
Proof. reflexivity. Qed.
Lemma copy_rule_in : In copy_rule (getRules thieleCore).
Proof. unfold copy_rule, normalization_rule; apply nth_In; change (5<12)%nat; lia. Qed.
Theorem copy_actual_action : forall old i j c1 c2 out a1 a2 src dst valid err code,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 4)) ->
 M.find "mc_i" old = Some (reg5 i) ->
 M.find "mc_j" old = Some (reg5 j) ->
 M.find "mc_src1_base" old = Some (reg4 a1) ->
 M.find "mc_src1_count" old = Some (reg5 c1) ->
 M.find "mc_src2_base" old = Some (reg4 a2) ->
 M.find "mc_src2_count" old = Some (reg5 c2) ->
 M.find "mc_write_ptr" old = Some (reg5 out) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 M.find "coupling_pair_valid_table" old = Some (regvalid valid) ->
 M.find "err" old = Some (regbool err) ->
 M.find "error_code" old = Some (reg32 code) ->
 SemAction old (attrType copy_rule type)
 (copy_updates i j c1 c2 out a1 a2 src dst valid err code) (M.empty _) WO.
Proof.
 intros old i j c1 c2 out a1 a2 src dst valid err code Hp Hi Hj Ha1 Hc1 Ha2 Hc2 Ho Hs Hd Hv He Hcode.
 unfold copy_rule, normalization_rule; cbn [nth getRules attrType].
 eapply SemReadReg; [exact Hp|]. apply SemAssertTrue; [reflexivity|].
 eapply SemReadReg; [exact Hi|]. eapply SemReadReg; [exact Hj|].
 eapply SemReadReg; [exact Ha1|]. eapply SemReadReg; [exact Hc1|].
 eapply SemReadReg; [exact Ha2|]. eapply SemReadReg; [exact Hc2|].
 eapply SemReadReg; [exact Ho|]. eapply SemReadReg; [exact Hs|].
 eapply SemReadReg; [exact Hd|]. eapply SemReadReg; [exact Hv|].
 eapply SemReadReg; [exact He|]. eapply SemReadReg; [exact Hcode|].
 repeat apply SemLet.
 unfold copy_updates, copy_done, copy_full, copy_index, copy_first, word_eqb, word_ltb, pair_index, put_vector.
 do 9 (eapply SemWriteReg; [shelve|reflexivity|]). apply SemReturn; reflexivity.
 Unshelve. all: reflexivity.
Qed.

Record copy_registers old i j c1 c2 out a1 a2 src dst valid err code : Prop := {
 cr_phase : M.find "mc_phase" old = Some (reg4 (natToWord 4 4));
 cr_i : M.find "mc_i" old = Some (reg5 (natToWord 5 i));
 cr_j : M.find "mc_j" old = Some (reg5 (natToWord 5 j));
 cr_a1 : M.find "mc_src1_base" old = Some (reg4 (natToWord 4 a1));
 cr_c1 : M.find "mc_src1_count" old = Some (reg5 (natToWord 5 c1));
 cr_a2 : M.find "mc_src2_base" old = Some (reg4 (natToWord 4 a2));
 cr_c2 : M.find "mc_src2_count" old = Some (reg5 (natToWord 5 c2));
 cr_out : M.find "mc_write_ptr" old = Some (reg5 (natToWord 5 out));
 cr_src : M.find "coupling_pair_src_table" old = Some (regpairs src);
 cr_dst : M.find "coupling_pair_dst_table" old = Some (regpairs dst);
 cr_valid : M.find "coupling_pair_valid_table" old = Some (regvalid valid);
 cr_err : M.find "err" old = Some (regbool err);
 cr_code : M.find "error_code" old = Some (reg32 code)
}.
Definition copy_state old i j c1 c2 out a1 a2 src dst valid err code :=
 M.union (copy_updates (natToWord 5 i) (natToWord 5 j) (natToWord 5 c1) (natToWord 5 c2)
 (natToWord 5 out) (natToWord 4 a1) (natToWord 4 a2) src dst valid err code) old.
Definition copy_footprint := ["err"; "error_code"; "coupling_pair_src_table";
 "coupling_pair_dst_table"; "coupling_pair_valid_table"; "mc_i"; "mc_j"; "mc_write_ptr"; "mc_phase"].
Lemma copy_frame : forall old i j c1 c2 out a1 a2 src dst valid err code key,
 ~ In key copy_footprint ->
 M.find key (copy_state old i j c1 c2 out a1 a2 src dst valid err code) = M.find key old.
Proof.
 intros. unfold copy_state; rewrite M.find_union. unfold copy_updates, copy_footprint in *.
 repeat rewrite M.find_add_2 by (simpl in H; intuition).
 rewrite M.find_empty; reflexivity.
Qed.
Lemma copy_actual_execution : forall old i j c1 c2 out a1 a2 src dst valid err code,
 copy_registers old i j c1 c2 out a1 a2 src dst valid err code ->
 Multistep thieleCore old (copy_state old i j c1 c2 out a1 a2 src dst valid err code)
 [normalization_label "mc_copy_loop"].
Proof.
 intros. apply normalization_substep_execution.
 eapply SingleRule with (a := attrType copy_rule); [exact copy_rule_in|].
 apply copy_actual_action; destruct H; assumption.
Qed.

Lemma pair_index_small : forall n, (n<16)%nat ->
 pair_index (natToWord 5 n) = natToWord 4 n.
Proof.
 intros; apply wordToNat_inj. rewrite normalization_pair_index_exact by assumption.
 rewrite wordToNat_natToWord_2 by (change (n<16)%nat; assumption). reflexivity.
Qed.
Lemma copy_first_nat : forall i c, (i<=16)%nat -> (c<=16)%nat ->
 copy_first (natToWord 5 i) (natToWord 5 c) = Nat.ltb i c.
Proof. intros; unfold copy_first; apply bounded_word_ltb; lia. Qed.
Lemma copy_done_nat : forall i j c1 c2,
 (i<=c1<=16)%nat -> (j<=c2<=16)%nat ->
 copy_done (natToWord 5 i) (natToWord 5 j) (natToWord 5 c1) (natToWord 5 c2) =
 andb (Nat.eqb i c1) (Nat.eqb j c2).
Proof.
 intros. unfold copy_done; rewrite !bounded_word_ltb by lia.
 destruct (Nat.eq_dec i c1) as [Ei|Ei]; destruct (Nat.eq_dec j c2) as [Ej|Ej];
 subst; repeat rewrite Nat.ltb_irrefl; repeat rewrite Nat.eqb_refl;
 try rewrite (proj2 (Nat.ltb_lt i c1) ltac:(lia));
 try rewrite (proj2 (Nat.ltb_lt j c2) ltac:(lia));
 try rewrite (proj2 (Nat.eqb_neq i c1) ltac:(lia));
 try rewrite (proj2 (Nat.eqb_neq j c2) ltac:(lia)); reflexivity.
Qed.
Lemma copy_full_nat : forall out, (out<=16)%nat ->
 copy_full (natToWord 5 out) = Nat.eqb out 16.
Proof. intros; unfold copy_full; apply bounded_word_eqb; lia. Qed.
Lemma copy_index_first_nat : forall i j c1 a1 a2,
 (i<c1<=16)%nat -> (a1+i<16)%nat ->
 copy_index (natToWord 5 i) (natToWord 5 j) (natToWord 5 c1)
 (natToWord 4 a1) (natToWord 4 a2) = pair_index (natToWord 5 (a1+i)).
Proof.
 intros. unfold copy_index. rewrite copy_first_nat by lia.
 rewrite (proj2 (Nat.ltb_lt i c1) ltac:(lia)), !pair_index_small by lia.
 rewrite <- natToWord_plus; reflexivity.
Qed.
Lemma copy_index_second_nat : forall i j c1 c2 a1 a2,
 (i=c1)%nat -> (c1<=16)%nat -> (j<c2<=16)%nat -> (a2+j<16)%nat ->
 copy_index (natToWord 5 i) (natToWord 5 j) (natToWord 5 c1)
 (natToWord 4 a1) (natToWord 4 a2) = pair_index (natToWord 5 (a2+j)).
Proof.
 intros; subst i. unfold copy_index. rewrite copy_first_nat by lia.
 rewrite Nat.ltb_irrefl, !pair_index_small by lia.
 rewrite <- natToWord_plus; reflexivity.
Qed.
Ltac copy_read_map := unfold copy_state; rewrite M.find_union;
 unfold copy_updates; repeat rewrite M.find_add_2 by discriminate;
 rewrite M.find_add_1 by reflexivity.

Lemma copy_done_control : forall c1 c2, (c1<=16)%nat -> (c2<=16)%nat ->
 copy_done (natToWord 5 c1) (natToWord 5 c2) (natToWord 5 c1) (natToWord 5 c2) = true.
Proof. intros; rewrite copy_done_nat by lia; rewrite !Nat.eqb_refl; reflexivity. Qed.
Lemma copy_active_first_control : forall i j c1 c2,
 (i<c1<=16)%nat -> (j<=c2<=16)%nat ->
 copy_done (natToWord 5 i) (natToWord 5 j) (natToWord 5 c1) (natToWord 5 c2) = false.
Proof. intros; rewrite copy_done_nat by lia; rewrite (proj2 (Nat.eqb_neq i c1) ltac:(lia)); reflexivity. Qed.
Lemma copy_active_second_control : forall c1 j c2,
 (c1<=16)%nat -> (j<c2<=16)%nat ->
 copy_done (natToWord 5 c1) (natToWord 5 j) (natToWord 5 c1) (natToWord 5 c2) = false.
Proof. intros; rewrite copy_done_nat by lia; rewrite Nat.eqb_refl, (proj2 (Nat.eqb_neq j c2) ltac:(lia)); reflexivity. Qed.

Lemma copy_terminal_result : forall old c1 c2 out a1 a2 src dst valid err code,
 (c1<=16)%nat -> (c2<=16)%nat ->
 let final := copy_state old c1 c2 c1 c2 out a1 a2 src dst valid err code in
 M.find "mc_phase" final = Some (reg4 (natToWord 4 5)) /\
 M.find "mc_write_ptr" final = Some (reg5 (natToWord 5 out)) /\
 M.find "mc_i" final = Some (reg5 (natToWord 5 c1)) /\
 M.find "mc_j" final = Some (reg5 (natToWord 5 (S c2))) /\
 M.find "coupling_pair_src_table" final = Some (regpairs src) /\
 M.find "coupling_pair_dst_table" final = Some (regpairs dst) /\
 M.find "coupling_pair_valid_table" final = Some (regvalid valid) /\
 M.find "err" final = Some (regbool err) /\
 M.find "error_code" final = Some (reg32 code).
Proof.
 intros old c1 c2 out a1 a2 src dst valid err code Hc1 Hc2; cbv zeta.
 repeat split; copy_read_map;
 try rewrite copy_done_control by assumption;
 try rewrite copy_first_nat by lia;
 try rewrite Nat.ltb_irrefl; cbn [andb orb negb];
 try rewrite orb_false_r; try rewrite <- natToWord_plus;
 try replace (c2+1)%nat with (S c2) by lia; reflexivity.
Qed.

Lemma copy_capacity_failure : forall old i j c1 c2 a1 a2 src dst valid err code,
 copy_done (natToWord 5 i) (natToWord 5 j) (natToWord 5 c1) (natToWord 5 c2) = false ->
 let final := copy_state old i j c1 c2 16 a1 a2 src dst valid err code in
 M.find "mc_phase" final = Some (reg4 (natToWord 4 0)) /\
 M.find "err" final = Some (regbool true) /\
 M.find "error_code" final = Some (reg32 ERR_COUPLING_INVALID) /\
 M.find "mc_write_ptr" final = Some (reg5 (natToWord 5 16)) /\
 M.find "coupling_pair_src_table" final = Some (regpairs src) /\
 M.find "coupling_pair_dst_table" final = Some (regpairs dst) /\
 M.find "coupling_pair_valid_table" final = Some (regvalid valid).
Proof.
 intros old i j c1 c2 a1 a2 src dst valid err code Hdone; cbv zeta.
 repeat split; copy_read_map; rewrite Hdone;
 change (copy_full (natToWord 5 16)) with true; cbn [andb orb negb]; try rewrite orb_true_r; reflexivity.
Qed.

Definition cursor_i i c1 := if Nat.ltb i c1 then S i else i.
Definition cursor_j i j c1 := if Nat.ltb i c1 then j else S j.
Definition source_index i j c1 a1 a2 := if Nat.ltb i c1 then (a1+i)%nat else (a2+j)%nat.
Definition pair_at (table : PairTable) k := table (pair_index (natToWord 5 k)).
Definition append_pair (table : PairTable) out value := put_vector table (pair_index (natToWord 5 out)) value.
Lemma copy_active_registers : forall old i j c1 c2 out a1 a2 src dst valid err code,
 (i<=c1<=16)%nat -> (j<=c2<=16)%nat -> (out<16)%nat ->
 ((i<c1) \/ (j<c2))%nat ->
 (a1+c1<=16)%nat -> (a2+c2<=16)%nat ->
 copy_registers old i j c1 c2 out a1 a2 src dst valid err code ->
 copy_registers (copy_state old i j c1 c2 out a1 a2 src dst valid err code)
 (cursor_i i c1) (cursor_j i j c1) c1 c2 (S out) a1 a2
 (append_pair src out (pair_at src (source_index i j c1 a1 a2)))
 (append_pair dst out (pair_at dst (source_index i j c1 a1 a2)))
 (put_vector valid (pair_index (natToWord 5 out)) true) err code.
Proof.
 intros old i j c1 c2 out a1 a2 src dst valid err code Hi Hj Ho Hactive Ha1 Ha2 Hr.
 assert (Hdone : copy_done (natToWord 5 i) (natToWord 5 j) (natToWord 5 c1) (natToWord 5 c2) = false).
 { destruct (Nat.lt_ge_cases i c1).
   - apply copy_active_first_control; lia.
   - assert (i=c1) by lia; subst; apply copy_active_second_control; lia. }
 assert (Hfull : copy_full (natToWord 5 out) = false).
 { rewrite copy_full_nat by lia; apply Nat.eqb_neq; lia. }
 assert (Hidx : copy_index (natToWord 5 i) (natToWord 5 j) (natToWord 5 c1)
 (natToWord 4 a1) (natToWord 4 a2) = pair_index (natToWord 5 (source_index i j c1 a1 a2))).
 { unfold source_index; destruct (Nat.ltb i c1) eqn:E.
   - apply Nat.ltb_lt in E; apply copy_index_first_nat; lia.
   - apply Nat.ltb_ge in E; eapply copy_index_second_nat with (c2:=c2); lia. }
 constructor;
 try (rewrite copy_frame by (unfold copy_footprint; simpl; intuition discriminate); destruct Hr; assumption);
 copy_read_map; try rewrite Hdone; try rewrite Hfull;
 try rewrite copy_first_nat by lia; try rewrite Hidx;
 cbn [andb orb negb]; try rewrite orb_false_r;
 unfold cursor_i, cursor_j, append_pair, pair_at;
 try rewrite <- natToWord_plus;
 try replace (out+1)%nat with (S out) by lia;
 try destruct (Nat.ltb i c1);
 try rewrite <- natToWord_plus;
 try replace (i+1)%nat with (S i) by lia;
 try replace (j+1)%nat with (S j) by lia; reflexivity.
Qed.

Definition low_agrees b (table raw : PairTable) := forall k, (k<b)%nat -> pair_at table k = pair_at raw k.
Lemma append_pair_preserves_low : forall b out table raw value,
 (b<=out<16)%nat -> low_agrees b table raw ->
 low_agrees b (append_pair table out value) raw.
Proof.
 intros b out table raw value Hb Hlow k Hk.
 unfold pair_at, append_pair, put_vector.
 destruct (weq (pair_index (natToWord 5 k)) (pair_index (natToWord 5 out))) as [E|E].
 - exfalso; apply (normalization_distinct_pair_indices k out ltac:(lia) ltac:(lia) ltac:(lia)); exact E.
 - apply Hlow; exact Hk.
Qed.
Definition remaining_pairs rawsrc rawdst a1 c1 a2 c2 i j :=
 List.app (table_slice rawsrc rawdst (a1+i) (c1-i))
 (table_slice rawsrc rawdst (a2+j) (c2-j)).
Lemma table_slice_cons : forall src dst start n,
 table_slice src dst start (S n) =
 cons (table_pair src dst start) (table_slice src dst (S start) n).
Proof. reflexivity. Qed.
Lemma remaining_pairs_length : forall rawsrc rawdst a1 c1 a2 c2 i j,
 List.length (remaining_pairs rawsrc rawdst a1 c1 a2 c2 i j) = (c1-i+(c2-j))%nat.
Proof.
 intros; unfold remaining_pairs, table_slice. rewrite app_length, !map_length, !seq_length; reflexivity.
Qed.
Lemma remaining_pairs_cons : forall rawsrc rawdst a1 c1 a2 c2 i j,
 (i<=c1)%nat -> (j<=c2)%nat -> ((i<c1) \/ (j<c2))%nat ->
 remaining_pairs rawsrc rawdst a1 c1 a2 c2 i j =
 cons (table_pair rawsrc rawdst (source_index i j c1 a1 a2))
 (remaining_pairs rawsrc rawdst a1 c1 a2 c2 (cursor_i i c1) (cursor_j i j c1)).
Proof.
 intros. unfold source_index, cursor_i, cursor_j.
 destruct (Nat.ltb i c1) eqn:E.
 - apply Nat.ltb_lt in E. unfold remaining_pairs.
   replace (c1-i)%nat with (S (c1-S i)) by lia.
   rewrite table_slice_cons. simpl List.app.
   replace (S (a1+i))%nat with (a1+S i)%nat by lia. reflexivity.
 - apply Nat.ltb_ge in E. assert (i=c1) by lia; subst.
   unfold remaining_pairs. rewrite Nat.sub_diag. cbn [table_slice seq map List.app].
   replace (c2-j)%nat with (S (c2-S j)) by lia.
   rewrite table_slice_cons. replace (S (a2+j))%nat with (a2+S j)%nat by lia. reflexivity.
Qed.
Fixpoint store_pairs (table : PairTable) out (pairs : list (word 32 * word 32)) (first : bool) : PairTable :=
 match pairs with
 | nil => table
 | p::ps => store_pairs (append_pair table out (if first then fst p else snd p)) (S out) ps first
 end.

Theorem copy_loop_execution : forall n old rawsrc rawdst src dst valid err code
 b out i j c1 c2 a1 a2,
 (c1-i+(c2-j)=n)%nat ->
 (i<=c1<=16)%nat -> (j<=c2<=16)%nat ->
 (b<=out)%nat -> (out+n<=16)%nat ->
 (a1+c1<=b)%nat -> (a2+c2<=b)%nat ->
 low_agrees b src rawsrc -> low_agrees b dst rawdst ->
 copy_registers old i j c1 c2 out a1 a2 src dst valid err code ->
 exists final,
 Multistep thieleCore old final (repeat (normalization_label "mc_copy_loop") (S n)) /\
 M.find "mc_phase" final = Some (reg4 (natToWord 4 5)) /\
 M.find "mc_write_ptr" final = Some (reg5 (natToWord 5 (out+n))) /\
 M.find "mc_i" final = Some (reg5 (natToWord 5 c1)) /\
 M.find "mc_j" final = Some (reg5 (natToWord 5 (S c2))) /\
 M.find "coupling_pair_src_table" final =
 Some (regpairs (store_pairs src out (remaining_pairs rawsrc rawdst a1 c1 a2 c2 i j) true)) /\
 M.find "coupling_pair_dst_table" final =
 Some (regpairs (store_pairs dst out (remaining_pairs rawsrc rawdst a1 c1 a2 c2 i j) false)) /\
 M.find "err" final = Some (regbool err) /\
 M.find "error_code" final = Some (reg32 code) /\
 (forall key, ~ In key copy_footprint -> M.find key final = M.find key old).
Proof.
 induction n as [|n IH]; intros old rawsrc rawdst src dst valid err code
 b out i j c1 c2 a1 a2 Hn Hi Hj Hb Hspace Ha1 Ha2 HlowS HlowD Hr.
 - assert (i=c1) by lia. assert (j=c2) by lia. subst i j.
   exists (copy_state old c1 c2 c1 c2 out a1 a2 src dst valid err code).
   split; [apply copy_actual_execution; exact Hr|].
   destruct (copy_terminal_result old c1 c2 out a1 a2 src dst valid err code ltac:(lia) ltac:(lia))
   as [Hp [Ho [Hii [Hjj [Hs [Hd [Hv [He Hc]]]]]]]].
   unfold remaining_pairs; rewrite !Nat.sub_diag; cbn [table_slice seq map List.app store_pairs].
   rewrite Nat.add_0_r. do 8 (split; [assumption|]). apply copy_frame.
 - assert (Hactive : ((i<c1) \/ (j<c2))%nat) by lia.
   assert (Hidx : (source_index i j c1 a1 a2 < b)%nat).
   { unfold source_index; destruct (Nat.ltb i c1) eqn:E;
     [apply Nat.ltb_lt in E|apply Nat.ltb_ge in E]; lia. }
   pose (idx := source_index i j c1 a1 a2).
   pose (next := copy_state old i j c1 c2 out a1 a2 src dst valid err code).
   pose (src1 := append_pair src out (pair_at rawsrc idx)).
   pose (dst1 := append_pair dst out (pair_at rawdst idx)).
   pose (valid1 := put_vector valid (pair_index (natToWord 5 out)) true).
   assert (Hnext : copy_registers next (cursor_i i c1) (cursor_j i j c1) c1 c2
    (S out) a1 a2 src1 dst1 valid1 err code).
   { pose proof (copy_active_registers old i j c1 c2 out a1 a2 src dst valid err code
     Hi Hj ltac:(lia) Hactive ltac:(lia) ltac:(lia) Hr) as H.
     rewrite HlowS, HlowD in H by exact Hidx. exact H. }
   assert (Hnnext : (c1-cursor_i i c1+(c2-cursor_j i j c1)=n)%nat).
   { unfold cursor_i, cursor_j. destruct (Nat.ltb i c1) eqn:E;
     [apply Nat.ltb_lt in E|apply Nat.ltb_ge in E]; lia. }
   assert (Hinext : (cursor_i i c1<=c1<=16)%nat).
   { unfold cursor_i; destruct (Nat.ltb i c1) eqn:E;
     [apply Nat.ltb_lt in E|apply Nat.ltb_ge in E]; lia. }
   assert (Hjnext : (cursor_j i j c1<=c2<=16)%nat).
   { unfold cursor_j; destruct (Nat.ltb i c1) eqn:E;
     [apply Nat.ltb_lt in E|apply Nat.ltb_ge in E]; lia. }
   destruct (IH next rawsrc rawdst src1 dst1 valid1 err code b (S out)
    (cursor_i i c1) (cursor_j i j c1) c1 c2 a1 a2
    Hnnext Hinext Hjnext ltac:(lia) ltac:(lia) Ha1 Ha2
    (append_pair_preserves_low b out src rawsrc _ ltac:(lia) HlowS)
    (append_pair_preserves_low b out dst rawdst _ ltac:(lia) HlowD) Hnext)
    as [final [Hrun [Hp [Ho [Hii [Hjj [Hs [Hd [He [Hc Hframe]]]]]]]]]].
   exists final. split.
   + replace (S (S n)) with (S n+1)%nat by lia. rewrite repeat_app; cbn [repeat].
     eapply normalization_multistep_trans; [apply copy_actual_execution; exact Hr|exact Hrun].
   + split; [exact Hp|]. split; [replace (out+S n)%nat with (S out+n)%nat by lia; exact Ho|].
     split; [exact Hii|]. split; [exact Hjj|].
     split; [rewrite remaining_pairs_cons by lia; exact Hs|].
     split; [rewrite remaining_pairs_cons by lia; exact Hd|].
     split; [exact He|]. split; [exact Hc|].
     intros key Hkey; rewrite Hframe by exact Hkey; apply copy_frame; exact Hkey.
Qed.

Lemma store_pairs_untouched : forall pairs table out first k,
 (out+List.length pairs<=16)%nat -> (k<16)%nat -> ((k<out) \/ (out+List.length pairs<=k))%nat ->
 pair_at (store_pairs table out pairs first) k = pair_at table k.
Proof.
 induction pairs as [|p ps IH]; intros table out first k Hb Hk Hout; cbn [store_pairs].
 - reflexivity.
 - rewrite IH by (simpl in *; lia).
   unfold pair_at, append_pair, put_vector.
   destruct (weq (pair_index (natToWord 5 k)) (pair_index (natToWord 5 out))) as [E|E].
   + exfalso; apply (normalization_distinct_pair_indices k out ltac:(lia) ltac:(simpl in *; lia) ltac:(simpl in *; lia)); exact E.
   + reflexivity.
Qed.
Lemma store_pairs_target : forall pairs p table out first,
 (out+S (List.length pairs)<=16)%nat ->
 pair_at (store_pairs table out (p::pairs) first) out = if first then fst p else snd p.
Proof.
 intros. cbn [store_pairs]. rewrite store_pairs_untouched by lia.
 unfold pair_at, append_pair, put_vector.
 destruct (weq (pair_index (natToWord 5 out)) (pair_index (natToWord 5 out)));
 [reflexivity|contradiction].
Qed.
Theorem store_pairs_slice : forall pairs src dst out,
 (out+List.length pairs<=16)%nat ->
 table_slice (store_pairs src out pairs true) (store_pairs dst out pairs false)
 out (List.length pairs) = pairs.
Proof.
 induction pairs as [|[s d] ps IH]; intros src dst out Hb; [reflexivity|].
 cbn [List.length]. rewrite table_slice_cons.
 change (cons (pair_at (store_pairs src out ((s,d)::ps) true) out,
 pair_at (store_pairs dst out ((s,d)::ps) false) out)
 (table_slice (store_pairs src out ((s,d)::ps) true)
 (store_pairs dst out ((s,d)::ps) false) (S out) (List.length ps)) = (s,d)::ps).
 rewrite !store_pairs_target by exact Hb. cbn [fst snd store_pairs].
 rewrite IH by (simpl in Hb; lia). reflexivity.
Qed.

Theorem copy_admitted_loading : forall old b a1 c1 a2 c2 src dst valid err code,
 (b+c1+c2<=16)%nat -> (a1+c1<=b)%nat -> (a2+c2<=b)%nat ->
 copy_registers old 0 0 c1 c2 b a1 a2 src dst valid err code ->
 exists final src' dst',
 Multistep thieleCore old final
 (repeat (normalization_label "mc_copy_loop") (S (c1+c2))) /\
 M.find "mc_phase" final = Some (reg4 (natToWord 4 5)) /\
 M.find "mc_write_ptr" final = Some (reg5 (natToWord 5 (b+c1+c2))) /\
 M.find "mc_i" final = Some (reg5 (natToWord 5 c1)) /\
 M.find "mc_j" final = Some (reg5 (natToWord 5 (S c2))) /\
 M.find "coupling_pair_src_table" final = Some (regpairs src') /\
 M.find "coupling_pair_dst_table" final = Some (regpairs dst') /\
 table_slice src' dst' b (c1+c2) =
 List.app (table_slice src dst a1 c1) (table_slice src dst a2 c2) /\
 low_agrees b src' src /\ low_agrees b dst' dst /\
 M.find "err" final = Some (regbool err) /\
 M.find "error_code" final = Some (reg32 code) /\
 (forall key, ~ In key copy_footprint -> M.find key final = M.find key old).
Proof.
 intros old b a1 c1 a2 c2 src dst valid err code Hcap Ha1 Ha2 Hr.
 destruct (copy_loop_execution (c1+c2) old src dst src dst valid err code
 b b 0 0 c1 c2 a1 a2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
 Ha1 Ha2 ltac:(intros k Hk; reflexivity) ltac:(intros k Hk; reflexivity) Hr)
 as [final [Hrun [Hp [Ho [Hi [Hj [Hs [Hd [He [Hcode Hframe]]]]]]]]]].
 unfold remaining_pairs in Hs, Hd. rewrite !Nat.add_0_r, !Nat.sub_0_r in Hs, Hd.
 pose (pairs := List.app (table_slice src dst a1 c1) (table_slice src dst a2 c2)).
 assert (Hlen : List.length pairs = (c1+c2)%nat).
 { unfold pairs,table_slice; rewrite app_length,!map_length,!seq_length; reflexivity. }
 exists final, (store_pairs src b pairs true), (store_pairs dst b pairs false).
 split; [exact Hrun|]. split; [exact Hp|].
 split; [replace (b+c1+c2)%nat with (b+(c1+c2))%nat by lia; exact Ho|].
 split; [exact Hi|]. split; [exact Hj|]. split; [exact Hs|]. split; [exact Hd|].
 split; [rewrite <- Hlen; apply store_pairs_slice; change (b+List.length pairs<=16)%nat; rewrite Hlen; lia|].
 split; [intros k Hk; apply (store_pairs_untouched pairs src b true k); [change (b+List.length pairs<=16)%nat; rewrite Hlen; lia|lia|left; exact Hk]|].
 split; [intros k Hk; apply (store_pairs_untouched pairs dst b false k); [change (b+List.length pairs<=16)%nat; rewrite Hlen; lia|lia|left; exact Hk]|].
 split; [exact He|]. split; [exact Hcode|exact Hframe].
Qed.

Theorem copy_cursor_updates_even_when_blocked : forall old i j c1 c2 out a1 a2 src dst valid err code,
 (i<=16)%nat -> (c1<=16)%nat ->
 M.find "mc_i" (copy_state old i j c1 c2 out a1 a2 src dst valid err code) =
 Some (reg5 (natToWord 5 (cursor_i i c1))) /\
 M.find "mc_j" (copy_state old i j c1 c2 out a1 a2 src dst valid err code) =
 Some (reg5 (natToWord 5 (cursor_j i j c1))).
Proof.
 intros; split; copy_read_map; rewrite copy_first_nat by assumption;
 unfold cursor_i,cursor_j; destruct (Nat.ltb i c1); try reflexivity;
 rewrite <- natToWord_plus;
 [replace (i+1)%nat with (S i) by lia|replace (j+1)%nat with (S j) by lia]; reflexivity.
Qed.
Theorem copy_admitted_firing_bound : forall b c1 c2,
 (b+c1+c2<=16)%nat ->
 (List.length (repeat (normalization_label "mc_copy_loop") (S (c1+c2))) <= 17)%nat.
Proof. intros; rewrite repeat_length; lia. Qed.

Definition copy_retirement_footprint := List.app copy_footprint outer_footprint.
Theorem copy_retirement : forall old b a1 c1 a2 c2 src dst valid err code
 d bases counts descvalid,
 (b+c1+c2<=16)%nat -> (a1+c1<=b)%nat -> (a2+c2<=b)%nat ->
 copy_registers old 0 0 c1 c2 b a1 a2 src dst valid err code ->
 M.find "mc_write_base" old = Some (reg5 (natToWord 5 b)) ->
 M.find "coupling_desc_next_id" old = Some (reg5 d) ->
 M.find "coupling_desc_base_table" old = Some (regbases bases) ->
 M.find "coupling_desc_count_table" old = Some (regcounts counts) ->
 M.find "coupling_desc_valid_table" old = Some (regvalid descvalid) ->
 exists precommit labels src' dst' out,
 (b<=out<=b+c1+c2)%nat /\
 Multistep thieleCore old
 (M.union (normalization_commit_updates (natToWord 5 b) (natToWord 5 out)
    d bases counts descvalid) precommit) labels /\
 M.find "mc_phase"
 (M.union (normalization_commit_updates (natToWord 5 b) (natToWord 5 out)
    d bases counts descvalid) precommit) = Some (reg4 (natToWord 4 0)) /\
 M.find "coupling_pair_src_table" precommit = Some (regpairs src') /\
 M.find "coupling_pair_dst_table" precommit = Some (regpairs dst') /\
 table_slice src' dst' b (out-b) = nodup coupling_pair_eq_dec
 (List.app (table_slice src dst a1 c1) (table_slice src dst a2 c2)) /\
 List.length labels = (c1+c2+3+outer_firings (c1+c2))%nat /\
 (forall key, ~ In key copy_retirement_footprint -> M.find key precommit = M.find key old) /\
 table_prefix_agrees b src' dst' src dst.
Proof.
 intros old b a1 c1 a2 c2 src dst valid err code d bases counts descvalid
 Hspace Ha1 Ha2 Hr Hbase Hd Hbs Hcs Hvs.
 destruct (copy_admitted_loading old b a1 c1 a2 c2 src dst valid err code Hspace Ha1 Ha2 Hr)
 as [loaded [lsrc [ldst [Hload [Hphase [Hend [Hii [Hjj [Hls [Hld [Hrawpairs
 [HlowS [HlowD [Herr [Hcode Hframe]]]]]]]]]]]]]]].
 assert (Lbase : M.find "mc_write_base" loaded = Some (reg5 (natToWord 5 b))).
 { rewrite Hframe; [assumption|unfold copy_footprint; simpl; intuition discriminate]. }
 assert (Ld : M.find "coupling_desc_next_id" loaded = Some (reg5 d)).
 { rewrite Hframe; [assumption|unfold copy_footprint; simpl; intuition discriminate]. }
 assert (Lbs : M.find "coupling_desc_base_table" loaded = Some (regbases bases)).
 { rewrite Hframe; [assumption|unfold copy_footprint; simpl; intuition discriminate]. }
 assert (Lcs : M.find "coupling_desc_count_table" loaded = Some (regcounts counts)).
 { rewrite Hframe; [assumption|unfold copy_footprint; simpl; intuition discriminate]. }
 assert (Lvs : M.find "coupling_desc_valid_table" loaded = Some (regvalid descvalid)).
 { rewrite Hframe; [assumption|unfold copy_footprint; simpl; intuition discriminate]. }
 destruct (normalization_retirement_with_prefix loaded lsrc ldst b (b+c1+c2) d bases counts descvalid
 ltac:(lia) Hspace Hphase Lbase Hend Hls Hld Ld Lbs Lcs Lvs)
 as [pre [labels [src' [dst' [out [Hbound [Hnorm [Hzero [Hs [Ht [Hpairs [Hnormframe [Hlen Hnormprefix]]]]]]]]]]]]].
 exists pre, (List.app labels (repeat (normalization_label "mc_copy_loop") (S (c1+c2)))), src', dst', out.
 split; [exact Hbound|]. split; [eapply normalization_multistep_trans; eassumption|].
 split; [exact Hzero|]. split; [exact Hs|]. split; [exact Ht|].
 split.
 - rewrite Hpairs. replace (b+c1+c2-b)%nat with (c1+c2)%nat by lia.
   rewrite Hrawpairs; reflexivity.
 - split.
   + rewrite app_length, repeat_length, Hlen.
     replace (b+c1+c2-b)%nat with (c1+c2)%nat by lia. lia.
   + split.
     * intros key Hkey. rewrite Hnormframe.
       -- apply Hframe. unfold copy_retirement_footprint in Hkey.
          rewrite in_app_iff in Hkey; intuition.
       -- unfold copy_retirement_footprint in Hkey. rewrite in_app_iff in Hkey; intuition.
     * intros k Hk. rewrite Hnormprefix by exact Hk.
       change ((pair_at lsrc k, pair_at ldst k) = (pair_at src k, pair_at dst k)).
       rewrite HlowS, HlowD by exact Hk. reflexivity.
Qed.
Theorem copy_retirement_firing_bound : forall b c1 c2,
 (b+c1+c2<=16)%nat -> (c1+c2+3+outer_firings (c1+c2)<=171)%nat.
Proof. intros; pose proof (normalization_outer_firing_formula (c1+c2)); nia. Qed.

(** The same prefix relation gives both component readouts and all old raw
    intervals below the append base. Descriptor metadata still requires its
    explicit frame/freshness conditions. *)
Lemma copy_retirement_prefix_components : forall b src dst rawsrc rawdst,
 table_prefix_agrees b src dst rawsrc rawdst ->
 low_agrees b src rawsrc /\ low_agrees b dst rawdst.
Proof.
 intros b src dst rawsrc rawdst Hprefix. split; intros k Hk.
 - exact (f_equal (@fst (word 32) (word 32)) (Hprefix k Hk)).
 - exact (f_equal (@snd (word 32) (word 32)) (Hprefix k Hk)).
Qed.
