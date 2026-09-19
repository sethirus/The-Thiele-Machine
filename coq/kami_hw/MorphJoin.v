(** Actual phase-7 relational join. The selected schedule is row-major and
    tests exact word equality. Input tables precede the append workspace. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart
 NormalizationSteps NormalizationLoop NormalizationExecution NormalizationRetirement NormalizationFrame MorphLoading MorphCopy.
From Coq Require Import List String Bool Arith Lia.
Import ListNotations.
Open Scope string_scope.
Definition join_rule := normalization_rule 6.
Definition join_empty (c1 c2 : word 5) :=
 orb (word_eqb c1 (natToWord 5 0)) (word_eqb c2 (natToWord 5 0)).
Definition join_index (a : word 4) (i : word 5) := wplus a (pair_index i).
Definition join_match i j a1 a2 (src dst : PairTable) :=
 word_eqb (dst (join_index a1 i)) (src (join_index a2 j)).
Definition join_emits i j c1 c2 out a1 a2 src dst :=
 andb (andb (negb (join_empty c1 c2)) (join_match i j a1 a2 src dst))
 (word_ltb out (natToWord 5 16)).
Definition join_overflow i j c1 c2 out a1 a2 src dst :=
 andb (andb (negb (join_empty c1 c2)) (join_match i j a1 a2 src dst))
 (negb (word_ltb out (natToWord 5 16))).
Definition join_wrap (j c2 : word 5) := word_eqb (wplus j (natToWord 5 1)) c2.
Definition join_done (i j c1 c2 : word 5) :=
 andb (join_wrap j c2) (word_eqb (wplus i (natToWord 5 1)) c1).
Definition join_updates (i j c1 c2 out : word 5) (a1 a2 : word 4)
 (src dst : PairTable) (valid : word 4 -> bool) err code : UpdatesT :=
 let emits := join_emits i j c1 c2 out a1 a2 src dst in
 let overflow := join_overflow i j c1 c2 out a1 a2 src dst in
 M.add "err" (regbool (orb err overflow))
 (M.add "error_code" (reg32 (if overflow then ERR_COUPLING_INVALID else code))
 (M.add "coupling_pair_src_table" (regpairs (if emits then
 append_pair src (wordToNat out) (src (join_index a1 i)) else src))
 (M.add "coupling_pair_dst_table" (regpairs (if emits then
 append_pair dst (wordToNat out) (dst (join_index a2 j)) else dst))
 (M.add "coupling_pair_valid_table" (regvalid (if emits then
 put_vector valid (pair_index out) true else valid))
 (M.add "mc_write_ptr" (reg5 (if emits then wplus out (natToWord 5 1) else out))
 (M.add "mc_j" (reg5 (if join_wrap j c2 then natToWord 5 0 else wplus j (natToWord 5 1)))
 (M.add "mc_i" (reg5 (if join_wrap j c2 then wplus i (natToWord 5 1) else i))
 (M.add "mc_phase" (reg4 (if overflow then natToWord 4 0 else
 if orb (join_empty c1 c2) (join_done i j c1 c2) then natToWord 4 5 else natToWord 4 7))
 (M.empty _))))))))).
Lemma join_rule_name : attrName join_rule = "mc_join_loop".
Proof. reflexivity. Qed.
Lemma join_rule_in : In join_rule (getRules thieleCore).
Proof. unfold join_rule,normalization_rule; apply nth_In; change (6<12)%nat; lia. Qed.
Theorem join_actual_action : forall old i j c1 c2 out a1 a2 src dst valid err code,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 7)) ->
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
 SemAction old (attrType join_rule type)
 (join_updates i j c1 c2 out a1 a2 src dst valid err code) (M.empty _) WO.
Proof.
 intros old i j c1 c2 out a1 a2 src dst valid err code Hp Hi Hj Ha1 Hc1 Ha2 Hc2 Ho Hs Hd Hv He Hcode.
 unfold join_rule, normalization_rule; cbn [nth getRules attrType].
 eapply SemReadReg; [exact Hp|]. apply SemAssertTrue; [reflexivity|].
 eapply SemReadReg; [exact Hi|]. eapply SemReadReg; [exact Hj|].
 eapply SemReadReg; [exact Ha1|]. eapply SemReadReg; [exact Hc1|].
 eapply SemReadReg; [exact Ha2|]. eapply SemReadReg; [exact Hc2|].
 eapply SemReadReg; [exact Ho|]. eapply SemReadReg; [exact Hs|].
 eapply SemReadReg; [exact Hd|]. eapply SemReadReg; [exact Hv|].
 eapply SemReadReg; [exact He|]. eapply SemReadReg; [exact Hcode|].
 repeat apply SemLet.
 unfold join_updates, join_emits, join_overflow, join_empty, join_done, join_wrap,
 join_match, join_index, word_eqb, word_ltb, append_pair.
 rewrite !natToWord_wordToNat.
 do 2 (eapply SemWriteReg; [shelve|reflexivity|]).
 repeat apply SemLet.
 unfold put_vector, pair_index.
 do 7 (eapply SemWriteReg; [shelve|reflexivity|]). apply SemReturn; reflexivity.
 Unshelve. all: reflexivity.
Qed.

Record join_registers_at (phase : nat) old i j c1 c2 out a1 a2 src dst valid err code : Prop := {
 jr_phase : M.find "mc_phase" old = Some (reg4 (natToWord 4 phase));
 jr_i : M.find "mc_i" old = Some (reg5 (natToWord 5 i));
 jr_j : M.find "mc_j" old = Some (reg5 (natToWord 5 j));
 jr_a1 : M.find "mc_src1_base" old = Some (reg4 (natToWord 4 a1));
 jr_c1 : M.find "mc_src1_count" old = Some (reg5 (natToWord 5 c1));
 jr_a2 : M.find "mc_src2_base" old = Some (reg4 (natToWord 4 a2));
 jr_c2 : M.find "mc_src2_count" old = Some (reg5 (natToWord 5 c2));
 jr_out : M.find "mc_write_ptr" old = Some (reg5 (natToWord 5 out));
 jr_src : M.find "coupling_pair_src_table" old = Some (regpairs src);
 jr_dst : M.find "coupling_pair_dst_table" old = Some (regpairs dst);
 jr_valid : M.find "coupling_pair_valid_table" old = Some (regvalid valid);
 jr_err : M.find "err" old = Some (regbool err);
 jr_code : M.find "error_code" old = Some (reg32 code)
}.
Definition join_registers := join_registers_at 7.
Definition join_state old i j c1 c2 out a1 a2 src dst valid err code :=
 M.union (join_updates (natToWord 5 i) (natToWord 5 j) (natToWord 5 c1) (natToWord 5 c2)
 (natToWord 5 out) (natToWord 4 a1) (natToWord 4 a2) src dst valid err code) old.
Definition join_footprint := ["err"; "error_code"; "coupling_pair_src_table";
 "coupling_pair_dst_table"; "coupling_pair_valid_table"; "mc_i"; "mc_j"; "mc_write_ptr"; "mc_phase"].
Lemma join_frame : forall old i j c1 c2 out a1 a2 src dst valid err code key,
 ~ In key join_footprint ->
 M.find key (join_state old i j c1 c2 out a1 a2 src dst valid err code) = M.find key old.
Proof.
 intros. unfold join_state; rewrite M.find_union. unfold join_updates, join_footprint in *.
 repeat rewrite M.find_add_2 by (simpl in H; intuition).
 rewrite M.find_empty; reflexivity.
Qed.

Lemma join_actual_execution : forall old i j c1 c2 out a1 a2 src dst valid err code,
 join_registers old i j c1 c2 out a1 a2 src dst valid err code ->
 Multistep thieleCore old (join_state old i j c1 c2 out a1 a2 src dst valid err code)
 [normalization_label "mc_join_loop"].
Proof.
 intros. apply normalization_substep_execution.
 eapply SingleRule with (a := attrType join_rule); [exact join_rule_in|].
 apply join_actual_action; destruct H; assumption.
Qed.


Lemma join_index_nat : forall a i, (a+i<16)%nat ->
 join_index (natToWord 4 a) (natToWord 5 i) = pair_index (natToWord 5 (a+i)).
Proof.
 intros; unfold join_index; rewrite !pair_index_small by lia;
 rewrite <- natToWord_plus; reflexivity.
Qed.
Definition candidate_match src dst a1 a2 i j :=
 word_eqb (pair_at dst (a1+i)) (pair_at src (a2+j)).
Definition candidate_pair src dst a1 a2 i j :=
 (pair_at src (a1+i), pair_at dst (a2+j)).
Definition candidate_output src dst a1 a2 i j :=
 if candidate_match src dst a1 a2 i j then [candidate_pair src dst a1 a2 i j] else nil.
Definition join_cursor_i i j c2 := if Nat.eqb (S j) c2 then S i else i.
Definition join_cursor_j j c2 := if Nat.eqb (S j) c2 then 0 else S j.
Definition candidate_row (i j c2 : nat) := map (fun k => (i,k)) (seq j (c2-j)).
Definition candidate_indices i j c1 c2 :=
 if Nat.ltb i c1 then
 List.app (candidate_row i j c2)
 (flat_map (fun k => candidate_row k 0 c2) (seq (S i) (c1-S i))) else nil.
Definition remaining_join src dst a1 a2 i j c1 c2 :=
 flat_map (fun p => candidate_output src dst a1 a2 (fst p) (snd p))
 (candidate_indices i j c1 c2).
Lemma full_rows_as_candidates : forall i c1 c2,
 (i<=c1)%nat ->
 flat_map (fun k => candidate_row k 0 c2) (seq i (c1-i)) = candidate_indices i 0 c1 c2.
Proof.
 intros. unfold candidate_indices. destruct (Nat.ltb i c1) eqn:E.
 - apply Nat.ltb_lt in E. replace (c1-i)%nat with (S (c1-S i)) by lia.
   reflexivity.
 - apply Nat.ltb_ge in E. assert (i=c1) by lia; subst; rewrite Nat.sub_diag; reflexivity.
Qed.
Lemma candidate_indices_cons : forall i j c1 c2,
 (i<c1)%nat -> (j<c2)%nat ->
 candidate_indices i j c1 c2 =
 (i,j)::candidate_indices (join_cursor_i i j c2) (join_cursor_j j c2) c1 c2.
Proof.
 intros i j c1 c2 Hi Hj. unfold join_cursor_i,join_cursor_j.
 destruct (Nat.eqb (S j) c2) eqn:E.
 - apply Nat.eqb_eq in E.
   unfold candidate_indices at 1. rewrite (proj2 (Nat.ltb_lt i c1) Hi).
   unfold candidate_row at 1. replace (c2-j)%nat with 1 by lia.
   cbn [seq map List.app]. f_equal. apply full_rows_as_candidates; lia.
 - apply Nat.eqb_neq in E.
   unfold candidate_indices. rewrite (proj2 (Nat.ltb_lt i c1) Hi).
   unfold candidate_row. replace (c2-j)%nat with (S (c2-S j)) by lia.
   reflexivity.
Qed.
Lemma remaining_join_cons : forall src dst a1 a2 i j c1 c2,
 (i<c1)%nat -> (j<c2)%nat ->
 remaining_join src dst a1 a2 i j c1 c2 =
 List.app (candidate_output src dst a1 a2 i j)
 (remaining_join src dst a1 a2 (join_cursor_i i j c2) (join_cursor_j j c2) c1 c2).
Proof.
 intros; unfold remaining_join; rewrite candidate_indices_cons by assumption; reflexivity.
Qed.
Lemma candidate_indices_length : forall i j c1 c2,
 (i<c1)%nat -> (j<c2)%nat ->
 List.length (candidate_indices i j c1 c2) = (c2-j+(c1-S i)*c2)%nat.
Proof.
 intros. unfold candidate_indices. rewrite (proj2 (Nat.ltb_lt i c1) H),app_length.
 unfold candidate_row. rewrite map_length,seq_length.
 assert (Hrows : forall (inds : list nat), List.length
 (flat_map (fun k => map (fun j0 => (k,j0)) (seq 0 (c2-0))) inds) =
 (List.length inds*c2)%nat).
 { induction inds; [reflexivity|]. cbn [flat_map].
   rewrite app_length,map_length,seq_length,IHinds,Nat.sub_0_r; reflexivity. }
 rewrite Hrows,seq_length; reflexivity.
Qed.
Lemma remaining_join_terminal : forall src dst a1 a2 c1 c2,
 remaining_join src dst a1 a2 c1 0 c1 c2 = nil.
Proof. intros; unfold remaining_join,candidate_indices; rewrite Nat.ltb_irrefl; reflexivity. Qed.
Lemma join_empty_nat : forall c1 c2, (c1<=16)%nat -> (c2<=16)%nat ->
 join_empty (natToWord 5 c1) (natToWord 5 c2) = orb (Nat.eqb c1 0) (Nat.eqb c2 0).
Proof. intros; unfold join_empty; rewrite !bounded_word_eqb by lia; reflexivity. Qed.
Lemma join_match_nat : forall i j a1 a2 src dst,
 (a1+i<16)%nat -> (a2+j<16)%nat ->
 join_match (natToWord 5 i) (natToWord 5 j) (natToWord 4 a1) (natToWord 4 a2) src dst =
 candidate_match src dst a1 a2 i j.
Proof. intros; unfold join_match,candidate_match,pair_at; rewrite !join_index_nat by assumption; reflexivity. Qed.
Lemma join_wrap_nat : forall j c2, (j<=16)%nat -> (c2<=16)%nat ->
 join_wrap (natToWord 5 j) (natToWord 5 c2) = Nat.eqb (S j) c2.
Proof.
 intros; unfold join_wrap; rewrite <- natToWord_plus.
 replace (j+1)%nat with (S j) by lia. apply bounded_word_eqb; lia.
Qed.
Lemma join_done_nat : forall i j c1 c2,
 (i<=16)%nat -> (j<=16)%nat -> (c1<=16)%nat -> (c2<=16)%nat ->
 join_done (natToWord 5 i) (natToWord 5 j) (natToWord 5 c1) (natToWord 5 c2) =
 andb (Nat.eqb (S j) c2) (Nat.eqb (S i) c1).
Proof.
 intros; unfold join_done; rewrite join_wrap_nat by assumption.
 rewrite <- natToWord_plus. replace (i+1)%nat with (S i) by lia.
 rewrite bounded_word_eqb by lia; reflexivity.
Qed.

Definition join_out out (matched : bool) := if matched then S out else out.
Definition join_table table out value (matched : bool) := if matched then append_pair table out value else table.
Definition join_valid_table valid out (matched : bool) :=
 if matched then put_vector valid (pair_index (natToWord 5 out)) true else valid.
Definition join_terminal i j c1 c2 := andb (Nat.eqb (S j) c2) (Nat.eqb (S i) c1).
Lemma join_admitted_controls : forall i j c1 c2 out a1 a2 src dst,
 (i<c1<=16)%nat -> (j<c2<=16)%nat -> (out<=16)%nat ->
 (a1+i<16)%nat -> (a2+j<16)%nat ->
 (candidate_match src dst a1 a2 i j = true -> (out<16)%nat) ->
 join_emits (natToWord 5 i) (natToWord 5 j) (natToWord 5 c1) (natToWord 5 c2)
 (natToWord 5 out) (natToWord 4 a1) (natToWord 4 a2) src dst = candidate_match src dst a1 a2 i j /\
 join_overflow (natToWord 5 i) (natToWord 5 j) (natToWord 5 c1) (natToWord 5 c2)
 (natToWord 5 out) (natToWord 4 a1) (natToWord 4 a2) src dst = false.
Proof.
 intros i j c1 c2 out a1 a2 src dst Hi Hj Ho Ha1 Ha2 Hroom.
 unfold join_emits,join_overflow. rewrite !join_empty_nat by lia.
 rewrite (proj2 (Nat.eqb_neq c1 0) ltac:(lia)), (proj2 (Nat.eqb_neq c2 0) ltac:(lia)).
 rewrite !join_match_nat by assumption. rewrite !bounded_word_ltb by lia.
 cbn [orb negb andb]. destruct (candidate_match src dst a1 a2 i j) eqn:E.
 - rewrite (proj2 (Nat.ltb_lt out 16) (Hroom eq_refl)); split; reflexivity.
 - split; reflexivity.
Qed.
Ltac join_read_map := unfold join_state; rewrite M.find_union;
 unfold join_updates; repeat rewrite M.find_add_2 by discriminate;
 rewrite M.find_add_1 by reflexivity.

Lemma join_admitted_step_registers : forall old i j c1 c2 out a1 a2 src dst valid err code,
 (i<c1<=16)%nat -> (j<c2<=16)%nat -> (out<=16)%nat ->
 (a1+i<16)%nat -> (a2+j<16)%nat ->
 (candidate_match src dst a1 a2 i j = true -> (out<16)%nat) ->
 join_registers old i j c1 c2 out a1 a2 src dst valid err code ->
 let matched := candidate_match src dst a1 a2 i j in
 join_registers_at (if join_terminal i j c1 c2 then 5 else 7)
 (join_state old i j c1 c2 out a1 a2 src dst valid err code)
 (join_cursor_i i j c2) (join_cursor_j j c2) c1 c2 (join_out out (matched : bool)) a1 a2
 (join_table src out (pair_at src (a1+i)) matched)
 (join_table dst out (pair_at dst (a2+j)) matched)
 (join_valid_table valid out (matched : bool)) err code.
Proof.
 intros old i j c1 c2 out a1 a2 src dst valid err code Hi Hj Ho Ha1 Ha2 Hroom Hr; cbv zeta.
 destruct (join_admitted_controls i j c1 c2 out a1 a2 src dst Hi Hj Ho Ha1 Ha2 Hroom) as [Hem Hov].
 assert (Hempty : join_empty (natToWord 5 c1) (natToWord 5 c2) = false).
 { rewrite join_empty_nat by lia.
   rewrite (proj2 (Nat.eqb_neq c1 0) ltac:(lia)), (proj2 (Nat.eqb_neq c2 0) ltac:(lia)); reflexivity. }
 constructor;
 try (rewrite join_frame by (unfold join_footprint; simpl; intuition discriminate); destruct Hr; assumption);
 join_read_map; try rewrite Hem; try rewrite Hov;
 try rewrite Hempty; try rewrite join_wrap_nat by lia;
 try rewrite join_done_nat by lia;
 try rewrite !join_index_nat by assumption;
 try rewrite wordToNat_natToWord_2 by (change (out<32)%nat; lia);
 cbn [orb andb negb]; try rewrite orb_false_r;
 unfold join_out,join_table,join_valid_table,join_cursor_i,join_cursor_j,join_terminal,pair_at;
 try destruct (candidate_match src dst a1 a2 i j);
 try destruct (Nat.eqb (S j) c2);
 try destruct (Nat.eqb (S i) c1);
 try rewrite <- natToWord_plus;
 try replace (out+1)%nat with (S out) by lia;
 try replace (i+1)%nat with (S i) by lia;
 try replace (j+1)%nat with (S j) by lia; reflexivity.
Qed.

Lemma join_table_preserves_low : forall b out table raw value matched,
 (b<=out<=16)%nat -> (matched=true -> (out<16)%nat) ->
 low_agrees b table raw -> low_agrees b (join_table table out value matched) raw.
Proof.
 intros; unfold join_table; destruct matched; [apply append_pair_preserves_low; [split; [lia|apply H0; reflexivity]|exact H1]|exact H1].
Qed.
Lemma join_next_bounds : forall i j c1 c2,
 (i<c1)%nat -> (j<c2)%nat -> join_terminal i j c1 c2 = false ->
 (join_cursor_i i j c2<c1)%nat /\ (join_cursor_j j c2<c2)%nat.
Proof.
 intros. unfold join_cursor_i,join_cursor_j,join_terminal in *.
 destruct (Nat.eqb (S j) c2) eqn:E; [apply Nat.eqb_eq in E|apply Nat.eqb_neq in E].
 - cbn [andb] in H1; apply Nat.eqb_neq in H1; split; lia.
 - split; lia.
Qed.
Lemma join_terminal_cursors : forall i j c1 c2,
 join_terminal i j c1 c2 = true ->
 join_cursor_i i j c2 = c1 /\ join_cursor_j j c2 = 0 /\ S i = c1 /\ S j = c2.
Proof.
 intros; unfold join_terminal in H; apply andb_true_iff in H; destruct H as [Hj Hi].
 unfold join_cursor_i,join_cursor_j; rewrite Hj.
 apply Nat.eqb_eq in Hi; apply Nat.eqb_eq in Hj; repeat split; assumption.
Qed.

Theorem join_loop_execution : forall n old rawsrc rawdst src dst valid err code
 b out i j c1 c2 a1 a2,
 List.length (candidate_indices i j c1 c2)=n ->
 (i<c1<=16)%nat -> (j<c2<=16)%nat -> (b<=out)%nat ->
 (out+List.length (remaining_join rawsrc rawdst a1 a2 i j c1 c2)<=16)%nat ->
 (a1+c1<=b)%nat -> (a2+c2<=b)%nat ->
 low_agrees b src rawsrc -> low_agrees b dst rawdst ->
 join_registers old i j c1 c2 out a1 a2 src dst valid err code ->
 exists final,
 Multistep thieleCore old final (repeat (normalization_label "mc_join_loop") n) /\
 M.find "mc_phase" final = Some (reg4 (natToWord 4 5)) /\
 M.find "mc_write_ptr" final = Some (reg5 (natToWord 5
 (out+List.length (remaining_join rawsrc rawdst a1 a2 i j c1 c2)))) /\
 M.find "mc_i" final = Some (reg5 (natToWord 5 c1)) /\
 M.find "mc_j" final = Some (reg5 (natToWord 5 0)) /\
 M.find "coupling_pair_src_table" final = Some (regpairs
 (store_pairs src out (remaining_join rawsrc rawdst a1 a2 i j c1 c2) true)) /\
 M.find "coupling_pair_dst_table" final = Some (regpairs
 (store_pairs dst out (remaining_join rawsrc rawdst a1 a2 i j c1 c2) false)) /\
 M.find "err" final = Some (regbool err) /\
 M.find "error_code" final = Some (reg32 code) /\
 (forall key, ~ In key join_footprint -> M.find key final = M.find key old).
Proof.
 induction n as [|n IH]; intros old rawsrc rawdst src dst valid err code
 b out i j c1 c2 a1 a2 Hn Hi Hj Hb Hcap Ha1 Ha2 HlowS HlowD Hr.
 - rewrite candidate_indices_cons in Hn by lia; discriminate.
 - pose (matched := candidate_match rawsrc rawdst a1 a2 i j).
   pose (ni := join_cursor_i i j c2). pose (nj := join_cursor_j j c2).
   pose (tail := remaining_join rawsrc rawdst a1 a2 ni nj c1 c2).
   assert (Hcons : remaining_join rawsrc rawdst a1 a2 i j c1 c2 =
    List.app (if matched then [candidate_pair rawsrc rawdst a1 a2 i j] else nil) tail).
   { apply remaining_join_cons; lia. }
   assert (Hroom : matched=true -> (out<16)%nat).
   { intros E; rewrite Hcons,E in Hcap; cbn [List.app List.length] in Hcap; lia. }
   assert (Hm : candidate_match src dst a1 a2 i j = matched).
   { unfold candidate_match; rewrite HlowD,HlowS by lia; reflexivity. }
   pose (next := join_state old i j c1 c2 out a1 a2 src dst valid err code).
   pose (src1 := join_table src out (pair_at rawsrc (a1+i)) matched).
   pose (dst1 := join_table dst out (pair_at rawdst (a2+j)) matched).
   pose (valid1 := join_valid_table valid out matched).
   assert (Hpost : join_registers_at (if join_terminal i j c1 c2 then 5 else 7)
     next ni nj c1 c2 (join_out out matched) a1 a2 src1 dst1 valid1 err code).
   { pose proof (join_admitted_step_registers old i j c1 c2 out a1 a2 src dst valid err code
      Hi Hj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros E; apply Hroom; rewrite <- Hm; exact E) Hr) as H.
     cbv zeta in H; rewrite Hm in H. rewrite HlowS,HlowD in H by lia. exact H. }
   pose proof (join_actual_execution old i j c1 c2 out a1 a2 src dst valid err code Hr) as Hex.
   destruct (join_terminal i j c1 c2) eqn:Eterm.
   + destruct (join_terminal_cursors i j c1 c2 Eterm) as [Eni [Enj [Ei Ej]]].
     assert (En : (n=0)%nat).
     { rewrite candidate_indices_length in Hn by lia. nia. }
     subst n. exists next. split; [exact Hex|].
     assert (Etail : tail=nil).
     { unfold tail,ni,nj; rewrite Eni,Enj; apply remaining_join_terminal. }
     rewrite Etail,app_nil_r in Hcons.
     destruct Hpost as [Hp Hii Hjj Ha Hc Haa Hcc Ho Hs Hd Hv He Hcode].
     unfold ni in Hii; unfold nj in Hjj; rewrite Eni in Hii; rewrite Enj in Hjj.
     split; [exact Hp|]. split.
     * rewrite Hcons; unfold join_out in Ho; destruct matched; cbn [List.length];
       [replace (out+1)%nat with (S out) by lia|rewrite Nat.add_0_r]; exact Ho.
     * split; [exact Hii|]. split; [exact Hjj|].
       split; [rewrite Hcons; unfold src1,join_table in Hs; destruct matched; exact Hs|].
       split; [rewrite Hcons; unfold dst1,join_table in Hd; destruct matched; exact Hd|].
       split; [exact He|]. split; [exact Hcode|apply join_frame].
   + destruct (join_next_bounds i j c1 c2 ltac:(lia) ltac:(lia) Eterm) as [Hni Hnj].
     assert (Hnnext : List.length (candidate_indices ni nj c1 c2)=n).
     { rewrite candidate_indices_cons in Hn by lia; cbn [List.length] in Hn; apply Nat.succ_inj in Hn; exact Hn. }
     assert (Hcapnext : (join_out out matched+List.length tail<=16)%nat).
     { rewrite Hcons in Hcap; unfold join_out; destruct matched; cbn [List.app List.length] in *; lia. }
     destruct (IH next rawsrc rawdst src1 dst1 valid1 err code b (join_out out matched)
     ni nj c1 c2 a1 a2 Hnnext ltac:(unfold ni; lia) ltac:(unfold nj; lia)
     ltac:(unfold join_out; destruct matched; lia) Hcapnext Ha1 Ha2
     (join_table_preserves_low b out src rawsrc _ matched ltac:(lia) Hroom HlowS)
     (join_table_preserves_low b out dst rawdst _ matched ltac:(lia) Hroom HlowD) Hpost)
     as [final [Hrun [Hp [Ho [Hii [Hjj [Hs [Hd [He [Hcode Hframe]]]]]]]]]].
     exists final. split.
     * replace (S n) with (n+1)%nat by lia. rewrite repeat_app; cbn [repeat].
       eapply normalization_multistep_trans; [exact Hex|exact Hrun].
     * split; [exact Hp|]. split.
       -- rewrite Hcons. change (M.find "mc_write_ptr" final = Some (reg5
          (natToWord 5 (out+List.length (List.app (if matched then
            [candidate_pair rawsrc rawdst a1 a2 i j] else nil) tail))))).
          unfold join_out in Ho; destruct matched; cbn [List.app List.length];
          [replace (out+S (List.length tail))%nat with (S out+List.length tail)%nat by lia|]; exact Ho.
       -- split; [exact Hii|]. split; [exact Hjj|].
          split; [rewrite Hcons; unfold src1,join_out,join_table in Hs; destruct matched; exact Hs|].
          split; [rewrite Hcons; unfold dst1,join_out,join_table in Hd; destruct matched; exact Hd|].
          split; [exact He|]. split; [exact Hcode|].
          intros key Hkey; rewrite Hframe by exact Hkey; apply join_frame; exact Hkey.
Qed.

Definition relational_word_join (left right : list (word 32 * word 32)) :=
 flat_map (fun p => flat_map (fun q =>
 if word_eqb (snd p) (fst q) then [(fst p,snd q)] else nil) right) left.
Definition raw_join src dst a1 c1 a2 c2 := remaining_join src dst a1 a2 0 0 c1 c2.
Lemma flat_map_map_local : forall A B C (f : B -> list C) (g : A -> B) xs,
 flat_map f (map g xs) = flat_map (fun x => f (g x)) xs.
Proof. intros A B C f g xs; induction xs; cbn [map flat_map]; congruence. Qed.
Lemma flat_map_assoc_local : forall A B C (f : B -> list C) (g : A -> list B) xs,
 flat_map f (flat_map g xs) = flat_map (fun x => flat_map f (g x)) xs.
Proof.
 intros A B C f g xs; induction xs; cbn [flat_map]; [reflexivity|].
 rewrite flat_map_app,IHxs; reflexivity.
Qed.
Theorem raw_join_relational : forall src dst a1 c1 a2 c2,
 raw_join src dst a1 c1 a2 c2 =
 relational_word_join (table_slice src dst a1 c1) (table_slice src dst a2 c2).
Proof.
 intros. unfold raw_join,remaining_join.
 rewrite <- full_rows_as_candidates by lia.
 rewrite Nat.sub_0_r,flat_map_assoc_local.
 unfold candidate_row. rewrite Nat.sub_0_r.
 unfold relational_word_join,table_slice.
 rewrite (seq_offset c1 a1), (seq_offset c2 a2), !map_map.
 rewrite flat_map_map_local.
 apply flat_map_ext. intros i.
 rewrite !flat_map_map_local.
 apply flat_map_ext. intros j.
 unfold candidate_output,candidate_match,candidate_pair,table_pair,pair_at.
 cbn [fst snd]; reflexivity.
Qed.
Lemma relational_word_join_empty_right : forall xs,
 relational_word_join xs nil = nil.
Proof. induction xs; cbn [relational_word_join flat_map]; assumption || reflexivity. Qed.
Lemma raw_join_empty : forall src dst a1 c1 a2 c2,
 c1=0 \/ c2=0 -> raw_join src dst a1 c1 a2 c2 = nil.
Proof.
 intros; rewrite raw_join_relational. destruct H; subst.
 - reflexivity.
 - apply relational_word_join_empty_right.
Qed.

Lemma join_empty_result : forall old c1 c2 out a1 a2 src dst valid err code,
 (c1<=16)%nat -> (c2<=16)%nat -> (c1=0 \/ c2=0) ->
 let final := join_state old 0 0 c1 c2 out a1 a2 src dst valid err code in
 M.find "mc_phase" final = Some (reg4 (natToWord 4 5)) /\
 M.find "mc_write_ptr" final = Some (reg5 (natToWord 5 out)) /\
 M.find "coupling_pair_src_table" final = Some (regpairs src) /\
 M.find "coupling_pair_dst_table" final = Some (regpairs dst) /\
 M.find "coupling_pair_valid_table" final = Some (regvalid valid) /\
 M.find "err" final = Some (regbool err) /\
 M.find "error_code" final = Some (reg32 code).
Proof.
 intros old c1 c2 out a1 a2 src dst valid err code Hc1 Hc2 Hempty; cbv zeta.
 assert (E : join_empty (natToWord 5 c1) (natToWord 5 c2) = true).
 { rewrite join_empty_nat by assumption. destruct Hempty; subst; rewrite Nat.eqb_refl;
   [reflexivity|apply orb_true_r]. }
 repeat split; join_read_map; unfold join_emits,join_overflow; rewrite E;
 cbn [orb andb negb]; try rewrite orb_false_r; reflexivity.
Qed.
Definition join_firings c1 c2 := if orb (Nat.eqb c1 0) (Nat.eqb c2 0) then 1 else (c1*c2)%nat.

Theorem join_admitted_loading : forall old b a1 c1 a2 c2 src dst valid err code,
 (c1<=16)%nat -> (c2<=16)%nat ->
 (b+List.length (raw_join src dst a1 c1 a2 c2)<=16)%nat ->
 (a1+c1<=b)%nat -> (a2+c2<=b)%nat ->
 join_registers old 0 0 c1 c2 b a1 a2 src dst valid err code ->
 exists final src' dst',
 Multistep thieleCore old final
 (repeat (normalization_label "mc_join_loop") (join_firings c1 c2)) /\
 M.find "mc_phase" final = Some (reg4 (natToWord 4 5)) /\
 M.find "mc_write_ptr" final = Some (reg5 (natToWord 5
 (b+List.length (raw_join src dst a1 c1 a2 c2)))) /\
 M.find "coupling_pair_src_table" final = Some (regpairs src') /\
 M.find "coupling_pair_dst_table" final = Some (regpairs dst') /\
 table_slice src' dst' b (List.length (raw_join src dst a1 c1 a2 c2)) = raw_join src dst a1 c1 a2 c2 /\
 low_agrees b src' src /\ low_agrees b dst' dst /\
 M.find "err" final = Some (regbool err) /\
 M.find "error_code" final = Some (reg32 code) /\
 (forall key, ~ In key join_footprint -> M.find key final = M.find key old).
Proof.
 intros old b a1 c1 a2 c2 src dst valid err code Hc1 Hc2 Hcap Ha1 Ha2 Hr.
 destruct (orb (Nat.eqb c1 0) (Nat.eqb c2 0)) eqn:E.
 - assert (Hempty : c1=0 \/ c2=0).
   { apply orb_true_iff in E; destruct E; [left|right]; apply Nat.eqb_eq; assumption. }
   exists (join_state old 0 0 c1 c2 b a1 a2 src dst valid err code),src,dst.
   split.
   + unfold join_firings; rewrite E; apply join_actual_execution; exact Hr.
   + destruct (join_empty_result old c1 c2 b a1 a2 src dst valid err code Hc1 Hc2 Hempty)
     as [Hp [Ho [Hs [Hd [Hv [He Hcode]]]]]].
     rewrite raw_join_empty by exact Hempty. cbn [List.length]; rewrite Nat.add_0_r.
     split; [exact Hp|]. split; [exact Ho|]. split; [exact Hs|]. split; [exact Hd|].
     split; [reflexivity|]. split; [intros k Hk; reflexivity|]. split; [intros k Hk; reflexivity|].
     split; [exact He|]. split; [exact Hcode|apply join_frame].
 - apply orb_false_iff in E; destruct E as [E1 E2].
   apply Nat.eqb_neq in E1; apply Nat.eqb_neq in E2.
   assert (Hn : List.length (candidate_indices 0 0 c1 c2)=(c1*c2)%nat).
   { rewrite candidate_indices_length by lia; nia. }
   destruct (join_loop_execution (c1*c2) old src dst src dst valid err code
   b b 0 0 c1 c2 a1 a2 Hn ltac:(lia) ltac:(lia) ltac:(lia) Hcap Ha1 Ha2
   ltac:(intros k Hk; reflexivity) ltac:(intros k Hk; reflexivity) Hr)
   as [final [Hrun [Hp [Ho [Hi [Hj [Hs [Hd [He [Hcode Hframe]]]]]]]]]].
   exists final, (store_pairs src b (raw_join src dst a1 c1 a2 c2) true),
    (store_pairs dst b (raw_join src dst a1 c1 a2 c2) false).
   split.
   + unfold join_firings. rewrite (proj2 (Nat.eqb_neq c1 0) E1), (proj2 (Nat.eqb_neq c2 0) E2); exact Hrun.
   + split; [exact Hp|]. split; [exact Ho|]. split; [exact Hs|]. split; [exact Hd|].
     split; [apply store_pairs_slice; exact Hcap|].
     split; [intros k Hk; apply store_pairs_untouched; [exact Hcap|lia|left; exact Hk]|].
     split; [intros k Hk; apply store_pairs_untouched; [exact Hcap|lia|left; exact Hk]|].
     split; [exact He|]. split; [exact Hcode|exact Hframe].
Qed.

Lemma join_nonmatch_preserves_error : forall old i j c1 c2 out a1 a2 src dst valid err code,
 join_match (natToWord 5 i) (natToWord 5 j) (natToWord 4 a1) (natToWord 4 a2) src dst = false ->
 M.find "err" (join_state old i j c1 c2 out a1 a2 src dst valid err code) = Some (regbool err) /\
 M.find "error_code" (join_state old i j c1 c2 out a1 a2 src dst valid err code) = Some (reg32 code).
Proof.
 intros; split; join_read_map; unfold join_overflow; rewrite H,andb_false_r;
 cbn [andb]; try rewrite orb_false_r; reflexivity.
Qed.
Theorem join_capacity_failure : forall old i j c1 c2 out a1 a2 src dst valid err code,
 join_empty (natToWord 5 c1) (natToWord 5 c2) = false ->
 join_match (natToWord 5 i) (natToWord 5 j) (natToWord 4 a1) (natToWord 4 a2) src dst = true ->
 (16<=out<32)%nat ->
 let final := join_state old i j c1 c2 out a1 a2 src dst valid err code in
 M.find "mc_phase" final = Some (reg4 (natToWord 4 0)) /\
 M.find "err" final = Some (regbool true) /\
 M.find "error_code" final = Some (reg32 ERR_COUPLING_INVALID) /\
 M.find "mc_write_ptr" final = Some (reg5 (natToWord 5 out)) /\
 M.find "coupling_pair_src_table" final = Some (regpairs src) /\
 M.find "coupling_pair_dst_table" final = Some (regpairs dst) /\
 M.find "coupling_pair_valid_table" final = Some (regvalid valid).
Proof.
 intros old i j c1 c2 out a1 a2 src dst valid err code Hempty Hmatch Hout; cbv zeta.
 assert (Hroom : word_ltb (natToWord 5 out) (natToWord 5 16) = false).
 { rewrite bounded_word_ltb by lia; apply Nat.ltb_ge; lia. }
 repeat split; join_read_map; unfold join_emits,join_overflow;
 rewrite Hempty,Hmatch,Hroom; cbn [andb negb orb]; try rewrite orb_true_r; reflexivity.
Qed.
Theorem join_cursor_updates_even_on_failure : forall old i j c1 c2 out a1 a2 src dst valid err code,
 (j<=16)%nat -> (c2<=16)%nat ->
 M.find "mc_i" (join_state old i j c1 c2 out a1 a2 src dst valid err code) =
 Some (reg5 (natToWord 5 (join_cursor_i i j c2))) /\
 M.find "mc_j" (join_state old i j c1 c2 out a1 a2 src dst valid err code) =
 Some (reg5 (natToWord 5 (join_cursor_j j c2))).
Proof.
 intros; split; join_read_map; rewrite join_wrap_nat by assumption;
 unfold join_cursor_i,join_cursor_j; destruct (Nat.eqb (S j) c2); try reflexivity;
 rewrite <- natToWord_plus;
 [replace (i+1)%nat with (S i) by lia|replace (j+1)%nat with (S j) by lia]; reflexivity.
Qed.
Definition join_retirement_footprint := List.app join_footprint outer_footprint.
Theorem join_retirement : forall old b a1 c1 a2 c2 src dst valid err code d bases counts descvalid,
 (c1<=16)%nat -> (c2<=16)%nat ->
 (b+List.length (raw_join src dst a1 c1 a2 c2)<=16)%nat ->
 (a1+c1<=b)%nat -> (a2+c2<=b)%nat ->
 join_registers old 0 0 c1 c2 b a1 a2 src dst valid err code ->
 M.find "mc_write_base" old = Some (reg5 (natToWord 5 b)) ->
 M.find "coupling_desc_next_id" old = Some (reg5 d) ->
 M.find "coupling_desc_base_table" old = Some (regbases bases) ->
 M.find "coupling_desc_count_table" old = Some (regcounts counts) ->
 M.find "coupling_desc_valid_table" old = Some (regvalid descvalid) ->
 exists precommit labels src' dst' out,
 (b<=out<=b+List.length (raw_join src dst a1 c1 a2 c2))%nat /\
 Multistep thieleCore old
 (M.union (normalization_commit_updates (natToWord 5 b) (natToWord 5 out)
    d bases counts descvalid) precommit) labels /\
 M.find "mc_phase"
 (M.union (normalization_commit_updates (natToWord 5 b) (natToWord 5 out)
    d bases counts descvalid) precommit) = Some (reg4 (natToWord 4 0)) /\
 M.find "coupling_pair_src_table" precommit = Some (regpairs src') /\
 M.find "coupling_pair_dst_table" precommit = Some (regpairs dst') /\
 table_slice src' dst' b (out-b) = nodup coupling_pair_eq_dec
 (relational_word_join (table_slice src dst a1 c1) (table_slice src dst a2 c2)) /\
 List.length labels = (join_firings c1 c2+2+outer_firings
 (List.length (raw_join src dst a1 c1 a2 c2)))%nat /\
 (forall key, ~ In key join_retirement_footprint -> M.find key precommit = M.find key old) /\
 table_prefix_agrees b src' dst' src dst.
Proof.
 intros old b a1 c1 a2 c2 src dst valid err code d bases counts descvalid
 Hc1 Hc2 Hspace Ha1 Ha2 Hr Hbase Hd Hbs Hcs Hvs.
 destruct (join_admitted_loading old b a1 c1 a2 c2 src dst valid err code Hc1 Hc2 Hspace Ha1 Ha2 Hr)
 as [loaded [lsrc [ldst [Hload [Hphase [Hend [Hls [Hld [Hrawpairs
 [HlowS [HlowD [Herr [Hcode Hframe]]]]]]]]]]]]].
 assert (Lbase : M.find "mc_write_base" loaded = Some (reg5 (natToWord 5 b))).
 { rewrite Hframe; [assumption|unfold join_footprint; simpl; intuition discriminate]. }
 assert (Ld : M.find "coupling_desc_next_id" loaded = Some (reg5 d)).
 { rewrite Hframe; [assumption|unfold join_footprint; simpl; intuition discriminate]. }
 assert (Lbs : M.find "coupling_desc_base_table" loaded = Some (regbases bases)).
 { rewrite Hframe; [assumption|unfold join_footprint; simpl; intuition discriminate]. }
 assert (Lcs : M.find "coupling_desc_count_table" loaded = Some (regcounts counts)).
 { rewrite Hframe; [assumption|unfold join_footprint; simpl; intuition discriminate]. }
 assert (Lvs : M.find "coupling_desc_valid_table" loaded = Some (regvalid descvalid)).
 { rewrite Hframe; [assumption|unfold join_footprint; simpl; intuition discriminate]. }
 destruct (normalization_retirement_with_prefix loaded lsrc ldst b
 (b+List.length (raw_join src dst a1 c1 a2 c2)) d bases counts descvalid
 ltac:(lia) Hspace Hphase Lbase Hend Hls Hld Ld Lbs Lcs Lvs)
 as [pre [labels [src' [dst' [out [Hbound [Hnorm [Hzero [Hs [Ht [Hpairs [Hnormframe [Hlen Hprefix]]]]]]]]]]]]].
 exists pre, (List.app labels (repeat (normalization_label "mc_join_loop") (join_firings c1 c2))), src', dst', out.
 split; [exact Hbound|]. split; [eapply normalization_multistep_trans; eassumption|].
 split; [exact Hzero|]. split; [exact Hs|]. split; [exact Ht|].
 split.
 - rewrite Hpairs. replace (b+List.length (raw_join src dst a1 c1 a2 c2)-b)%nat
   with (List.length (raw_join src dst a1 c1 a2 c2)) by lia.
   rewrite Hrawpairs,raw_join_relational; reflexivity.
 - split.
   + rewrite app_length,repeat_length,Hlen.
     replace (b+List.length (raw_join src dst a1 c1 a2 c2)-b)%nat
     with (List.length (raw_join src dst a1 c1 a2 c2)) by lia. lia.
   + split.
     * intros key Hkey. rewrite Hnormframe.
       -- apply Hframe. unfold join_retirement_footprint in Hkey; rewrite in_app_iff in Hkey; intuition.
       -- unfold join_retirement_footprint in Hkey; rewrite in_app_iff in Hkey; intuition.
     * intros k Hk. rewrite Hprefix by exact Hk.
       change ((pair_at lsrc k,pair_at ldst k) = (pair_at src k,pair_at dst k)).
       rewrite HlowS,HlowD by exact Hk; reflexivity.
Qed.
Theorem join_retirement_firing_bound : forall c1 c2 n,
 (c1<=16)%nat -> (c2<=16)%nat -> (n<=16)%nat ->
 (join_firings c1 c2+2+outer_firings n<=410)%nat.
Proof.
 intros. pose proof (normalization_outer_firing_formula n).
 unfold join_firings. destruct (orb (Nat.eqb c1 0) (Nat.eqb c2 0)); nia.
Qed.
