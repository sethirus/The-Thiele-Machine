(** Exact action semantics for the actual scan/emit/commit rule entries.
    These lemmas construct particular semantic executions; uniqueness and
    whole-loop refinement are not claimed here. Typed reads are the local premises; list invariants, capacity/no-wrap
    conditions and scheduling progress are additional retirement obligations. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart.
From Coq Require Import List String Bool.
Import ListNotations.
Open Scope string_scope.
Definition normalization_rule (n : nat) := nth n (getRules thieleCore)
 {| attrName := "unused"; attrType := fun ty => Return (Const ty (natToWord 0 0)) |}.
Definition normalization_scan_rule := normalization_rule 8.
Definition normalization_emit_rule := normalization_rule 9.
Definition normalization_commit_rule := normalization_rule 10.
Definition pair_index (w : word 5) : word 4 := split1 4 1 w.
Definition word_eqb {n} (a b : word n) := if weq a b then true else false.
Definition word_ltb {n} (a b : word n) := if wlt_dec a b then true else false.
Definition PairTable := word 4 -> word 32.
Definition regpairs (v : PairTable) :=
 existT (fullType type) (SyntaxKind (Vector (Bit 32) 4)) v.
Definition scan_match (i j : word 5) (src dst : PairTable) :=
 andb (word_eqb (src (pair_index i)) (src (pair_index j)))
      (word_eqb (dst (pair_index i)) (dst (pair_index j))).
Definition normalization_scan_updates (i j e : word 5) (dup : bool) (src dst : PairTable) : UpdatesT :=
 M.add "mc_duplicate" (regbool (orb dup (andb (word_ltb j e) (scan_match i j src dst))))
 (M.add "mc_j" (reg5 (wplus j (natToWord 5 1)))
 (M.add "mc_phase" (reg4 (if word_ltb j e then natToWord 4 8 else natToWord 4 9)) (M.empty _))).
Lemma normalization_scan_rule_name : attrName normalization_scan_rule = "mc_normalize_scan".
Proof. reflexivity. Qed.
Lemma normalization_scan_rule_in : In normalization_scan_rule (getRules thieleCore).
Proof. unfold normalization_scan_rule, normalization_rule; apply nth_In; change (8<12)%nat; repeat constructor. Qed.
Theorem normalization_scan_actual_action : forall old i j e dup src dst,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 8)) ->
 M.find "mc_i" old = Some (reg5 i) ->
 M.find "mc_j" old = Some (reg5 j) ->
 M.find "mc_write_ptr" old = Some (reg5 e) ->
 M.find "mc_duplicate" old = Some (regbool dup) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 SemAction old (attrType normalization_scan_rule type)
   (normalization_scan_updates i j e dup src dst) (M.empty _) WO.
Proof.
 intros old i j e dup src dst Hp Hi Hj He Hd Hs Ht.
 unfold normalization_scan_rule, normalization_rule. cbn [nth getRules attrType].
 eapply SemReadReg; [exact Hp|]. apply SemAssertTrue; [reflexivity|].
 eapply SemReadReg; [exact Hi|]. eapply SemReadReg; [exact Hj|].
 eapply SemReadReg; [exact He|]. eapply SemReadReg; [exact Hd|].
 eapply SemReadReg; [exact Hs|]. eapply SemReadReg; [exact Ht|].
 repeat apply SemLet.
 unfold normalization_scan_updates, scan_match, word_eqb, word_ltb, pair_index.
 do 3 (eapply SemWriteReg; [shelve|reflexivity|]).
 apply SemReturn; reflexivity.
 Unshelve. all: reflexivity.
Qed.
Theorem normalization_scan_actual_substep : forall old i j e dup src dst,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 8)) ->
 M.find "mc_i" old = Some (reg5 i) ->
 M.find "mc_j" old = Some (reg5 j) ->
 M.find "mc_write_ptr" old = Some (reg5 e) ->
 M.find "mc_duplicate" old = Some (regbool dup) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 Substep thieleCore old (normalization_scan_updates i j e dup src dst)
   (Rle (Some "mc_normalize_scan")) (M.empty _).
Proof.
 intros. eapply SingleRule with (a := attrType normalization_scan_rule).
 - exact normalization_scan_rule_in.
 - eapply normalization_scan_actual_action; eassumption.
Qed.

Definition put_vector {A} (table : word 4 -> A) (idx : word 4) (value : A) :=
 fun w => if weq w idx then value else table w.
Definition emit_next (out : word 5) (dup : bool) :=
 if dup then out else wplus out (natToWord 5 1).
Definition normalization_emit_updates (i e out : word 5) (dup : bool) (src dst : PairTable) : UpdatesT :=
 let next := wplus i (natToWord 5 1) in
 let out_next := emit_next out dup in
 let done := word_eqb next e in
 M.add "coupling_pair_src_table" (regpairs (if dup then src else put_vector src (pair_index out) (src (pair_index i))))
 (M.add "coupling_pair_dst_table" (regpairs (if dup then dst else put_vector dst (pair_index out) (dst (pair_index i))))
 (M.add "mc_norm_ptr" (reg5 out_next)
 (M.add "mc_write_ptr" (reg5 (if done then out_next else e))
 (M.add "mc_i" (reg5 next)
 (M.add "mc_j" (reg5 (wplus next (natToWord 5 1)))
 (M.add "mc_duplicate" (regbool false)
 (M.add "mc_phase" (reg4 (if done then natToWord 4 11 else natToWord 4 8)) (M.empty _)))))))).
Lemma normalization_emit_rule_name : attrName normalization_emit_rule = "mc_normalize_emit".
Proof. reflexivity. Qed.
Lemma normalization_emit_rule_in : In normalization_emit_rule (getRules thieleCore).
Proof. unfold normalization_emit_rule, normalization_rule; apply nth_In; change (9<12)%nat; repeat constructor. Qed.
Theorem normalization_emit_actual_action : forall old i e out dup src dst,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 9)) ->
 M.find "mc_i" old = Some (reg5 i) ->
 M.find "mc_write_ptr" old = Some (reg5 e) ->
 M.find "mc_norm_ptr" old = Some (reg5 out) ->
 M.find "mc_duplicate" old = Some (regbool dup) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 SemAction old (attrType normalization_emit_rule type)
   (normalization_emit_updates i e out dup src dst) (M.empty _) WO.
Proof.
 intros old i e out dup src dst Hp Hi He Ho Hd Hs Ht.
 unfold normalization_emit_rule, normalization_rule. cbn [nth getRules attrType].
 eapply SemReadReg; [exact Hp|]. apply SemAssertTrue; [reflexivity|].
 eapply SemReadReg; [exact Hi|]. eapply SemReadReg; [exact He|].
 eapply SemReadReg; [exact Ho|]. eapply SemReadReg; [exact Hd|].
 eapply SemReadReg; [exact Hs|]. eapply SemReadReg; [exact Ht|].
 repeat apply SemLet.
 unfold normalization_emit_updates, emit_next, put_vector, word_eqb, pair_index.
 do 8 (eapply SemWriteReg; [shelve|reflexivity|]).
 apply SemReturn; reflexivity.
 Unshelve. all: reflexivity.
Qed.
Theorem normalization_emit_actual_substep : forall old i e out dup src dst,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 9)) ->
 M.find "mc_i" old = Some (reg5 i) ->
 M.find "mc_write_ptr" old = Some (reg5 e) ->
 M.find "mc_norm_ptr" old = Some (reg5 out) ->
 M.find "mc_duplicate" old = Some (regbool dup) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 Substep thieleCore old (normalization_emit_updates i e out dup src dst)
   (Rle (Some "mc_normalize_emit")) (M.empty _).
Proof.
 intros. eapply SingleRule with (a := attrType normalization_emit_rule).
 - exact normalization_emit_rule_in.
 - eapply normalization_emit_actual_action; eassumption.
Qed.

Definition regbases (v : word 4 -> word 4) :=
 existT (fullType type) (SyntaxKind (Vector (Bit 4) 4)) v.
Definition regcounts (v : word 4 -> word 5) :=
 existT (fullType type) (SyntaxKind (Vector (Bit 5) 4)) v.
Definition regvalid (v : word 4 -> bool) :=
 existT (fullType type) (SyntaxKind (Vector Bool 4)) v.
Definition normalization_commit_updates (b e d : word 5)
 (bases : word 4 -> word 4) (counts : word 4 -> word 5) (valid : word 4 -> bool) : UpdatesT :=
 M.add "coupling_desc_base_table" (regbases (put_vector bases (pair_index d) (pair_index b)))
 (M.add "coupling_desc_count_table" (regcounts (put_vector counts (pair_index d) (wminus e b)))
 (M.add "coupling_desc_valid_table" (regvalid (put_vector valid (pair_index d) true))
 (M.add "coupling_desc_next_id" (reg5 (wplus d (natToWord 5 1)))
 (M.add "coupling_pair_next_id" (reg5 e)
 (M.add "mc_phase" (reg4 (natToWord 4 0)) (M.empty _)))))).
Lemma normalization_commit_rule_name : attrName normalization_commit_rule = "mc_commit".
Proof. reflexivity. Qed.
Lemma normalization_commit_rule_in : In normalization_commit_rule (getRules thieleCore).
Proof. unfold normalization_commit_rule, normalization_rule; apply nth_In; change (10<12)%nat; repeat constructor. Qed.
Theorem normalization_commit_actual_action : forall old b e d bases counts valid,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 11)) ->
 M.find "mc_write_base" old = Some (reg5 b) ->
 M.find "mc_write_ptr" old = Some (reg5 e) ->
 M.find "coupling_desc_next_id" old = Some (reg5 d) ->
 M.find "coupling_desc_base_table" old = Some (regbases bases) ->
 M.find "coupling_desc_count_table" old = Some (regcounts counts) ->
 M.find "coupling_desc_valid_table" old = Some (regvalid valid) ->
 SemAction old (attrType normalization_commit_rule type)
   (normalization_commit_updates b e d bases counts valid) (M.empty _) WO.
Proof.
 intros old b e d bases counts valid Hp Hb He Hd Hbs Hcs Hvs.
 unfold normalization_commit_rule, normalization_rule. cbn [nth getRules attrType].
 eapply SemReadReg; [exact Hp|]. apply SemAssertTrue; [reflexivity|].
 eapply SemReadReg; [exact Hb|]. eapply SemReadReg; [exact He|].
 eapply SemReadReg; [exact Hd|]. eapply SemReadReg; [exact Hbs|].
 eapply SemReadReg; [exact Hcs|]. eapply SemReadReg; [exact Hvs|].
 repeat apply SemLet.
 unfold normalization_commit_updates, put_vector, pair_index.
 do 6 (eapply SemWriteReg; [shelve|reflexivity|]).
 apply SemReturn; reflexivity.
 Unshelve. all: reflexivity.
Qed.
Theorem normalization_commit_actual_substep : forall old b e d bases counts valid,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 11)) ->
 M.find "mc_write_base" old = Some (reg5 b) ->
 M.find "mc_write_ptr" old = Some (reg5 e) ->
 M.find "coupling_desc_next_id" old = Some (reg5 d) ->
 M.find "coupling_desc_base_table" old = Some (regbases bases) ->
 M.find "coupling_desc_count_table" old = Some (regcounts counts) ->
 M.find "coupling_desc_valid_table" old = Some (regvalid valid) ->
 Substep thieleCore old (normalization_commit_updates b e d bases counts valid)
   (Rle (Some "mc_commit")) (M.empty _).
Proof.
 intros. eapply SingleRule with (a := attrType normalization_commit_rule).
 - exact normalization_commit_rule_in.
 - eapply normalization_commit_actual_action; eassumption.
Qed.

(** Frames apply to the real update maps already realized by the substeps.
    They include PC/mu/error/ordinary data: no field outside the named write
    footprint changes when the update map is unioned with the old registers. *)
Lemma normalization_scan_frame : forall old i j e dup src dst key,
 ~ In key ["mc_duplicate"; "mc_j"; "mc_phase"] ->
 M.find key (M.union (normalization_scan_updates i j e dup src dst) old) = M.find key old.
Proof.
 intros old i j e dup src dst key H.
 rewrite M.find_union. unfold normalization_scan_updates.
 repeat rewrite M.find_add_2 by (intro E; apply H; subst; simpl; auto).
 reflexivity.
Qed.
Lemma normalization_emit_frame : forall old i e out dup src dst key,
 ~ In key ["coupling_pair_src_table"; "coupling_pair_dst_table"; "mc_norm_ptr";
           "mc_write_ptr"; "mc_i"; "mc_j"; "mc_duplicate"; "mc_phase"] ->
 M.find key (M.union (normalization_emit_updates i e out dup src dst) old) = M.find key old.
Proof.
 intros old i e out dup src dst key H.
 rewrite M.find_union. unfold normalization_emit_updates.
 repeat rewrite M.find_add_2 by (intro E; apply H; subst; simpl; auto 10).
 reflexivity.
Qed.
Lemma normalization_commit_frame : forall old b e d bases counts valid key,
 ~ In key ["coupling_desc_base_table"; "coupling_desc_count_table";
           "coupling_desc_valid_table"; "coupling_desc_next_id";
           "coupling_pair_next_id"; "mc_phase"] ->
 M.find key (M.union (normalization_commit_updates b e d bases counts valid) old) = M.find key old.
Proof.
 intros old b e d bases counts valid key H.
 rewrite M.find_union. unfold normalization_commit_updates.
 repeat rewrite M.find_add_2 by (intro E; apply H; subst; simpl; auto 10).
 reflexivity.
Qed.

From Coq Require Import Arith Lia.
Lemma normalization_pointer_increment_no_wrap : forall n,
 (n <= 16)%nat ->
 wordToNat (wplus (natToWord 5 n) (natToWord 5 1)) = (n+1)%nat.
Proof.
 intros n Hn. rewrite <- natToWord_plus.
 apply wordToNat_natToWord_2. change (n+1<32)%nat. lia.
Qed.
Lemma normalization_pair_index_exact : forall n,
 (n < 16)%nat -> wordToNat (pair_index (natToWord 5 n)) = n.
Proof.
 intros n Hn. unfold pair_index. rewrite wordToNat_split1.
 rewrite wordToNat_natToWord_2 by (change (n<32)%nat; lia).
 change (n mod 16 = n)%nat. apply Nat.mod_small. exact Hn.
Qed.
Lemma normalization_distinct_pair_indices : forall k out,
 (k<16)%nat -> (out<16)%nat -> k<>out ->
 pair_index (natToWord 5 k) <> pair_index (natToWord 5 out).
Proof.
 intros k out Hk Ho Hne Heq. apply Hne.
 apply (f_equal (@wordToNat 4)) in Heq.
 rewrite !normalization_pair_index_exact in Heq by assumption. exact Heq.
Qed.
Lemma normalization_emit_preserves_other_pair : forall (table : PairTable) i out k (dup : bool),
 (out<16)%nat -> (k<16)%nat -> k<>out ->
 (if dup then table else put_vector table (pair_index (natToWord 5 out))
       (table (pair_index (natToWord 5 i)))) (pair_index (natToWord 5 k)) =
 table (pair_index (natToWord 5 k)).
Proof.
 intros table i out k dup Ho Hk Hne. destruct dup; [reflexivity|].
 unfold put_vector. destruct (weq (pair_index (natToWord 5 k)) (pair_index (natToWord 5 out))) as [Heq|Hneq].
 - exfalso. exact (normalization_distinct_pair_indices k out Hk Ho Hne Heq).
 - reflexivity.
Qed.
Lemma normalization_emit_preserves_unread_suffix : forall (table : PairTable) i out k (dup : bool),
 (out<=i)%nat -> (i<k)%nat -> (k<16)%nat ->
 (if dup then table else put_vector table (pair_index (natToWord 5 out))
       (table (pair_index (natToWord 5 i)))) (pair_index (natToWord 5 k)) =
 table (pair_index (natToWord 5 k)).
Proof.
 intros. apply normalization_emit_preserves_other_pair; lia.
Qed.
