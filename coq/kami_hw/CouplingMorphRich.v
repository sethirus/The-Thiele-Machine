(** CouplingMorphRich.v: the rich observation after a coupling commit.
    [rich_after_morph_commit]: when the morph, descriptor and pair tables of a
    boundary are the step's allocation followed by the FSM's commit, its rich
    observation is [rich_state_add_morph_with_coupling] of the earlier one. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool FunctionalExtensionality.
Import ListNotations.
From KamiHW Require Import ThieleTypes HWBoundary StepWordFacts StepRefineCommon StepRefineMorph
  ImplementationContract Abstraction NormalizationSteps NormalizationLoop MorphLoading.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Lemma write_coupling_pairs_aux_at : forall pairs tbl base i,
  write_coupling_pairs_aux tbl base pairs i =
  if andb (Nat.leb base i) (Nat.ltb i (base + List.length pairs))
  then Some {| coupling_pair_source := fst (nth (i - base) pairs (0, 0));
               coupling_pair_target := snd (nth (i - base) pairs (0, 0)) |}
  else tbl i.
Proof.
  induction pairs as [|[x y] pairs IH]; intros tbl base i; cbn [write_coupling_pairs_aux List.length].
  - rewrite Nat.add_0_r. destruct (Nat.leb_spec base i), (Nat.ltb_spec i base); cbn; try reflexivity; lia.
  - rewrite IH. destruct (Nat.leb_spec (S base) i) as [L|L].
    + rewrite (proj2 (Nat.leb_le base i)) by lia. cbn [andb].
      replace (S base + List.length pairs) with (base + S (List.length pairs)) by lia.
      replace (i - base) with (S (i - S base)) by lia. cbn [nth].
      destruct (Nat.eqb_spec i base); [lia|reflexivity].
    + cbn [andb]. destruct (Nat.eqb_spec i base) as [E|E].
      * subst i. rewrite Nat.leb_refl, Nat.sub_diag. cbn [andb nth fst snd].
        rewrite (proj2 (Nat.ltb_lt _ _)) by lia. reflexivity.
      * rewrite (proj2 (Nat.leb_gt base i)) by lia. reflexivity.
Qed.

Lemma pair_index_small : forall k, k < 16 -> pair_index (natToWord 5 k) = natToWord 4 k.
Proof. intros k Hk. do 16 (destruct k as [|k]; [reflexivity|]). lia. Qed.

Lemma loaded_valid_at : forall n out (v : word 4 -> bool) k,
  out + n <= 16 -> k < 16 ->
  loaded_valid out n v (natToWord 4 k) = if andb (Nat.leb out k) (Nat.ltb k (out + n)) then true else v (natToWord 4 k).
Proof.
  induction n as [|n IH]; intros out v k Hb Hk; cbn [loaded_valid].
  - rewrite Nat.add_0_r. destruct (Nat.leb_spec out k), (Nat.ltb_spec k out); cbn; try reflexivity; lia.
  - rewrite IH by lia. unfold load_valid_next, put_vector. rewrite (pair_index_small out) by lia.
    destruct (Nat.leb_spec (S out) k) as [L|L].
    + rewrite (proj2 (Nat.leb_le out k)) by lia. cbn [andb].
      replace (S out + n) with (out + S n) by lia.
      destruct (weq (natToWord 4 k) (natToWord 4 out)) as [E|E]; [|reflexivity].
      apply (f_equal (@wordToNat 4)) in E. rewrite !wordToNat_natToWord_2 in E by (cbn; lia). lia.
    + cbn [andb]. destruct (weq (natToWord 4 k) (natToWord 4 out)) as [E|E].
      * assert (k = out).
        { apply (f_equal (@wordToNat 4)) in E. rewrite !wordToNat_natToWord_2 in E by (cbn; lia). exact E. }
        subst k. rewrite Nat.leb_refl. rewrite (proj2 (Nat.ltb_lt _ _)) by lia. reflexivity.
      * destruct (Nat.leb_spec out k) as [L2|L2].
        -- exfalso. assert (k = out) by lia. subst. contradiction.
        -- reflexivity.
Qed.

Definition rich_rest_same (F b : HWB) : Prop :=
  hw_formula_desc_valid_table F = hw_formula_desc_valid_table b /\
  hw_formula_desc_base_table F = hw_formula_desc_base_table b /\
  hw_formula_desc_count_table F = hw_formula_desc_count_table b /\
  hw_formula_desc_next_id F = hw_formula_desc_next_id b /\
  hw_cert_desc_valid_table F = hw_cert_desc_valid_table b /\
  hw_cert_desc_base_table F = hw_cert_desc_base_table b /\
  hw_cert_desc_count_table F = hw_cert_desc_count_table b /\
  hw_cert_desc_next_id F = hw_cert_desc_next_id b /\
  hw_desc_meta_valid_table F = hw_desc_meta_valid_table b /\
  hw_desc_meta_subtype_table F = hw_desc_meta_subtype_table b /\
  hw_desc_meta_kind_table F = hw_desc_meta_kind_table b /\
  hw_desc_meta_inline_len_table F = hw_desc_meta_inline_len_table b /\
  hw_desc_meta_aux_table F = hw_desc_meta_aux_table b /\
  hw_desc_meta_next_id F = hw_desc_meta_next_id b.

Theorem rich_after_morph_commit : forall b F (srcm dstm : word PTableIdxSz) P out (pairs : list (nat * nat))
    (lw : word WordSz) (ln : word 6) (lab : string),
  wordToNat (hw_morph_next_id b) < 16 -> wordToNat (hw_coupling_desc_next_id b) < 16 ->
  hw_coupling_pair_next_id b = natToWord 5 P -> P < 16 -> P <= out -> out <= 16 ->
  hw_morph_valid_table F = (fun w => if weq w (split1 4 1 (hw_morph_next_id b)) then true else hw_morph_valid_table b w) ->
  hw_morph_src_table F = (fun w => if weq w (split1 4 1 (hw_morph_next_id b)) then srcm else hw_morph_src_table b w) ->
  hw_morph_dst_table F = (fun w => if weq w (split1 4 1 (hw_morph_next_id b)) then dstm else hw_morph_dst_table b w) ->
  hw_morph_coupling_desc_table F = (fun w => if weq w (split1 4 1 (hw_morph_next_id b))
                                     then split1 4 1 (hw_coupling_desc_next_id b) else hw_morph_coupling_desc_table b w) ->
  hw_morph_identity_table F = (fun w => if weq w (split1 4 1 (hw_morph_next_id b)) then false else hw_morph_identity_table b w) ->
  hw_morph_next_id F = wplus (hw_morph_next_id b) (natToWord MorphTableNextIdSz 1) ->
  hw_coupling_desc_valid_table F = (fun w => if weq w (split1 4 1 (hw_coupling_desc_next_id b)) then true else hw_coupling_desc_valid_table b w) ->
  hw_coupling_desc_base_table F = (fun w => if weq w (split1 4 1 (hw_coupling_desc_next_id b))
                                   then split1 4 1 (natToWord 5 P) else hw_coupling_desc_base_table b w) ->
  hw_coupling_desc_count_table F = (fun w => if weq w (split1 4 1 (hw_coupling_desc_next_id b))
                                    then wminus (natToWord 5 out) (natToWord 5 P) else hw_coupling_desc_count_table b w) ->
  hw_coupling_desc_label_table F = (fun w => if weq w (split1 4 1 (hw_coupling_desc_next_id b))
                                    then lw else hw_coupling_desc_label_table b w) ->
  hw_coupling_desc_label_len_table F = (fun w => if weq w (split1 4 1 (hw_coupling_desc_next_id b))
                                    then ln else hw_coupling_desc_label_len_table b w) ->
  atom_label (wordToNat ln) (wordToNat lw) = lab ->
  hw_coupling_desc_next_id F = wplus (hw_coupling_desc_next_id b) (natToWord 5 1) ->
  hw_coupling_pair_next_id F = natToWord 5 out ->
  (forall k, k < out -> hwb_valid (hw_coupling_pair_valid_table F) k =
     if Nat.ltb k P then hwb_valid (hw_coupling_pair_valid_table b) k else true) ->
  (forall k, k < P -> hwb_vector_nat (hw_coupling_pair_src_table F) k = hwb_vector_nat (hw_coupling_pair_src_table b) k /\
                      hwb_vector_nat (hw_coupling_pair_dst_table F) k = hwb_vector_nat (hw_coupling_pair_dst_table b) k) ->
  (forall k, P <= k < out -> (hwb_vector_nat (hw_coupling_pair_src_table F) k, hwb_vector_nat (hw_coupling_pair_dst_table F) k) =
     nth (k - P) pairs (0, 0)) ->
  List.length pairs = out - P ->
  rich_rest_same F b ->
  rich_state_add_morph_with_coupling (hwb_rich b) (wordToNat srcm) (wordToNat dstm) pairs lab false =
    (hwb_rich F, wordToNat (hw_morph_next_id b)).
Proof.
  intros b F srcm dstm P out pairs lw ln lab Hm Hd HP HP16 Ho Ho16 MV MS MD MC MI MN DV DB DC DL DLn HL DN PN PV PL PH Hlen
    [R1 [R2 [R3 [R4 [R5 [R6 [R7 [R8 [R9 [R10 [R11 [R12 [R13 R14]]]]]]]]]]]]].
  unfold rich_state_add_morph_with_coupling, rich_state_add_coupling_data, rich_state_add_morph.
  cbv beta iota zeta.
  unfold hwb_rich.
  rewrite MV, MS, MD, MC, MI, MN, DV, DB, DC, DL, DLn, DN, PN, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14.
  cbn [rich_morph_table rich_next_morph_id rich_coupling_desc_table rich_next_coupling_desc_id
       rich_coupling_pair_table rich_next_coupling_pair_id rich_formula_desc_table rich_next_formula_desc_id
       rich_cert_desc_table rich_next_cert_desc_id rich_desc_meta_table rich_next_desc_meta_id rich_lassert_state].
  f_equal. f_equal.
  all: try (extensionality i).
  all: rewrite ?hwb_valid_update, ?hwb_vector_nat_update.
  - change (@wordToNat MorphTableIdxSz) with (@wordToNat 4). change (@wordToNat DescIdxSz) with (@wordToNat 4).
    rewrite (wordToNat_trunc4_5_small _ Hm), (wordToNat_trunc4_5_small (hw_coupling_desc_next_id b) Hd).
    destruct (i =? _); reflexivity.
  - rewrite (wordToNat_wplus_one_bounded MorphTableNextIdSz) by (cbn; lia). lia.
  - change (@wordToNat CouplingDescIdxSz) with (@wordToNat 4). change (@wordToNat CouplingPairIdxSz) with (@wordToNat 4).
    change (@wordToNat CouplingPairCountSz) with (@wordToNat 5).
    rewrite (wordToNat_trunc4_5_small (hw_coupling_desc_next_id b) Hd). destruct (i =? _); [|reflexivity].
    change (split1 4 1 (natToWord 5 P)) with (pair_index (natToWord 5 P)).
    rewrite HP, (pair_index_small P HP16), (@wordToNat_natToWord_2 4 P) by (cbn; lia).
    assert (W5 : forall n, n <= 16 -> @wordToNat 5 (natToWord 5 n) = n) by (intros n Hn; apply wordToNat_natToWord_2; cbn; lia).
    rewrite wordToNat_wminus_le by (rewrite !W5 by lia; lia).
    rewrite !W5 by lia. rewrite Hlen, HL. reflexivity.
  - rewrite (wordToNat_wplus_one_bounded DescTableNextIdSz) by (cbn; lia). lia.
  - rewrite write_coupling_pairs_aux_at, HP. change (@wordToNat DescTableNextIdSz) with (@wordToNat 5).
    rewrite (@wordToNat_natToWord_2 5 P), (@wordToNat_natToWord_2 5 out) by (cbn; lia). rewrite Hlen.
    replace (P + (out - P)) with out by lia.
    destruct (Nat.leb_spec P i) as [L1|L1]; destruct (Nat.ltb_spec i out) as [L2|L2]; cbn [andb].
    + rewrite (PV i L2), (proj2 (Nat.ltb_ge i P) L1).
      rewrite <- (PH i (conj L1 L2)). reflexivity.
    + rewrite (proj2 (Nat.ltb_ge i P) L1). reflexivity.
    + rewrite (PV i L2), (proj2 (Nat.ltb_lt i P) L1). destruct (PL i L1) as [E1 E2]. rewrite E1, E2. reflexivity.
    + lia.
  - rewrite HP, Hlen. change (@wordToNat DescTableNextIdSz) with (@wordToNat 5). rewrite (@wordToNat_natToWord_2 5 P), (@wordToNat_natToWord_2 5 out) by (cbn; lia). lia.
Qed.
