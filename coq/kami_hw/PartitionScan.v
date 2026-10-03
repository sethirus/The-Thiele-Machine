(** PartitionScan.v: the step rule's partition-table scans against the
    natural-number checks of [kami_step].

    PNEW compares its range with every slot of the partition table, PMERGE
    tests whether two ranges touch, and PSPLIT and PMERGE clear the valid bit
    of every morphism that names a removed module. The step rule builds each
    check as a Kami expression: one comparator per slot, 33-bit range ends so
    that [base + size] never wraps. Each lemma below evaluates such an
    expression to the corresponding [Abstraction] definition on the
    observed table. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import Arith Lia List Bool FunctionalExtensionality.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary ImplementationContract Abstraction
  RuleNext RuleStep BoundaryDecoded StepEval StepWordFacts StepFields StepRefineCommon.
Import ListNotations.
Local Open Scope nat_scope.

Lemma bool_of_wlt : forall n (x y : word n),
  (if wlt_dec x y then true else false) = Nat.ltb (wordToNat x) (wordToNat y).
Proof.
  intros n x y. destruct (wlt_dec x y) as [L|L]; symmetry.
  - apply Nat.ltb_lt. apply wlt_lt. exact L.
  - apply Nat.ltb_ge. apply Nat.nlt_ge. intro H. apply L. apply lt_wlt. exact H.
Qed.

Lemma ev_Eq : forall n (e1 e2 : Expr type (SyntaxKind (Bit n))),
  evalExpr (Eq e1 e2) = Nat.eqb (wordToNat (evalExpr e1)) (wordToNat (evalExpr e2)).
Proof.
  intros n e1 e2. cbn [evalExpr].
  destruct (isEq (Bit n) (evalExpr e1) (evalExpr e2)) as [E|N]; symmetry.
  - cbn in E. rewrite E. apply Nat.eqb_refl.
  - apply Nat.eqb_neq. intro H. apply N. cbn.
    rewrite <- (natToWord_wordToNat (evalExpr e1)), <- (natToWord_wordToNat (evalExpr e2)), H.
    reflexivity.
Qed.

Lemma ev_Lt : forall n (e1 e2 : Expr type (SyntaxKind (Bit n))),
  evalExpr (BinBitBool (Lt n) e1 e2) = Nat.ltb (wordToNat (evalExpr e1)) (wordToNat (evalExpr e2)).
Proof. intros n e1 e2. cbn [evalExpr evalBinBitBool]. apply bool_of_wlt. Qed.

Lemma ev_andb : forall (a b : Expr type (SyntaxKind Bool)),
  evalExpr (BinBool AndB a b) = andb (evalExpr a) (evalExpr b).
Proof. reflexivity. Qed.
Lemma ev_orb : forall (a b : Expr type (SyntaxKind Bool)),
  evalExpr (BinBool OrB a b) = orb (evalExpr a) (evalExpr b).
Proof. reflexivity. Qed.
Lemma ev_negb : forall (a : Expr type (SyntaxKind Bool)),
  evalExpr (UniBool NegB a) = negb (evalExpr a).
Proof. reflexivity. Qed.
Lemma ev_read : forall n k (i : Expr type (SyntaxKind (Bit n))) (f : Expr type (SyntaxKind (Vector k n))),
  evalExpr (ReadIndex i f) = evalExpr f (evalExpr i).
Proof. reflexivity. Qed.

Lemma wordToNat_natToWord_lt : forall n i, i < 2 ^ n -> wordToNat (natToWord n i) = i.
Proof. intros n i H. apply wordToNat_natToWord_idempotent'. exact H. Qed.

Lemma slot_read : forall (S : word PTableIdxSz -> word WordSz) i, i < 64 ->
  wordToNat (S (natToWord PTableIdxSz i)) = hwb_vector_nat S i.
Proof.
  intros S i Hi. unfold hwb_vector_nat.
  assert (E : Nat.ltb i (2 ^ PTableIdxSz) = true)
    by (apply Nat.ltb_lt; change (2 ^ PTableIdxSz) with 64; exact Hi).
  rewrite E. reflexivity.
Qed.

Ltac ev_simp := repeat first [rewrite ev_Eq | rewrite ev_Lt | rewrite ev_andb | rewrite ev_orb
  | rewrite ev_negb | rewrite ev_read].

Lemma slot_live_spec : forall (S : word PTableIdxSz -> word WordSz) (N : word PTableNextIdSz) i,
  i < 64 ->
  evalExpr (pt_slot_live (Var type (SyntaxKind (Vector (Bit WordSz) PTableIdxSz)) S)
                         (Var type (SyntaxKind (Bit PTableNextIdSz)) N) i)
  = snap_slot_live (wordToNat N) (hwb_vector_nat S) i.
Proof.
  intros S N i Hi. unfold pt_slot_live, snap_slot_live. ev_simp.
  cbn [evalExpr evalConstT].
  rewrite (wordToNat_natToWord_lt PTableNextIdSz i) by (change (2 ^ PTableNextIdSz) with 128; lia).
  rewrite slot_read by exact Hi. rewrite wordToNat_word0_32. reflexivity.
Qed.

Lemma slot_same_spec : forall (B S : word PTableIdxSz -> word WordSz) (a len : word WordSz) i,
  i < 64 ->
  evalExpr (pt_slot_same (Var type (SyntaxKind (Vector (Bit WordSz) PTableIdxSz)) B)
                         (Var type (SyntaxKind (Vector (Bit WordSz) PTableIdxSz)) S)
                         (Var type (SyntaxKind (Bit WordSz)) a)
                         (Var type (SyntaxKind (Bit WordSz)) len) i)
  = snap_slot_same (hwb_vector_nat S) (hwb_vector_nat B) (wordToNat a) (wordToNat len) i.
Proof.
  intros B S a len i Hi. unfold pt_slot_same, snap_slot_same. ev_simp.
  cbn [evalExpr evalConstT]. rewrite !slot_read by exact Hi. reflexivity.
Qed.

Lemma eval_ext33 : forall (w : word WordSz),
  wordToNat (evalExpr (ext33 (Var type (SyntaxKind (Bit WordSz)) w))) = wordToNat w.
Proof.
  intro w. unfold ext33. cbn [evalExpr evalBinBit evalConstT]. exact (wordToNat_combine_zero_hi WordSz 1 _).
Qed.

Lemma eval_add33 : forall (x y : word WordSz),
  wordToNat (evalExpr (BinBit (Kami.Syntax.Add (S WordSz))
      (ext33 (Var type (SyntaxKind (Bit WordSz)) x)) (ext33 (Var type (SyntaxKind (Bit WordSz)) y))))
  = wordToNat x + wordToNat y.
Proof.
  intros x y. cbn [evalExpr evalBinBit].
  pose proof (wordToNat_bound x) as Bx. pose proof (wordToNat_bound y) as By.
  assert (P33 : pow2 (S WordSz) = 2 * pow2 WordSz) by apply pow2_S.
  rewrite wordToNat_wplus_bounded.
  - pose proof (eval_ext33 x) as Ex. pose proof (eval_ext33 y) as Ey.
    cbn [evalExpr] in Ex, Ey. rewrite Ex, Ey. reflexivity.
  - pose proof (eval_ext33 x) as Ex. pose proof (eval_ext33 y) as Ey.
    cbn [evalExpr] in Ex, Ey. rewrite Ex, Ey. lia.
Qed.

Lemma ev_ext33 : forall (e : Expr type (SyntaxKind (Bit WordSz))),
  wordToNat (evalExpr (ext33 e)) = wordToNat (evalExpr e).
Proof.
  intro e. unfold ext33. cbn [evalExpr evalBinBit evalConstT]. exact (wordToNat_combine_zero_hi WordSz 1 _).
Qed.

Lemma ev_add33 : forall (e1 e2 : Expr type (SyntaxKind (Bit WordSz))),
  wordToNat (evalExpr (BinBit (Kami.Syntax.Add (S WordSz)) (ext33 e1) (ext33 e2)))
  = wordToNat (evalExpr e1) + wordToNat (evalExpr e2).
Proof.
  intros e1 e2. cbn [evalExpr evalBinBit].
  pose proof (wordToNat_bound (evalExpr e1)) as B1. pose proof (wordToNat_bound (evalExpr e2)) as B2.
  assert (P33 : pow2 (S WordSz) = 2 * pow2 WordSz) by apply pow2_S.
  pose proof (ev_ext33 e1) as E1. pose proof (ev_ext33 e2) as E2.
  rewrite wordToNat_wplus_bounded; [rewrite E1, E2; reflexivity|].
  rewrite E1, E2. lia.
Qed.

Lemma ev_ITE : forall k (p : Expr type (SyntaxKind Bool)) (a b : Expr type k),
  evalExpr (ITE p a b) = if evalExpr p then evalExpr a else evalExpr b.
Proof. reflexivity. Qed.

Ltac ev_simp2 := repeat first [rewrite ev_Eq | rewrite ev_Lt | rewrite ev_andb | rewrite ev_orb
  | rewrite ev_negb | rewrite ev_read | rewrite ev_add33 | rewrite ev_ext33].

Lemma slot_overlap_spec : forall (B S : word PTableIdxSz -> word WordSz) (a len : word WordSz) i,
  i < 64 ->
  evalExpr (pt_slot_overlap (Var type (SyntaxKind (Vector (Bit WordSz) PTableIdxSz)) B)
                            (Var type (SyntaxKind (Vector (Bit WordSz) PTableIdxSz)) S)
                            (Var type (SyntaxKind (Bit WordSz)) a)
                            (Var type (SyntaxKind (Bit WordSz)) len) i)
  = snap_slot_overlap (hwb_vector_nat S) (hwb_vector_nat B) (wordToNat a) (wordToNat len) i.
Proof.
  intros B S a len i Hi. unfold pt_slot_overlap, snap_slot_overlap. ev_simp2.
  cbn [evalExpr evalConstT]. rewrite !slot_read by exact Hi. reflexivity.
Qed.

Lemma eval_pt_scan : forall (f : nat -> Expr type (SyntaxKind Bool)) n,
  evalExpr (pt_scan f n) = existsb (fun i => evalExpr (f i)) (seq 0 n).
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [pt_scan]. rewrite ev_orb, IH, seq_S, existsb_app. cbn [existsb]. rewrite orb_false_r.
  reflexivity.
Qed.

Lemma existsb_ext : forall A (f g : A -> bool) l,
  (forall x, In x l -> f x = g x) -> existsb f l = existsb g l.
Proof.
  intros A f g l H. induction l as [|x l IH]; [reflexivity|]. cbn [existsb].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy. apply H. right. exact Hy.
Qed.

Lemma pnew_conflict_spec : forall (B S : word PTableIdxSz -> word WordSz) (N : word PTableNextIdSz)
    (a len : word WordSz),
  evalExpr (pt_range_conflict (Var type (SyntaxKind (Vector (Bit WordSz) PTableIdxSz)) B)
                              (Var type (SyntaxKind (Vector (Bit WordSz) PTableIdxSz)) S)
                              (Var type (SyntaxKind (Bit PTableNextIdSz)) N)
                              (Var type (SyntaxKind (Bit WordSz)) a)
                              (Var type (SyntaxKind (Bit WordSz)) len))
  = snap_pt_conflict (wordToNat N) (hwb_vector_nat S) (hwb_vector_nat B) (wordToNat a) (wordToNat len).
Proof.
  intros B S N a len. unfold pt_range_conflict, snap_pt_conflict.
  rewrite eval_pt_scan. apply existsb_ext. intros i Hi. apply in_seq in Hi.
  change PTableSz with 64 in Hi.
  cbv beta. rewrite ev_andb, ev_andb, ev_negb.
  rewrite slot_live_spec, slot_same_spec, slot_overlap_spec by lia. reflexivity.
Qed.

Lemma pnew_present_spec : forall (B S : word PTableIdxSz -> word WordSz) (N : word PTableNextIdSz)
    (a len : word WordSz),
  evalExpr (pt_range_present (Var type (SyntaxKind (Vector (Bit WordSz) PTableIdxSz)) B)
                             (Var type (SyntaxKind (Vector (Bit WordSz) PTableIdxSz)) S)
                             (Var type (SyntaxKind (Bit PTableNextIdSz)) N)
                             (Var type (SyntaxKind (Bit WordSz)) a)
                             (Var type (SyntaxKind (Bit WordSz)) len))
  = snap_pt_present (wordToNat N) (hwb_vector_nat S) (hwb_vector_nat B) (wordToNat a) (wordToNat len).
Proof.
  intros B S N a len. unfold pt_range_present, snap_pt_present.
  rewrite eval_pt_scan. apply existsb_ext. intros i Hi. apply in_seq in Hi.
  change PTableSz with 64 in Hi.
  cbv beta. rewrite ev_andb.
  rewrite slot_live_spec, slot_same_spec by lia. reflexivity.
Qed.

Lemma hw_pnew_conflict_nat : forall b (a len : word WordSz),
  hw_pnew_conflict b a len =
  snap_pt_conflict (wordToNat (hw_pt_next_id b)) (hwb_vector_nat (hw_ptTable b))
    (hwb_vector_nat (hw_ptBases b)) (wordToNat a) (wordToNat len).
Proof. intros. unfold hw_pnew_conflict. apply pnew_conflict_spec. Qed.

Lemma hw_pnew_present_nat : forall b (a len : word WordSz),
  hw_pnew_present b a len =
  snap_pt_present (wordToNat (hw_pt_next_id b)) (hwb_vector_nat (hw_ptTable b))
    (hwb_vector_nat (hw_ptBases b)) (wordToNat a) (wordToNat len).
Proof. intros. unfold hw_pnew_present. apply pnew_present_spec. Qed.

Lemma hw_pmerge_adjacent_nat : forall b (m1 m2 : word PTableIdxSz),
  hw_pmerge_adjacent b m1 m2 =
  snap_pmerge_adjacent (hwb_vector_nat (hw_ptTable b)) (hwb_vector_nat (hw_ptBases b))
    (wordToNat m1) (wordToNat m2).
Proof.
  intros b m1 m2. unfold hw_pmerge_adjacent, snap_pmerge_adjacent. ev_simp2.
  cbn [evalExpr evalConstT]. rewrite !hwb_vector_nat_at. rewrite wordToNat_word0_32. reflexivity.
Qed.

Lemma hw_pmerge_base_nat : forall b (m1 m2 : word PTableIdxSz),
  wordToNat (hw_pmerge_base b m1 m2) =
  snap_pmerge_base (hwb_vector_nat (hw_ptTable b)) (hwb_vector_nat (hw_ptBases b))
    (wordToNat m1) (wordToNat m2).
Proof.
  intros b m1 m2. unfold hw_pmerge_base, snap_pmerge_base.
  rewrite !ev_ITE. ev_simp2. cbn [evalExpr evalConstT].
  rewrite !hwb_vector_nat_at. rewrite wordToNat_word0_32.
  destruct (Nat.eqb (wordToNat (hw_ptTable b m1)) 0); [reflexivity|].
  destruct (Nat.eqb (wordToNat (hw_ptTable b m2)) 0); [reflexivity|].
  destruct (Nat.eqb (wordToNat (hw_ptBases b m1) + wordToNat (hw_ptTable b m1))
                    (wordToNat (hw_ptBases b m2))); reflexivity.
Qed.

Lemma ev_UpdateVector : forall n k (v : Expr type (SyntaxKind (Vector k n)))
    (i : Expr type (SyntaxKind (Bit n))) (x : Expr type (SyntaxKind k)),
  evalExpr (UpdateVector v i x) =
  fun w => if weq w (evalExpr i) then evalExpr x else evalExpr v w.
Proof. reflexivity. Qed.

Definition wb {n} (x y : word n) : bool := Nat.eqb (wordToNat x) (wordToNat y).

Definition cascade_keep (V : word MorphTableIdxSz -> bool)
    (src dst : word MorphTableIdxSz -> word PTableIdxSz) (m1 m2 : word PTableIdxSz)
    (j : word MorphTableIdxSz) : bool :=
  andb (V j) (negb (orb (orb (wb (src j) m1) (wb (dst j) m1)) (orb (wb (src j) m2) (wb (dst j) m2)))).

Lemma eval_morph_cascade : forall V (src dst : word MorphTableIdxSz -> word PTableIdxSz)
    (m1 m2 : word PTableIdxSz) n j,
  n <= 16 ->
  evalExpr (morph_cascade (Var type (SyntaxKind (Vector Bool MorphTableIdxSz)) V)
              (Var type (SyntaxKind (Vector (Bit PTableIdxSz) MorphTableIdxSz)) src)
              (Var type (SyntaxKind (Vector (Bit PTableIdxSz) MorphTableIdxSz)) dst)
              (Var type (SyntaxKind (Bit PTableIdxSz)) m1)
              (Var type (SyntaxKind (Bit PTableIdxSz)) m2) n) j =
  if Nat.ltb (wordToNat j) n then cascade_keep V src dst m1 m2 j else V j.
Proof.
  intros V src dst m1 m2 n. induction n as [|n IH]; intros j Hn.
  - reflexivity.
  - cbn [morph_cascade]. rewrite ev_UpdateVector. cbv beta.
    destruct (weq j (evalExpr (Const type (ConstBit (natToWord MorphTableIdxSz n))))) as [E|N].
    + cbn [evalExpr evalConstT] in E. subst j.
      rewrite (wordToNat_natToWord_lt MorphTableIdxSz n) by (change (2 ^ MorphTableIdxSz) with 16; lia).
      assert (Hlt : Nat.ltb n (S n) = true) by (apply Nat.ltb_lt; lia). rewrite Hlt.
      unfold cascade_keep, wb. ev_simp2. cbn [evalExpr evalConstT]. reflexivity.
    + rewrite (IH j) by lia.
      cbn [evalExpr evalConstT] in N.
      assert (Hne : wordToNat j <> n).
      { intro H. apply N. rewrite <- H. symmetry. apply natToWord_wordToNat. }
      destruct (Nat.ltb (wordToNat j) n) eqn:L1.
      * apply Nat.ltb_lt in L1. assert (Nat.ltb (wordToNat j) (S n) = true) by (apply Nat.ltb_lt; lia).
        rewrite H. reflexivity.
      * apply Nat.ltb_ge in L1. assert (Nat.ltb (wordToNat j) (S n) = false) by (apply Nat.ltb_ge; lia).
        rewrite H. reflexivity.
Qed.

Lemma hw_morph_cascade_spec : forall b (m1 m2 : word PTableIdxSz) j,
  hw_morph_cascade b m1 m2 j =
  cascade_keep (hw_morph_valid_table b) (hw_morph_src_table b) (hw_morph_dst_table b) m1 m2 j.
Proof.
  intros b m1 m2 j. unfold hw_morph_cascade.
  rewrite eval_morph_cascade by (unfold MorphTableSz; lia).
  assert (Hj : Nat.ltb (wordToNat j) MorphTableSz = true).
  { apply Nat.ltb_lt. pose proof (wordToNat_bound j) as B. change (pow2 MorphTableIdxSz) with 16 in B.
    unfold MorphTableSz. lia. }
  rewrite Hj. reflexivity.
Qed.

Lemma step_rich_cascade : forall b (m1 m2 : word PTableIdxSz),
  hw_morph_valid_table (step_next b) = hw_morph_cascade b m1 m2 ->
  hw_morph_src_table (step_next b) = hw_morph_src_table b ->
  hw_morph_dst_table (step_next b) = hw_morph_dst_table b ->
  hw_morph_coupling_desc_table (step_next b) = hw_morph_coupling_desc_table b ->
  hw_morph_identity_table (step_next b) = hw_morph_identity_table b ->
  hw_morph_next_id (step_next b) = hw_morph_next_id b ->
  hw_coupling_desc_label_table (step_next b) = hw_coupling_desc_label_table b ->
  hw_coupling_desc_label_len_table (step_next b) = hw_coupling_desc_label_len_table b ->
  hwb_rich (step_next b) = rich_state_cascade (hwb_rich b) (wordToNat m1) (wordToNat m2).
Proof.
  intros b m1 m2 H1 H2 H3 H4 H5 H6 H7 H8. unfold hwb_rich at 1.
  rewrite H1, H2, H3, H4, H5, H6, H7, H8.
  rewrite step_keeps_coupling_desc_valid_table, step_keeps_coupling_desc_base_table,
    step_keeps_coupling_desc_count_table, step_keeps_coupling_desc_next_id,
    step_keeps_coupling_pair_valid_table, step_keeps_coupling_pair_src_table,
    step_keeps_coupling_pair_dst_table, step_keeps_coupling_pair_next_id,
    step_keeps_formula_desc_valid_table, step_keeps_formula_desc_base_table,
    step_keeps_formula_desc_count_table, step_keeps_formula_desc_next_id,
    step_keeps_cert_desc_valid_table, step_keeps_cert_desc_base_table,
    step_keeps_cert_desc_count_table, step_keeps_cert_desc_next_id,
    step_keeps_desc_meta_valid_table, step_keeps_desc_meta_subtype_table,
    step_keeps_desc_meta_kind_table, step_keeps_desc_meta_inline_len_table,
    step_keeps_desc_meta_aux_table, step_keeps_desc_meta_next_id.
  unfold rich_state_cascade, hwb_rich. cbn [rich_morph_table rich_next_morph_id].
  f_equal.
  extensionality i.
  unfold hwb_valid.
  destruct (Nat.ltb i (2 ^ MorphTableIdxSz)) eqn:Hi; [|reflexivity].
  rewrite hw_morph_cascade_spec. unfold cascade_keep, wb.
  destruct (hw_morph_valid_table b (natToWord MorphTableIdxSz i)) eqn:V; cbn [andb]; [|reflexivity].
  unfold hwb_vector_nat. rewrite Hi. cbn [morph_entry_source morph_entry_target].
  destruct (Nat.eqb (wordToNat (hw_morph_src_table b (natToWord MorphTableIdxSz i))) (wordToNat m1)),
           (Nat.eqb (wordToNat (hw_morph_dst_table b (natToWord MorphTableIdxSz i))) (wordToNat m1)),
           (Nat.eqb (wordToNat (hw_morph_src_table b (natToWord MorphTableIdxSz i))) (wordToNat m2)),
           (Nat.eqb (wordToNat (hw_morph_dst_table b (natToWord MorphTableIdxSz i))) (wordToNat m2));
    reflexivity.
Qed.

(** * Capacity checks

    PNEW and PMERGE need one free partition-table slot, PSPLIT two, and a
    nonempty PNEW range must end inside data memory. The step rule's
    word-level tests against [kami_step]'s natural-number tests. *)

Lemma pt_room_one_ltb : forall b,
  hw_pt_room_one b = Nat.ltb (wordToNat (hw_pt_next_id b)) 64.
Proof.
  intro b. unfold hw_pt_room_one. rewrite bool_of_wlt. reflexivity.
Qed.

Lemma pt_room_two_leb : forall b, wordToNat (hw_pt_next_id b) <= 64 ->
  hw_pt_room_two b = Nat.leb (S (S (wordToNat (hw_pt_next_id b)))) 64.
Proof.
  intros b H. unfold hw_pt_room_two.
  destruct (wlt_dec _ _) as [L|L].
  - apply wlt_lt in L. rewrite wordToNat_wplus_7 in L by lia.
    change (wordToNat (natToWord PTableNextIdSz 64)) with 64 in L.
    symmetry. apply Nat.leb_gt. lia.
  - symmetry. apply Nat.leb_le.
    destruct (Nat.le_gt_cases (S (S (wordToNat (hw_pt_next_id b)))) 64) as [Hle|Hgt]; [exact Hle|].
    exfalso. apply L. apply lt_wlt. rewrite wordToNat_wplus_7 by lia.
    change (wordToNat (natToWord PTableNextIdSz 64)) with 64. lia.
Qed.

Lemma hw_pnew_in_memory_nat : forall (a n : word 8),
  hw_pnew_in_memory (zext a 24) (zext n 24) =
  orb (Nat.eqb (wordToNat n) 0) (Nat.leb (wordToNat a + wordToNat n) 128).
Proof.
  intros a n. unfold hw_pnew_in_memory. ev_simp2.
  cbn [evalExpr evalConstT evalBinBit].
  pose proof (wordToNat_bound a) as Ba. pose proof (wordToNat_bound n) as Bn.
  change (pow2 8) with 256 in Ba, Bn.
  assert (H32 : 512 <= pow2 WordSz)
    by (change 512 with (pow2 9); apply Nat.lt_le_incl, pow2_inc; unfold WordSz; lia).
  rewrite wordToNat_wplus_bounded by (rewrite !wordToNat_zext8_32; lia).
  rewrite !wordToNat_zext8_32, wordToNat_word0_32.
  change (wordToNat (natToWord WordSz 128)) with 128.
  destruct (Nat.eqb_spec (wordToNat n) 0),
           (Nat.ltb_spec 128 (wordToNat a + wordToNat n)),
           (Nat.leb_spec (wordToNat a + wordToNat n) 128);
    cbn [negb andb orb]; try reflexivity; lia.
Qed.
