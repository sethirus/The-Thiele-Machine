(** CouplingComposeKami.v: [kami_step] for COMPOSE over a hardware snapshot.

    The kernel's descriptor pairs are the hardware pair-table slice as
    naturals, relational composition over naturals is the hardware join over
    words, a descriptor's label is the atom list its count and mask encode
    ("empty" for a morphism without a valid descriptor), and composing two
    labels is the hardware's count addition and shifted mask addition. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool FunctionalExtensionality.
Import ListNotations.
Require Import Kernel.VMState Kernel.VMStep.
Import VMStep.VMStep.
From KamiHW Require Import ThieleTypes HWBoundary StepWordFacts StepRefineCommon StepFieldsMorph
  StepRefineMorph ImplementationContract Abstraction NormalizationSteps NormalizationLoop MorphLoading
  MorphCopy MorphJoin CouplingMorphKami CouplingMorphRich.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(** * Invariants of the descriptor and pair tables *)

(** A valid descriptor's pairs lie below the pair allocation pointer. *)
Definition hwb_desc_pairs_below_next (b : HWB) : Prop :=
  forall d, hw_coupling_desc_valid_table b d = true ->
  wordToNat (hw_coupling_desc_base_table b d) + wordToNat (hw_coupling_desc_count_table b d) <=
  wordToNat (hw_coupling_pair_next_id b).

(** Every pair cell below the allocation pointer is marked valid. *)
Definition hwb_pairs_valid_below_next (b : HWB) : Prop :=
  forall k : word CouplingPairIdxSz, wordToNat k < wordToNat (hw_coupling_pair_next_id b) ->
  hw_coupling_pair_valid_table b k = true.

(** The reserved descriptor 0 has base 0 and count 0. *)
Definition hwb_desc_zero_empty (b : HWB) : Prop :=
  hw_coupling_desc_base_table b (natToWord CouplingDescIdxSz 0) = natToWord CouplingPairIdxSz 0 /\
  hw_coupling_desc_count_table b (natToWord CouplingDescIdxSz 0) = natToWord CouplingPairCountSz 0.

(** A valid morphism flagged identity refers to descriptor 0. *)
Definition hwb_identity_desc_zero (b : HWB) : Prop :=
  forall m, hw_morph_valid_table b m = true -> hw_morph_identity_table b m = true ->
  hw_morph_coupling_desc_table b m = natToWord DescIdxSz 0.

(** A valid descriptor stores between 1 and 32 atoms and a mask within its
    atom count. *)
Definition hwb_labels_represented (b : HWB) : Prop :=
  forall d, hw_coupling_desc_valid_table b d = true ->
  1 <= wordToNat (hw_coupling_desc_label_len_table b d) <= 32 /\
  wordToNat (hw_coupling_desc_label_table b d) < 2 ^ wordToNat (hw_coupling_desc_label_len_table b d).

(** * Pairs *)

Lemma word32_eqb_nat : forall x y : word 32, word_eqb x y = Nat.eqb (wordToNat x) (wordToNat y).
Proof.
  intros x y. unfold word_eqb. destruct (weq x y) as [E|E].
  - subst. symmetry. apply Nat.eqb_refl.
  - symmetry. apply Nat.eqb_neq. intro H. apply E. apply wordToNat_inj. exact H.
Qed.

Lemma compose_row_natpair : forall (a c : word 32) l2,
  map (fun '(_, c0) => (wordToNat a, c0))
    (filter (fun '(b', _) => Nat.eqb (wordToNat c) b') (map natpair l2)) =
  map natpair (flat_map (fun q => if word_eqb c (fst q) then [(a, snd q)] else nil) l2).
Proof.
  intros a c l2. induction l2 as [|[x y] l2 IH]; [reflexivity|].
  cbn [map filter flat_map fst snd]. unfold natpair at 1. cbn [fst snd].
  rewrite word32_eqb_nat.
  destruct (Nat.eqb (wordToNat c) (wordToNat x)); cbn [map List.app]; rewrite IH; reflexivity.
Qed.

Theorem relational_compose_natpair : forall l1 l2,
  relational_compose (map natpair l1) (map natpair l2) = map natpair (relational_word_join l1 l2).
Proof.
  intros l1 l2. unfold relational_compose, relational_word_join.
  induction l1 as [|[a c] l1 IH]; [reflexivity|].
  cbn [map flat_map]. rewrite map_app, IH. f_equal.
  unfold natpair at 1. cbn [fst snd]. apply compose_row_natpair.
Qed.

Lemma table_pair_nat : forall (src dst : PairTable) k, k < 16 ->
  natpair (table_pair src dst k) = (hwb_vector_nat src k, hwb_vector_nat dst k).
Proof.
  intros src dst k Hk. unfold natpair, table_pair, hwb_vector_nat. cbn [fst snd].
  rewrite (proj2 (Nat.ltb_lt k (2 ^ 4))) by (cbn; lia).
  rewrite (CouplingMorphRich.pair_index_small k Hk). reflexivity.
Qed.

Lemma filtermap_pairs : forall b count s base,
  hwb_pairs_valid_below_next b -> wordToNat (hw_coupling_pair_next_id b) <= 16 ->
  base + s + count <= wordToNat (hw_coupling_pair_next_id b) ->
  filtermap
    (fun ofs => match rich_coupling_pair_table (hwb_rich b) (base + ofs) with
                | Some cpair => Some (coupling_pair_source cpair, coupling_pair_target cpair)
                | None => None
                end) (seq s count) =
  map natpair (map (table_pair (hw_coupling_pair_src_table b) (hw_coupling_pair_dst_table b))
    (seq (base + s) count)).
Proof.
  induction count as [|n IH]; intros s base Hv H16 Hc; [reflexivity|].
  cbn [seq filtermap map].
  set (k := base + s).
  assert (Hk : k < wordToNat (hw_coupling_pair_next_id b)) by (unfold k; lia).
  cbn [hwb_rich rich_coupling_pair_table].
  rewrite (proj2 (Nat.ltb_lt _ _) Hk).
  unfold hwb_valid. rewrite (proj2 (Nat.ltb_lt k (2 ^ CouplingPairIdxSz))) by (cbn; lia).
  rewrite Hv by (rewrite wordToNat_natToWord_2 by (cbn; lia); exact Hk).
  cbn [coupling_pair_source coupling_pair_target].
  rewrite table_pair_nat by lia. f_equal.
  unfold k. replace (S (base + s)) with (base + S s) by lia.
  apply IH; [exact Hv|exact H16|lia].
Qed.

Definition hw_desc_slice (b : HWB) (d : word CouplingDescIdxSz) : list coupling_pair :=
  table_slice (hw_coupling_pair_src_table b) (hw_coupling_pair_dst_table b)
    (wordToNat (hw_coupling_desc_base_table b d)) (wordToNat (hw_coupling_desc_count_table b d)).

Lemma snap_valid_desc_pairs : forall b d,
  hwb_desc_pairs_below_next b -> hwb_pairs_valid_below_next b ->
  wordToNat (hw_coupling_pair_next_id b) <= 16 ->
  hw_coupling_desc_valid_table b d = true ->
  snapshot_coupling_pairs_from_desc (hwb_rich b) (wordToNat d) = map natpair (hw_desc_slice b d).
Proof.
  intros b d Hd Hv H16 Hval.
  unfold snapshot_coupling_pairs_from_desc. cbn [hwb_rich rich_coupling_desc_table].
  unfold hwb_valid at 1. rewrite (proj2 (Nat.ltb_lt _ _) (wordToNat_bound d)), natToWord_wordToNat, Hval.
  cbn [coupling_desc_base coupling_desc_count].
  unfold hwb_vector_nat. rewrite !(proj2 (Nat.ltb_lt _ _) (wordToNat_bound d)), !natToWord_wordToNat.
  rewrite (filtermap_pairs b _ 0 _ Hv H16) by (rewrite Nat.add_0_r; exact (Hd d Hval)).
  rewrite Nat.add_0_r. reflexivity.
Qed.

(** Pairs of a valid morphism's descriptor: a valid descriptor, or the
    empty descriptor 0. *)
Lemma snap_morph_desc_pairs : forall b m,
  hwb_morph_coupling_refs_ok b -> hwb_coupling_desc_zero_invalid b -> hwb_desc_zero_empty b ->
  hwb_desc_pairs_below_next b -> hwb_pairs_valid_below_next b ->
  wordToNat (hw_coupling_pair_next_id b) <= 16 ->
  hw_morph_valid_table b m = true ->
  snapshot_coupling_pairs_from_desc (hwb_rich b) (wordToNat (hw_morph_coupling_desc_table b m)) =
  map natpair (hw_desc_slice b (hw_morph_coupling_desc_table b m)).
Proof.
  intros b m Hr Hz [Hz0 Hc0] Hd Hv H16 Hm.
  pose proof (Hr m Hm) as R. revert R.
  set (d := hw_morph_coupling_desc_table b m).
  destruct (hw_coupling_desc_valid_table b d) eqn:Hval; intro R.
  - exact (snap_valid_desc_pairs b d Hd Hv H16 Hval).
  - unfold hw_coupling_ref_ok in R. revert R.
    destruct (weq d (natToWord DescIdxSz 0)) as [E|E]; intro R.
    + unfold snapshot_coupling_pairs_from_desc. cbn [hwb_rich rich_coupling_desc_table].
      unfold hwb_valid at 1. rewrite (proj2 (Nat.ltb_lt _ _) (wordToNat_bound _)), natToWord_wordToNat, Hval.
      unfold hw_desc_slice. rewrite E. change (natToWord DescIdxSz 0) with (natToWord CouplingDescIdxSz 0).
      rewrite Hc0. reflexivity.
    + exfalso. revert R. destruct (wlt_dec _ _); [|discriminate].
      rewrite Hval. discriminate.
Qed.

(** * Labels *)

(** The label atoms a morphism's descriptor contributes: its stored count and
    mask when the descriptor is valid, and the single "empty" atom otherwise. *)
Definition hw_label_len (b : HWB) (d : word CouplingDescIdxSz) : word 6 :=
  if hw_coupling_desc_valid_table b d then hw_coupling_desc_label_len_table b d else natToWord 6 1.
Definition hw_label_word (b : HWB) (d : word CouplingDescIdxSz) : word WordSz :=
  if hw_coupling_desc_valid_table b d then hw_coupling_desc_label_table b d else natToWord WordSz 1.

Lemma label_represented_at : forall b d, hwb_labels_represented b ->
  (1 <= wordToNat (hw_label_len b d) <= 32) /\
  wordToNat (hw_label_word b d) < 2 ^ wordToNat (hw_label_len b d).
Proof.
  intros b d H. unfold hw_label_len, hw_label_word.
  destruct (hw_coupling_desc_valid_table b d) eqn:V; [exact (H d V)|].
  rewrite wordToNat_word1_32. change (wordToNat (natToWord 6 1)) with 1. cbn. lia.
Qed.

Lemma desc_label_hw : forall b (d : word CouplingDescIdxSz),
  match rich_coupling_desc_table (hwb_rich b) (wordToNat d) with
  | Some desc => coupling_desc_label desc
  | None => coupling_label empty_coupling_data
  end = atom_label (wordToNat (hw_label_len b d)) (wordToNat (hw_label_word b d)).
Proof.
  intros b d. cbn [hwb_rich rich_coupling_desc_table].
  unfold hwb_valid at 1. rewrite (proj2 (Nat.ltb_lt _ _) (wordToNat_bound d)), natToWord_wordToNat.
  unfold hw_label_len, hw_label_word.
  destruct (hw_coupling_desc_valid_table b d); cbn [coupling_desc_label].
  - rewrite !hwb_vector_nat_at. reflexivity.
  - rewrite wordToNat_word1_32. reflexivity.
Qed.

Theorem compose_label_hw : forall b d1 d2, hwb_labels_represented b ->
  wordToNat (hw_label_len b d1) + wordToNat (hw_label_len b d2) <= 32 ->
  (atom_label (wordToNat (hw_label_len b d1)) (wordToNat (hw_label_word b d1)) ++ ";" ++
   atom_label (wordToNat (hw_label_len b d2)) (wordToNat (hw_label_word b d2)))%string =
  atom_label (wordToNat (wplus (hw_label_len b d1) (hw_label_len b d2)))
    (wordToNat (wplus (hw_label_word b d1)
                 (wlshift (hw_label_word b d2) (wordToNat (hw_label_len b d1))))).
Proof.
  intros b d1 d2 H Hsum.
  destruct (label_represented_at b d1 H) as [[A1 B1] C1].
  destruct (label_represented_at b d2 H) as [[A2 B2] C2].
  revert A1 B1 C1 A2 B2 C2 Hsum.
  generalize (hw_label_len b d1) (hw_label_len b d2) (hw_label_word b d1) (hw_label_word b d2).
  intros L1 L2 W1 W2 A1 B1 C1 A2 B2 C2 Hsum.
  rewrite atom_label_compose by assumption.
  assert (Hshift : wordToNat (wlshift W2 (wordToNat L1)) = wordToNat W2 * 2 ^ wordToNat L1).
  { rewrite wordToNat_wlshift. rewrite Nat.mod_small; [reflexivity|].
    eapply Nat.lt_le_trans; [exact C2|]. assert (WordSz = 32) by reflexivity. apply Nat.pow_le_mono_r; lia. }
  assert (Hbound : wordToNat W1 + wordToNat W2 * 2 ^ wordToNat L1 < 2 ^ 32).
  { assert (P : (wordToNat W2 + 1) * 2 ^ wordToNat L1 <= 2 ^ wordToNat L2 * 2 ^ wordToNat L1)
      by (apply Nat.mul_le_mono_r; lia).
    rewrite <- Nat.pow_add_r in P.
    assert (Q : 2 ^ (wordToNat L2 + wordToNat L1) <= 2 ^ 32) by (apply Nat.pow_le_mono_r; lia).
    nia. }
  f_equal.
  - rewrite wordToNat_wplus_bounded; [reflexivity|]. change (pow2 6) with 64. lia.
  - rewrite wordToNat_wplus_bounded; rewrite Hshift; [reflexivity|exact Hbound].
Qed.

(** * COMPOSE *)

Lemma rich_morph_at : forall b (M : word MorphTableIdxSz), hw_morph_valid_table b M = true ->
  rich_morph_table (hwb_rich b) (wordToNat M) =
  Some {| morph_entry_source := wordToNat (hw_morph_src_table b M);
          morph_entry_target := wordToNat (hw_morph_dst_table b M);
          morph_entry_coupling_desc := wordToNat (hw_morph_coupling_desc_table b M);
          morph_entry_is_identity := hw_morph_identity_table b M |}.
Proof.
  intros b M H. cbn [hwb_rich rich_morph_table].
  unfold hwb_valid. rewrite !(proj2 (Nat.ltb_lt _ _) (wordToNat_bound M)), !natToWord_wordToNat, H.
  rewrite !hwb_vector_nat_at. reflexivity.
Qed.

(** The kernel's raw composed pairs over the hardware tables: the other side's
    pairs when one side is an identity, their relational join otherwise. *)
Definition compose_pairs (b : HWB) (M1 M2 : word MorphTableIdxSz) : list coupling_pair :=
  let d1 := hw_morph_coupling_desc_table b M1 in
  let d2 := hw_morph_coupling_desc_table b M2 in
  if hw_morph_identity_table b M1 then hw_desc_slice b d2
  else if hw_morph_identity_table b M2 then hw_desc_slice b d1
  else relational_word_join (hw_desc_slice b d1) (hw_desc_slice b d2).

Theorem kami_step_compose_hw : forall b dst (M1 M2 : word MorphTableIdxSz) cost,
  hwb_morph_coupling_refs_ok b -> hwb_coupling_desc_zero_invalid b -> hwb_desc_zero_empty b ->
  hwb_desc_pairs_below_next b -> hwb_pairs_valid_below_next b ->
  wordToNat (hw_coupling_pair_next_id b) <= 16 ->
  hw_morph_valid_table b M1 = true -> hw_morph_valid_table b M2 = true ->
  hw_morph_dst_table b M1 = hw_morph_src_table b M2 ->
  let d1 := hw_morph_coupling_desc_table b M1 in
  let d2 := hw_morph_coupling_desc_table b M2 in
  let raw := compose_pairs b M1 M2 in
  let lab := (atom_label (wordToNat (hw_label_len b d1)) (wordToNat (hw_label_word b d1)) ++ ";" ++
              atom_label (wordToNat (hw_label_len b d2)) (wordToNat (hw_label_word b d2)))%string in
  kami_step (hwb_snapshot b) (instr_compose dst (wordToNat M1) (wordToNat M2) cost) =
  kami_advance_rich_morph (hwb_snapshot b) dst
    (snd (rich_state_add_morph_with_coupling (hwb_rich b) (wordToNat (hw_morph_src_table b M1))
       (wordToNat (hw_morph_dst_table b M2)) (map natpair (nodup coupling_pair_eq_dec raw)) lab false))
    cost
    (fst (rich_state_add_morph_with_coupling (hwb_rich b) (wordToNat (hw_morph_src_table b M1))
       (wordToNat (hw_morph_dst_table b M2)) (map natpair (nodup coupling_pair_eq_dec raw)) lab false)).
Proof.
  intros b dst M1 M2 cost Hr Hz Hz0 Hd Hv H16 V1 V2 Hmatch d1 d2 raw lab.
  unfold kami_step. change (snap_rich_state (hwb_snapshot b)) with (hwb_rich b).
  rewrite (rich_morph_at b M1 V1), (rich_morph_at b M2 V2).
  cbv beta iota zeta.
  cbn [morph_entry_coupling_desc morph_entry_target morph_entry_source morph_entry_is_identity].
  rewrite Hmatch, Nat.eqb_refl.
  rewrite (snap_morph_desc_pairs b M1 Hr Hz Hz0 Hd Hv H16 V1), (snap_morph_desc_pairs b M2 Hr Hz Hz0 Hd Hv H16 V2).
  unfold morph_coupling_label. cbn [morph_entry_coupling_desc].
  rewrite !desc_label_hw.
  unfold normalize_coupling. cbn [coupling_pairs].
  fold d1 d2. fold lab.
  assert (Raw : (if hw_morph_identity_table b M1 then map natpair (hw_desc_slice b d2)
                 else if hw_morph_identity_table b M2 then map natpair (hw_desc_slice b d1)
                 else relational_compose (map natpair (hw_desc_slice b d1)) (map natpair (hw_desc_slice b d2))) =
                map natpair raw).
  { unfold raw, compose_pairs. fold d1 d2. destruct (hw_morph_identity_table b M1); [reflexivity|].
    destruct (hw_morph_identity_table b M2); [reflexivity|]. apply relational_compose_natpair. }
  rewrite Raw, nodup_map_natpair.
  destruct (rich_state_add_morph_with_coupling _ _ _ _ _ _). reflexivity.
Qed.
