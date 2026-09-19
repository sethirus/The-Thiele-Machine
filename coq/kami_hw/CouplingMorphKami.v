(** CouplingMorphKami.v: [kami_step] for MORPH over a hardware snapshot.
    The kernel's serialized pairs read from snapshot memory are the hardware's
    loaded word pairs as naturals, deduplication commutes with that map, and
    under the region and empty-label premises MORPH adds the deduplicated pairs
    with the empty label. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool FunctionalExtensionality.
Import ListNotations.
Require Import Kernel.VMState Kernel.VMStep.
Import VMStep.VMStep.
From KamiHW Require Import ThieleTypes HWBoundary StepWordFacts StepRefineCommon
  ImplementationContract Abstraction NormalizationSteps NormalizationLoop MorphLoading.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Definition natpair (p : coupling_pair) : nat * nat := (wordToNat (fst p), wordToNat (snd p)).

Lemma natpair_inj : forall x y, natpair x = natpair y -> x = y.
Proof.
  intros [a b] [c d] H. unfold natpair in H. cbn in H. inversion H as [[E1 E2]].
  apply wordToNat_inj in E1. apply wordToNat_inj in E2. subst. reflexivity.
Qed.

Lemma nodup_map_natpair : forall l,
  nodup (pair_eq_dec Nat.eq_dec Nat.eq_dec) (map natpair l) = map natpair (nodup coupling_pair_eq_dec l).
Proof.
  induction l as [|x l IH]; [reflexivity|]. cbn [map nodup].
  destruct (in_dec (pair_eq_dec Nat.eq_dec Nat.eq_dec) (natpair x) (map natpair l)) as [I|I];
  destruct (in_dec coupling_pair_eq_dec x l) as [J|J].
  - exact IH.
  - exfalso. apply in_map_iff in I. destruct I as [y [E Y]]. apply natpair_inj in E. subst. contradiction.
  - exfalso. apply I. apply in_map. exact J.
  - cbn [map]. f_equal. exact IH.
Qed.

Lemma lt128_pow2_32 : forall k, k < 128 -> k < pow2 32.
Proof. intros k H. apply (Nat.lt_le_trans _ (2 ^ 7)); [exact H|]. change (pow2 32) with (2 ^ 32). apply Nat.pow_le_mono_r; lia. Qed.

Lemma mem_index_small : forall w : word 32, wordToNat w < 128 -> MorphLoading.mem_index w = natToWord 7 (wordToNat w).
Proof.
  intros w H. unfold MorphLoading.mem_index. apply wordToNat_inj.
  rewrite wordToNat_split1. rewrite (@wordToNat_natToWord_2 7 (wordToNat w)) by exact H. apply Nat.mod_small. exact H.
Qed.

Lemma loaded_addr : forall (base : word 7) j, wordToNat base + 1 + j < 128 ->
  MorphLoading.mem_index (wplus (wplus (zext base 25) (natToWord 32 1)) (natToWord 32 j)) =
  natToWord 7 (wordToNat base + 1 + j).
Proof.
  intros base j H.
  set (x := zext base 25).
  assert (Hx : @wordToNat 32 x = wordToNat base) by exact (wordToNat_zext base 25).
  assert (H1 : @wordToNat 32 (natToWord 32 1) = 1) by (apply wordToNat_natToWord_2; apply lt128_pow2_32; lia).
  assert (Hj : @wordToNat 32 (natToWord 32 j) = j) by (apply wordToNat_natToWord_2; apply lt128_pow2_32; lia).
  assert (Wx1 : @wordToNat 32 (wplus x (natToWord 32 1)) = wordToNat base + 1).
  { rewrite wordToNat_wplus_bounded; [exact (f_equal2 Nat.add Hx H1)|].
    eapply Nat.le_lt_trans; [apply Nat.eq_le_incl; exact (f_equal2 Nat.add Hx H1)|apply lt128_pow2_32; lia]. }
  assert (W : @wordToNat 32 (wplus (wplus x (natToWord 32 1)) (natToWord 32 j)) = wordToNat base + 1 + j).
  { rewrite wordToNat_wplus_bounded; [exact (f_equal2 Nat.add Wx1 Hj)|].
    eapply Nat.le_lt_trans; [apply Nat.eq_le_incl; exact (f_equal2 Nat.add Wx1 Hj)|apply lt128_pow2_32; lia]. }
  rewrite mem_index_small; [exact (f_equal (natToWord 7) W)|]. rewrite W. lia.
Qed.

Lemma memory_word_at_hw : forall b a, a < 128 ->
  memory_word_at (snapshot_mem_to_list (snap_mem (hwb_snapshot b))) a = wordToNat (hw_mem b (natToWord 7 a)).
Proof.
  intros b a H. unfold memory_word_at, list_read_at, VMState.mem_index, snapshot_mem_to_list.
  change MEM_SIZE with 128. rewrite Nat.mod_small by exact H.
  rewrite (nth_indep _ 0 (hwb_vector_nat (hw_mem b) 0)) by (rewrite map_length, seq_length; exact H).
  rewrite map_nth, seq_nth by exact H. cbn [snap_mem hwb_snapshot]. unfold hwb_vector_nat.
  rewrite (proj2 (Nat.ltb_lt _ _)) by (cbn; lia). reflexivity.
Qed.

Lemma load_pairs_seq : forall mem count addr,
  load_coupling_pairs_from_mem mem addr count =
  map (fun k => (memory_word_at mem (addr + 2 * k), memory_word_at mem (S (addr + 2 * k)))) (seq 0 count).
Proof.
  intros mem count. induction count as [|n IH]; intro addr; [reflexivity|].
  cbn [load_coupling_pairs_from_mem seq map]. rewrite IH. rewrite Nat.add_0_r. f_equal.
  rewrite <- seq_shift, map_map. apply map_ext. intro k. f_equal; f_equal; lia.
Qed.

Theorem raw_pairs_nat : forall b (base : word 7) count,
  2 * count + wordToNat base <= 127 ->
  map natpair (map (fun k => (hw_mem b (MorphLoading.mem_index (wplus (wplus (zext base 25) (natToWord 32 1)) (natToWord 32 (2 * k)))),
                               hw_mem b (MorphLoading.mem_index (wplus (wplus (zext base 25) (natToWord 32 1)) (natToWord 32 (2 * k + 1))))))
                   (seq 0 count)) =
  load_coupling_pairs_from_mem (snapshot_mem_to_list (snap_mem (hwb_snapshot b))) (S (wordToNat base)) count.
Proof.
  intros b base count H. rewrite load_pairs_seq, map_map. apply map_ext_in. intros k Hk. apply in_seq in Hk.
  unfold natpair. cbn [fst snd].
  rewrite !loaded_addr by lia. rewrite !memory_word_at_hw by lia.
  f_equal; f_equal; f_equal; f_equal; lia.
Qed.

Definition snap_region (hs : KamiSnapshot) (m : nat) : list nat :=
  match graph_lookup (snap_full_graph hs) m with
  | Some ms => module_region ms
  | None => nil
  end.

Lemma mem_to_string_empty : forall mem a, list_read_at mem a = 0 -> mem_to_string mem a = ""%string.
Proof. intros mem a H. unfold mem_to_string. rewrite H. reflexivity. Qed.

Lemma filter_all_true : forall A (f : A -> bool) l, forallb f l = true -> filter f l = l.
Proof.
  intros A f l. induction l as [|x l IH]; intro H; [reflexivity|].
  cbn [forallb filter] in *. apply andb_prop in H. destruct H as [Hx Hl]. rewrite Hx, IH by exact Hl. reflexivity.
Qed.

Theorem kami_step_morph_success : forall hs dst src dstm cidx cost,
  snap_pt_sizes hs src <> 0 -> snap_pt_sizes hs dstm <> 0 ->
  let mem := snapshot_mem_to_list (snap_mem hs) in
  let cnt := serialized_coupling_pair_count mem cidx in
  forallb (pair_respects_regions (snap_region hs src) (snap_region hs dstm))
    (load_coupling_pairs_from_mem mem (S cidx) cnt) = true ->
  list_read_at mem (VMState.mem_index (S cidx + 2 * cnt)) = 0 ->
  kami_step hs (instr_morph dst src dstm cidx cost) =
  kami_advance_rich_morph hs dst
    (snd (rich_state_add_morph_with_coupling (snap_rich_state hs) src dstm
       (nodup (pair_eq_dec Nat.eq_dec Nat.eq_dec) (load_coupling_pairs_from_mem mem (S cidx) cnt)) ""%string false))
    cost
    (fst (rich_state_add_morph_with_coupling (snap_rich_state hs) src dstm
       (nodup (pair_eq_dec Nat.eq_dec Nat.eq_dec) (load_coupling_pairs_from_mem mem (S cidx) cnt)) ""%string false)).
Proof.
  intros hs dst src dstm cidx cost Hs Hd mem cnt Hreg Hlab.
  unfold kami_step. cbv zeta.
  rewrite (proj2 (Nat.eqb_neq _ _) Hs), (proj2 (Nat.eqb_neq _ _) Hd). cbn [negb andb].
  unfold restrict_coupling_to_regions, normalize_coupling. cbn [coupling_pairs coupling_label].
  fold mem cnt. fold (snap_region hs src) (snap_region hs dstm).
  rewrite filter_all_true by exact Hreg.
  rewrite mem_to_string_empty by exact Hlab.
  destruct (rich_state_add_morph_with_coupling _ _ _ _ _ _). reflexivity.
Qed.
