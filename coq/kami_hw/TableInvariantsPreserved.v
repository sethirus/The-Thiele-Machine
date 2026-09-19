(** TableInvariantsPreserved.v: preservation of [TableInvariants.hwb_table_invariants]
    across [Retire], for the 47 of [RetireMaster.admitted]'s 55 constructors that
    leave every field the invariants mention unchanged ("frame" cases).

    [hwb_table_invariants_frame]: the generic combinator -- given the twelve
    field equalities the nine invariant clauses actually read (four morph-table
    fields, six coupling desc/pair-table fields via [StepEval]'s
    opcode-independent frame lemmas, two label-table fields), the invariants
    transfer from [b] to [d] verbatim.

    45 of the frame constructors retire in a single [step_next] firing
    ([Busy_runs _ _ 0], via [busy_done]): each opcode's own [StepFields]/
    [StepFieldsMorph]/[LassertStepFields] frame lemmas for the four morph
    fields and two label fields, plus [StepEval]'s six unconditional lemmas
    for the rest, close [hwb_table_invariants_frame] directly. The remaining
    two (CHSH_LASSERT, LASSERT_SAT) run a multi-cycle FSM after [step_next]
    ([chsh_iter 23], respectively [lscan_iter n (lhdr_next (step_next b))]);
    [ChshRun]'s and [LassertWord]/[LassertRetire]'s own [iter_keeps_X]/
    [lscan_iter_keeps_X]/[lhdr_keeps_X] frame catalogues chain onto the same
    opcode-specific [step_next] equations to reach the same twelve facts.

    NOT done here: the eight constructors that actually write the morph or
    coupling tables (MORPH_ID/DELETE, legacy and extended, MORPH_EXT,
    COMPOSE_EXT and their fault branches) -- [TableInvariants.v]'s closing
    note has the algebra already available for these (an explicit if-mux at
    the allocation/deletion index from [StepFieldsMorph.v], respectively
    [CouplingFsmRun.morph_fsm_run]/[CouplingComposeRetire]'s field equations
    for the FSM completions, [CouplingFaults.v]'s frame for the fault
    branches); building them is the next increment, after which
    [hwb_table_invariants_preserved : forall b i d, hwb_table_invariants b ->
    admitted b i -> Retire b i d -> hwb_table_invariants d] (all 55 cases) and
    the reachable-state induction it feeds can be stated. *)
Require Import Kami.Kami Kami.Semantics Kami.Lib.NatLib.
From Coq Require Import String List Arith Lia Bool FunctionalExtensionality.
Import ListNotations.
Require Import Kernel.VMState Kernel.VMStep Kernel.CertCheck.
Import VMStep.VMStep.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded StepEval
  StepWordFacts StepFields StepRefineCommon StepRefine StepFieldsMorph StepRefineMorph
  ImplementationContract Abstraction EmbedStep NormalizationSteps NormalizationLoop MorphLoading
  RuleEnabled FsmDecoded ChshDecoded ChshRun ChshStepFields ChshRetire
  LassertSpec LassertWord LassertStepFields LassertRetire CouplingFsmEnds CouplingFsmRun
  CouplingMorphRich CouplingMorphKami CouplingMorphRetire
  CouplingComposeRun CouplingComposeKami CouplingComposeRetire CouplingFaults
  BoundaryRun RetireRuns RetireRunsFsm RetireRunsOps RetireMaster
  DispatchReset StepFaults TableInvariants.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Lemma hw_coupling_ref_ok_frame : forall b d x,
  hw_coupling_desc_next_id d = hw_coupling_desc_next_id b ->
  hw_coupling_desc_valid_table d = hw_coupling_desc_valid_table b ->
  hw_coupling_ref_ok d x = hw_coupling_ref_ok b x.
Proof.
  intros b d x Ecn Ecv. unfold hw_coupling_ref_ok. rewrite Ecn, Ecv. reflexivity.
Qed.

(** A descriptor reference below [coupling_desc_next_id] and marked valid is
    accepted, regardless of whether it is also 0 (irrelevant: 0 is always
    accepted). Mirrors [StepRefineMorph.morph_room_of_lt]'s proof shape. *)
(** [x] is typed [word DescIdxSz] explicitly, matching [hw_coupling_ref_ok]'s
    own parameter: letting it be inferred instead (e.g. from a
    [CouplingDescIdxSz]-typed use elsewhere) elaborates the [weq]/[wlt_dec]
    calls below at a different, merely-convertible index-size instance, and
    then [destruct] does not simplify the (still syntactically different)
    occurrence inside [hw_coupling_ref_ok]'s own unfolded body. *)
Lemma coupling_ref_ok_of_lt : forall b (x : word DescIdxSz),
  wordToNat x < wordToNat (hw_coupling_desc_next_id b) ->
  hw_coupling_desc_valid_table b x = true ->
  hw_coupling_ref_ok b x = true.
Proof.
  intros b x Hlt Hv. unfold hw_coupling_ref_ok.
  destruct (weq x (natToWord DescIdxSz 0)) as [_|_]; [reflexivity|].
  destruct (wlt_dec (zext x 1) (hw_coupling_desc_next_id b)) as [_|L]; [exact Hv|].
  exfalso. apply L. apply lt_wlt. rewrite wordToNat_zext. exact Hlt.
Qed.

Lemma hwb_table_invariants_frame : forall b d,
  hw_morph_valid_table d = hw_morph_valid_table b ->
  hw_morph_next_id d = hw_morph_next_id b ->
  hw_morph_coupling_desc_table d = hw_morph_coupling_desc_table b ->
  hw_morph_identity_table d = hw_morph_identity_table b ->
  hw_coupling_desc_valid_table d = hw_coupling_desc_valid_table b ->
  hw_coupling_desc_next_id d = hw_coupling_desc_next_id b ->
  hw_coupling_desc_base_table d = hw_coupling_desc_base_table b ->
  hw_coupling_desc_count_table d = hw_coupling_desc_count_table b ->
  hw_coupling_pair_next_id d = hw_coupling_pair_next_id b ->
  hw_coupling_pair_valid_table d = hw_coupling_pair_valid_table b ->
  hw_coupling_desc_label_table d = hw_coupling_desc_label_table b ->
  hw_coupling_desc_label_len_table d = hw_coupling_desc_label_len_table b ->
  hwb_table_invariants b -> hwb_table_invariants d.
Proof.
  intros b d Emv Emn Emc Emi Ecv Ecn Ecb Ecc Epn Epv Elt Ell Hinv.
  destruct Hinv as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
  unfold hwb_table_invariants.
  split.
  { unfold hwb_morph_valid_below_next.
    intros i Hi. rewrite Emv in Hi. rewrite Emn. exact (H1 i Hi). }
  split.
  { unfold hwb_morph_coupling_refs_ok.
    intros i Hi. rewrite Emv in Hi. rewrite Emc.
    rewrite (hw_coupling_ref_ok_frame b d _ Ecn Ecv). exact (H2 i Hi). }
  split.
  { unfold hwb_coupling_desc_zero_invalid. rewrite Ecv. exact H3. }
  split.
  { unfold hwb_coupling_desc_valid_below_next.
    intros i Hi. rewrite Ecv in Hi. rewrite Ecn. exact (H4 i Hi). }
  split.
  { unfold hwb_desc_pairs_below_next.
    intros k Hk. rewrite Ecv in Hk. rewrite Ecb, Ecc, Epn. exact (H5 k Hk). }
  split.
  { unfold hwb_pairs_valid_below_next.
    intros k Hk. rewrite Epn in Hk. rewrite Epv. exact (H6 k Hk). }
  split.
  { unfold hwb_desc_zero_empty. rewrite Ecb, Ecc. exact H7. }
  split.
  { unfold hwb_identity_desc_zero.
    intros m Hv Hi. rewrite Emv in Hv. rewrite Emi in Hi. rewrite Emc. exact (H8 m Hv Hi). }
  split.
  { unfold hwb_labels_represented.
    intros k Hk. rewrite Ecv in Hk. rewrite Ell, Elt. exact (H9 k Hk). }
  { unfold hwb_coupling_desc_next_id_ge1. rewrite Ecn. exact H10. }
Qed.

(** [d]'s morph-valid set is a subset of [b]'s (deletion only clears bits);
    every other invariant-relevant field is unchanged. Covers MORPH_DELETE
    and MORPH_DELETE_EXT, where only [hw_morph_valid_table] moves. *)
Lemma hwb_table_invariants_frame_valid_subset : forall b d,
  (forall i, hw_morph_valid_table d i = true -> hw_morph_valid_table b i = true) ->
  hw_morph_next_id d = hw_morph_next_id b ->
  hw_morph_coupling_desc_table d = hw_morph_coupling_desc_table b ->
  hw_morph_identity_table d = hw_morph_identity_table b ->
  hw_coupling_desc_valid_table d = hw_coupling_desc_valid_table b ->
  hw_coupling_desc_next_id d = hw_coupling_desc_next_id b ->
  hw_coupling_desc_base_table d = hw_coupling_desc_base_table b ->
  hw_coupling_desc_count_table d = hw_coupling_desc_count_table b ->
  hw_coupling_pair_next_id d = hw_coupling_pair_next_id b ->
  hw_coupling_pair_valid_table d = hw_coupling_pair_valid_table b ->
  hw_coupling_desc_label_table d = hw_coupling_desc_label_table b ->
  hw_coupling_desc_label_len_table d = hw_coupling_desc_label_len_table b ->
  hwb_table_invariants b -> hwb_table_invariants d.
Proof.
  intros b d Hsub Emn Emc Emi Ecv Ecn Ecb Ecc Epn Epv Elt Ell Hinv.
  destruct Hinv as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
  unfold hwb_table_invariants.
  split.
  { unfold hwb_morph_valid_below_next. intros i Hi. rewrite Emn. exact (H1 i (Hsub i Hi)). }
  split.
  { unfold hwb_morph_coupling_refs_ok. intros i Hi. rewrite Emc.
    rewrite (hw_coupling_ref_ok_frame b d _ Ecn Ecv). exact (H2 i (Hsub i Hi)). }
  split.
  { unfold hwb_coupling_desc_zero_invalid. rewrite Ecv. exact H3. }
  split.
  { unfold hwb_coupling_desc_valid_below_next. intros i Hi. rewrite Ecv in Hi. rewrite Ecn. exact (H4 i Hi). }
  split.
  { unfold hwb_desc_pairs_below_next. intros k Hk. rewrite Ecv in Hk. rewrite Ecb, Ecc, Epn. exact (H5 k Hk). }
  split.
  { unfold hwb_pairs_valid_below_next. intros k Hk. rewrite Epn in Hk. rewrite Epv. exact (H6 k Hk). }
  split.
  { unfold hwb_desc_zero_empty. rewrite Ecb, Ecc. exact H7. }
  split.
  { unfold hwb_identity_desc_zero. intros m Hv Hi. rewrite Emi in Hi. rewrite Emc. exact (H8 m (Hsub m Hv) Hi). }
  split.
  { unfold hwb_labels_represented. intros k Hk. rewrite Ecv in Hk. rewrite Ell, Elt. exact (H9 k Hk). }
  { unfold hwb_coupling_desc_next_id_ge1. rewrite Ecn. exact H10. }
Qed.

(** A fresh morph slot [s] (below the pre-write [morph_next_id b], which
    then increments by exactly 1) is allocated as an entry referring to
    descriptor 0; every coupling-table field is unchanged. Covers
    MORPH_ID/MORPH_ID_EXT with the write actually firing (room and module
    both present). *)
Lemma hwb_table_invariants_alloc_morph : forall b d (s : word MorphTableIdxSz),
  wordToNat s = wordToNat (hw_morph_next_id b) ->
  wordToNat (hw_morph_next_id b) < 16 ->
  hw_morph_valid_table d = (fun w => if weq w s then true else hw_morph_valid_table b w) ->
  hw_morph_coupling_desc_table d = (fun w => if weq w s then natToWord DescIdxSz 0 else hw_morph_coupling_desc_table b w) ->
  hw_morph_identity_table d = (fun w => if weq w s then true else hw_morph_identity_table b w) ->
  hw_morph_next_id d = wplus (hw_morph_next_id b) (natToWord MorphTableNextIdSz 1) ->
  hw_coupling_desc_valid_table d = hw_coupling_desc_valid_table b ->
  hw_coupling_desc_next_id d = hw_coupling_desc_next_id b ->
  hw_coupling_desc_base_table d = hw_coupling_desc_base_table b ->
  hw_coupling_desc_count_table d = hw_coupling_desc_count_table b ->
  hw_coupling_pair_next_id d = hw_coupling_pair_next_id b ->
  hw_coupling_pair_valid_table d = hw_coupling_pair_valid_table b ->
  hw_coupling_desc_label_table d = hw_coupling_desc_label_table b ->
  hw_coupling_desc_label_len_table d = hw_coupling_desc_label_len_table b ->
  hwb_table_invariants b -> hwb_table_invariants d.
Proof.
  intros b d s Hs Hlt Hmv Hmc Hmi Emn Ecv Ecn Ecb Ecc Epn Epv Elt Ell Hinv.
  destruct Hinv as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
  assert (Hnd : wordToNat (hw_morph_next_id d) = wordToNat (hw_morph_next_id b) + 1).
  { rewrite Emn. apply wordToNat_wplus_bounded. cbn. lia. }
  assert (Hzero : hw_coupling_ref_ok d (natToWord DescIdxSz 0) = true).
  { unfold hw_coupling_ref_ok. destruct (weq (natToWord DescIdxSz 0) (natToWord DescIdxSz 0)) as [_|Hne].
    - reflexivity.
    - exfalso. apply Hne. reflexivity. }
  unfold hwb_table_invariants.
  split.
  { unfold hwb_morph_valid_below_next. intros i Hi. rewrite Hmv in Hi.
    destruct (weq i s) as [E|N].
    - subst i. rewrite Hnd, Hs. lia.
    - rewrite Hnd. pose proof (H1 i Hi). lia. }
  split.
  { unfold hwb_morph_coupling_refs_ok. intros i Hi. rewrite Hmv in Hi. rewrite Hmc.
    destruct (weq i s) as [E|N].
    - exact Hzero.
    - rewrite (hw_coupling_ref_ok_frame b d _ Ecn Ecv). exact (H2 i Hi). }
  split.
  { unfold hwb_coupling_desc_zero_invalid. rewrite Ecv. exact H3. }
  split.
  { unfold hwb_coupling_desc_valid_below_next. intros i Hi. rewrite Ecv in Hi. rewrite Ecn. exact (H4 i Hi). }
  split.
  { unfold hwb_desc_pairs_below_next. intros k Hk. rewrite Ecv in Hk. rewrite Ecb, Ecc, Epn. exact (H5 k Hk). }
  split.
  { unfold hwb_pairs_valid_below_next. intros k Hk. rewrite Epn in Hk. rewrite Epv. exact (H6 k Hk). }
  split.
  { unfold hwb_desc_zero_empty. rewrite Ecb, Ecc. exact H7. }
  split.
  { unfold hwb_identity_desc_zero. intros m Hv Hi. rewrite Hmv in Hv. rewrite Hmi in Hi. rewrite Hmc.
    destruct (weq m s) as [E|N].
    - reflexivity.
    - exact (H8 m Hv Hi). }
  split.
  { unfold hwb_labels_represented. intros k Hk. rewrite Ecv in Hk. rewrite Ell, Elt. exact (H9 k Hk). }
  { unfold hwb_coupling_desc_next_id_ge1. rewrite Ecn. exact H10. }
Qed.

Lemma preserved_add : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = add_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_add (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b4 b5 b6 b7)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_add_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_add_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_add_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_add_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_add_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_add_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_add_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_add_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_add_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_sub : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = sub_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_sub (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b4 b5 b6 b7)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_sub_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_sub_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_sub_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_sub_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_sub_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_sub_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_sub_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_sub_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_sub_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_and : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = and_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_and (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b4 b5 b6 b7)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_and_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_and_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_and_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_and_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_and_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_and_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_and_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_and_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_and_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_or : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = or_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_or (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b4 b5 b6 b7)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_or_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_or_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_or_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_or_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_or_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_or_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_or_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_or_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_or_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_xor_add : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = xor_add_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_xor_add (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_xor_add_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_xor_add_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_xor_add_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_xor_add_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_add_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_add_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_add_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_xor_add_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_add_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_mul : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = mul_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_mul (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b4 b5 b6 b7)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_mul_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_mul_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_mul_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_mul_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_mul_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_mul_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_mul_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_mul_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_mul_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_xfer : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = xfer_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_xfer (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_xfer_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_xfer_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_xfer_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_xfer_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xfer_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xfer_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xfer_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_xfer_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xfer_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_load_imm : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = load_imm_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_load_imm (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits8 b0 b1 b2 b3 b4 b5 b6 b7)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_load_imm_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_load_imm_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_load_imm_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_load_imm_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_load_imm_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_load_imm_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_load_imm_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_load_imm_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_load_imm_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_shl : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = shl_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_shl (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b4 b5 b6 b7)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_shl_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_shl_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_shl_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_shl_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_shl_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_shl_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_shl_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_shl_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_shl_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_shr : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = shr_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_shr (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b4 b5 b6 b7)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_shr_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_shr_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_shr_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_shr_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_shr_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_shr_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_shr_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_shr_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_shr_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_lui : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = lui_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_lui (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits8 b0 b1 b2 b3 b4 b5 b6 b7)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_lui_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_lui_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_lui_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_lui_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_lui_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_lui_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_lui_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_lui_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_lui_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_xor_load : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = xor_load_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_xor_load (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits8 b0 b1 b2 b3 b4 b5 b6 b7)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_xor_load_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_xor_load_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_xor_load_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_xor_load_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_load_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_load_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_load_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_xor_load_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_load_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_jump : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = jump_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_jump (wordToNat (bits8 b0 b1 b2 b3 b4 b5 b6 b7) + 256 * wordToNat (bits8 a0 a1 a2 a3 a4 a5 a6 a7)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_jump_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_jump_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_jump_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_jump_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_jump_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_jump_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_jump_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_jump_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_jump_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_jnez : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = jnez_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_jnez (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits8 b0 b1 b2 b3 b4 b5 b6 b7)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_jnez_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_jnez_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_jnez_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_jnez_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_jnez_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_jnez_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_jnez_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_jnez_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_jnez_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_mdlacc : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = mdlacc_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_mdlacc (wordToNat (bits8 a0 a1 a2 a3 a4 a5 a6 a7)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_mdlacc_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_mdlacc_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_mdlacc_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_mdlacc_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_mdlacc_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_mdlacc_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_mdlacc_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_mdlacc_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_mdlacc_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_ljoin : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = ljoin_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_ljoin (wordToNat (bits8 a0 a1 a2 a3 a4 a5 a6 a7)) (wordToNat (bits8 b0 b1 b2 b3 b4 b5 b6 b7)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_ljoin_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_ljoin_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_ljoin_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_ljoin_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_ljoin_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_ljoin_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_ljoin_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_ljoin_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_ljoin_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_certify : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = certify_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_certify (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_certify_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_certify_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_certify_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_certify_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_certify_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_certify_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_certify_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_certify_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_certify_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_read_port : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (chan : nat) (d : HWB),
  step_fetched b = read_port_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_read_port (wordToNat (bits4 a0 a1 a2 a3)) chan 0 (wordToNat (bits8 b0 b1 b2 b3 b4 b5 b6 b7)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b chan d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_read_port_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_read_port_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_read_port_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_read_port_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_read_port_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_read_port_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_read_port_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_read_port_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_read_port_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_emit : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (payload : string) (d : HWB),
  step_fetched b = emit_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_emit (wordToNat (bits8 a0 a1 a2 a3 a4 a5 a6 a7)) payload (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b payload d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_emit_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_emit_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_emit_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_emit_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_emit_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_emit_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_emit_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_emit_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_emit_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_reveal : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (cert : string) (d : HWB),
  step_fetched b = reveal_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_reveal (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits8 b0 b1 b2 b3 b4 b5 b6 b7)) cert (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b cert d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_reveal_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_reveal_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_reveal_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_reveal_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_reveal_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_reveal_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_reveal_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_reveal_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_reveal_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_xor_swap : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = xor_swap_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_xor_swap (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_xor_swap_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_xor_swap_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_xor_swap_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_xor_swap_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_swap_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_swap_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_swap_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_xor_swap_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_swap_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_tensor_set : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = tensor_set_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_tensor_set (wordToNat (bits4 a4 a5 a6 a7)) (wordToNat (bits2 a2 a3)) (wordToNat (bits2 a0 a1)) (wordToNat (bits8 b0 b1 b2 b3 b4 b5 b6 b7)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_tensor_set_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_tensor_set_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_tensor_set_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_tensor_set_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_tensor_set_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_tensor_set_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_tensor_set_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_tensor_set_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_tensor_set_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_tensor_get : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = tensor_get_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_tensor_get (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b4 b5 b6 b7)) (wordToNat (bits2 b2 b3)) (wordToNat (bits2 b0 b1)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_tensor_get_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_tensor_get_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_tensor_get_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_tensor_get_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_tensor_get_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_tensor_get_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_tensor_get_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_tensor_get_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_tensor_get_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_pdiscover : forall a0 a1 a2 a3 a4 a5 a6 a7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (evidence : list VMAxiom) (d : HWB),
  step_fetched b = pdiscover_word a0 a1 a2 a3 a4 a5 a6 a7 false false false false false false false false c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_pdiscover (wordToNat (bits8 a0 a1 a2 a3 a4 a5 a6 a7)) evidence (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 c0 c1 c2 c3 c4 c5 c6 c7 b evidence d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_pdiscover_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 false false false false false false false false c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_pdiscover_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 false false false false false false false false c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_pdiscover_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 false false false false false false false false c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_pdiscover_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 false false false false false false false false c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_pdiscover_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 false false false false false false false false c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_pdiscover_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 false false false false false false false false c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_pdiscover_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 false false false false false false false false c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_pdiscover_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 false false false false false false false false c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_pdiscover_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 false false false false false false false false c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_load : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = load_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_load (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_load_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_load_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_load_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_load_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_load_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_load_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_load_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_load_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_load_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_store : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = store_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_store (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_store_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_store_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_store_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_store_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_store_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_store_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_store_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_store_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_store_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_heap_load : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = heap_load_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_heap_load (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_heap_load_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_heap_load_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_heap_load_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_heap_load_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_heap_load_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_heap_load_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_heap_load_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_heap_load_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_heap_load_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_heap_store : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = heap_store_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_heap_store (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_heap_store_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_heap_store_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_heap_store_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_heap_store_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_heap_store_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_heap_store_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_heap_store_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_heap_store_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_heap_store_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_call : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = call_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_call (wordToNat (bits8 b0 b1 b2 b3 b4 b5 b6 b7) + 256 * wordToNat (bits8 a0 a1 a2 a3 a4 a5 a6 a7)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_call_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_call_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_call_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_call_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_call_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_call_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_call_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_call_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_call_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_ret : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = ret_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_ret (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_ret_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_ret_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_ret_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_ret_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_ret_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_ret_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_ret_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_ret_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_ret_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_pnew : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (region : list nat) (d : HWB),
  step_fetched b = pnew_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_pnew region (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b region d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_pnew_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_pnew_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_pnew_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_pnew_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_pnew_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_pnew_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_pnew_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_pnew_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_pnew_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_psplit : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (left : list nat) (right : list nat) (d : HWB),
  step_fetched b = psplit_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_psplit (wordToNat (bits8 a0 a1 a2 a3 a4 a5 a6 a7)) left right (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b left right d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_psplit_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_psplit_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_psplit_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_psplit_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_psplit_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_psplit_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_psplit_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_psplit_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_psplit_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_pmerge : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = pmerge_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_pmerge (wordToNat (bits8 a0 a1 a2 a3 a4 a5 a6 a7)) (wordToNat (bits8 b0 b1 b2 b3 b4 b5 b6 b7)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_pmerge_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_pmerge_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_pmerge_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_pmerge_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_pmerge_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_pmerge_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_pmerge_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_pmerge_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_pmerge_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_chsh_trial : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = chsh_trial_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_chsh_trial (if a1 then 1 else 0) (if a0 then 1 else 0) (if b1 then 1 else 0) (if b0 then 1 else 0) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_chsh_trial_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_chsh_trial_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_chsh_trial_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_chsh_trial_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_chsh_trial_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_chsh_trial_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_chsh_trial_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_chsh_trial_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_chsh_trial_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_xor_rank : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = xor_rank_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_xor_rank (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_xor_rank_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_xor_rank_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_xor_rank_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_xor_rank_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_rank_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_rank_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_rank_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_xor_rank_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_xor_rank_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_halt : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = halt_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_halt (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_halt_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_halt_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_halt_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_halt_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_halt_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_halt_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_halt_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_halt_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_halt_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_checkpoint : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (label : string) (d : HWB),
  step_fetched b = checkpoint_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_checkpoint label (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b label d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_checkpoint_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_checkpoint_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_checkpoint_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_checkpoint_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_checkpoint_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_checkpoint_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_checkpoint_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_checkpoint_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_checkpoint_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_write_port : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (chan : nat) (src : nat) (d : HWB),
  step_fetched b = write_port_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_write_port chan src (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b chan src d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_write_port_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_write_port_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_write_port_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_write_port_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_write_port_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_write_port_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_write_port_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_write_port_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_write_port_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_morph_assert : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (property : string) (cert : string) (d : HWB),
  step_fetched b = morph_assert_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_morph_assert (wordToNat (bits4 a0 a1 a2 a3)) property cert (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b property cert d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_morph_assert_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_morph_assert_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_morph_assert_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_morph_assert_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_assert_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_assert_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_assert_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_morph_assert_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_assert_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_morph_get : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = morph_get_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_morph_get (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) 0 (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_morph_get_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_morph_get_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_morph_get_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_morph_get_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_get_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_get_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_get_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_morph_get_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_get_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_morph_assert_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB) (property : string) (cert : string) (d : HWB),
  step_fetched b = morph_assert_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_morph_assert (wordToNat (bits4 a0 a1 a2 a3)) property cert (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b property cert d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_morph_assert_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
    - exact (step_morph_assert_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
    - exact (step_morph_assert_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_morph_assert_ext_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_assert_ext_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_assert_ext_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_assert_ext_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_morph_assert_ext_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_assert_ext_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_morph_get_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB) (d : HWB),
  step_fetched b = morph_get_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_morph_get (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (bits2 e0 e1)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_morph_get_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
    - exact (step_morph_get_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
    - exact (step_morph_get_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_morph_get_ext_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_get_ext_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_get_ext_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_get_ext_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_morph_get_ext_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_get_ext_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_morph_tensor : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (f : nat) (g : nat) (d : HWB),
  step_fetched b = morph_tensor_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_morph_tensor (wordToNat (bits4 a0 a1 a2 a3)) f g (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b f g d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_morph_tensor_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_morph_tensor_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_morph_tensor_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_morph_tensor_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_tensor_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_tensor_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_tensor_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_morph_tensor_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_tensor_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_morph_tensor_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB) (f : nat) (g : nat) (d : HWB),
  step_fetched b = morph_tensor_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_morph_tensor (wordToNat (bits4 a0 a1 a2 a3)) f g (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b f g d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_morph_tensor_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
    - exact (step_morph_tensor_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
    - exact (step_morph_tensor_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_morph_tensor_ext_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_tensor_ext_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_tensor_ext_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_tensor_ext_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_morph_tensor_ext_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_tensor_ext_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_lassert_unsat : forall a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) flen (d : HWB),
  step_fetched b = lassert_unsat_word a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_lassert (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) false flen (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b flen d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_lassert_unsat_lassert_phase a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_lassert_unsat_chsh_phase a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_lassert_unsat_mc_phase a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - exact (step_lassert_unsat_morph_valid_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_lassert_unsat_morph_next_id a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_lassert_unsat_morph_coupling_desc_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_lassert_unsat_morph_identity_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_lassert_unsat_coupling_desc_label_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_lassert_unsat_coupling_desc_label_len_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.
Lemma preserved_chsh_lassert : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = chsh_lassert_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hw_live b ->
  hwb_table_invariants b ->
  Retire b (instr_chsh_lassert (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hlive Hinv HR.
  assert (Hidle : hw_idle (chsh_iter 23 (step_next b))).
  { split; [rewrite iter_keeps_lassert_phase; exact (step_chsh_lassert_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb)|split].
    - destruct (chsh_run_result (step_next b) (step_chsh_lassert_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb)) as [_ [Hc _]]. exact Hc.
    - rewrite iter_keeps_mc_phase. exact (step_chsh_lassert_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  pose proof (chsh_lassert_runs a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb Hlive) as Hrun.
  assert (Hd : d = chsh_iter 23 (step_next b)).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ Hrun Hidle)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - rewrite iter_keeps_morph_valid_table. exact (step_chsh_lassert_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - rewrite iter_keeps_morph_next_id. exact (step_chsh_lassert_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - rewrite iter_keeps_morph_coupling_desc_table. exact (step_chsh_lassert_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - rewrite iter_keeps_morph_identity_table. exact (step_chsh_lassert_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - rewrite iter_keeps_coupling_desc_valid_table. exact (step_keeps_coupling_desc_valid_table b).
  - rewrite iter_keeps_coupling_desc_next_id. exact (step_keeps_coupling_desc_next_id b).
  - rewrite iter_keeps_coupling_desc_base_table. exact (step_keeps_coupling_desc_base_table b).
  - rewrite iter_keeps_coupling_desc_count_table. exact (step_keeps_coupling_desc_count_table b).
  - rewrite iter_keeps_coupling_pair_next_id. exact (step_keeps_coupling_pair_next_id b).
  - rewrite iter_keeps_coupling_pair_valid_table. exact (step_keeps_coupling_pair_valid_table b).
  - rewrite iter_keeps_coupling_desc_label_table. exact (step_chsh_lassert_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - rewrite iter_keeps_coupling_desc_label_len_table. exact (step_chsh_lassert_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_lassert_sat : forall a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) flen (d : HWB),
  step_fetched b = lassert_sat_word a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hw_live b ->
  wordToNat (hw_pc b) + 1 < pow2 WordSz ->
  wordToNat (hw_trap_vector b) = LASSERT_TRAP_PC ->
  mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3))) = flen ->
  wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 3 + flen < pow2 32 ->
  1 <= mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 2) ->
  mem_at b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)) + 2) <= count_zeros (lassert_words b (wordToNat (hw_regs b (bits4 a0 a1 a2 a3)))) ->
  wordToNat (hw_mu b) + flen * 8 + wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7) + 1 < pow2 32 ->
  hwb_table_invariants b ->
  Retire b (instr_lassert (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) true flen (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b flen d
    Hf Hb Hlive Hpc Htrap Hflen Hfit Hcl1 Hcl2 Hmu Hinv HR.
  destruct (lassert_sat_runs a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b flen Hf Hb Hlive Hpc Htrap Hflen Hfit Hcl1 Hcl2 Hmu)
    as [n [_ [Hr [Hi _]]]].
  assert (Hd : d = lscan_iter n (lhdr_next (step_next b))).
  { destruct HR as [_ [[n' Hn'] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn' Hdi _ _ Hr Hi)). }
  subst d.
  eapply hwb_table_invariants_frame.
  - rewrite lscan_iter_keeps_morph_valid_table, lhdr_keeps_morph_valid_table. exact (step_lassert_sat_morph_valid_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - rewrite lscan_iter_keeps_morph_next_id, lhdr_keeps_morph_next_id. exact (step_lassert_sat_morph_next_id a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - rewrite lscan_iter_keeps_morph_coupling_desc_table, lhdr_keeps_morph_coupling_desc_table. exact (step_lassert_sat_morph_coupling_desc_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - rewrite lscan_iter_keeps_morph_identity_table, lhdr_keeps_morph_identity_table. exact (step_lassert_sat_morph_identity_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - rewrite lscan_iter_keeps_coupling_desc_valid_table, lhdr_keeps_coupling_desc_valid_table. exact (step_keeps_coupling_desc_valid_table b).
  - rewrite lscan_iter_keeps_coupling_desc_next_id, lhdr_keeps_coupling_desc_next_id. exact (step_keeps_coupling_desc_next_id b).
  - rewrite lscan_iter_keeps_coupling_desc_base_table, lhdr_keeps_coupling_desc_base_table. exact (step_keeps_coupling_desc_base_table b).
  - rewrite lscan_iter_keeps_coupling_desc_count_table, lhdr_keeps_coupling_desc_count_table. exact (step_keeps_coupling_desc_count_table b).
  - rewrite lscan_iter_keeps_coupling_pair_next_id, lhdr_keeps_coupling_pair_next_id. exact (step_keeps_coupling_pair_next_id b).
  - rewrite lscan_iter_keeps_coupling_pair_valid_table, lhdr_keeps_coupling_pair_valid_table. exact (step_keeps_coupling_pair_valid_table b).
  - rewrite lscan_iter_keeps_coupling_desc_label_table, lhdr_keeps_coupling_desc_label_table. exact (step_lassert_sat_coupling_desc_label_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - rewrite lscan_iter_keeps_coupling_desc_label_len_table, lhdr_keeps_coupling_desc_label_len_table. exact (step_lassert_sat_coupling_desc_label_len_table a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

(** The 8 remaining [RetireMaster.admitted] constructors that actually write
    the morph or coupling tables: MORPH_ID/MORPH_DELETE (legacy and
    extended) allocate/clear a morph slot via [hwb_table_invariants_alloc_morph]/
    [hwb_table_invariants_frame_valid_subset] above; MORPH_EXT/COMPOSE_EXT
    and their fault branches are further below. *)

Lemma preserved_morph_id : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = morph_id_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  wordToNat (hw_morph_next_id b) < 16 ->
  hwb_table_invariants b ->
  Retire b (instr_morph_id (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hlt Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_morph_id_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_morph_id_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_morph_id_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  pose proof (morph_room_of_lt b Hlt) as Hroom.
  pose proof (step_morph_id_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as F_mv.
  pose proof (step_morph_id_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as F_mc.
  pose proof (step_morph_id_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as F_mi.
  pose proof (step_morph_id_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as F_mn.
  pose proof (step_morph_id_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as F_lt.
  pose proof (step_morph_id_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as F_ll.
  rewrite Hroom in F_mv, F_mc, F_mi, F_mn.
  destruct (hw_module_present b (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) eqn:Hpres.
  - eapply (hwb_table_invariants_alloc_morph b _ (split1 4 1 (hw_morph_next_id b))).
    + apply wordToNat_trunc4_5_small. exact Hlt.
    + exact Hlt.
    + exact F_mv.
    + exact F_mc.
    + exact F_mi.
    + exact F_mn.
    + exact (step_keeps_coupling_desc_valid_table b).
    + exact (step_keeps_coupling_desc_next_id b).
    + exact (step_keeps_coupling_desc_base_table b).
    + exact (step_keeps_coupling_desc_count_table b).
    + exact (step_keeps_coupling_pair_next_id b).
    + exact (step_keeps_coupling_pair_valid_table b).
    + exact F_lt.
    + exact F_ll.
    + exact Hinv.
  - eapply hwb_table_invariants_frame.
    + exact F_mv.
    + exact F_mn.
    + exact F_mc.
    + exact F_mi.
    + exact (step_keeps_coupling_desc_valid_table b).
    + exact (step_keeps_coupling_desc_next_id b).
    + exact (step_keeps_coupling_desc_base_table b).
    + exact (step_keeps_coupling_desc_count_table b).
    + exact (step_keeps_coupling_pair_next_id b).
    + exact (step_keeps_coupling_pair_valid_table b).
    + exact F_lt.
    + exact F_ll.
    + exact Hinv.
Qed.

Lemma preserved_morph_id_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB) (d : HWB),
  step_fetched b = morph_id_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false ->
  wordToNat (hw_morph_next_id b) < 16 ->
  hwb_table_invariants b ->
  Retire b (instr_morph_id (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b d Hf Hb Hlt Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_morph_id_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
    - exact (step_morph_id_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
    - exact (step_morph_id_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  pose proof (morph_room_of_lt b Hlt) as Hroom.
  pose proof (step_morph_id_ext_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mv.
  pose proof (step_morph_id_ext_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc.
  pose proof (step_morph_id_ext_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mi.
  pose proof (step_morph_id_ext_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mn.
  pose proof (step_morph_id_ext_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_lt.
  pose proof (step_morph_id_ext_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_ll.
  rewrite Hroom in F_mv, F_mc, F_mi, F_mn.
  destruct (hw_module_present b (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) eqn:Hpres.
  - eapply (hwb_table_invariants_alloc_morph b _ (split1 4 1 (hw_morph_next_id b))).
    + apply wordToNat_trunc4_5_small. exact Hlt.
    + exact Hlt.
    + exact F_mv.
    + exact F_mc.
    + exact F_mi.
    + exact F_mn.
    + exact (step_keeps_coupling_desc_valid_table b).
    + exact (step_keeps_coupling_desc_next_id b).
    + exact (step_keeps_coupling_desc_base_table b).
    + exact (step_keeps_coupling_desc_count_table b).
    + exact (step_keeps_coupling_pair_next_id b).
    + exact (step_keeps_coupling_pair_valid_table b).
    + exact F_lt.
    + exact F_ll.
    + exact Hinv.
  - eapply hwb_table_invariants_frame.
    + exact F_mv.
    + exact F_mn.
    + exact F_mc.
    + exact F_mi.
    + exact (step_keeps_coupling_desc_valid_table b).
    + exact (step_keeps_coupling_desc_next_id b).
    + exact (step_keeps_coupling_desc_base_table b).
    + exact (step_keeps_coupling_desc_count_table b).
    + exact (step_keeps_coupling_pair_next_id b).
    + exact (step_keeps_coupling_pair_valid_table b).
    + exact F_lt.
    + exact F_ll.
    + exact Hinv.
Qed.

Lemma preserved_morph_delete : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB) (d : HWB),
  step_fetched b = morph_delete_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_morph_delete (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_morph_delete_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_morph_delete_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
    - exact (step_morph_delete_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  pose proof (step_morph_delete_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb) as F_mv.
  eapply hwb_table_invariants_frame_valid_subset.
  - intros i Hi. rewrite F_mv in Hi. destruct (hw_morph_live b (bits4 a0 a1 a2 a3)) eqn:Hlive.
    + destruct (weq i (bits4 a0 a1 a2 a3)) as [E|N]; [discriminate Hi | exact Hi].
    + exact Hi.
  - exact (step_morph_delete_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_delete_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_delete_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_morph_delete_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact (step_morph_delete_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hf Hb).
  - exact Hinv.
Qed.

Lemma preserved_morph_delete_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB) (d : HWB),
  step_fetched b = morph_delete_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false ->
  hwb_table_invariants b ->
  Retire b (instr_morph_delete (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b d Hf Hb Hinv HR.
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle.
    - exact (step_morph_delete_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
    - exact (step_morph_delete_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
    - exact (step_morph_delete_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb). }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  pose proof (step_morph_delete_ext_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mv.
  eapply hwb_table_invariants_frame_valid_subset.
  - intros i Hi. rewrite F_mv in Hi. destruct (hw_morph_live b (bits4 a0 a1 a2 a3)) eqn:Hlive.
    + destruct (weq i (bits4 a0 a1 a2 a3)) as [E|N]; [discriminate Hi | exact Hi].
    + exact Hi.
  - exact (step_morph_delete_ext_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_delete_ext_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_delete_ext_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - exact (step_morph_delete_ext_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact (step_morph_delete_ext_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb).
  - exact Hinv.
Qed.

(** MORPH_EXT: the harder remaining case, where [step_next] itself
    provisionally allocates the new morph slot [s] pointing at the not-yet-
    committed coupling descriptor [cd] (both at the boundary's own
    allocation pointers), and the [morph_fsm_final] tail (already scheduled
    by [morph_ext_runs]) commits [cd]'s base/count/valid fields and the
    underlying pair table via [CouplingFsmRun.morph_fsm_run]. Both stages
    are needed together: no intermediate boundary mid-FSM is observed. *)

Lemma wordToNat_natToWord5_small : forall n, n <= 16 -> wordToNat (natToWord 5 n) = n.
Proof. intros n H. apply wordToNat_natToWord_idempotent'. cbn. lia. Qed.

Lemma preserved_morph_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB) count (d : HWB),
  step_fetched b = morph_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false -> hw_live b ->
  wordToNat (hw_morph_next_id b) < 16 -> wordToNat (hw_coupling_desc_next_id b) < 16 ->
  wordToNat (hw_ptTable b (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) <> 0 ->
  wordToNat (hw_ptTable b (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) <> 0 ->
  hw_mem b (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) = natToWord 32 count ->
  count + wordToNat (hw_coupling_pair_next_id b) <= 16 -> wordToNat (hw_coupling_pair_next_id b) < 16 ->
  2 * count + wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) <= 127 ->
  hwb_table_invariants b ->
  Retire b (instr_morph (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) (wordToNat (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b count d
    Hf Hb Hlive Hroom Hdesc Hsrc Hdst Hcount Hfit HP16 Hbase Hinv HR.
  pose proof (step_morph_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_lassert_phase.
  pose proof (step_morph_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_chsh_phase.
  pose proof (step_morph_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_phase.
  pose proof (step_morph_ext_mc_mem_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_mem_base.
  pose proof (step_morph_ext_mc_write_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_base.
  pose proof (step_morph_ext_mc_write_ptr a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_write_ptr.
  pose proof (step_morph_ext_mem a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mem.
  pose proof (step_morph_ext_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_valid_table.
  pose proof (step_morph_ext_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_coupling_desc_table.
  pose proof (step_morph_ext_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_identity_table.
  pose proof (step_morph_ext_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_next_id.
  pose proof (step_morph_ext_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_coupling_desc_label_table.
  pose proof (step_morph_ext_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_coupling_desc_label_len_table.
  rewrite (morph_room_of_lt b Hroom), (desc_room_of_lt b Hdesc), !module_present_eqb,
    (proj2 (Nat.eqb_neq _ _) Hsrc), (proj2 (Nat.eqb_neq _ _) Hdst) in *.
  cbv beta iota delta [negb] in F_lassert_phase, F_chsh_phase, F_mc_phase, F_mc_mem_base, F_mc_write_base,
    F_mc_write_ptr, F_mem, F_morph_valid_table, F_morph_coupling_desc_table, F_morph_identity_table,
    F_morph_next_id, F_coupling_desc_label_table, F_coupling_desc_label_len_table.
  set (P := wordToNat (hw_coupling_pair_next_id b)) in *.
  assert (HPb : hw_coupling_pair_next_id b = natToWord 5 P) by (unfold P; symmetry; apply natToWord_wordToNat).
  assert (HP : hw_coupling_pair_next_id (step_next b) = natToWord 5 P)
    by (rewrite step_keeps_coupling_pair_next_id; exact HPb).
  destruct (morph_fsm_run (step_next b) (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) P count
    ltac:(rewrite F_mc_phase; reflexivity) F_mc_mem_base HP
    ltac:(rewrite F_mc_write_base; exact HP) ltac:(rewrite F_mc_write_ptr; exact HP)
    ltac:(rewrite F_mem, split1_zext7; exact Hcount) ltac:(lia) Hbase)
    as [l [out [src' [dst' [_ [Hout [Hslice [Hpre [Rs [Rd [Rv [Rn [Rph [Rwb [RdB [RdC [RdV [RdN [Rerr Rec]]]]]]]]]]]]]]]]]]].
  rewrite step_keeps_coupling_pair_valid_table in Rv.
  rewrite step_keeps_coupling_desc_base_table, step_keeps_coupling_desc_next_id in RdB.
  rewrite step_keeps_coupling_desc_count_table, step_keeps_coupling_desc_next_id in RdC.
  rewrite step_keeps_coupling_desc_valid_table, step_keeps_coupling_desc_next_id in RdV.
  rewrite step_keeps_coupling_desc_next_id in RdN.
  set (s := split1 4 1 (hw_morph_next_id b)) in *.
  set (cd := split1 4 1 (hw_coupling_desc_next_id b)) in *.
  assert (Hidle : hw_idle (morph_fsm_final count (step_next b))).
  { unfold hw_idle. split; [|split].
    - rewrite morph_fsm_keeps_lassert_phase. exact F_lassert_phase.
    - rewrite morph_fsm_keeps_chsh_phase. exact F_chsh_phase.
    - exact Rph. }
  assert (Hd : d = morph_fsm_final count (step_next b)).
  { destruct (morph_ext_runs a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b count Hf Hb Hlive Hroom Hdesc Hsrc Hdst Hcount Hfit Hbase) as [k Rk].
    destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ Rk Hidle)). }
  subst d.
  destruct Hinv as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
  assert (Hsn : wordToNat s = wordToNat (hw_morph_next_id b)) by (apply wordToNat_trunc4_5_small; exact Hroom).
  assert (Hcdn : wordToNat cd = wordToNat (hw_coupling_desc_next_id b)) by (apply wordToNat_trunc4_5_small; exact Hdesc).
  clearbody s cd.
  assert (Hmnd : wordToNat (hw_morph_next_id (morph_fsm_final count (step_next b))) = wordToNat (hw_morph_next_id b) + 1).
  { rewrite morph_fsm_keeps_morph_next_id, F_morph_next_id. apply wordToNat_wplus_bounded. cbn. lia. }
  assert (Hdnd : wordToNat (hw_coupling_desc_next_id (morph_fsm_final count (step_next b))) = wordToNat (hw_coupling_desc_next_id b) + 1).
  { rewrite RdN. apply wordToNat_wplus_bounded. cbn. lia. }
  assert (Hcdneq0 : cd <> natToWord CouplingDescIdxSz 0).
  { intro E. assert (Hcdn0 : wordToNat cd = 0) by (rewrite E; reflexivity).
    rewrite Hcdn in Hcdn0. unfold hwb_coupling_desc_next_id_ge1 in H10. lia. }
  assert (HcdV : hw_coupling_desc_valid_table (morph_fsm_final count (step_next b)) cd = true).
  { rewrite RdV. unfold put_vector. destruct (weq cd cd) as [_|Hne]; [reflexivity|exfalso; apply Hne; reflexivity]. }
  assert (HcdOk : hw_coupling_ref_ok (morph_fsm_final count (step_next b)) cd = true).
  { apply coupling_ref_ok_of_lt.
    - change (@wordToNat DescIdxSz cd) with (wordToNat cd). rewrite Hdnd, Hcdn. lia.
    - exact HcdV. }
  assert (Hgrow : forall x, hw_coupling_ref_ok b x = true -> hw_coupling_ref_ok (morph_fsm_final count (step_next b)) x = true).
  { intros x Hx. unfold hw_coupling_ref_ok in Hx |- *.
    destruct (weq x (natToWord DescIdxSz 0)) as [E0|N0]; [exact Hx|].
    destruct (wlt_dec (zext x 1) (hw_coupling_desc_next_id b)) as [Hlt1|Hnlt1]; [|discriminate Hx].
    apply wlt_lt in Hlt1. rewrite wordToNat_zext in Hlt1.
    destruct (wlt_dec (zext x 1) (hw_coupling_desc_next_id (morph_fsm_final count (step_next b)))) as [_|Hnl2].
    - rewrite RdV. unfold put_vector. destruct (@weq 4 x cd) as [Exc|Nxc].
      + exfalso. subst x. change (@wordToNat DescIdxSz cd) with (wordToNat cd) in Hlt1.
        rewrite Hcdn in Hlt1. exact (Nat.lt_irrefl _ Hlt1).
      + exact Hx.
    - exfalso. apply Hnl2. apply lt_wlt. rewrite wordToNat_zext.
      assert (Hgoal : wordToNat x < wordToNat (hw_coupling_desc_next_id (morph_fsm_final count (step_next b)))).
      { rewrite Hdnd, Nat.add_1_r. apply Nat.lt_lt_succ_r. exact Hlt1. }
      exact Hgoal. }
  unfold hwb_table_invariants.
  split.
  { unfold hwb_morph_valid_below_next. intros i Hi.
    rewrite morph_fsm_keeps_morph_valid_table, F_morph_valid_table in Hi.
    destruct (weq i s) as [E|N].
    - subst i. rewrite Hmnd.
      change (@wordToNat MorphTableIdxSz s) with (wordToNat s). rewrite Hsn. lia.
    - rewrite Hmnd. pose proof (H1 i Hi). lia. }
  split.
  { unfold hwb_morph_coupling_refs_ok. intros i Hi.
    rewrite morph_fsm_keeps_morph_valid_table, F_morph_valid_table in Hi.
    rewrite morph_fsm_keeps_morph_coupling_desc_table, F_morph_coupling_desc_table.
    destruct (weq i s) as [E|N].
    - exact HcdOk.
    - apply Hgrow. exact (H2 i Hi). }
  split.
  { unfold hwb_coupling_desc_zero_invalid. rewrite RdV. unfold put_vector.
    destruct (@weq 4 (natToWord CouplingDescIdxSz 0) cd) as [E|_].
    - exfalso. apply Hcdneq0. symmetry. exact E.
    - exact H3. }
  split.
  { unfold hwb_coupling_desc_valid_below_next. intros i Hi. rewrite RdV in Hi. unfold put_vector in Hi.
    destruct (@weq 4 i cd) as [E|N].
    - subst i. change (@wordToNat CouplingDescIdxSz cd) with (wordToNat cd).
      rewrite Hdnd, Hcdn. lia.
    - rewrite Hdnd. pose proof (H4 i Hi). lia. }
  split.
  { unfold hwb_desc_pairs_below_next. intros d0 Hd0.
    rewrite RdV in Hd0. unfold put_vector in Hd0.
    rewrite RdB, RdC, Rn. unfold put_vector.
    destruct (@weq 4 d0 cd) as [E|N].
    - change (@wordToNat CouplingPairIdxSz (split1 4 1 (natToWord 5 P)) +
               @wordToNat CouplingPairCountSz (wminus (natToWord 5 out) (natToWord 5 P)) <=
               @wordToNat DescTableNextIdSz (natToWord 5 out))
        with (wordToNat (split1 4 1 (natToWord 5 P)) + wordToNat (wminus (natToWord 5 out) (natToWord 5 P))
              <= wordToNat (natToWord 5 out)).
      rewrite (wordToNat_natToWord5_small out ltac:(lia)).
      rewrite (wordToNat_trunc4_5_small (natToWord 5 P)
        ltac:(change (@wordToNat MorphTableNextIdSz (natToWord 5 P)) with (wordToNat (natToWord 5 P));
              rewrite (wordToNat_natToWord5_small P ltac:(lia)); lia)).
      change (@wordToNat MorphTableNextIdSz (natToWord 5 P)) with (wordToNat (natToWord 5 P)).
      rewrite (wordToNat_natToWord5_small P ltac:(lia)).
      rewrite (wordToNat_wminus_le 5 (natToWord 5 out) (natToWord 5 P)
        ltac:(rewrite (wordToNat_natToWord5_small out ltac:(lia)), (wordToNat_natToWord5_small P ltac:(lia)); lia)).
      rewrite (wordToNat_natToWord5_small out ltac:(lia)), (wordToNat_natToWord5_small P ltac:(lia)). lia.
    - change (@wordToNat CouplingPairIdxSz (hw_coupling_desc_base_table b d0) +
               @wordToNat CouplingPairCountSz (hw_coupling_desc_count_table b d0) <=
               @wordToNat DescTableNextIdSz (natToWord 5 out))
        with (wordToNat (hw_coupling_desc_base_table b d0) + wordToNat (hw_coupling_desc_count_table b d0)
              <= wordToNat (natToWord 5 out)).
      rewrite (wordToNat_natToWord5_small out ltac:(lia)).
      pose proof (H5 d0 Hd0) as Hb5.
      rewrite HPb in Hb5.
      change (@wordToNat DescTableNextIdSz (natToWord 5 P)) with (wordToNat (natToWord 5 P)) in Hb5.
      rewrite (wordToNat_natToWord5_small P ltac:(lia)) in Hb5. lia. }
  split.
  { unfold hwb_pairs_valid_below_next. intros k Hk. rewrite Rn in Hk. rewrite Rv.
    change (@wordToNat DescTableNextIdSz (natToWord 5 out)) with (wordToNat (natToWord 5 out)) in Hk.
    rewrite (wordToNat_natToWord5_small out ltac:(lia)) in Hk.
    change (@wordToNat CouplingPairIdxSz k) with (@wordToNat 4 k) in Hk.
    rewrite <- (@natToWord_wordToNat 4 k).
    rewrite (loaded_valid_at count P (hw_coupling_pair_valid_table b) (@wordToNat 4 k) ltac:(lia)
      ltac:(pose proof (@wordToNat_lt_pow2_small 4 k) as Hk4; cbn in Hk4; lia)).
    destruct (Nat.leb_spec P (@wordToNat 4 k)) as [HPk|HPk].
    - rewrite (proj2 (Nat.ltb_lt (@wordToNat 4 k) (P + count))) by lia. reflexivity.
    - cbn [andb].
      rewrite (@natToWord_wordToNat 4 k). apply (H6 k). rewrite HPb.
      change (@wordToNat DescTableNextIdSz (natToWord 5 P)) with (wordToNat (natToWord 5 P)).
      rewrite (wordToNat_natToWord5_small P ltac:(lia)).
      change (@wordToNat 4 k) with (@wordToNat CouplingPairIdxSz k) in HPk. exact HPk. }
  split.
  { unfold hwb_desc_zero_empty. split.
    - rewrite RdB. unfold put_vector. destruct (@weq 4 (natToWord CouplingDescIdxSz 0) cd) as [E|_].
      + exfalso. apply Hcdneq0. symmetry. exact E.
      + exact (proj1 H7).
    - rewrite RdC. unfold put_vector. destruct (@weq 4 (natToWord CouplingDescIdxSz 0) cd) as [E|_].
      + exfalso. apply Hcdneq0. symmetry. exact E.
      + exact (proj2 H7). }
  split.
  { unfold hwb_identity_desc_zero. intros m Hv Hi.
    rewrite morph_fsm_keeps_morph_valid_table, F_morph_valid_table in Hv.
    rewrite morph_fsm_keeps_morph_identity_table, F_morph_identity_table in Hi.
    rewrite morph_fsm_keeps_morph_coupling_desc_table, F_morph_coupling_desc_table.
    destruct (weq m s) as [E|N].
    - subst m. discriminate Hi.
    - exact (H8 m Hv Hi). }
  split.
  { unfold hwb_labels_represented. intros d0 Hd0.
    rewrite RdV in Hd0. unfold put_vector in Hd0.
    rewrite morph_fsm_keeps_coupling_desc_label_table, morph_fsm_keeps_coupling_desc_label_len_table,
      F_coupling_desc_label_table, F_coupling_desc_label_len_table. cbn beta.
    destruct (@weq 4 d0 cd) as [E|N].
    - destruct (@weq CouplingDescIdxSz d0 cd) as [E2|N2]; [|exfalso; apply N2; exact E].
      split; vm_compute; lia.
    - destruct (@weq CouplingDescIdxSz d0 cd) as [E2|N2]; [exfalso; apply N; exact E2|].
      exact (H9 d0 Hd0). }
  { unfold hwb_coupling_desc_next_id_ge1. rewrite Hdnd. lia. }
Qed.

(** MORPH_EXT_FAULT and COMPOSE_EXT_FAULT: [step_next] alone (no FSM), and
    since one of the two module/type guards fails, every field stays at
    its "else" (frame) value regardless of the value of the OTHER guard --
    a fact that does not depend on which specific guard failed. *)
Lemma mux2_frame : forall T (m1 m2 : bool) (X Y : T),
  m1 = false \/ m2 = false -> (if m1 then (if m2 then X else Y) else Y) = Y.
Proof.
  intros T m1 m2 X Y [H|H]; rewrite H; [reflexivity|destruct m1; reflexivity].
Qed.

Lemma module_absent_of_zero : forall b m, wordToNat (hw_ptTable b m) = 0 -> hw_module_present b m = false.
Proof. intros b m H. rewrite module_present_eqb, H. reflexivity. Qed.

Lemma preserved_morph_ext_fault : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB) (d : HWB),
  step_fetched b = morph_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false ->
  wordToNat (hw_morph_next_id b) < 16 -> wordToNat (hw_coupling_desc_next_id b) < 16 ->
  wordToNat (hw_ptTable b (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) = 0 \/
    wordToNat (hw_ptTable b (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) = 0 ->
  hwb_table_invariants b ->
  Retire b (instr_morph (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7))) (wordToNat (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) (wordToNat (split1 7 19 (split2 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b d
    Hf Hb Hroom Hdesc Hor Hinv HR.
  pose proof (morph_room_of_lt b Hroom) as Hroom'.
  pose proof (desc_room_of_lt b Hdesc) as Hdesc'.
  assert (Hpres : hw_module_present b (split1 6 2 (bits8 b0 b1 b2 b3 b4 b5 b6 b7)) = false \/
                  hw_module_present b (split1 6 26 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) = false).
  { destruct Hor as [Hor|Hor]; [left|right]; apply module_absent_of_zero; exact Hor. }
  pose proof (step_morph_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_lassert_phase.
  pose proof (step_morph_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_chsh_phase.
  pose proof (step_morph_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc_phase.
  rewrite Hroom', Hdesc' in F_mc_phase.
  assert (Hidle : hw_idle (step_next b)).
  { unfold hw_idle. split; [|split].
    - exact F_lassert_phase.
    - exact F_chsh_phase.
    - rewrite F_mc_phase. apply mux2_frame. exact Hpres. }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  pose proof (step_morph_ext_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_valid_table.
  pose proof (step_morph_ext_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_next_id.
  pose proof (step_morph_ext_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_coupling_desc_table.
  pose proof (step_morph_ext_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_morph_identity_table.
  pose proof (step_morph_ext_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_coupling_desc_label_table.
  pose proof (step_morph_ext_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_coupling_desc_label_len_table.
  rewrite Hroom', Hdesc' in F_morph_valid_table, F_morph_next_id, F_morph_coupling_desc_table,
    F_morph_identity_table, F_coupling_desc_label_table, F_coupling_desc_label_len_table.
  eapply hwb_table_invariants_frame.
  - rewrite F_morph_valid_table. apply mux2_frame. exact Hpres.
  - rewrite F_morph_next_id. apply mux2_frame. exact Hpres.
  - rewrite F_morph_coupling_desc_table. apply mux2_frame. exact Hpres.
  - rewrite F_morph_identity_table. apply mux2_frame. exact Hpres.
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - rewrite F_coupling_desc_label_table. apply mux2_frame. exact Hpres.
  - rewrite F_coupling_desc_label_len_table. apply mux2_frame. exact Hpres.
  - exact Hinv.
Qed.

(** COMPOSE at its extended encoding. *)

Lemma mux3_frame : forall T (g1 g2 g3 : bool) (X Y : T),
  g1 = false \/ g2 = false \/ g3 = false ->
  (if g1 then (if g2 then (if g3 then X else Y) else Y) else Y) = Y.
Proof.
  intros T g1 g2 g3 X Y [H|[H|H]]; subst.
  - reflexivity.
  - destruct g1; reflexivity.
  - destruct g1; destruct g2; reflexivity.
Qed.

(** The COMPOSE step's morph-phase equation collapses to 0 whenever one of
    the live/live/type-match guards fails. *)
Lemma compose_mc_zero : forall (v1 v2 m dr i1 i2 : bool),
  v1 = false \/ v2 = false \/ m = false ->
  (if v1 then (if v2 then (if m then
      (if dr then (if i1 then natToWord 4 4 else if i2 then natToWord 4 4 else natToWord 4 7)
       else natToWord 4 0) else natToWord 4 0) else natToWord 4 0) else natToWord 4 0)
  = natToWord 4 0.
Proof.
  intros v1 v2 m dr i1 i2 [H|[H|H]]; subst.
  - reflexivity.
  - destruct v1; reflexivity.
  - destruct v1; destruct v2; reflexivity.
Qed.

(** The composed label of two sides is a represented label: its atom count
    stays within [1, 32] and its mask within the count. *)
Lemma compose_label_represented : forall b (d1 d2 : word CouplingDescIdxSz),
  hwb_labels_represented b ->
  wordToNat (hw_label_len b d1) + wordToNat (hw_label_len b d2) <= 32 ->
  1 <= wordToNat (wplus (hw_label_len b d1) (hw_label_len b d2)) <= 32 /\
  wordToNat (wplus (hw_label_word b d1) (wlshift (hw_label_word b d2) (wordToNat (hw_label_len b d1))))
    < 2 ^ wordToNat (wplus (hw_label_len b d1) (hw_label_len b d2)).
Proof.
  intros b d1 d2 H Hsum.
  destruct (label_represented_at b d1 H) as [[A1 B1] C1].
  destruct (label_represented_at b d2 H) as [[A2 B2] C2].
  assert (Hlen : wordToNat (wplus (hw_label_len b d1) (hw_label_len b d2)) =
    wordToNat (hw_label_len b d1) + wordToNat (hw_label_len b d2)).
  { apply wordToNat_wplus_bounded. change (pow2 6) with 64. lia. }
  assert (Hshift : wordToNat (wlshift (hw_label_word b d2) (wordToNat (hw_label_len b d1))) =
    wordToNat (hw_label_word b d2) * 2 ^ wordToNat (hw_label_len b d1)).
  { rewrite wordToNat_wlshift. rewrite Nat.mod_small; [reflexivity|].
    eapply Nat.lt_le_trans; [exact C2|].
    assert (WordSz = 32) by reflexivity. apply Nat.pow_le_mono_r; lia. }
  assert (Hbd : wordToNat (hw_label_word b d1) +
      wordToNat (hw_label_word b d2) * 2 ^ wordToNat (hw_label_len b d1)
      < 2 ^ (wordToNat (hw_label_len b d1) + wordToNat (hw_label_len b d2))).
  { assert (M2 : wordToNat (hw_label_word b d2) + 1 <= 2 ^ wordToNat (hw_label_len b d2)) by lia.
    assert (Step1 : wordToNat (hw_label_word b d1) +
        wordToNat (hw_label_word b d2) * 2 ^ wordToNat (hw_label_len b d1)
        < 2 ^ wordToNat (hw_label_len b d1) +
        wordToNat (hw_label_word b d2) * 2 ^ wordToNat (hw_label_len b d1))
      by (apply Nat.add_lt_mono_r; exact C1).
    assert (Step2 : (wordToNat (hw_label_word b d2) + 1) * 2 ^ wordToNat (hw_label_len b d1)
        = 2 ^ wordToNat (hw_label_len b d1) +
          wordToNat (hw_label_word b d2) * 2 ^ wordToNat (hw_label_len b d1))
      by (rewrite Nat.mul_add_distr_r, Nat.mul_1_l, Nat.add_comm; reflexivity).
    assert (Step3 : (wordToNat (hw_label_word b d2) + 1) * 2 ^ wordToNat (hw_label_len b d1)
        <= 2 ^ wordToNat (hw_label_len b d2) * 2 ^ wordToNat (hw_label_len b d1))
      by (apply Nat.mul_le_mono_r; exact M2).
    assert (Step4 : 2 ^ wordToNat (hw_label_len b d2) * 2 ^ wordToNat (hw_label_len b d1)
        = 2 ^ (wordToNat (hw_label_len b d1) + wordToNat (hw_label_len b d2)))
      by (rewrite <- Nat.pow_add_r, Nat.add_comm; reflexivity).
    assert (Hle : 2 ^ wordToNat (hw_label_len b d1) +
        wordToNat (hw_label_word b d2) * 2 ^ wordToNat (hw_label_len b d1)
        <= 2 ^ (wordToNat (hw_label_len b d1) + wordToNat (hw_label_len b d2)))
      by (rewrite <- Step2, <- Step4; exact Step3).
    lia. }
  split.
  { rewrite Hlen. lia. }
  rewrite Hlen.
  assert (Hwp : wordToNat (wplus (hw_label_word b d1)
      (wlshift (hw_label_word b d2) (wordToNat (hw_label_len b d1)))) =
    wordToNat (hw_label_word b d1) +
    wordToNat (wlshift (hw_label_word b d2) (wordToNat (hw_label_len b d1)))).
  { apply wordToNat_wplus_bounded. rewrite Hshift.
    eapply Nat.lt_le_trans; [exact Hbd|].
    unfold pow2. apply Nat.pow_le_mono_r; [vm_compute; discriminate|exact Hsum]. }
  rewrite Hwp, Hshift. exact Hbd.
Qed.

Lemma preserved_compose_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB) (d : HWB),
  step_fetched b = compose_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false -> hw_live b ->
  wordToNat (hw_pc b) + 1 < pow2 WordSz ->
  wordToNat (hw_mu b) + wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7) < pow2 WordSz ->
  wordToNat (hw_morph_next_id b) < 16 -> wordToNat (hw_coupling_desc_next_id b) < 16 ->
  wordToNat (hw_coupling_pair_next_id b) < 16 ->
  hwb_morph_valid_below_next b -> hwb_morph_coupling_refs_ok b -> hwb_coupling_desc_zero_invalid b ->
  hwb_desc_zero_empty b -> hwb_desc_pairs_below_next b -> hwb_pairs_valid_below_next b ->
  hwb_identity_desc_zero b -> hwb_labels_represented b ->
  hw_morph_valid_table b (bits4 b0 b1 b2 b3) = true ->
  hw_morph_valid_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) = true ->
  hw_morph_dst_table b (bits4 b0 b1 b2 b3) = hw_morph_src_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) ->
  wordToNat (hw_label_len b (hw_morph_coupling_desc_table b (bits4 b0 b1 b2 b3))) + wordToNat (hw_label_len b (hw_morph_coupling_desc_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) <= 32 ->
  wordToNat (hw_coupling_pair_next_id b) + List.length (compose_pairs b (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) <= 16 ->
  hwb_table_invariants b ->
  Retire b (instr_compose (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b d
    Hf Hb Hlive Hpc Hmu Hroom Hdesc HP16 I1 I2 I3 I7 I5 I6 I8 I9 V1 V2 Hmatch Hlab Hcap Hinv HR.
  destruct Hinv as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
  pose proof (step_compose_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_lp.
  pose proof (step_compose_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_cp.
  pose proof (step_compose_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mp.
  pose proof (step_compose_ext_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mv.
  pose proof (step_compose_ext_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mn.
  pose proof (step_compose_ext_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc.
  pose proof (step_compose_ext_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mi.
  pose proof (step_compose_ext_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_lt.
  pose proof (step_compose_ext_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_ll.
  pose proof (step_compose_ext_mc_i a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_i.
  pose proof (step_compose_ext_mc_j a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_j.
  pose proof (step_compose_ext_mc_write_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wb.
  pose proof (step_compose_ext_mc_write_ptr a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_wp.
  pose proof (step_compose_ext_mc_src1_count a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_c1.
  pose proof (step_compose_ext_mc_src2_count a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_c2.
  pose proof (step_compose_ext_mc_src1_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_b1.
  pose proof (step_compose_ext_mc_src2_base a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_b2.
  rewrite (morph_room_of_lt b Hroom), (desc_room_of_lt b Hdesc),
    (morph_live_valid b (bits4 b0 b1 b2 b3) H1),
    (morph_live_valid b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) H1),
    V1, V2, Hmatch in *.
  destruct (weq (hw_morph_src_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))
                (hw_morph_src_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) as [_|NE]; [|contradiction].
  cbv beta iota in F_lp, F_cp, F_mp, F_mv, F_mn, F_mc, F_mi, F_lt, F_ll, F_i, F_j, F_wb, F_wp, F_c1, F_c2, F_b1, F_b2.
  set (P := wordToNat (hw_coupling_pair_next_id b)) in *.
  assert (HPb : hw_coupling_pair_next_id b = natToWord 5 P) by (unfold P; symmetry; apply natToWord_wordToNat).
  assert (HP : hw_coupling_pair_next_id (step_next b) = natToWord 5 P)
    by (rewrite step_keeps_coupling_pair_next_id; exact HPb).
  pose proof (desc_fits b (bits4 b0 b1 b2 b3) H2 H7 H5 V1) as Fit1.
  pose proof (desc_fits b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) H2 H7 H5 V2) as Fit2.
  fold P in Fit1, Fit2.
  set (D1 := hw_morph_coupling_desc_table b (bits4 b0 b1 b2 b3)) in *.
  set (D2 := hw_morph_coupling_desc_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) in *.
  assert (Hr1 : wordToNat (hw_mc_src1_base (step_next b)) + wordToNat (hw_mc_src1_count (step_next b)) <= P).
  { rewrite F_b1, F_c1. destruct (hw_morph_identity_table b (bits4 b0 b1 b2 b3)); cbn.
    - lia.
    - exact Fit1. }
  assert (Hr2 : wordToNat (hw_mc_src2_base (step_next b)) + wordToNat (hw_mc_src2_count (step_next b)) <= P).
  { rewrite F_b2, F_c2. destruct (hw_morph_identity_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))); cbn.
    - lia.
    - exact Fit2. }
  assert (Hc1 : wordToNat (hw_mc_src1_count (step_next b)) <= 16).
  { rewrite F_c1. destruct (hw_morph_identity_table b (bits4 b0 b1 b2 b3)); cbn; lia. }
  assert (Hc2 : wordToNat (hw_mc_src2_count (step_next b)) <= 16).
  { rewrite F_c2. destruct (hw_morph_identity_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))); cbn; lia. }
  assert (Raw : compose_raw (step_next b) = compose_pairs b (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))
    by exact (compose_raw_step b (step_next b) (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) H8 H7 V2
      (step_keeps_coupling_pair_src_table b) (step_keeps_coupling_pair_dst_table b)
      F_mp F_c1 F_c2 F_b1 F_b2).
  destruct (compose_fsm_run (step_next b) P
    ltac:(rewrite F_mp; destruct (hw_morph_identity_table b (bits4 b0 b1 b2 b3)), (hw_morph_identity_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))); auto)
    F_i F_j ltac:(rewrite F_wb; exact HPb) ltac:(rewrite F_wp; exact HPb)
    Hc1 Hc2 Hr1 Hr2
    ltac:(rewrite Raw; exact Hcap))
    as [l [out [src' [dst' [_ [Hout [Hslice [Hpre [Rs [Rd [Rv [Rn [Rph [RdB [RdC [RdV [RdN [Rerr Rec]]]]]]]]]]]]]]]]]].
  rewrite Raw in Hout, Rv.
  rewrite step_keeps_coupling_pair_valid_table in Rv.
  rewrite step_keeps_coupling_desc_base_table, step_keeps_coupling_desc_next_id in RdB.
  rewrite step_keeps_coupling_desc_count_table, step_keeps_coupling_desc_next_id in RdC.
  rewrite step_keeps_coupling_desc_valid_table, step_keeps_coupling_desc_next_id in RdV.
  rewrite step_keeps_coupling_desc_next_id in RdN.
  set (s := split1 4 1 (hw_morph_next_id b)) in *.
  set (cd := split1 4 1 (hw_coupling_desc_next_id b)) in *.
  assert (Hidle : hw_idle (compose_fsm_final (step_next b))).
  { unfold hw_idle. split; [|split].
    - rewrite compose_fsm_keeps_lassert_phase. exact F_lp.
    - rewrite compose_fsm_keeps_chsh_phase. exact F_cp.
    - exact Rph. }
  assert (Hd : d = compose_fsm_final (step_next b)).
  { destruct (compose_ext_runs a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb Hlive Hpc Hmu Hroom Hdesc HP16 H1 H2 H3 H7 H5 H6 H8 H9 V1 V2 Hmatch Hlab Hcap) as [k Rk].
    destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ Rk Hidle)). }
  subst d.
  assert (Hsn : wordToNat s = wordToNat (hw_morph_next_id b)) by (apply wordToNat_trunc4_5_small; exact Hroom).
  assert (Hcdn : wordToNat cd = wordToNat (hw_coupling_desc_next_id b)) by (apply wordToNat_trunc4_5_small; exact Hdesc).
  clearbody s cd D1 D2.
  assert (Hmnd : wordToNat (hw_morph_next_id (compose_fsm_final (step_next b))) = wordToNat (hw_morph_next_id b) + 1).
  { rewrite compose_fsm_keeps_morph_next_id, F_mn. apply wordToNat_wplus_bounded. cbn. lia. }
  assert (Hdnd : wordToNat (hw_coupling_desc_next_id (compose_fsm_final (step_next b))) = wordToNat (hw_coupling_desc_next_id b) + 1).
  { rewrite RdN. apply wordToNat_wplus_bounded. cbn. lia. }
  assert (Hcdneq0 : cd <> natToWord CouplingDescIdxSz 0).
  { intro E. assert (Hcdn0 : wordToNat cd = 0) by (rewrite E; reflexivity).
    rewrite Hcdn in Hcdn0. unfold hwb_coupling_desc_next_id_ge1 in H10. lia. }
  assert (HcdV : hw_coupling_desc_valid_table (compose_fsm_final (step_next b)) cd = true).
  { rewrite RdV. unfold put_vector. destruct (weq cd cd) as [_|Hne]; [reflexivity|exfalso; apply Hne; reflexivity]. }
  assert (HcdOk : hw_coupling_ref_ok (compose_fsm_final (step_next b)) cd = true).
  { apply coupling_ref_ok_of_lt.
    - change (@wordToNat DescIdxSz cd) with (wordToNat cd). rewrite Hdnd, Hcdn. lia.
    - exact HcdV. }
  assert (Hgrow : forall x, hw_coupling_ref_ok b x = true -> hw_coupling_ref_ok (compose_fsm_final (step_next b)) x = true).
  { intros x Hx. unfold hw_coupling_ref_ok in Hx |- *.
    destruct (weq x (natToWord DescIdxSz 0)) as [E0|N0]; [exact Hx|].
    destruct (wlt_dec (zext x 1) (hw_coupling_desc_next_id b)) as [Hlt1|Hnlt1]; [|discriminate Hx].
    apply wlt_lt in Hlt1. rewrite wordToNat_zext in Hlt1.
    destruct (wlt_dec (zext x 1) (hw_coupling_desc_next_id (compose_fsm_final (step_next b)))) as [_|Hnl2].
    - rewrite RdV. unfold put_vector. destruct (@weq 4 x cd) as [Exc|Nxc].
      + exfalso. subst x. change (@wordToNat DescIdxSz cd) with (wordToNat cd) in Hlt1.
        rewrite Hcdn in Hlt1. exact (Nat.lt_irrefl _ Hlt1).
      + exact Hx.
    - exfalso. apply Hnl2. apply lt_wlt. rewrite wordToNat_zext.
      assert (Hgoal : wordToNat x < wordToNat (hw_coupling_desc_next_id (compose_fsm_final (step_next b)))).
      { rewrite Hdnd, Nat.add_1_r. apply Nat.lt_lt_succ_r. exact Hlt1. }
      exact Hgoal. }
  unfold hwb_table_invariants.
  split.
  { unfold hwb_morph_valid_below_next. intros i Hi.
    rewrite compose_fsm_keeps_morph_valid_table, F_mv in Hi.
    destruct (weq i s) as [E|N].
    - subst i. rewrite Hmnd.
      change (@wordToNat MorphTableIdxSz s) with (wordToNat s). rewrite Hsn. lia.
    - rewrite Hmnd. pose proof (H1 i Hi). lia. }
  split.
  { unfold hwb_morph_coupling_refs_ok. intros i Hi.
    rewrite compose_fsm_keeps_morph_valid_table, F_mv in Hi.
    rewrite compose_fsm_keeps_morph_coupling_desc_table, F_mc.
    destruct (weq i s) as [E|N].
    - exact HcdOk.
    - apply Hgrow. exact (H2 i Hi). }
  split.
  { unfold hwb_coupling_desc_zero_invalid. rewrite RdV. unfold put_vector.
    destruct (@weq 4 (natToWord CouplingDescIdxSz 0) cd) as [E|_].
    - exfalso. apply Hcdneq0. symmetry. exact E.
    - exact H3. }
  split.
  { unfold hwb_coupling_desc_valid_below_next. intros i Hi. rewrite RdV in Hi. unfold put_vector in Hi.
    destruct (@weq 4 i cd) as [E|N].
    - subst i. change (@wordToNat CouplingDescIdxSz cd) with (wordToNat cd).
      rewrite Hdnd, Hcdn. lia.
    - rewrite Hdnd. pose proof (H4 i Hi). lia. }
  split.
  { unfold hwb_desc_pairs_below_next. intros d0 Hd0.
    rewrite RdV in Hd0. unfold put_vector in Hd0.
    rewrite RdB, RdC, Rn. unfold put_vector.
    destruct (@weq 4 d0 cd) as [E|N].
    - change (@wordToNat CouplingPairIdxSz (split1 4 1 (natToWord 5 P)) +
               @wordToNat CouplingPairCountSz (wminus (natToWord 5 out) (natToWord 5 P)) <=
               @wordToNat DescTableNextIdSz (natToWord 5 out))
        with (wordToNat (split1 4 1 (natToWord 5 P)) + wordToNat (wminus (natToWord 5 out) (natToWord 5 P))
              <= wordToNat (natToWord 5 out)).
      rewrite (wordToNat_natToWord5_small out ltac:(lia)).
      rewrite (wordToNat_trunc4_5_small (natToWord 5 P)
        ltac:(change (@wordToNat MorphTableNextIdSz (natToWord 5 P)) with (wordToNat (natToWord 5 P));
              rewrite (wordToNat_natToWord5_small P ltac:(lia)); lia)).
      change (@wordToNat MorphTableNextIdSz (natToWord 5 P)) with (wordToNat (natToWord 5 P)).
      rewrite (wordToNat_natToWord5_small P ltac:(lia)).
      rewrite (wordToNat_wminus_le 5 (natToWord 5 out) (natToWord 5 P)
        ltac:(rewrite (wordToNat_natToWord5_small out ltac:(lia)), (wordToNat_natToWord5_small P ltac:(lia)); lia)).
      rewrite (wordToNat_natToWord5_small out ltac:(lia)), (wordToNat_natToWord5_small P ltac:(lia)). lia.
    - change (@wordToNat CouplingPairIdxSz (hw_coupling_desc_base_table b d0) +
               @wordToNat CouplingPairCountSz (hw_coupling_desc_count_table b d0) <=
               @wordToNat DescTableNextIdSz (natToWord 5 out))
        with (wordToNat (hw_coupling_desc_base_table b d0) + wordToNat (hw_coupling_desc_count_table b d0)
              <= wordToNat (natToWord 5 out)).
      rewrite (wordToNat_natToWord5_small out ltac:(lia)).
      pose proof (H5 d0 Hd0) as Hb5.
      rewrite HPb in Hb5.
      change (@wordToNat DescTableNextIdSz (natToWord 5 P)) with (wordToNat (natToWord 5 P)) in Hb5.
      rewrite (wordToNat_natToWord5_small P ltac:(lia)) in Hb5. lia. }
  split.
  { unfold hwb_pairs_valid_below_next. intros k Hk. rewrite Rn in Hk. rewrite Rv.
    change (@wordToNat DescTableNextIdSz (natToWord 5 out)) with (wordToNat (natToWord 5 out)) in Hk.
    rewrite (wordToNat_natToWord5_small out ltac:(lia)) in Hk.
    change (@wordToNat CouplingPairIdxSz k) with (@wordToNat 4 k) in Hk.
    rewrite <- (@natToWord_wordToNat 4 k).
    assert (Hk4 : @wordToNat 4 k < 16) by (pose proof (@wordToNat_lt_pow2_small 4 k) as H; cbn in H; lia).
    rewrite (loaded_valid_at (List.length (compose_pairs b (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) P (hw_coupling_pair_valid_table b) (@wordToNat 4 k) ltac:(lia) Hk4).
    destruct (Nat.leb_spec P (@wordToNat 4 k)) as [HPk|HPk].
    - assert (Hlt : Nat.ltb (@wordToNat 4 k) (P + List.length (compose_pairs b (bits4 b0 b1 b2 b3) (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt. reflexivity.
    - cbn [andb].
      rewrite (@natToWord_wordToNat 4 k). apply (H6 k). rewrite HPb.
      change (@wordToNat DescTableNextIdSz (natToWord 5 P)) with (wordToNat (natToWord 5 P)).
      rewrite (wordToNat_natToWord5_small P ltac:(lia)).
      change (@wordToNat 4 k) with (@wordToNat CouplingPairIdxSz k) in HPk. exact HPk. }
  split.
  { unfold hwb_desc_zero_empty. split.
    - rewrite RdB. unfold put_vector. destruct (@weq 4 (natToWord CouplingDescIdxSz 0) cd) as [E|_].
      + exfalso. apply Hcdneq0. symmetry. exact E.
      + exact (proj1 H7).
    - rewrite RdC. unfold put_vector. destruct (@weq 4 (natToWord CouplingDescIdxSz 0) cd) as [E|_].
      + exfalso. apply Hcdneq0. symmetry. exact E.
      + exact (proj2 H7). }
  split.
  { unfold hwb_identity_desc_zero. intros m Hv Hi.
    rewrite compose_fsm_keeps_morph_valid_table, F_mv in Hv.
    rewrite compose_fsm_keeps_morph_identity_table, F_mi in Hi.
    rewrite compose_fsm_keeps_morph_coupling_desc_table, F_mc.
    destruct (weq m s) as [E|N].
    - subst m. discriminate Hi.
    - exact (H8 m Hv Hi). }
  split.
  { unfold hwb_labels_represented. intros d0 Hd0.
    rewrite RdV in Hd0. unfold put_vector in Hd0.
    rewrite compose_fsm_keeps_coupling_desc_label_table, compose_fsm_keeps_coupling_desc_label_len_table,
      F_lt, F_ll. cbn beta.
    destruct (@weq 4 d0 cd) as [E|N].
    - destruct (@weq CouplingDescIdxSz d0 cd) as [E2|N2]; [|exfalso; apply N2; exact E].
      exact (compose_label_represented b D1 D2 H9 Hlab).
    - destruct (@weq CouplingDescIdxSz d0 cd) as [E2|N2]; [exfalso; apply N; exact E2|].
      exact (H9 d0 Hd0). }
  { unfold hwb_coupling_desc_next_id_ge1. rewrite Hdnd. lia. }
Qed.

(** COMPOSE_EXT_FAULT: [step_next] alone (no FSM). One of the live/live/type-match
    guards fails, so every field keeps its "else" (frame) value, and the morph
    phase lands on 0 whichever guard that is. *)
Lemma preserved_compose_ext_fault : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB) (d : HWB),
  step_fetched b = compose_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 ->
  hwb_bianchi b = false ->
  wordToNat (hw_morph_next_id b) < 16 ->
  (hw_morph_valid_table b (bits4 b0 b1 b2 b3) = false \/
   hw_morph_valid_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) = false \/
   hw_morph_dst_table b (bits4 b0 b1 b2 b3) <> hw_morph_src_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) ->
  hwb_table_invariants b ->
  Retire b (instr_compose (wordToNat (bits4 a0 a1 a2 a3)) (wordToNat (bits4 b0 b1 b2 b3)) (wordToNat (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31))) (wordToNat (bits8 c0 c1 c2 c3 c4 c5 c6 c7))) d ->
  hwb_table_invariants d.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b d
    Hf Hb Hroom Hfail Hinv HR.
  pose proof Hinv as Hinv0.
  destruct Hinv as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]].
  pose proof (morph_room_of_lt b Hroom) as Hroom'.
  pose proof (step_compose_ext_lassert_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_lp.
  pose proof (step_compose_ext_chsh_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_cp.
  pose proof (step_compose_ext_mc_phase a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mp.
  rewrite Hroom' in F_mp.
  assert (Hpres : hw_morph_live b (bits4 b0 b1 b2 b3) = false \/
      hw_morph_live b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) = false \/
      (if weq (hw_morph_dst_table b (bits4 b0 b1 b2 b3))
              (hw_morph_src_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))
       then true else false) = false).
  { destruct Hfail as [Hf1|[Hf2|Hf3]].
    - left. rewrite (morph_live_valid b (bits4 b0 b1 b2 b3) H1). exact Hf1.
    - right; left. rewrite (morph_live_valid b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)) H1). exact Hf2.
    - right; right. destruct (weq (hw_morph_dst_table b (bits4 b0 b1 b2 b3))
          (hw_morph_src_table b (split1 4 28 (bits32 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31)))) as [E|N]; [exfalso; exact (Hf3 E)|reflexivity]. }
  assert (Hmc0 : hw_mc_phase (step_next b) = natToWord 4 0).
  { rewrite F_mp. apply compose_mc_zero. exact Hpres. }
  assert (Hidle : hw_idle (step_next b)).
  { apply step_idle; [exact F_lp|exact F_cp|exact Hmc0]. }
  assert (Hd : d = step_next b).
  { destruct HR as [_ [[n Hn] [Hdi _]]].
    exact (proj1 (busy_runs_unique _ _ _ Hn Hdi _ _ (busy_done _) Hidle)). }
  subst d.
  pose proof (step_compose_ext_morph_valid_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mv.
  pose proof (step_compose_ext_morph_next_id a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mn.
  pose proof (step_compose_ext_morph_coupling_desc_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mc.
  pose proof (step_compose_ext_morph_identity_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_mi.
  pose proof (step_compose_ext_coupling_desc_label_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_lt.
  pose proof (step_compose_ext_coupling_desc_label_len_table a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hf Hb) as F_ll.
  rewrite Hroom'
    in F_mv, F_mn, F_mc, F_mi, F_lt, F_ll.
  eapply hwb_table_invariants_frame.
  - rewrite F_mv. apply mux3_frame. exact Hpres.
  - rewrite F_mn. apply mux3_frame. exact Hpres.
  - rewrite F_mc. apply mux3_frame. exact Hpres.
  - rewrite F_mi. apply mux3_frame. exact Hpres.
  - exact (step_keeps_coupling_desc_valid_table b).
  - exact (step_keeps_coupling_desc_next_id b).
  - exact (step_keeps_coupling_desc_base_table b).
  - exact (step_keeps_coupling_desc_count_table b).
  - exact (step_keeps_coupling_pair_next_id b).
  - exact (step_keeps_coupling_pair_valid_table b).
  - rewrite F_lt. apply mux3_frame. exact Hpres.
  - rewrite F_ll. apply mux3_frame. exact Hpres.
  - exact Hinv0.
Qed.

(** * The master preservation statement

    All 55 [admitted] constructors are covered: the 47 frame cases and the
    eight table-writing cases above. This is the induction step for C1/C2's
    reachable-state invariants, whose base case is
    [TableInvariants.hwb_table_invariants_reset]. *)
Theorem hwb_table_invariants_preserved : forall b i d,
  hwb_table_invariants b -> admitted b i -> Retire b i d -> hwb_table_invariants d.
Proof.
  intros b i d Hinv Hadm HR.
  destruct Hadm;
    [ eapply preserved_add; eassumption | eapply preserved_sub; eassumption
    | eapply preserved_and; eassumption | eapply preserved_or; eassumption
    | eapply preserved_xor_add; eassumption | eapply preserved_mul; eassumption
    | eapply preserved_xfer; eassumption | eapply preserved_load_imm; eassumption
    | eapply preserved_shl; eassumption | eapply preserved_shr; eassumption
    | eapply preserved_lui; eassumption | eapply preserved_xor_load; eassumption
    | eapply preserved_jump; eassumption | eapply preserved_jnez; eassumption
    | eapply preserved_mdlacc; eassumption | eapply preserved_ljoin; eassumption
    | eapply preserved_certify; eassumption | eapply preserved_read_port; eassumption
    | eapply preserved_emit; eassumption | eapply preserved_reveal; eassumption
    | eapply preserved_xor_swap; eassumption | eapply preserved_tensor_set; eassumption
    | eapply preserved_tensor_get; eassumption | eapply preserved_pdiscover; eassumption
    | eapply preserved_load; eassumption | eapply preserved_store; eassumption
    | eapply preserved_heap_load; eassumption | eapply preserved_heap_store; eassumption
    | eapply preserved_call; eassumption | eapply preserved_ret; eassumption
    | eapply preserved_pnew; eassumption | eapply preserved_psplit; eassumption
    | eapply preserved_pmerge; eassumption | eapply preserved_chsh_trial; eassumption
    | eapply preserved_xor_rank; eassumption | eapply preserved_halt; eassumption
    | eapply preserved_checkpoint; eassumption | eapply preserved_write_port; eassumption
    | eapply preserved_morph_delete; eassumption | eapply preserved_morph_assert; eassumption
    | eapply preserved_morph_get; eassumption | eapply preserved_morph_id; eassumption
    | eapply preserved_morph_delete_ext; eassumption | eapply preserved_morph_id_ext; eassumption
    | eapply preserved_morph_assert_ext; eassumption | eapply preserved_morph_get_ext; eassumption
    | eapply preserved_morph_tensor; eassumption | eapply preserved_morph_tensor_ext; eassumption
    | eapply preserved_morph_ext_fault; eassumption | eapply preserved_compose_ext_fault; eassumption
    | eapply preserved_lassert_unsat; eassumption | eapply preserved_chsh_lassert; eassumption
    | eapply preserved_morph_ext; eassumption | eapply preserved_compose_ext; eassumption
    | eapply preserved_lassert_sat; eassumption ].
Qed.
