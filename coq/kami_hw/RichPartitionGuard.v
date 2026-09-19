(** RichPartitionGuard.v: the partition-overflow guard-falsity lemmas
    generalized from legacy to all six ISA-v2 encodings -- PNEW, PSPLIT,
    PMERGE -- mirroring [LegacyPartitionGuard.v].

    As in the legacy file, [dd_pnew_overflow]/[dd_psplit_overflow]/
    [dd_pmerge_overflow] read no operand byte, only [hw_pt_next_id] and the
    opcode, so the only encoding-dependent step is the opcode decode via
    [RichWordDecode.rw_op_correct]; the capacity arithmetic is unchanged
    from [LegacyPartitionGuard.v]. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Bool Arith Lia.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded
  StepEval StepWordFacts DispatchLets Abstraction ImplementationContract
  StepFields StepFieldsMorph StepFaults StepRefineCommon LegacyWordDecode RichWordDecode.
Local Open Scope nat_scope.

Ltac dd_cbn := cbn [evalExpr evalBinBool evalUniBool evalConstT isEq evalBinBitBool evalUniBit evalZeroExtendTrunc evalBinBit].
Ltac bool_red := cbv beta iota delta [orb andb negb].

Lemma dd_pnew_overflow_false_rich : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (hw_pt_next_id bd) < 64 ->
  dd_pnew_overflow bd (rich_word isa fid flags reserved ext0 OP_PNEW a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hroom.
  unfold dd_pnew_overflow, dd_ptable_room_one, dd_ptable_full.
  dd_cbn. bool_red.
  rewrite rw_op_correct.
  destruct (weq OP_PNEW OP_PNEW) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  destruct (wlt_dec _ _) as [_|Hnlt]; [reflexivity|].
  exfalso. apply Hnlt. apply lt_wlt.
  change (wordToNat (natToWord PTableNextIdSz 64)) with 64. exact Hroom.
Qed.

Lemma dd_psplit_overflow_false_rich : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (hw_pt_next_id bd) + 2 <= 64 ->
  dd_psplit_overflow bd (rich_word isa fid flags reserved ext0 OP_PSPLIT a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hroom.
  unfold dd_psplit_overflow, dd_ptable_room_two.
  dd_cbn. bool_red.
  rewrite rw_op_correct.
  destruct (weq OP_PSPLIT OP_PSPLIT) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  destruct (wlt_dec _ _) as [L|_]; [|reflexivity].
  exfalso. apply wlt_lt in L.
  rewrite wordToNat_wplus_7 in L by lia.
  change (wordToNat (natToWord PTableNextIdSz 64)) with 64 in L. lia.
Qed.

Lemma dd_pmerge_overflow_false_rich : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (hw_pt_next_id bd) < 64 ->
  dd_pmerge_overflow bd (rich_word isa fid flags reserved ext0 OP_PMERGE a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hroom.
  unfold dd_pmerge_overflow, dd_ptable_room_one, dd_ptable_full.
  dd_cbn. bool_red.
  rewrite rw_op_correct.
  destruct (weq OP_PMERGE OP_PMERGE) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  destruct (wlt_dec _ _) as [_|Hnlt]; [reflexivity|].
  exfalso. apply Hnlt. apply lt_wlt.
  change (wordToNat (natToWord PTableNextIdSz 64)) with 64. exact Hroom.
Qed.
