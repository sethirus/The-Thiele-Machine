(** RichNfiGuard.v: the NFI guard-falsity lemma generalized from legacy to
    all six ISA-v2 encodings -- PDISCOVER, the last of the ten guard-class
    opcodes -- mirroring [LegacyNfiGuard.v].

    [dd_nfi_violation] compares two word-decoded operand bytes directly, so
    this needs [RichWordDecode.rw_b_correct]/[rw_c_correct] in place of
    [LegacyWordDecode.dd_b_correct]/[dd_c_correct]; the rest of the proof is
    unchanged. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Bool Arith Lia.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded
  StepEval StepWordFacts DispatchLets Abstraction ImplementationContract
  StepFields StepFieldsMorph StepFaults StepRefineCommon LegacyWordDecode RichWordDecode.
Local Open Scope nat_scope.

Ltac dd_cbn := cbn [evalExpr evalBinBool evalUniBool evalConstT isEq evalBinBitBool evalUniBit evalZeroExtendTrunc].
Ltac bool_red := cbv beta iota delta [orb andb negb].

Lemma dd_nfi_violation_false_rich : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat b <= wordToNat c ->
  dd_nfi_violation bd (rich_word isa fid flags reserved ext0 OP_PDISCOVER a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  unfold dd_nfi_violation, dd_is_declared_bound_op, dd_cost32, dd_op_b_32.
  dd_cbn. bool_red.
  rewrite rw_op_correct.
  destruct (weq OP_PDISCOVER OP_PDISCOVER) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  rewrite rw_b_correct, rw_c_correct.
  destruct (wlt_dec _ _) as [Hlt|_]; [|reflexivity].
  exfalso.
  apply wlt_lt in Hlt.
  rewrite wordToNat_zext8_ext, wordToNat_zext8_ext in Hlt.
  lia.
Qed.
