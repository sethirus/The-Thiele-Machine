(** LegacyNfiGuard.v: the NFI guard-falsity lemma over the legacy word
    encoding -- PDISCOVER, the last of the ten guard-class opcodes.

    [dd_nfi_violation] compares two word-decoded operand bytes directly
    ([dd_cost_v] against [dd_op_b], zero-extended), not a register-read
    address, so this is closed with [LegacyWordDecode.dd_b_correct]/
    [dd_c_correct] plus [StepRefineCommon.wordToNat_zext8_ext] rather than
    the [check_bounds] route the locality guards use. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Bool Arith Lia.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded
  StepEval StepWordFacts DispatchLets Abstraction ImplementationContract
  StepFields StepFieldsMorph StepFaults StepRefineCommon LegacyWordDecode.
Local Open Scope nat_scope.

Ltac dd_cbn := cbn [evalExpr evalBinBool evalUniBool evalConstT isEq evalBinBitBool evalUniBit evalZeroExtendTrunc].
Ltac bool_red := cbv beta iota delta [orb andb negb].

Lemma dd_nfi_violation_false : forall bd (a b c : word 8),
  wordToNat b <= wordToNat c ->
  dd_nfi_violation bd (legacy_word OP_PDISCOVER a b c) = false.
Proof.
  intros bd a b c Hbound.
  unfold dd_nfi_violation, dd_is_declared_bound_op, dd_cost32, dd_op_b_32.
  dd_cbn. bool_red.
  rewrite dd_op_correct.
  destruct (weq OP_PDISCOVER OP_PDISCOVER) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  rewrite dd_b_correct, dd_c_correct.
  destruct (wlt_dec _ _) as [Hlt|_]; [|reflexivity].
  exfalso.
  apply wlt_lt in Hlt.
  rewrite wordToNat_zext8_ext, wordToNat_zext8_ext in Hlt.
  lia.
Qed.
