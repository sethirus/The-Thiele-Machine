(** RichLoadGuard.v: the LOAD guard-class bound premise as decoded-guard
    falsity, generalized from the legacy word encoding to all six ISA-v2
    encodings at once.

    [LegacyLoadGuard.v] proved this for [legacy_word] alone. [RichWordDecode.v]
    then showed the six formats do not actually lay out [dd_opcode]/[dd_op_a]/
    [dd_op_b]/[dd_cost_v] differently -- every one of those is a fixed
    [ConstExtract] at a fixed absolute bit range, independent of [format_id] --
    so [rich_word] with its header fields left as arbitrary [isa]/[fid]/
    [flags]/[reserved]/[ext0] covers every encoding including legacy itself
    (legacy is the special case [fid = FMT_LEGACY], [flags = ext0 = 0]).

    The proof body below is otherwise identical to [LegacyLoadGuard.v]'s: the
    guard's own address getter ([dd_mem_addr]) and region-size getter stay
    fully opaque throughout, never unfolded against the word's encoding, so
    the only encoding fact the proof actually needs is the opcode decode --
    [RichWordDecode.rw_op_correct] in place of [LegacyWordDecode.dd_op_correct].
    This is what makes the same nine-line tactic script carry over verbatim
    to the other nine guard-class opcodes via a generator, exactly as it did
    for the legacy files.

    Still open: the same argument for the other nine guard-class opcodes
    (STORE, HEAP_LOAD, HEAP_STORE, CALL, RET, PNEW, PSPLIT, PMERGE,
    PDISCOVER), then assembling all ten opcodes across both [legacy_word] and
    [rich_word] into [OutsideDomain.v]'s master statement. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Bool Arith Lia.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded
  StepEval StepWordFacts DispatchLets Abstraction ImplementationContract
  StepFields StepFieldsMorph StepFaults StepRefineCommon LegacyWordDecode RichWordDecode.
Local Open Scope nat_scope.

Ltac dd_cbn := cbn [evalExpr evalBinBool evalUniBool evalConstT isEq evalBinBitBool evalUniBit evalZeroExtendTrunc].
Ltac bool_red := cbv beta iota delta [orb andb negb].

Lemma dd_load_locality_bad_false_rich : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (dd_mem_addr bd (rich_word isa fid flags reserved ext0 OP_LOAD a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_load_locality_bad bd (rich_word isa fid flags reserved ext0 OP_LOAD a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  unfold dd_load_locality_bad, dd_is_load_op, dd_load_in_bounds.
  dd_cbn. bool_red.
  rewrite rw_op_correct.
  destruct (weq OP_LOAD OP_LOAD) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  destruct (weq OP_LOAD OP_HEAP_LOAD) as [Heq|_]; [discriminate Heq|].
  simpl.
  unfold dd_active_region_size.
  destruct (wlt_dec _ _) as [_|Hnlt]; [reflexivity|].
  exfalso. apply Hnlt.
  apply lt_wlt.
  rewrite wordToNat_zext7_ext.
  exact Hbound.
Qed.
