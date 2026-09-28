(** LegacyLoadGuard.v: the LOAD guard-class bound premise as decoded-guard
    falsity, for the legacy word encoding.

    [OutsideDomain.v]'s closing note leaves open, for each of the ten
    guard-class opcodes, restating its own admission bound as the falsity of
    its own decoded guard predicate ([dd_load_locality_bad], ...). This is
    the first such result: for a legacy LOAD word, [dd_load_locality_bad] is
    false whenever the decoded memory address lies within the active
    partition's region -- the same premise [StepRefineCommon.region_ok_of_lt]
    already names for the bit-variable route [StepRefine.step_load_refines]
    takes. The two routes reach the same guard via different means:
    [StepRefine.v] states its premise directly over eight per-bit variables
    with no opcode symbolically fixed; here the opcode, and every operand
    byte, are decoded from an arbitrary [legacy_word OP_LOAD a b c] via
    [LegacyWordDecode]'s lane identity, which is what the outside-domain
    relation needs: a guard stated over the concrete instruction word, not
    over already-split bit variables.

    Still open: the same argument for the other nine guard-class opcodes
    (STORE, HEAP_LOAD, HEAP_STORE, CALL, RET, PNEW, PSPLIT, PMERGE,
    PDISCOVER), and the rich-format guard, which needs the same lane
    identity for the other five encodings (BRANCH_EXT, TENSOR_EXT,
    MORPH_INLINE, DESC, CERT_INLINE). *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Bool Arith Lia.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded
  StepEval StepWordFacts DispatchLets Abstraction ImplementationContract
  StepFields StepFieldsMorph StepFaults StepRefineCommon LegacyWordDecode.
Local Open Scope nat_scope.

Ltac dd_cbn := cbn [evalExpr evalBinBool evalUniBool evalConstT isEq evalBinBitBool evalUniBit evalZeroExtendTrunc].
Ltac bool_red := cbv beta iota delta [orb andb negb].

Lemma dd_load_locality_bad_false : forall bd (a b c : word 8),
  wordToNat (dd_mem_addr bd (legacy_word OP_LOAD a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_load_locality_bad bd (legacy_word OP_LOAD a b c) = false.
Proof.
  intros bd a b c Hbound.
  unfold dd_load_locality_bad, dd_is_load_op, dd_load_in_bounds.
  dd_cbn. bool_red.
  rewrite dd_op_correct.
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
