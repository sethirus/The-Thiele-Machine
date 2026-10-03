(** LegacyLoadGuard.v: the LOAD guard-class bound premise as decoded-guard
    falsity, for the legacy word encoding.

    For each of the seven guard-class opcodes, the admission bound can be
    restated as the falsity of the opcode's own decoded guard predicate
    ([dd_load_locality_bad], ...). For a legacy LOAD word,
    [dd_load_locality_bad] is false whenever the decoded memory address lies
    within the active partition's region, the same premise
    [StepRefineCommon.region_ok_of_range] names for the bit-variable route
    [StepRefine.step_load_refines] takes. The two routes reach the same guard
    via different means: [StepRefine.v] states its premise directly over
    eight per-bit variables with no opcode symbolically fixed; here the
    opcode, and every operand byte, are decoded from an arbitrary
    [legacy_word OP_LOAD a b c] via [LegacyWordDecode]'s lane identity, which
    is what the outside-domain relation needs: a guard stated over the
    concrete instruction word, not over already-split bit variables.

    The other locality opcodes are in [LegacyLocalityGuard.v], PDISCOVER is
    in [LegacyNfiGuard.v], and the same results over every ISA-v2 encoding
    are [RichLoadGuard.v], [RichLocalityGuard.v] and [RichNfiGuard.v]. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Bool Arith Lia.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded
  StepEval StepWordFacts DispatchLets Abstraction ImplementationContract
  StepFields StepFieldsMorph StepFaults StepRefineCommon LegacyWordDecode.
Local Open Scope nat_scope.
(* The range test zero-extends by concatenation; keep it folded. *)
Local Arguments Word.combine : simpl never.

Ltac dd_cbn := cbn [evalExpr evalBinBool evalUniBool evalConstT isEq evalBinBitBool evalUniBit evalZeroExtendTrunc].
Ltac bool_red := cbv beta iota delta [orb andb negb].

Lemma dd_load_locality_bad_false : forall bd (a b c : word 8),
  hwb_addr_in_active_range bd (wordToNat (dd_mem_addr bd (legacy_word OP_LOAD a b c))) ->
  dd_load_locality_bad bd (legacy_word OP_LOAD a b c) = false.
Proof.
  intros bd a b c Hbound.
  unfold dd_load_locality_bad, dd_is_load_op, dd_load_in_bounds.
  dd_cbn. bool_red.
  rewrite dd_op_correct.
  destruct (weq OP_LOAD OP_LOAD) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  destruct (weq OP_LOAD OP_HEAP_LOAD) as [Heq|_]; [discriminate Heq|].
  simpl.
  close_dd_bounds Hbound.
Qed.
