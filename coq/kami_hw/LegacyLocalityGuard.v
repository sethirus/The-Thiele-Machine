(** LegacyLocalityGuard.v: the remaining locality-class guard-falsity
    lemmas over the legacy word encoding -- STORE, HEAP_LOAD, HEAP_STORE,
    CALL, RET -- completing the set [LegacyLoadGuard.v] started with LOAD.

    Same technique throughout: decode the opcode (and, for the two heap
    variants, resolve the mux the non-heap proof left untouched) via
    [LegacyWordDecode]'s lane identity, then close the bound premise with
    the same [check_bounds]/[wlt_dec] reasoning [StepRefineCommon.region_ok_of_lt]
    already names for the bit-variable route. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Bool Arith Lia.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded
  StepEval StepWordFacts DispatchLets Abstraction ImplementationContract
  StepFields StepFieldsMorph StepFaults StepRefineCommon LegacyWordDecode.
Local Open Scope nat_scope.

Ltac dd_cbn := cbn [evalExpr evalBinBool evalUniBool evalConstT isEq evalBinBitBool evalUniBit evalZeroExtendTrunc].
Ltac bool_red := cbv beta iota delta [orb andb negb].

Lemma dd_store_locality_bad_false : forall bd (a b c : word 8),
  wordToNat (dd_mem_addr_a bd (legacy_word OP_STORE a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_store_locality_bad bd (legacy_word OP_STORE a b c) = false.
Proof.
  intros bd a b c Hbound.
  unfold dd_store_locality_bad, dd_is_store_op, dd_store_in_bounds.
  dd_cbn. bool_red.
  rewrite dd_op_correct.
  destruct (weq OP_STORE OP_STORE) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  destruct (weq OP_STORE OP_HEAP_STORE) as [Heq|_]; [discriminate Heq|].
  simpl.
  unfold dd_active_region_size.
  destruct (wlt_dec _ _) as [_|Hnlt]; [reflexivity|].
  exfalso. apply Hnlt.
  apply lt_wlt.
  rewrite wordToNat_zext7_ext.
  exact Hbound.
Qed.

Lemma dd_call_locality_bad_false : forall bd (a b c : word 8),
  wordToNat (dd_sp_addr bd (legacy_word OP_CALL a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_call_locality_bad bd (legacy_word OP_CALL a b c) = false.
Proof.
  intros bd a b c Hbound.
  unfold dd_call_locality_bad, dd_is_call_op, dd_call_in_bounds.
  dd_cbn. bool_red.
  rewrite dd_op_correct.
  destruct (weq OP_CALL OP_CALL) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  simpl.
  unfold dd_active_region_size.
  destruct (wlt_dec _ _) as [_|Hnlt]; [reflexivity|].
  exfalso. apply Hnlt.
  apply lt_wlt.
  rewrite wordToNat_zext7_ext.
  exact Hbound.
Qed.

Lemma dd_ret_locality_bad_false : forall bd (a b c : word 8),
  wordToNat (dd_sp_dec_addr bd (legacy_word OP_RET a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_ret_locality_bad bd (legacy_word OP_RET a b c) = false.
Proof.
  intros bd a b c Hbound.
  unfold dd_ret_locality_bad, dd_is_ret_op, dd_ret_in_bounds.
  dd_cbn. bool_red.
  rewrite dd_op_correct.
  destruct (weq OP_RET OP_RET) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  simpl.
  unfold dd_active_region_size.
  destruct (wlt_dec _ _) as [_|Hnlt]; [reflexivity|].
  exfalso. apply Hnlt.
  apply lt_wlt.
  rewrite wordToNat_zext7_ext.
  exact Hbound.
Qed.

Lemma dd_load_locality_bad_heap_false : forall bd (a b c : word 8),
  wordToNat (dd_heap_addr bd (legacy_word OP_HEAP_LOAD a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_load_locality_bad bd (legacy_word OP_HEAP_LOAD a b c) = false.
Proof.
  intros bd a b c Hbound.
  unfold dd_load_locality_bad, dd_is_load_op, dd_load_in_bounds.
  dd_cbn. bool_red.
  rewrite dd_op_correct.
  destruct (weq OP_HEAP_LOAD OP_LOAD) as [Heq|_]; [discriminate Heq|].
  destruct (weq OP_HEAP_LOAD OP_HEAP_LOAD) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  simpl.
  unfold dd_active_region_size.
  destruct (wlt_dec _ _) as [_|Hnlt]; [reflexivity|].
  exfalso. apply Hnlt.
  apply lt_wlt.
  rewrite wordToNat_zext7_ext.
  exact Hbound.
Qed.

Lemma dd_store_locality_bad_heap_false : forall bd (a b c : word 8),
  wordToNat (dd_heap_addr_a bd (legacy_word OP_HEAP_STORE a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_store_locality_bad bd (legacy_word OP_HEAP_STORE a b c) = false.
Proof.
  intros bd a b c Hbound.
  unfold dd_store_locality_bad, dd_is_store_op, dd_store_in_bounds.
  dd_cbn. bool_red.
  rewrite dd_op_correct.
  destruct (weq OP_HEAP_STORE OP_STORE) as [Heq|_]; [discriminate Heq|].
  destruct (weq OP_HEAP_STORE OP_HEAP_STORE) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  simpl.
  unfold dd_active_region_size.
  destruct (wlt_dec _ _) as [_|Hnlt]; [reflexivity|].
  exfalso. apply Hnlt.
  apply lt_wlt.
  rewrite wordToNat_zext7_ext.
  exact Hbound.
Qed.
