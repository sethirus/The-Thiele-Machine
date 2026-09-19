(** RichLocalityGuard.v: the remaining locality-class guard-falsity lemmas
    generalized from legacy to all six ISA-v2 encodings -- STORE, HEAP_LOAD,
    HEAP_STORE, CALL, RET -- completing the set [RichLoadGuard.v] started
    with LOAD, mirroring [LegacyLocalityGuard.v]'s five legacy lemmas.

    Same technique as [RichLoadGuard.v]: the address getter and mux structure
    stay opaque to the word's encoding, so only the opcode decode changes
    from [LegacyWordDecode.dd_op_correct] to [RichWordDecode.rw_op_correct];
    every other tactic step is verbatim. Generated (not hand-written per
    lemma) since the five lemmas are structurally identical modulo names,
    the same reasoning [LegacyLocalityGuard.v]'s own generator used; each is
    still checked individually by the guarded [coqc], not assumed correct
    from the generator. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Bool Arith Lia.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded
  StepEval StepWordFacts DispatchLets Abstraction ImplementationContract
  StepFields StepFieldsMorph StepFaults StepRefineCommon LegacyWordDecode RichWordDecode.
Local Open Scope nat_scope.

Ltac dd_cbn := cbn [evalExpr evalBinBool evalUniBool evalConstT isEq evalBinBitBool evalUniBit evalZeroExtendTrunc].
Ltac bool_red := cbv beta iota delta [orb andb negb].

Lemma dd_store_locality_bad_false_rich : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (dd_mem_addr_a bd (rich_word isa fid flags reserved ext0 OP_STORE a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_store_locality_bad bd (rich_word isa fid flags reserved ext0 OP_STORE a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  unfold dd_store_locality_bad, dd_is_store_op, dd_store_in_bounds.
  dd_cbn. bool_red.
  rewrite rw_op_correct.
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

Lemma dd_call_locality_bad_false_rich : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (dd_sp_addr bd (rich_word isa fid flags reserved ext0 OP_CALL a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_call_locality_bad bd (rich_word isa fid flags reserved ext0 OP_CALL a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  unfold dd_call_locality_bad, dd_is_call_op, dd_call_in_bounds.
  dd_cbn. bool_red.
  rewrite rw_op_correct.
  destruct (weq OP_CALL OP_CALL) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  simpl.
  unfold dd_active_region_size.
  destruct (wlt_dec _ _) as [_|Hnlt]; [reflexivity|].
  exfalso. apply Hnlt.
  apply lt_wlt.
  rewrite wordToNat_zext7_ext.
  exact Hbound.
Qed.

Lemma dd_ret_locality_bad_false_rich : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (dd_sp_dec_addr bd (rich_word isa fid flags reserved ext0 OP_RET a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_ret_locality_bad bd (rich_word isa fid flags reserved ext0 OP_RET a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  unfold dd_ret_locality_bad, dd_is_ret_op, dd_ret_in_bounds.
  dd_cbn. bool_red.
  rewrite rw_op_correct.
  destruct (weq OP_RET OP_RET) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  simpl.
  unfold dd_active_region_size.
  destruct (wlt_dec _ _) as [_|Hnlt]; [reflexivity|].
  exfalso. apply Hnlt.
  apply lt_wlt.
  rewrite wordToNat_zext7_ext.
  exact Hbound.
Qed.

Lemma dd_load_locality_bad_heap_false_rich : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (dd_heap_addr bd (rich_word isa fid flags reserved ext0 OP_HEAP_LOAD a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_load_locality_bad bd (rich_word isa fid flags reserved ext0 OP_HEAP_LOAD a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  unfold dd_load_locality_bad, dd_is_load_op, dd_load_in_bounds.
  dd_cbn. bool_red.
  rewrite rw_op_correct.
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

Lemma dd_store_locality_bad_heap_false_rich : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (dd_heap_addr_a bd (rich_word isa fid flags reserved ext0 OP_HEAP_STORE a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_store_locality_bad bd (rich_word isa fid flags reserved ext0 OP_HEAP_STORE a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  unfold dd_store_locality_bad, dd_is_store_op, dd_store_in_bounds.
  dd_cbn. bool_red.
  rewrite rw_op_correct.
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

