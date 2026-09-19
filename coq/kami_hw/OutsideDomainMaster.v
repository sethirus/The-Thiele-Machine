(** OutsideDomainMaster.v: the master outside-domain theorem for the ten
    guard-class opcodes.

    [OutsideDomain.v]'s [not_guard_of_opcode] handles every opcode outside
    [guard_opcodes]: the whole trap-class guard disjunction
    ([dd_locality_violation || dd_ptable_overflow_violation ||
    dd_nfi_violation]) is false by opcode non-membership alone, no decode
    reasoning needed. The ten guard-class opcodes need the complementary
    argument: given that opcode's own admission bound, the *same*
    disjunction is false, this time because each of the disjunction's eight
    leaves (four locality sub-guards, three partition sub-guards, the NFI
    guard) is individually false -- one by the bound premise (via
    [RichLoadGuard]/[RichLocalityGuard]/[RichPartitionGuard]/[RichNfiGuard]),
    the other seven because the decoded opcode does not match their own
    gating constant, which needs no bound and no encoding fact at all.

    Stated over [rich_word] throughout, so (unlike [LegacyLoadGuard.v] and
    its three siblings) this single set of ten theorems already covers every
    ISA-v2 encoding, legacy included as the special case [fid = FMT_LEGACY].
    Together with [OutsideDomain.not_guard_of_opcode], this closes the
    syntactic half of C1's outside-domain relation: for an arbitrary
    [rich_word], whatever its opcode, either it is outside the guard class
    (guard false by computation) or it is one of the ten guard-class opcodes
    and its own admission bound makes the guard false. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Bool Arith Lia.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded
  StepEval StepWordFacts DispatchLets Abstraction ImplementationContract
  StepFields StepFieldsMorph StepFaults StepRefineCommon LegacyWordDecode RichWordDecode
  RichLoadGuard RichLocalityGuard RichPartitionGuard RichNfiGuard.
Local Open Scope nat_scope.

Ltac dd_cbn := cbn [evalExpr evalBinBool evalUniBool evalConstT isEq evalBinBitBool evalUniBit evalZeroExtendTrunc evalBinBit].
Ltac bool_red := cbv beta iota delta [orb andb negb].

(** The two umbrella guards, unfolded to the flat disjunction of their own
    sub-guards. Both are already stated this way in [DispatchLets.v]; this
    just names the fact so the master theorems below do not repeat the
    unfold every time. *)
Lemma dd_locality_violation_unfold : forall bd w,
  dd_locality_violation bd w =
  dd_load_locality_bad bd w || dd_store_locality_bad bd w ||
  dd_call_locality_bad bd w || dd_ret_locality_bad bd w.
Proof. intros bd w. unfold dd_locality_violation. dd_cbn. reflexivity. Qed.

Lemma dd_ptable_overflow_violation_unfold : forall bd w,
  dd_ptable_overflow_violation bd w =
  dd_pnew_overflow bd w || dd_psplit_overflow bd w || dd_pmerge_overflow bd w.
Proof. intros bd w. unfold dd_ptable_overflow_violation. dd_cbn. reflexivity. Qed.

(** * Sibling nullification

    Each of the eight leaves is gated by its own opcode test(s); if the
    decoded opcode is not among them, the leaf is false regardless of the
    operand bytes or the boundary -- no bound premise, no encoding fact.
    Fully generic over [w]: unlike the guard-falsity lemmas, these never
    look past [dd_opcode]. *)

Lemma dd_load_locality_bad_false_of_neq : forall bd w,
  dd_opcode bd w <> OP_LOAD -> dd_opcode bd w <> OP_HEAP_LOAD ->
  dd_load_locality_bad bd w = false.
Proof.
  intros bd w H1 H2. unfold dd_load_locality_bad, dd_is_load_op.
  dd_cbn. bool_red.
  destruct (weq (dd_opcode bd w) OP_LOAD) as [E|_]; [contradiction|].
  destruct (weq (dd_opcode bd w) OP_HEAP_LOAD) as [E|_]; [contradiction|].
  reflexivity.
Qed.

Lemma dd_store_locality_bad_false_of_neq : forall bd w,
  dd_opcode bd w <> OP_STORE -> dd_opcode bd w <> OP_HEAP_STORE ->
  dd_store_locality_bad bd w = false.
Proof.
  intros bd w H1 H2. unfold dd_store_locality_bad, dd_is_store_op.
  dd_cbn. bool_red.
  destruct (weq (dd_opcode bd w) OP_STORE) as [E|_]; [contradiction|].
  destruct (weq (dd_opcode bd w) OP_HEAP_STORE) as [E|_]; [contradiction|].
  reflexivity.
Qed.

Lemma dd_call_locality_bad_false_of_neq : forall bd w,
  dd_opcode bd w <> OP_CALL -> dd_call_locality_bad bd w = false.
Proof.
  intros bd w H1. unfold dd_call_locality_bad, dd_is_call_op.
  dd_cbn. bool_red.
  destruct (weq (dd_opcode bd w) OP_CALL) as [E|_]; [contradiction|].
  reflexivity.
Qed.

Lemma dd_ret_locality_bad_false_of_neq : forall bd w,
  dd_opcode bd w <> OP_RET -> dd_ret_locality_bad bd w = false.
Proof.
  intros bd w H1. unfold dd_ret_locality_bad, dd_is_ret_op.
  dd_cbn. bool_red.
  destruct (weq (dd_opcode bd w) OP_RET) as [E|_]; [contradiction|].
  reflexivity.
Qed.

Lemma dd_pnew_overflow_false_of_neq : forall bd w,
  dd_opcode bd w <> OP_PNEW -> dd_pnew_overflow bd w = false.
Proof.
  intros bd w H1. unfold dd_pnew_overflow.
  dd_cbn. bool_red.
  destruct (weq (dd_opcode bd w) OP_PNEW) as [E|_]; [contradiction|].
  reflexivity.
Qed.

Lemma dd_psplit_overflow_false_of_neq : forall bd w,
  dd_opcode bd w <> OP_PSPLIT -> dd_psplit_overflow bd w = false.
Proof.
  intros bd w H1. unfold dd_psplit_overflow.
  dd_cbn. bool_red.
  destruct (weq (dd_opcode bd w) OP_PSPLIT) as [E|_]; [contradiction|].
  reflexivity.
Qed.

Lemma dd_pmerge_overflow_false_of_neq : forall bd w,
  dd_opcode bd w <> OP_PMERGE -> dd_pmerge_overflow bd w = false.
Proof.
  intros bd w H1. unfold dd_pmerge_overflow.
  dd_cbn. bool_red.
  destruct (weq (dd_opcode bd w) OP_PMERGE) as [E|_]; [contradiction|].
  reflexivity.
Qed.

Lemma dd_nfi_violation_false_of_neq : forall bd w,
  dd_opcode bd w <> OP_PDISCOVER -> dd_nfi_violation bd w = false.
Proof.
  intros bd w H1. unfold dd_nfi_violation, dd_is_declared_bound_op.
  dd_cbn. bool_red.
  destruct (weq (dd_opcode bd w) OP_PDISCOVER) as [E|_]; [contradiction|].
  reflexivity.
Qed.

(** Discharges a [dd_opcode bd w <> TARGET] side condition from a known
    [dd_opcode bd w = OWN] fact, for two opcode constants [OWN <> TARGET]
    decided by [discriminate] on the resulting word equality. *)
Ltac neq_from_op Hop :=
  let H := fresh in intro H; rewrite Hop in H; discriminate H.

(** * The ten master theorems

    Each combines its own leaf (already proved false by the admission bound
    in [RichLoadGuard]/[RichLocalityGuard]/[RichPartitionGuard]/[RichNfiGuard])
    with the seven sibling-nullification facts above, closing the full
    trap-class guard disjunction -- the same conclusion
    [OutsideDomain.not_guard_of_opcode] reaches for opcodes outside the
    guard class, reached here through the bound instead of non-membership. *)

Lemma guard_false_of_load : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (dd_mem_addr bd (rich_word isa fid flags reserved ext0 OP_LOAD a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_locality_violation bd (rich_word isa fid flags reserved ext0 OP_LOAD a b c) ||
  dd_ptable_overflow_violation bd (rich_word isa fid flags reserved ext0 OP_LOAD a b c) ||
  dd_nfi_violation bd (rich_word isa fid flags reserved ext0 OP_LOAD a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  pose proof (rw_op_correct bd isa fid flags reserved ext0 OP_LOAD a b c) as Hop.
  rewrite dd_locality_violation_unfold, dd_ptable_overflow_violation_unfold.
  rewrite (dd_load_locality_bad_false_rich bd isa fid flags reserved ext0 a b c Hbound).
  rewrite (dd_store_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_call_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_ret_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pnew_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_psplit_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pmerge_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_nfi_violation_false_of_neq bd _ ltac:(neq_from_op Hop)).
  reflexivity.
Qed.

Lemma guard_false_of_heap_load : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (dd_heap_addr bd (rich_word isa fid flags reserved ext0 OP_HEAP_LOAD a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_locality_violation bd (rich_word isa fid flags reserved ext0 OP_HEAP_LOAD a b c) ||
  dd_ptable_overflow_violation bd (rich_word isa fid flags reserved ext0 OP_HEAP_LOAD a b c) ||
  dd_nfi_violation bd (rich_word isa fid flags reserved ext0 OP_HEAP_LOAD a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  pose proof (rw_op_correct bd isa fid flags reserved ext0 OP_HEAP_LOAD a b c) as Hop.
  rewrite dd_locality_violation_unfold, dd_ptable_overflow_violation_unfold.
  rewrite (dd_load_locality_bad_heap_false_rich bd isa fid flags reserved ext0 a b c Hbound).
  rewrite (dd_store_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_call_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_ret_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pnew_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_psplit_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pmerge_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_nfi_violation_false_of_neq bd _ ltac:(neq_from_op Hop)).
  reflexivity.
Qed.

Lemma guard_false_of_store : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (dd_mem_addr_a bd (rich_word isa fid flags reserved ext0 OP_STORE a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_locality_violation bd (rich_word isa fid flags reserved ext0 OP_STORE a b c) ||
  dd_ptable_overflow_violation bd (rich_word isa fid flags reserved ext0 OP_STORE a b c) ||
  dd_nfi_violation bd (rich_word isa fid flags reserved ext0 OP_STORE a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  pose proof (rw_op_correct bd isa fid flags reserved ext0 OP_STORE a b c) as Hop.
  rewrite dd_locality_violation_unfold, dd_ptable_overflow_violation_unfold.
  rewrite (dd_load_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_store_locality_bad_false_rich bd isa fid flags reserved ext0 a b c Hbound).
  rewrite (dd_call_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_ret_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pnew_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_psplit_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pmerge_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_nfi_violation_false_of_neq bd _ ltac:(neq_from_op Hop)).
  reflexivity.
Qed.

Lemma guard_false_of_heap_store : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (dd_heap_addr_a bd (rich_word isa fid flags reserved ext0 OP_HEAP_STORE a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_locality_violation bd (rich_word isa fid flags reserved ext0 OP_HEAP_STORE a b c) ||
  dd_ptable_overflow_violation bd (rich_word isa fid flags reserved ext0 OP_HEAP_STORE a b c) ||
  dd_nfi_violation bd (rich_word isa fid flags reserved ext0 OP_HEAP_STORE a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  pose proof (rw_op_correct bd isa fid flags reserved ext0 OP_HEAP_STORE a b c) as Hop.
  rewrite dd_locality_violation_unfold, dd_ptable_overflow_violation_unfold.
  rewrite (dd_load_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_store_locality_bad_heap_false_rich bd isa fid flags reserved ext0 a b c Hbound).
  rewrite (dd_call_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_ret_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pnew_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_psplit_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pmerge_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_nfi_violation_false_of_neq bd _ ltac:(neq_from_op Hop)).
  reflexivity.
Qed.

Lemma guard_false_of_call : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (dd_sp_addr bd (rich_word isa fid flags reserved ext0 OP_CALL a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_locality_violation bd (rich_word isa fid flags reserved ext0 OP_CALL a b c) ||
  dd_ptable_overflow_violation bd (rich_word isa fid flags reserved ext0 OP_CALL a b c) ||
  dd_nfi_violation bd (rich_word isa fid flags reserved ext0 OP_CALL a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  pose proof (rw_op_correct bd isa fid flags reserved ext0 OP_CALL a b c) as Hop.
  rewrite dd_locality_violation_unfold, dd_ptable_overflow_violation_unfold.
  rewrite (dd_load_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_store_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_call_locality_bad_false_rich bd isa fid flags reserved ext0 a b c Hbound).
  rewrite (dd_ret_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pnew_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_psplit_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pmerge_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_nfi_violation_false_of_neq bd _ ltac:(neq_from_op Hop)).
  reflexivity.
Qed.

Lemma guard_false_of_ret : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (dd_sp_dec_addr bd (rich_word isa fid flags reserved ext0 OP_RET a b c))
    < wordToNat (hw_ptTable bd (hw_active_module bd)) ->
  dd_locality_violation bd (rich_word isa fid flags reserved ext0 OP_RET a b c) ||
  dd_ptable_overflow_violation bd (rich_word isa fid flags reserved ext0 OP_RET a b c) ||
  dd_nfi_violation bd (rich_word isa fid flags reserved ext0 OP_RET a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  pose proof (rw_op_correct bd isa fid flags reserved ext0 OP_RET a b c) as Hop.
  rewrite dd_locality_violation_unfold, dd_ptable_overflow_violation_unfold.
  rewrite (dd_load_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_store_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_call_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_ret_locality_bad_false_rich bd isa fid flags reserved ext0 a b c Hbound).
  rewrite (dd_pnew_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_psplit_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pmerge_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_nfi_violation_false_of_neq bd _ ltac:(neq_from_op Hop)).
  reflexivity.
Qed.

Lemma guard_false_of_pnew : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (hw_pt_next_id bd) < 64 ->
  dd_locality_violation bd (rich_word isa fid flags reserved ext0 OP_PNEW a b c) ||
  dd_ptable_overflow_violation bd (rich_word isa fid flags reserved ext0 OP_PNEW a b c) ||
  dd_nfi_violation bd (rich_word isa fid flags reserved ext0 OP_PNEW a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  pose proof (rw_op_correct bd isa fid flags reserved ext0 OP_PNEW a b c) as Hop.
  rewrite dd_locality_violation_unfold, dd_ptable_overflow_violation_unfold.
  rewrite (dd_load_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_store_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_call_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_ret_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pnew_overflow_false_rich bd isa fid flags reserved ext0 a b c Hbound).
  rewrite (dd_psplit_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pmerge_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_nfi_violation_false_of_neq bd _ ltac:(neq_from_op Hop)).
  reflexivity.
Qed.

Lemma guard_false_of_psplit : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (hw_pt_next_id bd) + 2 <= 64 ->
  dd_locality_violation bd (rich_word isa fid flags reserved ext0 OP_PSPLIT a b c) ||
  dd_ptable_overflow_violation bd (rich_word isa fid flags reserved ext0 OP_PSPLIT a b c) ||
  dd_nfi_violation bd (rich_word isa fid flags reserved ext0 OP_PSPLIT a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  pose proof (rw_op_correct bd isa fid flags reserved ext0 OP_PSPLIT a b c) as Hop.
  rewrite dd_locality_violation_unfold, dd_ptable_overflow_violation_unfold.
  rewrite (dd_load_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_store_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_call_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_ret_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pnew_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_psplit_overflow_false_rich bd isa fid flags reserved ext0 a b c Hbound).
  rewrite (dd_pmerge_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_nfi_violation_false_of_neq bd _ ltac:(neq_from_op Hop)).
  reflexivity.
Qed.

Lemma guard_false_of_pmerge : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat (hw_pt_next_id bd) < 64 ->
  dd_locality_violation bd (rich_word isa fid flags reserved ext0 OP_PMERGE a b c) ||
  dd_ptable_overflow_violation bd (rich_word isa fid flags reserved ext0 OP_PMERGE a b c) ||
  dd_nfi_violation bd (rich_word isa fid flags reserved ext0 OP_PMERGE a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  pose proof (rw_op_correct bd isa fid flags reserved ext0 OP_PMERGE a b c) as Hop.
  rewrite dd_locality_violation_unfold, dd_ptable_overflow_violation_unfold.
  rewrite (dd_load_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_store_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_call_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_ret_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pnew_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_psplit_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pmerge_overflow_false_rich bd isa fid flags reserved ext0 a b c Hbound).
  rewrite (dd_nfi_violation_false_of_neq bd _ ltac:(neq_from_op Hop)).
  reflexivity.
Qed.

Lemma guard_false_of_pdiscover : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (a b c : word 8),
  wordToNat b <= wordToNat c ->
  dd_locality_violation bd (rich_word isa fid flags reserved ext0 OP_PDISCOVER a b c) ||
  dd_ptable_overflow_violation bd (rich_word isa fid flags reserved ext0 OP_PDISCOVER a b c) ||
  dd_nfi_violation bd (rich_word isa fid flags reserved ext0 OP_PDISCOVER a b c) = false.
Proof.
  intros bd isa fid flags reserved ext0 a b c Hbound.
  pose proof (rw_op_correct bd isa fid flags reserved ext0 OP_PDISCOVER a b c) as Hop.
  rewrite dd_locality_violation_unfold, dd_ptable_overflow_violation_unfold.
  rewrite (dd_load_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_store_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop) ltac:(neq_from_op Hop)).
  rewrite (dd_call_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_ret_locality_bad_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pnew_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_psplit_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_pmerge_overflow_false_of_neq bd _ ltac:(neq_from_op Hop)).
  rewrite (dd_nfi_violation_false_rich bd isa fid flags reserved ext0 a b c Hbound).
  reflexivity.
Qed.
