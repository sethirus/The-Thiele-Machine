(** RichFaultMaster.v: the outside-domain relation for [dd_rich_fault], the
    fifth guard [OutsideDomain.v]/[OutsideDomainMaster.v] left uncovered.

    [DispatchLets.dd_rich_fault] is the disjunction of six checks:
    ISA-version validity, format validity for the decoded opcode,
    inline-payload/reserved-flag malformation, generic descriptor-range
    faults (only under [FMT_DESC]), morph/coupling table overflow, and
    certification-descriptor validity (only under [FMT_DESC]). Every
    [RetireMaster.admitted] constructor fetches one of two word shapes:
    [StepEval.legacy_word] (format [FMT_LEGACY], flags 0) or
    [StepFieldsMorph.rich_word] at a fixed format literal (3 =
    [FMT_MORPH_INLINE] for the six morph/compose "_ext" opcodes, 5 =
    [FMT_CERT_INLINE] for MORPH_ASSERT's extended form) with flags fixed to
    4. Neither shape ever instantiates [FMT_DESC], so the two
    [FMT_DESC]-gated disjuncts (generic descriptor range, certification
    descriptor validity) are false for every admitted instruction by format
    alone, needing no admission premise at all. The ISA-version and
    inline-malformation disjuncts are likewise closed constants once the
    format is fixed. The only disjunct that reads live hardware state is
    table overflow, and only for the three morph-allocating opcodes (MORPH,
    COMPOSE, MORPH_ID); exactly those constructors already carry the
    [hw_morph_next_id]/[hw_coupling_desc_next_id] room bound the guard
    needs, so no new admission premise is introduced here -- this file only
    restates facts the constructors already establish.

    [dd_rich_fault_false_legacy] covers all 46 legacy-word admitted
    constructors in one theorem (opcode is universally quantified; the room
    hypothesis is vacuous for every opcode but MORPH_ID). Together with
    [dd_rich_fault_false_morph_inline] (the 8 constructors at [fmt = 3]) and
    [dd_rich_fault_false_cert_inline] (the 1 constructor at [fmt = 5],
    MORPH_ASSERT's extended form), this covers all 55 constructors, and
    each theorem is general over every opcode/operand instance of its word
    shape, not just the ones [RetireMaster.v] happens to use. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Bool Arith Lia NArith.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded
  StepEval StepWordFacts DispatchLets Abstraction ImplementationContract
  StepFields StepFieldsMorph StepFaults StepRefineCommon LegacyWordDecode RichWordDecode
  RichFaultWords.
Local Open Scope nat_scope.

Ltac dd_cbn := cbn [evalExpr evalBinBool evalUniBool evalConstT isEq evalBinBitBool evalUniBit evalZeroExtendTrunc evalBinBit].
Ltac bool_red := cbv beta iota delta [orb andb negb].

(** [dd_rich_fault] unfolded to its flat six-leaf disjunction, mirroring
    [OutsideDomainMaster.v]'s [_unfold] lemmas for the other two guards. *)
Lemma dd_rich_fault_unfold : forall bd w,
  dd_rich_fault bd w =
  dd_isa_version_invalid bd w || dd_format_invalid bd w || dd_inline_malformed bd w ||
  dd_generic_desc_range_fault bd w || dd_rich_table_overflow bd w || dd_cert_desc_invalid bd w.
Proof. intros bd w. unfold dd_rich_fault. dd_cbn. reflexivity. Qed.

(** * Leaves gated by [format_id = FMT_DESC]: false whenever the format is
    anything else, with no opcode or operand reasoning at all. *)
Lemma dd_generic_desc_range_fault_false_of_format : forall bd w fid,
  dd_format_id bd w = fid -> fid <> FMT_DESC -> dd_generic_desc_range_fault bd w = false.
Proof.
  intros bd w fid Hf Hne. unfold dd_generic_desc_range_fault.
  dd_cbn. bool_red. rewrite Hf.
  destruct (weq fid FMT_DESC) as [E|_]; [contradiction|reflexivity].
Qed.

Lemma dd_cert_desc_invalid_false_of_format : forall bd w fid,
  dd_format_id bd w = fid -> fid <> FMT_DESC -> dd_cert_desc_invalid bd w = false.
Proof.
  intros bd w fid Hf Hne. unfold dd_cert_desc_invalid.
  dd_cbn. bool_red. rewrite Hf.
  destruct (weq fid FMT_DESC) as [E|_]; [contradiction|reflexivity].
Qed.

(** * ISA version: false whenever the decoded version is 2. *)
Lemma dd_isa_version_invalid_false_of_isa : forall bd w,
  dd_isa_version bd w = natToWord 8 2 -> dd_isa_version_invalid bd w = false.
Proof.
  intros bd w Hi. unfold dd_isa_version_invalid.
  dd_cbn. bool_red. rewrite Hi.
  destruct (weq (natToWord 8 2) (natToWord 8 2)) as [_|Hne]; [reflexivity|exfalso; apply Hne; reflexivity].
Qed.

(** * Format validity: false for the legacy encoding, whatever the opcode --
    [dd_format_allowed_for_opcode]'s first branch is unconditional on
    [format_id = FMT_LEGACY]. *)
Lemma dd_format_invalid_false_legacy : forall bd op a bo c,
  dd_format_invalid bd (legacy_word op a bo c) = false.
Proof.
  intros bd op a bo c. unfold dd_format_invalid, dd_format_known,
    dd_format_allowed_for_opcode, dd_morph_desc_kind_mismatch.
  rewrite (dd_format_id_correct bd op a bo c).
  dd_cbn. bool_red.
  destruct (weq FMT_LEGACY FMT_LEGACY) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  reflexivity.
Qed.

(** * Format validity for the fixed-flags rich encodings: false whenever the
    opcode matches the format's own allowance test ([dd_is_morph_opcode] for
    [FMT_MORPH_INLINE], [dd_is_cert_opcode] for [FMT_CERT_INLINE]). *)
Lemma dd_format_invalid_false_morph_inline : forall bd (op a bo c : word 8) (e : word 32),
  dd_is_morph_opcode bd (StepFieldsMorph.rich_word 3%N op a bo c e) = true ->
  dd_format_invalid bd (StepFieldsMorph.rich_word 3%N op a bo c e) = false.
Proof.
  intros bd op a bo c e Hmorph. unfold dd_format_invalid, dd_format_known,
    dd_format_allowed_for_opcode, dd_morph_desc_kind_mismatch.
  rewrite (rich_format_correct 3%N ltac:(auto) bd op a bo c e).
  rewrite fmt3_is_morph_inline.
  dd_cbn. bool_red.
  destruct (weq FMT_MORPH_INLINE FMT_LEGACY) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_MORPH_INLINE FMT_BRANCH_EXT) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_MORPH_INLINE FMT_TENSOR_EXT) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_MORPH_INLINE FMT_MORPH_INLINE) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  rewrite Hmorph. reflexivity.
Qed.

Lemma dd_format_invalid_false_cert_inline : forall bd (op a bo c : word 8) (e : word 32),
  dd_is_cert_opcode bd (StepFieldsMorph.rich_word 5%N op a bo c e) = true ->
  dd_format_invalid bd (StepFieldsMorph.rich_word 5%N op a bo c e) = false.
Proof.
  intros bd op a bo c e Hcert. unfold dd_format_invalid, dd_format_known,
    dd_format_allowed_for_opcode, dd_morph_desc_kind_mismatch.
  rewrite (rich_format_correct 5%N ltac:(auto) bd op a bo c e).
  rewrite fmt5_is_cert_inline.
  dd_cbn. bool_red.
  destruct (weq FMT_CERT_INLINE FMT_LEGACY) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_CERT_INLINE FMT_BRANCH_EXT) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_CERT_INLINE FMT_TENSOR_EXT) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_CERT_INLINE FMT_MORPH_INLINE) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_CERT_INLINE FMT_DESC) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_CERT_INLINE FMT_CERT_INLINE) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  rewrite Hcert. reflexivity.
Qed.

(** * Inline/reserved-flag malformation: false for the legacy encoding,
    whose flags are always 0 -- [dd_reserved_flag_fault] needs nonzero
    flags, and the other two leaves are gated by formats other than
    [FMT_LEGACY]. *)
Lemma dd_inline_malformed_false_legacy : forall bd op a bo c,
  dd_inline_malformed bd (legacy_word op a bo c) = false.
Proof.
  intros bd op a bo c. unfold dd_inline_malformed, dd_reserved_flag_fault,
    dd_inline_payload_fault, dd_desc_flag_fault, dd_flags_are_zero,
    dd_desc_kind_is_zero, dd_desc_kind_valid, dd_inline_len_zero, dd_inline_len_too_large,
    dd_desc_kind, dd_inline_len.
  rewrite (dd_format_id_correct bd op a bo c), (dd_flags_correct bd op a bo c).
  dd_cbn. bool_red.
  destruct (weq (natToWord 16 0) (natToWord 16 0)) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  destruct (weq FMT_LEGACY FMT_MORPH_INLINE) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_LEGACY FMT_CERT_INLINE) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_LEGACY FMT_DESC) as [Habs|_]; [discriminate Habs|].
  reflexivity.
Qed.

(** * Inline/reserved-flag malformation for the fixed-flags rich encodings:
    [dd_reserved_flag_fault] needs a format outside the rich class (false
    here, format is [FMT_MORPH_INLINE]/[FMT_CERT_INLINE]); [dd_desc_flag_fault]
    needs [FMT_DESC] (false here too); and [dd_inline_payload_fault]'s own
    well-formedness test is satisfied by the fixed flags value 4
    (descriptor kind 0, inline length 4: kind is zero, length is neither
    zero nor over 8). *)
Lemma dd_inline_malformed_false_morph_inline : forall bd (op a bo c : word 8) (e : word 32),
  dd_inline_malformed bd (StepFieldsMorph.rich_word 3%N op a bo c e) = false.
Proof.
  intros bd op a bo c e. unfold dd_inline_malformed, dd_reserved_flag_fault,
    dd_inline_payload_fault, dd_desc_flag_fault, dd_flags_are_zero,
    dd_desc_kind_is_zero, dd_desc_kind_valid, dd_inline_len_zero, dd_inline_len_too_large,
    dd_desc_kind, dd_inline_len.
  rewrite (rich_format_correct 3%N ltac:(auto) bd op a bo c e).
  rewrite (rich_flags_correct 3%N ltac:(auto) bd op a bo c e).
  rewrite fmt3_is_morph_inline.
  dd_cbn. bool_red.
  destruct (weq FMT_MORPH_INLINE FMT_LEGACY) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_MORPH_INLINE FMT_BRANCH_EXT) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_MORPH_INLINE FMT_TENSOR_EXT) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_MORPH_INLINE FMT_MORPH_INLINE) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  destruct (weq FMT_MORPH_INLINE FMT_CERT_INLINE) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_MORPH_INLINE FMT_DESC) as [Habs|_]; [discriminate Habs|].
  vm_compute. reflexivity.
Qed.

Lemma dd_inline_malformed_false_cert_inline : forall bd (op a bo c : word 8) (e : word 32),
  dd_inline_malformed bd (StepFieldsMorph.rich_word 5%N op a bo c e) = false.
Proof.
  intros bd op a bo c e. unfold dd_inline_malformed, dd_reserved_flag_fault,
    dd_inline_payload_fault, dd_desc_flag_fault, dd_flags_are_zero,
    dd_desc_kind_is_zero, dd_desc_kind_valid, dd_inline_len_zero, dd_inline_len_too_large,
    dd_desc_kind, dd_inline_len.
  rewrite (rich_format_correct 5%N ltac:(auto) bd op a bo c e).
  rewrite (rich_flags_correct 5%N ltac:(auto) bd op a bo c e).
  rewrite fmt5_is_cert_inline.
  dd_cbn. bool_red.
  destruct (weq FMT_CERT_INLINE FMT_LEGACY) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_CERT_INLINE FMT_BRANCH_EXT) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_CERT_INLINE FMT_TENSOR_EXT) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_CERT_INLINE FMT_MORPH_INLINE) as [Habs|_]; [discriminate Habs|].
  destruct (weq FMT_CERT_INLINE FMT_CERT_INLINE) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  destruct (weq FMT_CERT_INLINE FMT_DESC) as [Habs|_]; [discriminate Habs|].
  vm_compute. reflexivity.
Qed.

(** * Table overflow: the only disjunct that reads live hardware state, and
    only for the three morph-allocating opcodes. Fully opcode/format
    generic over the already-decoded values, so one lemma covers every
    encoding: supply the room bound only when the corresponding opcode/
    format combination can actually reach it. *)
Lemma dd_morph_alloc_opcode_false_of_neq : forall bd w,
  dd_opcode bd w <> OP_MORPH -> dd_opcode bd w <> OP_COMPOSE -> dd_opcode bd w <> OP_MORPH_ID ->
  dd_morph_alloc_opcode bd w = false.
Proof.
  intros bd w H1 H2 H3. unfold dd_morph_alloc_opcode. dd_cbn. bool_red.
  destruct (weq (dd_opcode bd w) OP_MORPH) as [E|_]; [contradiction|].
  destruct (weq (dd_opcode bd w) OP_COMPOSE) as [E|_]; [contradiction|].
  destruct (weq (dd_opcode bd w) OP_MORPH_ID) as [E|_]; [contradiction|].
  reflexivity.
Qed.

Lemma dd_rich_table_overflow_false : forall bd w,
  (dd_opcode bd w = OP_MORPH \/ dd_opcode bd w = OP_COMPOSE \/ dd_opcode bd w = OP_MORPH_ID ->
    wordToNat (hw_morph_next_id bd) < 16) ->
  ((dd_format_id bd w = FMT_MORPH_INLINE \/ dd_format_id bd w = FMT_DESC) /\ dd_opcode bd w = OP_MORPH ->
    wordToNat (hw_coupling_desc_next_id bd) < 16) ->
  dd_rich_table_overflow bd w = false.
Proof.
  intros bd w Hroom1 Hroom2. unfold dd_rich_table_overflow, dd_morph_alloc_opcode.
  dd_cbn. bool_red.
  destruct (weq (dd_opcode bd w) OP_MORPH) as [Hm|Hm].
  - (* op = OP_MORPH: both disjuncts' own opcode test picks the "true" arm,
       via the single shared [weq (dd_opcode bd w) OP_MORPH] destruct above. *)
    destruct (wlt_dec (hw_morph_next_id bd) (natToWord MorphTableNextIdSz 16)) as [_|Hnlt1].
    + destruct (weq (dd_format_id bd w) FMT_MORPH_INLINE) as [Hf1|Hf1].
      * destruct (wlt_dec (hw_coupling_desc_next_id bd) (natToWord DescTableNextIdSz 16)) as [_|Hnlt2];
          [reflexivity|].
        exfalso. apply Hnlt2. apply lt_wlt. apply Hroom2. split; [left; exact Hf1|exact Hm].
      * destruct (weq (dd_format_id bd w) FMT_DESC) as [Hf2|Hf2].
        -- destruct (wlt_dec (hw_coupling_desc_next_id bd) (natToWord DescTableNextIdSz 16)) as [_|Hnlt2];
             [reflexivity|].
           exfalso. apply Hnlt2. apply lt_wlt. apply Hroom2. split; [right; exact Hf2|exact Hm].
        -- reflexivity.
    + exfalso. apply Hnlt1. apply lt_wlt. apply Hroom1. left. exact Hm.
  - (* op <> OP_MORPH: the second disjunct's own [opcode == OP_MORPH] test
       (the same shared term) already picked its "false" arm, but the
       [if COND then false else false] shape around it still needs the
       format condition destructed once (either way) to reduce, since
       both branches being literally equal doesn't make the term
       convertible to [false] while the scrutinee stays symbolic. *)
    destruct (weq (dd_opcode bd w) OP_COMPOSE) as [Hc|Hc].
    + destruct (wlt_dec (hw_morph_next_id bd) (natToWord MorphTableNextIdSz 16)) as [_|Hnlt1].
      * destruct (weq (dd_format_id bd w) FMT_MORPH_INLINE) as [_|_]; [reflexivity|].
        destruct (weq (dd_format_id bd w) FMT_DESC) as [_|_]; reflexivity.
      * exfalso. apply Hnlt1. apply lt_wlt. apply Hroom1. right; left. exact Hc.
    + destruct (weq (dd_opcode bd w) OP_MORPH_ID) as [Hi|Hi].
      * destruct (wlt_dec (hw_morph_next_id bd) (natToWord MorphTableNextIdSz 16)) as [_|Hnlt1].
        -- destruct (weq (dd_format_id bd w) FMT_MORPH_INLINE) as [_|_]; [reflexivity|].
           destruct (weq (dd_format_id bd w) FMT_DESC) as [_|_]; reflexivity.
        -- exfalso. apply Hnlt1. apply lt_wlt. apply Hroom1. right; right. exact Hi.
      * destruct (weq (dd_format_id bd w) FMT_MORPH_INLINE) as [_|_]; [reflexivity|].
        destruct (weq (dd_format_id bd w) FMT_DESC) as [_|_]; reflexivity.
Qed.

Lemma fmt_morph_inline_not_desc : FMT_MORPH_INLINE <> FMT_DESC.
Proof. vm_compute. discriminate. Qed.
Lemma fmt_cert_inline_not_desc : FMT_CERT_INLINE <> FMT_DESC.
Proof. vm_compute. discriminate. Qed.

Lemma dd_is_morph_opcode_true_of_class : forall bd w,
  dd_opcode bd w = OP_MORPH \/ dd_opcode bd w = OP_COMPOSE \/ dd_opcode bd w = OP_MORPH_ID \/
  dd_opcode bd w = OP_MORPH_DELETE \/ dd_opcode bd w = OP_MORPH_ASSERT \/
  dd_opcode bd w = OP_MORPH_TENSOR \/ dd_opcode bd w = OP_MORPH_GET ->
  dd_is_morph_opcode bd w = true.
Proof.
  intros bd w H. unfold dd_is_morph_opcode.
  destruct H as [H|[H|[H|[H|[H|[H|H]]]]]]; rewrite H; vm_compute; reflexivity.
Qed.

(** * The three top-level theorems.

    [dd_rich_fault_false_legacy] is fully general over every legacy-word
    opcode: the room bound is only exercised when the opcode happens to be
    MORPH_ID (the one legacy-word opcode in the morph-allocating class),
    and is vacuous otherwise. *)
Lemma dd_rich_fault_false_legacy : forall (b : HWB) (op a bo c : word 8),
  (op = OP_MORPH \/ op = OP_COMPOSE \/ op = OP_MORPH_ID -> wordToNat (hw_morph_next_id b) < 16) ->
  dd_rich_fault b (legacy_word op a bo c) = false.
Proof.
  intros b op a bo c Hroom.
  pose proof (dd_op_correct b op a bo c) as Hop.
  rewrite dd_rich_fault_unfold.
  rewrite (dd_isa_version_invalid_false_of_isa b _ (dd_isa_version_correct b op a bo c)).
  rewrite (dd_format_invalid_false_legacy b op a bo c).
  rewrite (dd_inline_malformed_false_legacy b op a bo c).
  rewrite (dd_generic_desc_range_fault_false_of_format b _ FMT_LEGACY
    (dd_format_id_correct b op a bo c) ltac:(discriminate)).
  rewrite (dd_cert_desc_invalid_false_of_format b _ FMT_LEGACY
    (dd_format_id_correct b op a bo c) ltac:(discriminate)).
  rewrite dd_rich_table_overflow_false; [reflexivity | | ].
  - rewrite Hop. exact Hroom.
  - intros [Hfmt _]. rewrite (dd_format_id_correct b op a bo c) in Hfmt.
    destruct Hfmt as [Hfmt|Hfmt]; discriminate Hfmt.
Qed.

(** [dd_rich_fault_false_morph_inline] covers the six morph/compose "_ext"
    admitted constructors (MORPH_ID, MORPH_DELETE, MORPH_ASSERT,
    MORPH_TENSOR, MORPH_GET, MORPH, COMPOSE): every opcode this fixed
    format actually admits, with both room bounds vacuous except for the
    three morph-allocating opcodes as in the legacy case. *)
Lemma dd_rich_fault_false_morph_inline : forall (b : HWB) (op a bo c : word 8) (e : word 32),
  op = OP_MORPH \/ op = OP_COMPOSE \/ op = OP_MORPH_ID \/ op = OP_MORPH_DELETE \/
    op = OP_MORPH_ASSERT \/ op = OP_MORPH_TENSOR \/ op = OP_MORPH_GET ->
  (op = OP_MORPH \/ op = OP_COMPOSE \/ op = OP_MORPH_ID -> wordToNat (hw_morph_next_id b) < 16) ->
  (op = OP_MORPH -> wordToNat (hw_coupling_desc_next_id b) < 16) ->
  dd_rich_fault b (StepFieldsMorph.rich_word 3%N op a bo c e) = false.
Proof.
  intros b op a bo c e Hclass Hroom1 Hroom2.
  assert (Hop : dd_opcode b (StepFieldsMorph.rich_word 3%N op a bo c e) = op)
    by (apply rich_op_correct; auto).
  assert (Hmorph : dd_is_morph_opcode b (StepFieldsMorph.rich_word 3%N op a bo c e) = true).
  { apply dd_is_morph_opcode_true_of_class. rewrite Hop. exact Hclass. }
  assert (Hfmt : dd_format_id b (StepFieldsMorph.rich_word 3%N op a bo c e) = FMT_MORPH_INLINE).
  { rewrite (rich_format_correct 3%N ltac:(auto) b op a bo c e). exact fmt3_is_morph_inline. }
  rewrite dd_rich_fault_unfold.
  rewrite (dd_isa_version_invalid_false_of_isa b _ (rich_isa_correct 3%N ltac:(auto) b op a bo c e)).
  rewrite (dd_format_invalid_false_morph_inline b op a bo c e Hmorph).
  rewrite (dd_inline_malformed_false_morph_inline b op a bo c e).
  rewrite (dd_generic_desc_range_fault_false_of_format b _ FMT_MORPH_INLINE Hfmt fmt_morph_inline_not_desc).
  rewrite (dd_cert_desc_invalid_false_of_format b _ FMT_MORPH_INLINE Hfmt fmt_morph_inline_not_desc).
  rewrite dd_rich_table_overflow_false; [reflexivity | | ].
  - intro H. apply Hroom1. rewrite <- Hop. destruct H as [H|[H|H]]; [left|right;left|right;right];
    congruence.
  - intros [_ Hm2]. apply Hroom2. rewrite <- Hop. exact Hm2.
Qed.

(** [dd_rich_fault_false_cert_inline] covers MORPH_ASSERT's extended
    encoding: neither in the morph-allocating class nor equal to OP_MORPH,
    so the table-overflow disjunct is unconditionally false, with no room
    premise at all. *)
Lemma dd_rich_fault_false_cert_inline : forall (b : HWB) (a bo c : word 8) (e : word 32),
  dd_rich_fault b (StepFieldsMorph.rich_word 5%N OP_MORPH_ASSERT a bo c e) = false.
Proof.
  intros b a bo c e.
  assert (Hop : dd_opcode b (StepFieldsMorph.rich_word 5%N OP_MORPH_ASSERT a bo c e) = OP_MORPH_ASSERT)
    by (apply rich_op_correct; auto).
  assert (Hcert : dd_is_cert_opcode b (StepFieldsMorph.rich_word 5%N OP_MORPH_ASSERT a bo c e) = true).
  { unfold dd_is_cert_opcode. rewrite Hop. vm_compute. reflexivity. }
  assert (Hfmt : dd_format_id b (StepFieldsMorph.rich_word 5%N OP_MORPH_ASSERT a bo c e) = FMT_CERT_INLINE).
  { rewrite (rich_format_correct 5%N ltac:(auto) b OP_MORPH_ASSERT a bo c e). exact fmt5_is_cert_inline. }
  rewrite dd_rich_fault_unfold.
  rewrite (dd_isa_version_invalid_false_of_isa b _ (rich_isa_correct 5%N ltac:(auto) b OP_MORPH_ASSERT a bo c e)).
  rewrite (dd_format_invalid_false_cert_inline b OP_MORPH_ASSERT a bo c e Hcert).
  rewrite (dd_inline_malformed_false_cert_inline b OP_MORPH_ASSERT a bo c e).
  rewrite (dd_generic_desc_range_fault_false_of_format b _ FMT_CERT_INLINE Hfmt fmt_cert_inline_not_desc).
  rewrite (dd_cert_desc_invalid_false_of_format b _ FMT_CERT_INLINE Hfmt fmt_cert_inline_not_desc).
  rewrite dd_rich_table_overflow_false; [reflexivity | | ].
  - intro H. rewrite Hop in H. destruct H as [H|[H|H]]; discriminate H.
  - intros [_ Hm2]. rewrite Hop in Hm2. discriminate Hm2.
Qed.
