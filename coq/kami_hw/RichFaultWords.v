(** RichFaultWords.v: the word-encoding bridge for [dd_rich_fault]'s
    outside-domain obligation.

    [StepFieldsMorph.rich_word fmt op a b c e] is the fixed-flags encoding
    the seven "_ext" retirement theorems use (morph-inline opcodes at
    [fmt = 3], MORPH_ASSERT's descriptor-carrying form at [fmt = 5]), with
    flags fixed to 4 (subtype 0, descriptor kind 0, inline length 4). This
    is exactly one instance of [RichWordDecode.rich_word] -- the general
    six-encoding word -- with [isa = 2], [flags = 4], [reserved = 0] and
    [format_id] fixed to the literal [fmt]. Bridging the two lets every
    [dd_*] decode fact [RichWordDecode.v] already proved (opcode, isa
    version, format id, flags) transfer directly, without re-deriving the
    lane arithmetic. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String NArith Arith Lia.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep
  BoundaryDecoded DispatchLets StepEval StepFieldsMorph LegacyWordDecode RichWordDecode.
Require Import Kami.Lib.NatLib.
Local Open Scope nat_scope.

(** The fixed 64-bit header tail (isa=2, format=[fmt], flags=4, reserved=0)
    StepFieldsMorph.rich_word builds via N-shift arithmetic is the same
    value RichWordDecode.rich_top96's combine-based tail builds, for both
    format literals the retirement theorems use. Both sides are fully
    concrete once [fmt] is instantiated, so this is a closed computation. *)
Lemma rich_word_tail_eq : forall (fmt : N),
  fmt = 3%N \/ fmt = 5%N ->
  NToWord 64 (N.lor (N.shiftl 2 56) (N.lor (N.shiftl fmt 48) (N.shiftl 4 32)))
  = combine (wzero 32) (combine (natToWord 16 4) (combine (NToWord FormatIdSz fmt) (natToWord 8 2))).
Proof. intros fmt [-> | ->]; vm_compute; reflexivity. Qed.

Lemma rich_word_eq : forall (fmt : N), fmt = 3%N \/ fmt = 5%N ->
  forall (op a b c : word 8) (e : word 32),
  StepFieldsMorph.rich_word fmt op a b c e
  = RichWordDecode.rich_word (natToWord 8 2) (NToWord FormatIdSz fmt) (natToWord 16 4) (wzero 32) e op a b c.
Proof.
  intros fmt Hfmt op a b c e.
  unfold StepFieldsMorph.rich_word, RichWordDecode.rich_word, RichWordDecode.rich_top96.
  rewrite (rich_word_tail_eq fmt Hfmt). reflexivity.
Qed.

(** Decode corollaries for the fixed-flags encoding, transferred from
    [RichWordDecode.v]'s general lemmas through the bridge above. *)
Lemma rich_op_correct : forall (fmt : N), fmt = 3%N \/ fmt = 5%N ->
  forall bd (op a b c : word 8) (e : word 32),
  dd_opcode bd (StepFieldsMorph.rich_word fmt op a b c e) = op.
Proof. intros fmt Hf bd op a b c e. rewrite (rich_word_eq fmt Hf). apply rw_op_correct. Qed.

Lemma rich_isa_correct : forall (fmt : N), fmt = 3%N \/ fmt = 5%N ->
  forall bd (op a b c : word 8) (e : word 32),
  dd_isa_version bd (StepFieldsMorph.rich_word fmt op a b c e) = natToWord 8 2.
Proof. intros fmt Hf bd op a b c e. rewrite (rich_word_eq fmt Hf). apply rw_isa_correct. Qed.

Lemma rich_format_correct : forall (fmt : N), fmt = 3%N \/ fmt = 5%N ->
  forall bd (op a b c : word 8) (e : word 32),
  dd_format_id bd (StepFieldsMorph.rich_word fmt op a b c e) = NToWord FormatIdSz fmt.
Proof. intros fmt Hf bd op a b c e. rewrite (rich_word_eq fmt Hf). apply rw_format_correct. Qed.

Lemma rich_flags_correct : forall (fmt : N), fmt = 3%N \/ fmt = 5%N ->
  forall bd (op a b c : word 8) (e : word 32),
  dd_flags bd (StepFieldsMorph.rich_word fmt op a b c e) = natToWord 16 4.
Proof. intros fmt Hf bd op a b c e. rewrite (rich_word_eq fmt Hf). apply rw_flags_correct. Qed.

(** The two format literals used, related to their named constants. *)
Lemma fmt3_is_morph_inline : NToWord FormatIdSz 3 = FMT_MORPH_INLINE.
Proof. vm_compute. reflexivity. Qed.
Lemma fmt5_is_cert_inline : NToWord FormatIdSz 5 = FMT_CERT_INLINE.
Proof. vm_compute. reflexivity. Qed.
Lemma fmt3_not_desc : NToWord FormatIdSz 3 <> FMT_DESC.
Proof. vm_compute. discriminate. Qed.
Lemma fmt5_not_desc : NToWord FormatIdSz 5 <> FMT_DESC.
Proof. vm_compute. discriminate. Qed.
