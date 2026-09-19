(** RichWordDecode.v: the word-lane decode identity generalized to all six
    ISA-v2 instruction-word encodings, not just legacy.

    [LegacyWordDecode.v] proved the decode identity for [legacy_word], whose
    top 96 bits are a fixed constant (isa_version=2, format_id=FMT_LEGACY,
    flags=0, everything else 0). Reading [DispatchLets.v]'s field extractors
    directly shows the six formats do not actually have different bit
    layouts: every one of [dd_isa_version]/[dd_format_id]/[dd_flags]/
    [dd_ext0]/[dd_opcode]/[dd_op_a]/[dd_op_b]/[dd_cost_v] is a fixed
    [ConstExtract] at a fixed absolute bit range, independent of what
    [format_id] happens to decode to -- only the *interpretation* of those
    ranges (what a rich-format opcode does with [dd_ext0], say) depends on
    the format. So instead of five per-encoding word constructors and five
    lane-arithmetic files, one general constructor covers all six: [rich_word]
    takes the five header fields explicitly (isa_version, format_id, flags,
    a 32-bit reserved lane nothing reads, and the 32-bit ext0 operand lane)
    plus the same four legacy operand bytes.

    Same technique as [LegacyWordDecode.v] throughout: [wordToNat_combine]
    only, never [split]/[combine] terms directly; keep every large [pow2]
    exponent as an explicit product of [pow2 8]/[16]/[24]/[32] via
    [pow2_add_mul], and never let [ring]/[nia]/[exact]'s conversion check see
    an unevaluated large exponent or a raw large decimal literal. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String NArith Arith Lia Nnat.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext
  BoundaryDecoded RuleStep DispatchLets StepEval LegacyWordDecode.
Require Import Kami.Lib.NatLib.

Local Open Scope nat_scope.

(** The top 96 bits, general: isa_version, format_id, flags, a 32-bit
    reserved lane no [dd_*] accessor reads, and the 32-bit ext0 operand
    lane, packed exactly where [DispatchLets.v]'s [ConstExtract] calls
    expect them (absolute bits 120-127, 112-119, 96-111, 64-95, 32-63). *)
Definition rich_top96 (isa : word 8) (fid : word FormatIdSz) (flags : word 16)
    (reserved : word 32) (ext0 : word WordSz) : word 96 :=
  combine ext0 (combine reserved (combine flags (combine fid isa))).

Definition rich_word (isa : word 8) (fid : word FormatIdSz) (flags : word 16)
    (reserved : word 32) (ext0 : word WordSz) (op a b c : word 8) : word InstrSz :=
  combine c (combine b (combine a (combine op (rich_top96 isa fid flags reserved ext0)))).

Lemma H64 : pow2 64 = pow2 32 * pow2 32.
Proof. change (pow2 64) with (pow2 (32+32)). apply pow2_add_mul. Qed.
Lemma H80 : pow2 80 = pow2 64 * pow2 16.
Proof. change (pow2 80) with (pow2 (64+16)). apply pow2_add_mul. Qed.
Lemma H88 : pow2 88 = pow2 80 * pow2 8.
Proof. change (pow2 88) with (pow2 (80+8)). apply pow2_add_mul. Qed.
Lemma H96 : pow2 96 = pow2 64 * pow2 32.
Proof. change (pow2 96) with (pow2 (64+32)). apply pow2_add_mul. Qed.
Lemma H112 : pow2 112 = pow2 96 * pow2 16.
Proof. change (pow2 112) with (pow2 (96+16)). apply pow2_add_mul. Qed.
Lemma H120 : pow2 120 = pow2 112 * pow2 8.
Proof. change (pow2 120) with (pow2 (112+8)). apply pow2_add_mul. Qed.

(** Direct (non-cascading) relations used only to fold a multi-term tail
    into one [pow2 K * (...)] factor before [mod_add_pow2]/[div_small_add]:
    each states its target exponent as [pow2] of the *specific* boundary
    being peeled plus a remainder, so a single [rewrite] on each produces a
    common factor without leaving an intermediate exponent (64, 96, 112)
    unreduced for a later rewrite to miss. *)
Lemma H112_from64 : pow2 112 = pow2 64 * pow2 48.
Proof. change (pow2 112) with (pow2 (64+48)). apply pow2_add_mul. Qed.
Lemma H120_from64 : pow2 120 = pow2 64 * pow2 56.
Proof. change (pow2 120) with (pow2 (64+56)). apply pow2_add_mul. Qed.
Lemma H120_from96 : pow2 120 = pow2 96 * pow2 24.
Proof. change (pow2 120) with (pow2 (96+24)). apply pow2_add_mul. Qed.

(** The 96-bit header lane as a flat nat sum, relative to its own frame
    (bit 0 = absolute bit 32). *)
Lemma rich_top96_nat : forall (isa : word 8) (fid : word FormatIdSz) (flags : word 16)
    (reserved : word 32) (ext0 : word WordSz),
  wordToNat (rich_top96 isa fid flags reserved ext0)
  = wordToNat ext0 + pow2 32 * wordToNat reserved + pow2 64 * wordToNat flags
    + pow2 80 * wordToNat fid + pow2 88 * wordToNat isa.
Proof.
  intros isa fid flags reserved ext0.
  unfold rich_top96.
  rewrite (@wordToNat_combine WordSz ext0 64).
  rewrite (@wordToNat_combine 32 reserved 32).
  rewrite (@wordToNat_combine 16 flags 16).
  rewrite (@wordToNat_combine FormatIdSz fid 8).
  change WordSz with 32. change FormatIdSz with 8.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  rewrite ! Nat.add_assoc.
  reflexivity.
Qed.

(** The whole word, low 32-bit lane left symbolic (mirrors [legacy_word_nat]
    exactly, with the fixed top-96 constant replaced by the general
    [rich_top96] value). *)
Lemma rich_word_nat_factored : forall (isa : word 8) (fid : word FormatIdSz) (flags : word 16)
    (reserved : word 32) (ext0 : word WordSz) (op a b c : word 8),
  wordToNat (rich_word isa fid flags reserved ext0 op a b c)
  = wordToNat c + pow2 8 * wordToNat b + pow2 16 * wordToNat a + pow2 24 * wordToNat op
    + pow2 32 * wordToNat (rich_top96 isa fid flags reserved ext0).
Proof.
  intros isa fid flags reserved ext0 op a b c.
  unfold rich_word.
  rewrite (@wordToNat_combine 8 c 120).
  rewrite (@wordToNat_combine 8 b 112).
  rewrite (@wordToNat_combine 8 a 104).
  rewrite (@wordToNat_combine 8 op 96).
  rewrite (expand4 (wordToNat c) (wordToNat b) (wordToNat a) (wordToNat op)
    (wordToNat (rich_top96 isa fid flags reserved ext0))).
  rewrite ! Nat.add_assoc.
  reflexivity.
Qed.

(** The whole 128-bit word as a flat nat lane sum. *)
Lemma rich_word_nat : forall (isa : word 8) (fid : word FormatIdSz) (flags : word 16)
    (reserved : word 32) (ext0 : word WordSz) (op a b c : word 8),
  wordToNat (rich_word isa fid flags reserved ext0 op a b c)
  = wordToNat c + pow2 8 * wordToNat b + pow2 16 * wordToNat a + pow2 24 * wordToNat op
    + pow2 32 * wordToNat ext0 + pow2 64 * wordToNat reserved + pow2 96 * wordToNat flags
    + pow2 112 * wordToNat fid + pow2 120 * wordToNat isa.
Proof.
  intros isa fid flags reserved ext0 op a b c.
  rewrite rich_word_nat_factored, rich_top96_nat.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  rewrite ! Nat.add_assoc.
  reflexivity.
Qed.

Lemma rich_word_low32_nat : forall (op a b c : word 8),
  (wordToNat c + pow2 8 * wordToNat b + pow2 16 * wordToNat a + pow2 24 * wordToNat op)
  < pow2 32.
Proof. intros. apply lanes_below32; apply wordToNat_bound. Qed.

(** [dd_legacy_instr] is the low 32-bit lane for every encoding, not just
    legacy: it is a plain [Trunc] on the raw word, oblivious to format. *)
Lemma rich_legacy_instr_correct : forall bd (isa : word 8) (fid : word FormatIdSz)
    (flags : word 16) (reserved : word 32) (ext0 : word WordSz) (op a b c : word 8),
  dd_legacy_instr bd (rich_word isa fid flags reserved ext0 op a b c)
  = combine c (combine b (combine a op)).
Proof.
  intros bd isa fid flags reserved ext0 op a b c.
  apply wordToNat_eqw.
  rewrite dd_legacy_instr_form.
  rewrite (@wordToNat_split1 32 96).
  rewrite rich_word_nat_factored, mod_add_mul32.
  rewrite (Nat.mod_small _ (pow2 32)) by apply rich_word_low32_nat.
  rewrite (@wordToNat_combine 8 c 24), (@wordToNat_combine 8 b 16), (@wordToNat_combine 8 a 8).
  rewrite expand3'.
  reflexivity.
Qed.

(** Low-word fields: opcode, op_a, op_b, cost. Identical statements and
    proofs to [LegacyWordDecode]'s, since [dd_legacy_instr] does not depend
    on the format. *)

Lemma rw_op_correct : forall bd (isa : word 8) (fid : word FormatIdSz) (flags : word 16)
    (reserved : word 32) (ext0 : word WordSz) (op a b c : word 8),
  dd_opcode bd (rich_word isa fid flags reserved ext0 op a b c) = op.
Proof.
  intros bd isa fid flags reserved ext0 op a b c.
  apply wordToNat_eqw.
  rewrite dd_opcode_form, rich_legacy_instr_correct.
  rewrite (@wordToNat_split2 24 8), (@wordToNat_split1 32 0), legacy_low32_flat.
  rewrite (Nat.mod_small
    (wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a + pow2 24*wordToNat op)
    (pow2 32))
    by (apply lanes_below32; apply wordToNat_bound).
  apply div_small_add.
  apply lanes_below24; apply wordToNat_bound.
Qed.

Lemma rw_a_correct : forall bd (isa : word 8) (fid : word FormatIdSz) (flags : word 16)
    (reserved : word 32) (ext0 : word WordSz) (op a b c : word 8),
  dd_op_a bd (rich_word isa fid flags reserved ext0 op a b c) = a.
Proof.
  intros bd isa fid flags reserved ext0 op a b c.
  apply wordToNat_eqw.
  rewrite dd_op_a_form, rich_legacy_instr_correct.
  rewrite (@wordToNat_split2 16 8), (@wordToNat_split1 24 8), legacy_low32_flat.
  rewrite (mod_add_pow2 24
    (wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a) (wordToNat op)).
  rewrite (Nat.mod_small
    (wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a) (pow2 24))
    by (apply lanes_below24; apply wordToNat_bound).
  apply div_small_add.
  apply lanes_below16; apply wordToNat_bound.
Qed.

Lemma rw_b_correct : forall bd (isa : word 8) (fid : word FormatIdSz) (flags : word 16)
    (reserved : word 32) (ext0 : word WordSz) (op a b c : word 8),
  dd_op_b bd (rich_word isa fid flags reserved ext0 op a b c) = b.
Proof.
  intros bd isa fid flags reserved ext0 op a b c.
  apply wordToNat_eqw.
  rewrite dd_op_b_form, rich_legacy_instr_correct.
  rewrite (@wordToNat_split2 8 8), (@wordToNat_split1 16 16), legacy_low32_flat.
  rewrite H24_16_8, <- (Nat.mul_assoc (pow2 16) (pow2 8) (wordToNat op)).
  rewrite (mod_add_pow2 16
    (wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a)
    (pow2 8*wordToNat op)).
  rewrite (mod_add_pow2 16 (wordToNat c + pow2 8*wordToNat b) (wordToNat a)).
  rewrite (Nat.mod_small
    (wordToNat c + pow2 8*wordToNat b) (pow2 16))
    by (apply lanes_below16; apply wordToNat_bound).
  apply div_small_add.
  apply wordToNat_bound.
Qed.

Lemma rw_c_correct : forall bd (isa : word 8) (fid : word FormatIdSz) (flags : word 16)
    (reserved : word 32) (ext0 : word WordSz) (op a b c : word 8),
  dd_cost_v bd (rich_word isa fid flags reserved ext0 op a b c) = c.
Proof.
  intros bd isa fid flags reserved ext0 op a b c.
  apply wordToNat_eqw.
  rewrite dd_cost_v_form, rich_legacy_instr_correct.
  rewrite (@wordToNat_split1 8 24).
  rewrite (@wordToNat_combine 8 c 24).
  rewrite mod_add_pow2.
  apply Nat.mod_small, wordToNat_bound.
Qed.

(** Header fields: isa_version, format_id, flags, ext0. Each is bounded
    below its own frame using the same "everything above vanishes mod,
    everything below is small enough to survive Nat.mod_small" pattern
    [LegacyWordDecode]'s header proofs use, now against the general
    [rich_word_nat] sum instead of a single folded constant. *)

(** A clean, variable-only nonlinear bound: [nia] fails to find this
    directly when [low] is left as the compound sum it actually is in the
    call sites below (a four-term [wordToNat] expression confuses its
    product-hint heuristic), but succeeds once the shape is abstracted to
    plain nat variables first. *)
Lemma bound_mul_add : forall (P Q low y : nat), low < P -> y < Q -> low + P * y < P * Q.
Proof. nia. Qed.

Lemma rw_below64 : forall (op a b c : word 8) (ext0 : word WordSz),
  wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a + pow2 24*wordToNat op
    + pow2 32 * wordToNat ext0 < pow2 64.
Proof.
  intros op a b c ext0.
  pose proof (rich_word_low32_nat op a b c) as Hlow.
  pose proof (wordToNat_bound ext0) as Hext0.
  change WordSz with 32 in Hext0.
  rewrite H64.
  apply bound_mul_add; assumption.
Qed.

(** Header fields are extracted by peeling [rich_top96]'s own natural
    [combine] nesting one level at a time (ext0, then reserved, then flags,
    then the final fid/isa pair), the same technique [rich_top96_nat] and
    [rich_word_nat] already use, stopping as soon as the target field's own
    coefficient is exposed rather than flattening all the way down. A
    left-associated flat sum (as [rich_word_nat] gives) cannot be refactored
    back into a common-factor form by [rewrite <- Nat.mul_add_distr_l]: in
    [(((A+B)+C)+D)], the addend pairs [rewrite] actually finds adjacent are
    never the [B,C] or [C,D] this needs, since everything before an addend
    is bundled into its left sibling. Working forward from the natural
    nesting sidesteps that entirely. *)

Lemma rw_ext0_correct : forall bd (isa : word 8) (fid : word FormatIdSz) (flags : word 16)
    (reserved : word 32) (ext0 : word WordSz) (op a b c : word 8),
  dd_ext0 bd (rich_word isa fid flags reserved ext0 op a b c) = ext0.
Proof.
  intros bd isa fid flags reserved ext0 op a b c.
  apply wordToNat_eqw.
  unfold dd_ext0.
  cbn [evalExpr evalUniBit].
  change WordSz with 32.
  rewrite (@wordToNat_split2 32 32), (@wordToNat_split1 64 64).
  rewrite rich_word_nat_factored.
  unfold rich_top96.
  rewrite (@wordToNat_combine WordSz ext0 64).
  change WordSz with 32.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  cbn [Nat.add].
  rewrite Nat.add_assoc.
  rewrite mod_add_pow2.
  rewrite (Nat.mod_small _ (pow2 64)) by (apply rw_below64).
  apply div_small_add.
  apply rich_word_low32_nat.
Qed.

Lemma rw_below96 : forall (op a b c : word 8) (ext0 : word WordSz) (reserved : word 32),
  wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a + pow2 24*wordToNat op
    + pow2 32 * wordToNat ext0 + pow2 64 * wordToNat reserved < pow2 96.
Proof.
  intros op a b c ext0 reserved.
  pose proof (rw_below64 op a b c ext0) as Hlow.
  pose proof (wordToNat_bound reserved) as Hres.
  rewrite H96.
  apply bound_mul_add; assumption.
Qed.

Lemma rw_below112 : forall (op a b c : word 8) (ext0 : word WordSz) (reserved : word 32)
    (flags : word 16),
  wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a + pow2 24*wordToNat op
    + pow2 32 * wordToNat ext0 + pow2 64 * wordToNat reserved + pow2 96 * wordToNat flags
  < pow2 112.
Proof.
  intros op a b c ext0 reserved flags.
  pose proof (rw_below96 op a b c ext0 reserved) as Hlow.
  pose proof (wordToNat_bound flags) as Hflags.
  rewrite H112.
  apply bound_mul_add; assumption.
Qed.

Lemma rw_flags_correct : forall bd (isa : word 8) (fid : word FormatIdSz) (flags : word 16)
    (reserved : word 32) (ext0 : word WordSz) (op a b c : word 8),
  dd_flags bd (rich_word isa fid flags reserved ext0 op a b c) = flags.
Proof.
  intros bd isa fid flags reserved ext0 op a b c.
  apply wordToNat_eqw.
  rewrite dd_flags_form.
  rewrite (@wordToNat_split2 96 16), (@wordToNat_split1 112 16).
  rewrite rich_word_nat_factored.
  unfold rich_top96.
  rewrite (@wordToNat_combine WordSz ext0 64).
  rewrite (@wordToNat_combine 32 reserved 32).
  rewrite (@wordToNat_combine 16 flags 16).
  change WordSz with 32.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  cbn [Nat.add].
  rewrite ! Nat.add_assoc.
  rewrite mod_add_pow2.
  rewrite (Nat.mod_small _ (pow2 112)) by (apply rw_below112).
  apply div_small_add.
  apply rw_below96.
Qed.

Lemma rw_below120 : forall (op a b c : word 8) (ext0 : word WordSz) (reserved : word 32)
    (flags : word 16) (fid : word FormatIdSz),
  wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a + pow2 24*wordToNat op
    + pow2 32 * wordToNat ext0 + pow2 64 * wordToNat reserved + pow2 96 * wordToNat flags
    + pow2 112 * wordToNat fid
  < pow2 120.
Proof.
  intros op a b c ext0 reserved flags fid.
  pose proof (rw_below112 op a b c ext0 reserved flags) as Hlow.
  pose proof (wordToNat_bound fid) as Hfid.
  change FormatIdSz with 8 in Hfid.
  rewrite H120.
  apply bound_mul_add; assumption.
Qed.

(** [dd_format_id] is [ConstExtract 112 FormatIdSz 8]: mod pow2 120 *first*
    (dropping isa), *then* div pow2 112 (dropping fid) -- the opposite order
    of what the field's own bit position might suggest. Since
    [rich_word_nat]'s fully flat form already isolates isa as its trailing
    addend, no regrouping is needed at all here, exactly as for
    [rw_isa_correct] below. *)
Lemma rw_format_correct : forall bd (isa : word 8) (fid : word FormatIdSz) (flags : word 16)
    (reserved : word 32) (ext0 : word WordSz) (op a b c : word 8),
  dd_format_id bd (rich_word isa fid flags reserved ext0 op a b c) = fid.
Proof.
  intros bd isa fid flags reserved ext0 op a b c.
  apply wordToNat_eqw.
  rewrite dd_format_id_form.
  rewrite (@wordToNat_split2 112 FormatIdSz), (@wordToNat_split1 120 8).
  change FormatIdSz with 8.
  rewrite rich_word_nat.
  rewrite mod_add_pow2.
  rewrite (Nat.mod_small _ (pow2 120)) by (apply rw_below120).
  apply div_small_add.
  apply rw_below112.
Qed.

Lemma rw_isa_correct : forall bd (isa : word 8) (fid : word FormatIdSz) (flags : word 16)
    (reserved : word 32) (ext0 : word WordSz) (op a b c : word 8),
  dd_isa_version bd (rich_word isa fid flags reserved ext0 op a b c) = isa.
Proof.
  intros bd isa fid flags reserved ext0 op a b c.
  apply wordToNat_eqw.
  rewrite dd_isa_version_form.
  rewrite (@wordToNat_split2 120 8), (@wordToNat_split1 128 0).
  rewrite (Nat.mod_small _ (pow2 128)) by apply wordToNat_bound.
  rewrite rich_word_nat.
  apply div_small_add.
  apply rw_below120.
Qed.
