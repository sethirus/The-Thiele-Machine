(** LegacyWordDecode.v: the word-lane decode identity for the ISA-v2 legacy
    encoding, over symbolic operand bytes. This is the missing piece
    [OutsideDomain.v]'s closing note names: reducing a decoded field
    ([dd_isa_version], [dd_opcode], ...) on a concrete instruction word with
    symbolic operands.

    The technique: work entirely through [wordToNat] ([wordToNat_combine],
    [wordToNat_split1], [wordToNat_split2], which reduce to plain [mod]/[div]
    on naturals), never through [split]/[combine] terms directly. The
    dependent-size casts that come from re-associating [split]/[combine] at
    boundaries that do not line up with [legacy_word]'s own nesting are what
    defeated earlier attempts; going through [wordToNat] and back via
    [wordToNat_eqw] avoids them entirely, since two words of the same size
    are equal whenever their [wordToNat] values are equal.

    The one real trap: [ring], [nia] and [exact]'s conversion check must
    never be asked to relate two forms of a term containing an unevaluated
    [pow2 n] for large [n] (here, 89, 96 or 121) -- the kernel represents
    [nat] in unary, so normalizing [pow2 89] this way does not finish. Every
    proof below stays on plain [rewrite] with named facts near such terms,
    and only lets [ring]/[nia] touch [pow2 8]/[16]/[24]/[32] (safe: bounded
    by concrete products of 256, already computed in [H8]-[H32]). *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String NArith Arith Lia Nnat.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext
  BoundaryDecoded RuleStep DispatchLets StepEval.
Require Import Kami.Lib.NatLib.

Local Open Scope nat_scope.

Lemma wordToNat_eqw : forall sz (w1 w2 : word sz),
  wordToNat w1 = wordToNat w2 -> w1 = w2.
Proof.
  intros sz w1 w2 H.
  rewrite <- (@natToWord_wordToNat sz w1).
  rewrite <- (@natToWord_wordToNat sz w2).
  rewrite H.
  reflexivity.
Qed.

(** Definitional forms: [evalUniBit] on [Trunc]/[ConstExtract] unfolds to
    [split1]/[split2] by conversion; recorded once so later proofs cite a
    stable name instead of re-unfolding [evalExpr]/[evalUniBit] each time. *)
Lemma dd_isa_version_form : forall b w,
  dd_isa_version b w = split2 120 8 (split1 (120+8) 0 w).
Proof. intros. reflexivity. Qed.

Lemma dd_legacy_instr_form : forall b w,
  dd_legacy_instr b w = split1 32 96 w.
Proof. intros. reflexivity. Qed.

Lemma dd_opcode_form : forall b w,
  dd_opcode b w = split2 24 8 (split1 (24+8) 0 (dd_legacy_instr b w)).
Proof. intros. reflexivity. Qed.

Lemma dd_op_a_form : forall b w,
  dd_op_a b w = split2 16 8 (split1 (16+8) 8 (dd_legacy_instr b w)).
Proof. intros. reflexivity. Qed.

Lemma dd_op_b_form : forall b w,
  dd_op_b b w = split2 8 8 (split1 (8+8) 16 (dd_legacy_instr b w)).
Proof. intros. reflexivity. Qed.

Lemma dd_cost_v_form : forall b w,
  dd_cost_v b w = split1 8 24 (dd_legacy_instr b w).
Proof. intros. reflexivity. Qed.

Lemma dd_format_id_form : forall b w,
  dd_format_id b w = split2 112 FormatIdSz (split1 (112+FormatIdSz) 8 w).
Proof. intros. reflexivity. Qed.

Lemma dd_flags_form : forall b w,
  dd_flags b w = split2 96 16 (split1 (96+16) 16 w).
Proof. intros. reflexivity. Qed.

Lemma legacy_word_form : forall op a b c,
  legacy_word op a b c
  = combine c (combine b (combine a (combine op (NToWord 96 (N.shiftl 2 88))))).
Proof. intros. reflexivity. Qed.

Lemma pow2_nz : forall n, pow2 n <> 0.
Proof. intros n. apply Nat.pow_nonzero. discriminate. Qed.

(** The top-96-bit constant (encodes ISA version 2 at bit 120) as a nat. *)
Lemma top96_nat : wordToNat (NToWord 96 (N.shiftl 2 88)) = pow2 89.
Proof.
  rewrite NToWord_nat.
  assert (Hn : nat_of_N (N.shiftl 2 88) = pow2 89).
  { change (N.shiftl 2 88) with (2 * 2 ^ 88)%N.
    rewrite <- (N.pow_succ_r' 2 88).
    change (N.succ 88) with 89%N.
    rewrite N2Nat.inj_pow.
    reflexivity. }
  rewrite Hn.
  apply (@wordToNat_natToWord_2 96).
  apply Nat.pow_lt_mono_r; lia.
Qed.

Lemma H8 : pow2 8 = 256. Proof. reflexivity. Qed.
Lemma H16 : pow2 16 = 256 * 256.
Proof. change (pow2 16) with (pow2 (8 + 8)). rewrite pow2_add_mul, H8. reflexivity. Qed.
Lemma H24 : pow2 24 = 256 * 256 * 256.
Proof. change (pow2 24) with (pow2 (8 + 16)). rewrite pow2_add_mul, H8, H16. ring. Qed.
Lemma H32 : pow2 32 = 256 * 256 * 256 * 256.
Proof. change (pow2 32) with (pow2 (16 + 16)). rewrite pow2_add_mul, H16. ring. Qed.
Lemma H121 : pow2 121 = pow2 32 * pow2 89.
Proof. rewrite <- pow2_add_mul. reflexivity. Qed.

Lemma expand4 : forall c b a o V,
  c + pow2 8*(b + pow2 8*(a + pow2 8*(o + pow2 8*V)))
  = c + (pow2 8*b + (pow2 16*a + (pow2 24*o + pow2 32*V))).
Proof.
  intros c b a o V.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  reflexivity.
Qed.

Lemma lanes_below32 : forall c b a o,
  c < pow2 8 -> b < pow2 8 -> a < pow2 8 -> o < pow2 8 ->
  c + pow2 8*b + pow2 16*a + pow2 24*o < pow2 32.
Proof. intros. rewrite H8, H16, H24, H32 in *. nia. Qed.

Lemma lanes_below24 : forall c b a,
  c < pow2 8 -> b < pow2 8 -> a < pow2 8 ->
  c + pow2 8*b + pow2 16*a < pow2 24.
Proof. intros. rewrite H8, H16, H24 in *. nia. Qed.

Lemma lanes_below16 : forall c b,
  c < pow2 8 -> b < pow2 8 -> c + pow2 8*b < pow2 16.
Proof. intros. rewrite H8, H16 in *. nia. Qed.

(** The whole 128-bit word as a flat nat lane sum. *)
Lemma legacy_word_nat : forall (op a b c : word 8),
  wordToNat (legacy_word op a b c)
  = wordToNat c + pow2 8 * wordToNat b + pow2 16 * wordToNat a
    + pow2 24 * wordToNat op + pow2 121.
Proof.
  intros op a b c.
  rewrite legacy_word_form.
  rewrite (@wordToNat_combine 8 c 120).
  rewrite (@wordToNat_combine 8 b 112).
  rewrite (@wordToNat_combine 8 a 104).
  rewrite (@wordToNat_combine 8 op 96).
  rewrite top96_nat.
  rewrite H121.
  rewrite (expand4 (wordToNat c) (wordToNat b) (wordToNat a) (wordToNat op) (pow2 89)).
  rewrite ! Nat.add_assoc.
  reflexivity.
Qed.

Lemma legacy_word_low32_nat : forall (op a b c : word 8),
  (wordToNat c + pow2 8 * wordToNat b + pow2 16 * wordToNat a + pow2 24 * wordToNat op)
  < pow2 32.
Proof. intros. apply lanes_below32; apply wordToNat_bound. Qed.

Lemma mod_add_pow2 : forall K x y, (x + pow2 K * y) mod pow2 K = x mod pow2 K.
Proof. intros. rewrite Nat.mul_comm. apply Nat.Div0.mod_add. Qed.

Lemma mod_add_mul32 : forall x y, (x + pow2 32 * y) mod pow2 32 = x mod pow2 32.
Proof. intros. apply mod_add_pow2. Qed.

Lemma expand3 : forall c b a o,
  c + pow2 8*(b + pow2 8*(a + pow2 8*o)) = c + (pow2 8*b + (pow2 16*a + pow2 24*o)).
Proof.
  intros c b a o.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  rewrite Nat.mul_add_distr_l, Nat.mul_assoc, <- pow2_add_mul.
  reflexivity.
Qed.

Lemma expand3' : forall c b a o,
  c + pow2 8*(b + pow2 8*(a + pow2 8*o)) = c + pow2 8*b + pow2 16*a + pow2 24*o.
Proof. intros. rewrite expand3. rewrite ! Nat.add_assoc. reflexivity. Qed.

(** [dd_legacy_instr]: the low 32-bit legacy lane, as a 4-byte combine. *)
Lemma dd_legacy_instr_correct : forall bd (op a b c : word 8),
  dd_legacy_instr bd (legacy_word op a b c)
  = combine c (combine b (combine a op)).
Proof.
  intros bd op a b c.
  apply wordToNat_eqw.
  rewrite dd_legacy_instr_form.
  rewrite (@wordToNat_split1 32 96).
  rewrite legacy_word_nat, H121, mod_add_mul32.
  rewrite (Nat.mod_small _ (pow2 32)) by apply legacy_word_low32_nat.
  rewrite (@wordToNat_combine 8 c 24).
  rewrite (@wordToNat_combine 8 b 16).
  rewrite (@wordToNat_combine 8 a 8).
  rewrite expand3.
  ring.
Qed.

Lemma legacy_low32_flat : forall (op a b c : word 8),
  wordToNat (combine c (combine b (combine a op)))
  = wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a + pow2 24*wordToNat op.
Proof.
  intros op a b c.
  rewrite (@wordToNat_combine 8 c 24), (@wordToNat_combine 8 b 16), (@wordToNat_combine 8 a 8).
  apply expand3'.
Qed.

Lemma div_small_add : forall M v D, M < D -> (M + D*v)/D = v.
Proof.
  intros M v D Hlt.
  assert (Hnz : D <> 0) by lia.
  rewrite Nat.mul_comm, (Nat.div_add M v D Hnz), Nat.div_small; auto.
Qed.

Lemma H24_16_8 : pow2 24 = pow2 16 * pow2 8.
Proof. change (pow2 24) with (pow2 (16+8)). apply pow2_add_mul. Qed.

(** Low-word fields: opcode, op_a, op_b, cost. Every intermediate value stays
    below [pow2 32], so [ring]/[nia] never touch a large [pow2] exponent. *)

Lemma dd_op_correct : forall bd (op a b c : word 8),
  dd_opcode bd (legacy_word op a b c) = op.
Proof.
  intros bd op a b c.
  apply wordToNat_eqw.
  rewrite dd_opcode_form, dd_legacy_instr_correct.
  rewrite (@wordToNat_split2 24 8), (@wordToNat_split1 32 0), legacy_low32_flat.
  rewrite (Nat.mod_small
    (wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a + pow2 24*wordToNat op)
    (pow2 32))
    by (apply lanes_below32; apply wordToNat_bound).
  apply div_small_add.
  apply lanes_below24; apply wordToNat_bound.
Qed.

Lemma dd_a_correct : forall bd (op a b c : word 8),
  dd_op_a bd (legacy_word op a b c) = a.
Proof.
  intros bd op a b c.
  apply wordToNat_eqw.
  rewrite dd_op_a_form, dd_legacy_instr_correct.
  rewrite (@wordToNat_split2 16 8), (@wordToNat_split1 24 8), legacy_low32_flat.
  rewrite (mod_add_pow2 24
    (wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a) (wordToNat op)).
  rewrite (Nat.mod_small
    (wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a) (pow2 24))
    by (apply lanes_below24; apply wordToNat_bound).
  apply div_small_add.
  apply lanes_below16; apply wordToNat_bound.
Qed.

Lemma dd_b_correct : forall bd (op a b c : word 8),
  dd_op_b bd (legacy_word op a b c) = b.
Proof.
  intros bd op a b c.
  apply wordToNat_eqw.
  rewrite dd_op_b_form, dd_legacy_instr_correct.
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

Lemma dd_c_correct : forall bd (op a b c : word 8),
  dd_cost_v bd (legacy_word op a b c) = c.
Proof.
  intros bd op a b c.
  apply wordToNat_eqw.
  rewrite dd_cost_v_form, dd_legacy_instr_correct.
  rewrite (@wordToNat_split1 8 24).
  rewrite (@wordToNat_combine 8 c 24).
  rewrite mod_add_pow2.
  apply Nat.mod_small, wordToNat_bound.
Qed.

(** Header fields: only the top 96 bits matter, so these go through
    [legacy_word_nat] directly rather than [dd_legacy_instr_correct]. Every
    step stays a plain [rewrite] on named facts; nothing here lets [ring],
    [nia] or [exact]'s conversion check touch a term still holding an
    unevaluated [pow2 89]/[pow2 96]/[pow2 112]/[pow2 120]/[pow2 121]. *)

Lemma pow2_le : forall a b, a <= b -> pow2 a <= pow2 b.
Proof.
  intros a b Hab.
  replace b with (a + (b - a)) by lia.
  rewrite pow2_add_mul.
  pose proof (pow2_nz (b - a)).
  nia.
Qed.

Lemma N_below_120 : forall (op a b c : word 8),
  wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a + pow2 24*wordToNat op
  < pow2 120.
Proof.
  intros.
  eapply Nat.lt_le_trans.
  - apply lanes_below32; apply wordToNat_bound.
  - apply pow2_le. lia.
Qed.

Lemma H121_120 : pow2 121 = pow2 120 * pow2 1.
Proof. change (pow2 121) with (pow2 (120+1)). apply pow2_add_mul. Qed.

Lemma H121_112 : pow2 121 = pow2 112 * pow2 9.
Proof. change (pow2 121) with (pow2 (112+9)). apply pow2_add_mul. Qed.

Lemma dd_isa_version_correct : forall bd (op a b c : word 8),
  dd_isa_version bd (legacy_word op a b c) = natToWord 8 2.
Proof.
  intros bd op a b c.
  apply wordToNat_eqw.
  rewrite (@wordToNat_natToWord_2 8 2) by (rewrite H8; lia).
  rewrite dd_isa_version_form.
  rewrite (@wordToNat_split2 120 8), (@wordToNat_split1 128 0).
  rewrite (Nat.mod_small _ (pow2 128)) by apply wordToNat_bound.
  rewrite legacy_word_nat, H121_120.
  rewrite (div_small_add
    (wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a + pow2 24*wordToNat op)
    (pow2 1) (pow2 120)) by apply N_below_120.
  reflexivity.
Qed.

Lemma dd_format_id_correct : forall bd (op a b c : word 8),
  dd_format_id bd (legacy_word op a b c) = FMT_LEGACY.
Proof.
  intros bd op a b c.
  apply wordToNat_eqw.
  rewrite dd_format_id_form.
  rewrite (@wordToNat_split2 112 FormatIdSz), (@wordToNat_split1 120 8).
  rewrite legacy_word_nat, H121_120.
  rewrite (mod_add_pow2 120
    (wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a + pow2 24*wordToNat op)
    (pow2 1)).
  rewrite (Nat.mod_small _ (pow2 120)) by apply N_below_120.
  rewrite (Nat.div_small _ (pow2 112))
    by (eapply Nat.lt_le_trans; [apply lanes_below32; apply wordToNat_bound
        | apply pow2_le; lia]).
  reflexivity.
Qed.

Lemma dd_flags_correct : forall bd (op a b c : word 8),
  dd_flags bd (legacy_word op a b c) = natToWord 16 0.
Proof.
  intros bd op a b c.
  apply wordToNat_eqw.
  rewrite (@wordToNat_natToWord_2 16 0) by (rewrite H16; lia).
  rewrite dd_flags_form.
  rewrite (@wordToNat_split2 96 16), (@wordToNat_split1 112 16).
  rewrite legacy_word_nat, H121_112.
  rewrite (mod_add_pow2 112
    (wordToNat c + pow2 8*wordToNat b + pow2 16*wordToNat a + pow2 24*wordToNat op)
    (pow2 9)).
  rewrite (Nat.mod_small _ (pow2 112))
    by (eapply Nat.lt_le_trans; [apply lanes_below32; apply wordToNat_bound
        | apply pow2_le; lia]).
  apply Nat.div_small.
  eapply Nat.lt_le_trans; [apply lanes_below32; apply wordToNat_bound
        | apply pow2_le; lia].
Qed.
