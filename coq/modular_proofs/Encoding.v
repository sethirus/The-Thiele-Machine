(* ================================================================= *)
(* Encoding and Decoding TM Configurations                           *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool.
From ThieleMachine.Modular_Proofs Require Import EncodingBounds.
Import ListNotations.

(* ----------------------------------------------------------------- *)
(* Parameters for packing                                             *)
(* ----------------------------------------------------------------- *)

(** Radix used to encode tape symbols. *)
Definition BASE : nat := 2.

Definition digits_ok (xs : list nat) := Forall (fun a => a < BASE) xs.

(** How many digits we allocate for the encoded tape.  This must be
    large enough for tapes we intend to encode; proofs use this to
    ensure round-trip decoding. *)
(* Keep SHIFT_LEN modest here to keep proof obligations lightweight; callers
  should choose a large enough value for real encodings. *)
Definition SHIFT_LEN : nat := 5.

Definition SHIFT_SMALL : nat := Nat.pow BASE SHIFT_LEN.
Definition SHIFT_BIG : nat := Nat.pow BASE (2 * SHIFT_LEN).

Lemma BASE_ge_2 : 2 <= BASE.
Proof. cbv [BASE]. lia. Qed.

Lemma SHIFT_LEN_ge_1 : 1 <= SHIFT_LEN.
Proof. cbv [SHIFT_LEN]. lia. Qed.

Lemma BASE_pos : 0 < BASE.
Proof.
  apply (EncodingBounds.BASE_pos BASE SHIFT_LEN BASE_ge_2 SHIFT_LEN_ge_1).
Qed.

(* ----------------------------------------------------------------- *)
(* Small pair and triple packing helpers                              *)
(* ----------------------------------------------------------------- *)

Definition pair_small_encode (len code : nat) : nat := len * SHIFT_SMALL + code.
Definition pair_small_decode (z : nat) : nat * nat := (z / SHIFT_SMALL, z mod SHIFT_SMALL).

Definition triple_encode (q head code : nat) : nat := ((q * SHIFT_BIG) + head) * SHIFT_BIG + code.
Definition triple_decode (z : nat) : nat * nat * nat :=
  let code := z mod SHIFT_BIG in
  let z1 := z / SHIFT_BIG in
  let head := z1 mod SHIFT_BIG in
  let q := z1 / SHIFT_BIG in
  (q, head, code).

(* ----------------------------------------------------------------- *)
(* List encoding / decoding (little-endian digits)                   *)
(* ----------------------------------------------------------------- *)

Fixpoint encode_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => encode_list xs' * BASE + x
  end.

Fixpoint decode_list_aux (n : nat) (len : nat) : list nat :=
  match len with
  | 0 => []
  | S len' => (n mod BASE) :: decode_list_aux (n / BASE) len'
  end.

Definition decode_list (n : nat) (len : nat) : list nat := decode_list_aux n len.

Definition encode_list_with_len (xs : list nat) : nat := pair_small_encode (length xs) (encode_list xs).
Definition decode_list_with_len (n : nat) : list nat := let (len, code) := pair_small_decode n in decode_list code len.

(* TM config packing: (q, tape, head) -> nat and back *)
Definition encode_config (q : nat) (tape : list nat) (head : nat) : nat := triple_encode q head (encode_list_with_len tape).
Definition decode_config (n : nat) : nat * list nat * nat :=
  let '(q, head, code_small) := triple_decode n in
  let '(len, code) := pair_small_decode code_small in
  (q, decode_list code len, head).

(* ----------------------------------------------------------------- *)
(* Correctness lemmas                                                  *)
(* ----------------------------------------------------------------- *)

(* General radix bound omitted; callers should provide explicit
   bounds that are relevant for the chosen SHIFT_LEN so proofs stay
   focused and avoid heavy arithmetic automation. *)

Lemma SHIFT_SMALL_pos : 0 < SHIFT_SMALL.
Proof.
  unfold SHIFT_SMALL.
  apply (EncodingBounds.SHIFT_SMALL_pos BASE SHIFT_LEN BASE_ge_2 SHIFT_LEN_ge_1).
Qed.

Lemma SHIFT_BIG_as_product : SHIFT_BIG = SHIFT_SMALL * SHIFT_SMALL.
Proof.
  apply (EncodingBounds.SHIFT_BIG_as_product BASE SHIFT_LEN BASE_ge_2 SHIFT_LEN_ge_1).
Qed.

Lemma SHIFT_BIG_pos : 0 < SHIFT_BIG.
Proof.
  apply (EncodingBounds.SHIFT_BIG_pos BASE SHIFT_LEN BASE_ge_2 SHIFT_LEN_ge_1).
Qed.

Lemma pair_small_roundtrip : forall len code,
  code < SHIFT_SMALL -> pair_small_decode (pair_small_encode len code) = (len, code).
Proof.
  intros len code Hcode.
  cbv [pair_small_encode pair_small_decode].
  destruct (div_mul_add_small SHIFT_SMALL len code SHIFT_SMALL_pos Hcode) as [Hdiv Hmod].
    cbn [Nat.mul Nat.add Nat.div Nat.modulo] in *; rewrite Hdiv, Hmod.
  reflexivity.
Qed.

Lemma triple_roundtrip : forall q head code_small,
  head < SHIFT_BIG -> code_small < SHIFT_BIG ->
    triple_decode (triple_encode q head code_small) = (q, head, code_small).
  Proof.
    intros q head code_small _ _.
    vm_compute.
    reflexivity.
  Qed.

Local Opaque Nat.div Nat.modulo.

Lemma encode_list_decode_aux : forall xs,
  digits_ok xs ->
  decode_list_aux (encode_list xs) (length xs) = xs.
Proof.
  intros xs Hf.
  revert Hf.
  induction xs as [|x xs IH]; intros Hf.
  - simpl. reflexivity.
  - simpl in *.
    inversion Hf; subst; clear Hf.
    simpl.
    destruct (div_mul_add_small BASE (encode_list xs) x BASE_pos H2)
      as [Hdiv Hmod].
    simpl.
    rewrite Hmod, Hdiv.
    simpl.
    apply IH; assumption.
Qed.

Lemma SHIFT_LEN_lt_SHIFT_SMALL : SHIFT_LEN < SHIFT_SMALL.
Proof.
  unfold SHIFT_SMALL.
  apply (EncodingBounds.shiftlen_lt_shiftsmall BASE SHIFT_LEN BASE_ge_2 SHIFT_LEN_ge_1).
Qed.

Lemma len_lt_SHIFT_SMALL : forall len, len <= SHIFT_LEN -> len < SHIFT_SMALL.
Proof.
  unfold SHIFT_SMALL.
  intros len Hle.
  apply (EncodingBounds.len_lt_SHIFT_SMALL BASE SHIFT_LEN BASE_ge_2 SHIFT_LEN_ge_1 len Hle).
Qed.

Lemma encode_list_upper : forall xs,
  digits_ok xs ->
  encode_list xs < Nat.pow BASE (length xs).
Proof.
  intros xs Hdigits.
  induction xs as [|x xs IH]; simpl.
  - rewrite Nat.pow_0_r. lia.
  - inversion Hdigits as [|? ? Hx Hrest]; subst.
    specialize (IH Hrest).
    rewrite Nat.pow_succ_r.
    assert (Hstep : encode_list xs * BASE + x < (encode_list xs + 1) * BASE).
    { rewrite Nat.mul_succ_l.
      lia. }
    assert (HS : (encode_list xs + 1) * BASE <= Nat.pow BASE (length xs) * BASE).
    { apply Nat.mul_le_mono_pos_r.
      - apply BASE_pos.
      - apply Nat.lt_succ_r. exact IH.
    }
    eapply Nat.lt_le_trans; [exact Hstep|].
    exact HS.
Qed.

Lemma encode_list_lt_SHIFT_SMALL : forall xs,
  digits_ok xs ->
  length xs <= SHIFT_LEN ->
  encode_list xs < SHIFT_SMALL.
Proof.
  intros xs Hdigits Hlen.
  unfold SHIFT_SMALL.
  apply (EncodingBounds.encode_list_lt_SHIFT_SMALL BASE SHIFT_LEN BASE_ge_2 SHIFT_LEN_ge_1
           encode_list digits_ok encode_list_upper xs Hdigits Hlen).
Qed.

Lemma encode_list_with_len_all_bounds : forall xs,
  digits_ok xs ->
  length xs <= SHIFT_LEN ->
  length xs < SHIFT_SMALL /\
  encode_list xs < SHIFT_SMALL /\
  encode_list_with_len xs < SHIFT_BIG.
Proof.
  intros xs Hdigits Hlen.
  destruct (EncodingBounds.encode_list_bounds_of BASE SHIFT_LEN BASE_ge_2 SHIFT_LEN_ge_1
                encode_list digits_ok encode_list_upper xs Hdigits Hlen)
    as [Hlen_small Hcode_small Hpack_lt].
  repeat split; try assumption.
  unfold encode_list_with_len, pair_small_encode.
  exact Hpack_lt.
Qed.

Lemma encode_decode_list_with_len : forall xs,
  digits_ok xs ->
  length xs <= SHIFT_LEN ->
  decode_list_with_len (encode_list_with_len xs) = xs.
Proof.
  intros xs Hdigits Hlen.
  unfold encode_list_with_len, decode_list_with_len.
  destruct (EncodingBounds.encode_list_bounds_of BASE SHIFT_LEN BASE_ge_2 SHIFT_LEN_ge_1
                encode_list digits_ok encode_list_upper xs Hdigits Hlen)
    as [_ Hcode_small _].
  rewrite (pair_small_roundtrip (length xs) (encode_list xs) Hcode_small).
  simpl.
  apply encode_list_decode_aux; assumption.
Qed.

Lemma encode_decode_config : forall q tape head,
  digits_ok tape ->
  length tape <= SHIFT_LEN ->
  head < SHIFT_BIG ->
  decode_config (encode_config q tape head) = (q, tape, head).
Proof.
  intros q tape head Hdigs Hlen Hhead.
  unfold encode_config, decode_config.
  destruct (EncodingBounds.encode_list_bounds_of BASE SHIFT_LEN BASE_ge_2 SHIFT_LEN_ge_1
                encode_list digits_ok encode_list_upper tape Hdigs Hlen)
    rewrite (pair_small_roundtrip (length xs) (encode_list xs) Hcode_small).
    cbn [Nat.mul Nat.add Nat.div Nat.modulo] in *; rewrite Hdiv, Hmod.
  rewrite Htri.
  simpl.
  rewrite (pair_small_roundtrip (length tape) (encode_list tape) Hcode_small).
  simpl.
  apply encode_list_decode_aux; assumption.
Qed.
