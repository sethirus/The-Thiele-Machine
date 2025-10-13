From Coq Require Import Arith.Arith Arith.PeanoNat micromega.Lia.
From Coq Require Import Lists.List.

Lemma pow2_gt_succ : forall n, S n < Nat.pow 2 (S n).
Proof.
  intro n.
  induction n as [|n IH]; simpl; [lia|].
  assert (Hle : S (S n) <= 2 * S n) by lia.
  assert (Hlt : 2 * S n < 2 * Nat.pow 2 (S n)).
  { apply Nat.mul_lt_mono_pos_l; [lia|exact IH]. }
  eapply Nat.le_lt_trans; [exact Hle|exact Hlt].
Qed.

(** * Encoding mini-sandbox

    This sandbox file is intentionally decoupled from the main
    [modular_proofs] development.  It hosts the atomic arithmetic
    lemmas that will later be promoted into a dedicated helper module
    once they are individually validated.  Each lemma corresponds to a
    checkbox in [docs/encoding/02-GOALS.todo.md]. *)

Section EncodingMini.
  Context {BASE SHIFT_LEN : nat}.

  Definition SHIFT_SMALL := Nat.pow BASE SHIFT_LEN.
  Definition SHIFT_BIG := SHIFT_SMALL * SHIFT_SMALL.

  Hypothesis BASE_ge_2 : 2 <= BASE.
  Hypothesis SHIFT_LEN_ge_1 : 1 <= SHIFT_LEN.

  Lemma BASE_pos : 0 < BASE.
  Proof. lia. Qed.

  Lemma SHIFT_SMALL_pos : 0 < SHIFT_SMALL.
  Proof.
    unfold SHIFT_SMALL.
    destruct SHIFT_LEN as [|len]; [lia|].
    simpl.
    assert (Hbase : 0 < BASE) by lia.
    assert (Hpow_all : forall n, 0 < Nat.pow BASE n).
    { intro n.
      induction n as [|n IH]; simpl; [lia|].
      apply Nat.mul_pos_pos; [assumption|exact IH]. }
    specialize (Hpow_all len) as Hpow.
    apply Nat.mul_pos_pos; [assumption|exact Hpow].
  Qed.

  Lemma shiftlen_lt_shiftsmall : SHIFT_LEN < SHIFT_SMALL.
  Proof.
    destruct SHIFT_LEN as [|len] eqn:Hlen; [lia|].
    unfold SHIFT_SMALL; simpl.
    pose proof (pow2_gt_succ len) as Hpow.
    assert (Hmono : Nat.pow 2 (S len) <= Nat.pow BASE SHIFT_LEN).
    { rewrite Hlen.
      apply (Nat.pow_le_mono_l 2 BASE (S len)); lia. }
    eapply Nat.lt_le_trans.
    - exact Hpow.
    - exact Hmono.
  Qed.

  Lemma len_lt_SHIFT_SMALL : forall len, len <= SHIFT_LEN -> len < SHIFT_SMALL.
  Proof.
    intros len Hle. eapply Nat.le_lt_trans; [exact Hle|apply shiftlen_lt_shiftsmall].
  Qed.

  Lemma pack_lt_square : forall k a c, 0 < k -> a < k -> c < k -> a * k + c < k * k.
  Proof.
    intros k a c Hk Ha Hc.
    apply Nat.lt_le_trans with (m := a * k + k).
    - apply Nat.add_lt_mono_l; exact Hc.
    - replace (a * k + k) with ((S a) * k) by (rewrite Nat.mul_succ_l; lia).
      apply Nat.mul_le_mono_pos_r; lia.
  Qed.

  Parameter encode_list : list nat -> nat.
  Parameter digits_ok : list nat -> Prop.
  Parameter encode_list_upper :
    forall xs, digits_ok xs -> encode_list xs < Nat.pow BASE (length xs).

  Lemma encode_list_lt_SHIFT_SMALL :
    forall xs, digits_ok xs -> length xs <= SHIFT_LEN -> encode_list xs < SHIFT_SMALL.
  Proof.
    intros xs Hdig Hlen.
    eapply Nat.lt_le_trans.
    - apply encode_list_upper; exact Hdig.
    - unfold SHIFT_SMALL. apply Nat.pow_le_mono_r; lia.
  Qed.

  Lemma pair_fits_in_SHIFT_BIG :
    forall len code,
      len < SHIFT_SMALL ->
      code < SHIFT_SMALL ->
      len * SHIFT_SMALL + code < SHIFT_BIG.
  Proof.
    intros len code Hlen Hcode.
    unfold SHIFT_BIG.
    apply pack_lt_square; try apply SHIFT_SMALL_pos; assumption.
  Qed.

  Record encode_list_bounds (xs : list nat) := {
    bounds_len_small : length xs < SHIFT_SMALL;
    bounds_code_small : encode_list xs < SHIFT_SMALL;
    bounds_packed_lt : length xs * SHIFT_SMALL + encode_list xs < SHIFT_BIG
  }.

  Lemma encode_list_bounds_of :
    forall xs,
      digits_ok xs ->
      length xs <= SHIFT_LEN ->
      encode_list_bounds xs.
  Proof.
    intros xs Hdig Hlen.
    refine ({|
      bounds_len_small := _;
      bounds_code_small := _;
      bounds_packed_lt := _
    |}).
    - apply len_lt_SHIFT_SMALL; assumption.
    - apply encode_list_lt_SHIFT_SMALL; assumption.
    - apply pair_fits_in_SHIFT_BIG.
      + apply len_lt_SHIFT_SMALL; assumption.
      + apply encode_list_lt_SHIFT_SMALL; assumption.
  Qed.

  Definition pair_small_encode (len code : nat) : nat := len * SHIFT_SMALL + code.
  Definition pair_small_decode (z : nat) : nat * nat := (z / SHIFT_SMALL, z mod SHIFT_SMALL).

  Definition triple_encode (q head code_small : nat) : nat :=
    ((q * SHIFT_BIG) + head) * SHIFT_BIG + code_small.

  Definition triple_decode (z : nat) : nat * nat * nat :=
    let code_small := z mod SHIFT_BIG in
    let z1 := z / SHIFT_BIG in
    let head := z1 mod SHIFT_BIG in
    let q := z1 / SHIFT_BIG in
    (q, head, code_small).

  Lemma SHIFT_SMALL_nonzero : SHIFT_SMALL <> 0.
  Proof.
    pose proof SHIFT_SMALL_pos as Hpos.
    lia.
  Qed.

  Lemma SHIFT_BIG_pos : 0 < SHIFT_BIG.
  Proof.
    unfold SHIFT_BIG.
    apply Nat.mul_pos_pos; [apply SHIFT_SMALL_pos | apply SHIFT_SMALL_pos].
  Qed.

  Lemma SHIFT_BIG_nonzero : SHIFT_BIG <> 0.
  Proof.
    pose proof SHIFT_BIG_pos as Hpos.
    lia.
  Qed.

  Lemma div_mul_add_small :
    forall a b c,
      b <> 0 ->
      c < b ->
      (a * b + c) / b = a /\
      (a * b + c) mod b = c.
  Proof.
    intros a b c Hb Hc.
    split.
    - rewrite (Nat.div_add_l a b c) by exact Hb.
      rewrite (Nat.div_small c b) by exact Hc.
      rewrite Nat.add_0_r.
      reflexivity.
    - assert (Hdiv : (a * b + c) / b = a).
      { rewrite (Nat.div_add_l a b c) by exact Hb.
        rewrite (Nat.div_small c b) by exact Hc.
        rewrite Nat.add_0_r.
        reflexivity. }
      pose proof (Nat.div_mod (a * b + c) b Hb) as Hdm.
      rewrite Hdiv in Hdm.
      replace (b * a) with (a * b) in Hdm by apply Nat.mul_comm.
      apply (proj1 (Nat.add_cancel_l _ _ (a * b))) in Hdm.
      symmetry.
      exact Hdm.
  Qed.

  Lemma pair_small_roundtrip :
    forall len code,
      code < SHIFT_SMALL ->
      pair_small_decode (pair_small_encode len code) = (len, code).
  Proof.
    intros len code Hcode.
    unfold pair_small_encode, pair_small_decode.
    assert (Hb : SHIFT_SMALL <> 0) by apply SHIFT_SMALL_nonzero.
    destruct (div_mul_add_small len SHIFT_SMALL code Hb Hcode) as [Hdiv Hmod].
    rewrite Hdiv, Hmod.
    reflexivity.
  Qed.

  Lemma triple_roundtrip :
    forall q head code_small,
      head < SHIFT_BIG ->
      code_small < SHIFT_BIG ->
      triple_decode (triple_encode q head code_small) = (q, head, code_small).
  Proof.
    intros q head code_small Hhead Hcode.
    unfold triple_encode, triple_decode.
    assert (Hb : SHIFT_BIG <> 0) by apply SHIFT_BIG_nonzero.
    destruct (div_mul_add_small (q * SHIFT_BIG + head) SHIFT_BIG code_small Hb Hcode) as [Hz_div Hz_mod].
    destruct (div_mul_add_small q SHIFT_BIG head Hb Hhead) as [Hz1_div Hz1_mod].
    simpl.
    rewrite Hz_mod, Hz_div, Hz1_mod, Hz1_div.
    reflexivity.
  Qed.

  Lemma triple_roundtrip_with_pair :
    forall q head len code,
      head < SHIFT_BIG ->
      len < SHIFT_SMALL ->
      code < SHIFT_SMALL ->
      triple_decode (triple_encode q head (pair_small_encode len code)) =
      (q, head, pair_small_encode len code).
  Proof.
    intros q head len code Hhead Hlen Hcode.
    apply triple_roundtrip; try assumption.
    apply pair_fits_in_SHIFT_BIG; assumption.
  Qed.

  Lemma encode_list_len_code_small :
    forall xs,
      digits_ok xs ->
      length xs <= SHIFT_LEN ->
      length xs < SHIFT_SMALL /\ encode_list xs < SHIFT_SMALL.
  Proof.
    intros xs Hdig Hlen.
    split.
    - apply len_lt_SHIFT_SMALL; assumption.
    - apply encode_list_lt_SHIFT_SMALL; assumption.
  Qed.

  Lemma encode_list_pack_lt_SHIFT_BIG :
    forall xs,
      digits_ok xs ->
      length xs <= SHIFT_LEN ->
      length xs * SHIFT_SMALL + encode_list xs < SHIFT_BIG.
  Proof.
    intros xs Hdig Hlen.
    destruct (encode_list_len_code_small xs Hdig Hlen) as [Hlen_small Hcode_small].
    apply pair_fits_in_SHIFT_BIG; assumption.
  Qed.

End EncodingMini.
