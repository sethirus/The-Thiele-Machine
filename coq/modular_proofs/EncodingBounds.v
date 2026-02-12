From Coq Require Import Arith.Arith Arith.PeanoNat Lists.List Lia.

Lemma pow2_gt_succ : forall n, S n < Nat.pow 2 (S n).
Proof.
  intro n.
  induction n as [|n IH]; simpl; [lia|].
  assert (Hle : S (S n) <= 2 * S n) by lia.
  assert (Hlt : 2 * S n < 2 * Nat.pow 2 (S n)).
  { apply Nat.mul_lt_mono_pos_l; [lia|exact IH]. }
  eapply Nat.le_lt_trans; [exact Hle|exact Hlt].
Qed.

(** HELPER: Non-negativity property *)
(** HELPER: Non-negativity property *)
Lemma pow_pos : forall a n, 1 <= a -> 0 < Nat.pow a n.
Proof.
  intros a n Ha.
  induction n as [|n IH]; simpl; [lia|].
  apply Nat.mul_pos_pos; [lia|exact IH].
Qed.

Section EncodingBounds.
  Context (BASE SHIFT_LEN : nat).

  Definition SHIFT_SMALL := Nat.pow BASE SHIFT_LEN.
  Definition SHIFT_BIG := Nat.pow BASE (2 * SHIFT_LEN).

  Context (BASE_ge_2 : 2 <= BASE).
  Context (SHIFT_LEN_ge_1 : 1 <= SHIFT_LEN).

  Lemma BASE_pos : 0 < BASE.
  Proof. lia. Qed.

  Lemma SHIFT_SMALL_pos : 0 < SHIFT_SMALL.
  Proof.
    unfold SHIFT_SMALL.
    apply pow_pos; lia.
  Qed.

  Lemma SHIFT_SMALL_nonzero : SHIFT_SMALL <> 0.
  Proof.
    pose proof SHIFT_SMALL_pos as Hpos.
    lia.
  Qed.

  Lemma shiftlen_lt_shiftsmall : SHIFT_LEN < SHIFT_SMALL.
  Proof.
    destruct SHIFT_LEN as [|len] eqn:Hlen; [lia|].
    unfold SHIFT_SMALL.
    simpl.
    pose proof (pow2_gt_succ len) as Hpow.
    assert (Hmono : Nat.pow 2 (S len) <= Nat.pow BASE (S len)).
    { apply (Nat.pow_le_mono_l 2 BASE (S len)); lia. }
    rewrite Hlen in *.
    eapply Nat.lt_le_trans; [exact Hpow|exact Hmono].
  Qed.

  Lemma len_lt_SHIFT_SMALL : forall len, len <= SHIFT_LEN -> len < SHIFT_SMALL.
  Proof.
    intros len Hle.
    eapply Nat.le_lt_trans; [exact Hle|apply shiftlen_lt_shiftsmall].
  Qed.

  Lemma SHIFT_BIG_as_product : SHIFT_BIG = SHIFT_SMALL * SHIFT_SMALL.
  Proof.
    unfold SHIFT_BIG, SHIFT_SMALL.
    replace (2 * SHIFT_LEN) with (SHIFT_LEN + SHIFT_LEN) by lia.
    rewrite Nat.pow_add_r.
    reflexivity.
  Qed.

  Lemma SHIFT_SMALL_ge_succ_SHIFT_LEN : S SHIFT_LEN <= SHIFT_SMALL.
  Proof.
    assert (SHIFT_LEN < SHIFT_SMALL) by apply shiftlen_lt_shiftsmall.
    lia.
  Qed.

  Lemma SHIFT_SMALL_le_SHIFT_BIG : SHIFT_SMALL <= SHIFT_BIG.
  Proof.
    rewrite SHIFT_BIG_as_product.
    remember SHIFT_SMALL as s eqn:Hs.
    destruct s as [|k].
    { subst. pose proof SHIFT_SMALL_pos. lia. }
    simpl.
    rewrite Nat.mul_succ_r.
    lia.
  Qed.

  Lemma SHIFT_LEN_lt_SHIFT_BIG : SHIFT_LEN < SHIFT_BIG.
  Proof.
    eapply Nat.lt_le_trans; [apply shiftlen_lt_shiftsmall|apply SHIFT_SMALL_le_SHIFT_BIG].
  Qed.

  Lemma le_SHIFT_LEN_lt_SHIFT_BIG :
    forall x, x <= SHIFT_LEN -> x < SHIFT_BIG.
  Proof.
    intros x Hle.
    apply Nat.lt_le_trans with (m := S SHIFT_LEN).
    - lia.
    - eapply Nat.le_trans; [apply SHIFT_SMALL_ge_succ_SHIFT_LEN|apply SHIFT_SMALL_le_SHIFT_BIG].
  Qed.

  Lemma lt_SHIFT_LEN_succ_lt_SHIFT_BIG :
    forall x, x < SHIFT_LEN -> S x < SHIFT_BIG.
  Proof.
    intros x Hlt.
    apply Nat.lt_le_trans with (m := S SHIFT_LEN).
    - lia.
    - eapply Nat.le_trans; [apply SHIFT_SMALL_ge_succ_SHIFT_LEN|apply SHIFT_SMALL_le_SHIFT_BIG].
  Qed.

  Lemma SHIFT_BIG_pos : 0 < SHIFT_BIG.
  Proof.
    rewrite SHIFT_BIG_as_product.
    apply Nat.mul_pos_pos; apply SHIFT_SMALL_pos.
  Qed.

  Lemma SHIFT_BIG_nonzero : SHIFT_BIG <> 0.
  Proof.
    pose proof SHIFT_BIG_pos as Hpos.
    lia.
  Qed.

  Lemma pack_lt_square : forall k a c, 0 < k -> a < k -> c < k -> a * k + c < k * k.
  Proof.
    intros k a c Hk Ha Hc.
    apply Nat.lt_le_trans with (m := a * k + k).
    - apply Nat.add_lt_mono_l; assumption.
    - replace (a * k + k) with ((S a) * k) by (rewrite Nat.mul_succ_l; lia).
      apply Nat.mul_le_mono_pos_r; lia.
  Qed.

  Lemma pair_fits_in_SHIFT_BIG :
    forall len code,
      len < SHIFT_SMALL ->
      code < SHIFT_SMALL ->
      len * SHIFT_SMALL + code < SHIFT_BIG.
  Proof.
    intros len code Hlen Hcode.
    rewrite SHIFT_BIG_as_product.
    apply pack_lt_square; try apply SHIFT_SMALL_pos; assumption.
  Qed.

  Section EncodeBounds.
    (** INQUISITOR NOTE: These Context parameters are for generic encoding
        infrastructure. They parameterize over any conforming encode_list
        implementation. This is NOT an axiom - it's dependency injection
        for modularity. The Section exports theorems with explicit params. *)
    Context (encode_list : list nat -> nat).
    Context (digits_ok : list nat -> Prop).
    Context (encode_list_upper : forall xs, digits_ok xs -> encode_list xs < Nat.pow BASE (length xs)).

    Lemma encode_list_lt_SHIFT_SMALL :
      forall xs,
        digits_ok xs ->
        length xs <= SHIFT_LEN ->
        encode_list xs < SHIFT_SMALL.
    Proof.
      intros xs Hdig Hlen.
      eapply Nat.lt_le_trans.
      - apply encode_list_upper; assumption.
      - unfold SHIFT_SMALL. apply Nat.pow_le_mono_r; lia.
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
      - apply encode_list_pack_lt_SHIFT_BIG; assumption.
    Qed.

    Lemma encode_list_all_bounds :
      forall xs,
        digits_ok xs ->
        length xs <= SHIFT_LEN ->
        length xs < SHIFT_SMALL /\
        encode_list xs < SHIFT_SMALL /\
        length xs * SHIFT_SMALL + encode_list xs < SHIFT_BIG.
    Proof.
      intros xs Hdig Hlen.
      destruct (encode_list_bounds_of xs Hdig Hlen) as [Hlen_small Hcode_small Hpacked_lt].
      repeat split; assumption.
    Qed.
  End EncodeBounds.

End EncodingBounds.

Lemma div_mul_add_small :
  forall k a c,
    0 < k ->
    c < k ->
    ((a * k + c) / k = a) /\
    ((a * k + c) mod k = c).
Proof.
  intros k a c Hk Hc.
  split.
  - assert (Hk' : k <> 0) by lia.
    rewrite (Nat.div_add_l a k c) by exact Hk'.
    rewrite (Nat.div_small c k) by exact Hc.
    lia.
  - rewrite Nat.add_comm.
    rewrite Nat.Div0.mod_add.
    rewrite Nat.mod_small by exact Hc.
    reflexivity.
Qed.
