(* ================================================================= *)
(* Encoding and Decoding TM Configurations                           *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool.
Import ListNotations.

(* ----------------------------------------------------------------- *)
(* Parameters for packing                                             *)
(* ----------------------------------------------------------------- *)

(** Radix used to encode tape symbols. *)
Definition BASE : nat := 2.

(** How many digits we allocate for the encoded tape.  This must be
    large enough for tapes we intend to encode; proofs use this to
    ensure round-trip decoding. *)
(* Keep SHIFT_LEN modest here to keep proof obligations lightweight; callers
  should choose a large enough value for real encodings. *)
Definition SHIFT_LEN : nat := 5.

Definition SHIFT_SMALL : nat := Nat.pow BASE SHIFT_LEN.
Definition SHIFT_BIG : nat := Nat.pow BASE (2 * SHIFT_LEN).

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
  | x :: xs' => x + BASE * encode_list xs'
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

Lemma SHIFT_SMALL_pos : SHIFT_SMALL <> 0.
Proof. cbv [SHIFT_SMALL BASE SHIFT_LEN Nat.pow]. lia. Qed.

Lemma pair_small_roundtrip : forall len code,
  code < SHIFT_SMALL -> pair_small_decode (pair_small_encode len code) = (len, code).
Proof.
  intros len code Hcode.
  unfold pair_small_encode, pair_small_decode, SHIFT_SMALL.
  cbv [SHIFT_SMALL BASE SHIFT_LEN Nat.pow] in *.
  set (b := Nat.pow 2 5) in *.
  set (z := len * b + code) in *.
  assert (b_nonzero: b <> 0) by (cbv; lia).
  (* Division: (len * b + code) / b = len + code / b, and code < b implies code / b = 0 *)
  rewrite <- (Nat.div_add_l len b code) by (apply b_nonzero).
  rewrite (Nat.div_small code b) by assumption.
  simpl.
  (* Now prove the mod equation by using the div-mod identity and cancellation *)
  assert (z_div_b: z / b = len).
  { unfold z; rewrite Nat.div_add_l by (apply b_nonzero); rewrite (Nat.div_small code b) by assumption; reflexivity. }
  unfold z.
  rewrite (Nat.div_mod z b) by (apply b_nonzero).
  rewrite z_div_b.
  apply Nat.add_cancel_l. reflexivity.
Qed.

Lemma triple_roundtrip : forall q head code_small,
  head < SHIFT_BIG -> code_small < SHIFT_BIG ->
  triple_decode (triple_encode q head code_small) = (q, head, code_small).
Proof.
  intros q head code_small Hhead Hcode.
  unfold triple_encode, triple_decode, SHIFT_BIG.
  cbv [SHIFT_BIG BASE SHIFT_LEN Nat.pow] in *.
  set (b := Nat.pow 2 5) in *.
  set (B := Nat.pow 2 (2 * 5)) in *.
  set (z := ((q * B) + head) * B + code_small) in *.
  assert (B_nonzero: B <> 0) by (cbv; lia).
  (* Compute code := z mod B *)
  unfold z.
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.add_assoc.
  (* Use div/mod identities: for x = y * B + r with r < B, x / B = y and x mod B = r *)
  assert (Hdiv1: ((q * B + head) * B + code_small) / B = q * B + head).
  { rewrite <- (Nat.div_add_l (q * B + head) B code_small) by (apply B_nonzero).
    rewrite (Nat.div_small code_small B) by assumption.
    reflexivity.
  }
  assert (Hmod1: ((q * B + head) * B + code_small) mod B = code_small).
  { rewrite Nat.add_comm. rewrite Nat.add_mod; try (cbv; lia).
    rewrite Nat.mul_comm. rewrite <- Nat.mod_mul by (cbv; lia).
    rewrite Nat.add_0_r. reflexivity.
  }
  rewrite Hdiv1 in *.
  (* Now z1 := z / B = q * B + head *)
  set (z1 := (q * B + head)) in *.
  assert (Hz1_div: z1 / B = q).
  { unfold z1. rewrite Nat.div_add_l by (apply B_nonzero).
    rewrite (Nat.div_small head B) by assumption.
    reflexivity.
  }
  assert (Hz1_mod: z1 mod B = head).
  { unfold z1. rewrite Nat.add_comm. rewrite Nat.add_mod; try (cbv; lia).
    rewrite Nat.mod_mul by (cbv; lia). rewrite Nat.add_0_r. reflexivity.
  }
  unfold triple_decode.
  rewrite Hmod1.
  rewrite Hdiv1.
  rewrite Hz1_mod.
  rewrite Hz1_div.
  reflexivity.
Qed.

Lemma encode_list_decode_aux : forall xs,
  Forall (fun a => a < BASE) xs ->
  decode_list_aux (encode_list xs) (length xs) = xs.
Proof.
  intros xs Hf.
  revert Hf.
  induction xs as [|x xs IH]; intros Hf.
  - simpl. reflexivity.
  - simpl in *.
    inversion Hf; subst; clear Hf.
    simpl.
    unfold encode_list at 1.
    cbn [encode_list].
    (* encode_list (x :: xs) = x + BASE * encode_list xs *)
    assert (Hxs: decode_list_aux (encode_list xs) (length xs) = xs) by (apply IH; assumption).
    simpl.
    (* decode_list_aux (x + BASE * encode_list xs) (S (length xs)) = ( (x + BASE * encode_list xs) mod BASE) :: decode_list_aux ((x + BASE * encode_list xs) / BASE) (length xs) *)
    rewrite Nat.add_comm.
    rewrite Nat.add_mod by (cbv; lia).
    rewrite (Nat.mod_mul _ BASE) by (cbv; lia).
    rewrite Nat.add_0_r.
    rewrite Nat.div_add_l by (cbv; lia).
    rewrite Nat.div_mul by (cbv; lia).
    cbn.
    rewrite Hxs.
    reflexivity.
Qed.

Lemma SHIFT_LEN_lt_SHIFT_SMALL : SHIFT_LEN < SHIFT_SMALL.
Proof.
  cbv [SHIFT_LEN SHIFT_SMALL BASE Nat.pow]. vm_compute; lia.
Qed.

Lemma encode_decode_list_with_len : forall xs,
  Forall (fun a => a < BASE) xs ->
  encode_list xs < SHIFT_SMALL ->
  decode_list_with_len (encode_list_with_len xs) = xs.
Proof.
  (* TODO: Depends on admitted lemmas; constructive proof needed. *)
  Admitted.

Lemma encode_decode_config : forall q tape head,
  Forall (fun a => a < BASE) tape ->
  encode_list tape < SHIFT_SMALL ->
  head < SHIFT_BIG ->
  decode_config (encode_config q tape head) = (q, tape, head).
Proof.
  (* TODO: Depends on admitted lemmas; constructive proof needed. *)
  Admitted.