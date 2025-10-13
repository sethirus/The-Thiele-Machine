From Coq Require Import List PeanoNat.
Import ListNotations.

From ThieleMachine.Modular_Proofs Require Import Encoding EncodingBounds.
From ThieleUniversal Require Import TM.

Definition tm_encode_config (conf : TMConfig) : nat :=
  let '(q, tape, head) := conf in encode_config q tape head.

Definition tm_decode_config (code : nat) : TMConfig :=
  decode_config code.

Definition tm_config_ok (conf : TMConfig) : Prop :=
  let '(q, tape, head) := conf in
  digits_ok tape /\ length tape <= SHIFT_LEN /\ head < SHIFT_LEN.

Lemma tm_decode_encode_roundtrip :
  forall conf,
    tm_config_ok conf ->
    tm_decode_config (tm_encode_config conf) = conf.
Proof.
  intros [[q tape] head] [Hdigs [Hlen Hhead]].
  simpl in *.
  pose proof (EncodingBounds.le_SHIFT_LEN_lt_SHIFT_BIG
                Encoding.BASE Encoding.SHIFT_LEN
                Encoding.BASE_ge_2 Encoding.SHIFT_LEN_ge_1
                head (Nat.lt_le_incl _ _ Hhead)) as Hhead_big.
  apply encode_decode_config; auto.
Qed.
