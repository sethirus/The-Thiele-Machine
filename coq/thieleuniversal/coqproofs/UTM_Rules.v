From Coq Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.

From ThieleMachine.Modular_Proofs Require Import Encoding.
Require Import ThieleUniversal.TM.

Definition utm_accept : nat := 4.
Definition utm_reject : nat := 5.
Definition utm_blank  : nat := Nat.sub 1 1.

Definition utm_rules : list (nat * nat * nat * nat * Z) :=
  [ (0, 0, 1, 0, 1%Z);
    (0, 1, 0, 1, 0%Z);
    (1, 0, 2, 1, (-1)%Z);
    (1, 1, 0, 0, 1%Z);
    (2, 0, 3, 1, 0%Z);
    (2, 1, 4, 1, 1%Z);
    (3, 0, 3, 0, 0%Z);
    (3, 1, 3, 1, 0%Z)
  ].

Definition utm_tm : TM :=
  {| tm_accept := utm_accept;
     tm_reject := utm_reject;
     tm_blank  := utm_blank;
     tm_rules  := utm_rules |}.

(* ------------------------------------------------------------------ *)
(* Basic catalogue witnesses                                          *)
(* ------------------------------------------------------------------ *)

Lemma utm_blank_lt_base : utm_blank < Encoding.BASE.
Proof. cbv [utm_blank Encoding.BASE]; lia. Qed.

Lemma utm_rules_write_lt_base :
  Forall (fun rule => let '(_, _, _, write, _) := rule in write < Encoding.BASE) utm_rules.
Proof.
  repeat constructor; cbn; lia.
Qed.

Lemma utm_rules_move_abs_le_one :
  (* SAFE: Bounded arithmetic operation with explicit domain *)
  Forall (fun rule => let '(_, _, _, _, move) := rule in (Z.abs move <= 1)%Z) utm_rules.
Proof.
  repeat constructor; cbn; lia.
Qed.


