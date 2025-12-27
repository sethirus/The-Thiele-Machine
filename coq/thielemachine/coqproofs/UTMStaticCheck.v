(* SPDX-License-Identifier: Apache-2.0 *)
(* Static catalogue check for the archived universal Turing machine. *)

From Coq Require Import List ZArith Bool.
From ThieleUniversal Require Import TM UTM_Rules UTM_Encode UTM_Program.
From ModularProofs Require Import Encoding.

Import ListNotations.

Definition rule_write_lt_base_check
  (rule : nat * nat * nat * nat * Z) : bool :=
  let '(_, _, _, write, _) := rule in Nat.ltb write Encoding.BASE.

Definition rule_move_le_one_check
  (rule : nat * nat * nat * nat * Z) : bool :=
  (* SAFE: Bounded arithmetic operation with explicit domain *)
  let '(_, _, _, _, move) := rule in Z.leb (Z.abs move) 1%Z.

Definition catalogue_static_check (tm : TM) : bool :=
  Nat.ltb (tm_blank tm) Encoding.BASE &&
  forallb rule_write_lt_base_check (tm_rules tm) &&
  forallb rule_move_le_one_check (tm_rules tm).

Lemma utm_catalogue_static_check_proved :
  catalogue_static_check utm_tm = true.
Proof.
  vm_compute. reflexivity.
Qed.

