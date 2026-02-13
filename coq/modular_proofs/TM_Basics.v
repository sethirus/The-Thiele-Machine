(* ================================================================= *)
(* Modular Proofs for Thiele Machine Simulation                       *)
(* ================================================================= *)
(* This file provides the lightweight single-tape Turing machine       *)
(* semantics together with the list lemmas reused by the modular      *)
(* simulation proof.                                                  *)
(* ================================================================= *)

From Coq Require Import List Arith Lia Bool.
From ModularProofs Require Import Encoding.
Import ListNotations.

(* ----------------------------------------------------------------- *)
(* Basic TM Definitions                                              *)
(* ----------------------------------------------------------------- *)

Definition TMState := (nat * list nat * nat)%type.
Definition TMConfig := TMState.
Definition TMTransition := nat -> nat -> (nat * nat * nat).

Definition BASE : nat := 2.
Definition tm_blank : nat := Nat.sub 1 1.
Definition digits_ok (xs : list nat) : Prop := Forall (fun d => d < BASE) xs.

Fixpoint replace_nth (l : list nat) (n : nat) (v : nat) : list nat :=
  match l, n with
  | [], _ => []
  | x :: xs, 0 => v :: xs
  | x :: xs, S n' => x :: replace_nth xs n' v
  end.

Definition move_head (head move : nat) : nat :=
  match move with
  | 0 => head
  | 1 => S head
  | _ => Nat.pred head
  end.

Definition tm_step (tm : TMTransition) (conf : TMConfig) : TMConfig :=
  let '(q, tape, head) := conf in
  let symbol := nth head tape tm_blank in
  let '(q', write, move) := tm q symbol in
  let tape' := replace_nth tape head write in
  let head' := move_head head move in
  (q', tape', head').

Fixpoint tm_run_n (tm : TMTransition) (conf : TMConfig) (n : nat) : TMConfig :=
  match n with
  | 0 => conf
  | S n' => tm_run_n tm (tm_step tm conf) n'
  end.

(* ----------------------------------------------------------------- *)
(* Structural List Lemmas                                            *)
(* ----------------------------------------------------------------- *)

Lemma replace_nth_length : forall l n v, length (replace_nth l n v) = length l.
Proof.
  induction l as [|x xs IH]; intros [|n] v; simpl; auto.
Qed.

Lemma replace_nth_Forall :
  forall (P : nat -> Prop) (l : list nat) n v,
    Forall P l ->
    P v ->
    Forall P (replace_nth l n v).
Proof.
  intros P l.
  induction l as [|x xs IH]; intros [|n] v Hall Hv; simpl; auto.
  - inversion Hall; subst; constructor; auto.
  - inversion Hall; subst; constructor; auto.
Qed.

(* ----------------------------------------------------------------- *)
(* Configuration Well-formedness                                     *)
(* ----------------------------------------------------------------- *)

Definition tm_config_ok (conf : TMConfig) : Prop :=
  let '(q, tape, head) := conf in
  digits_ok tape /\ length tape <= Encoding.SHIFT_LEN /\ head < length tape.

(* INQUISITOR NOTE: Extraction lemma exposing component of compound definition for modular reasoning. *)
Lemma tm_config_ok_digits :
  forall q tape head,
    tm_config_ok (q, tape, head) ->
    digits_ok tape.
Proof. intros q tape head [Hdigs _]. exact Hdigs. Qed.

(* INQUISITOR NOTE: Extraction lemma exposing component of compound definition for modular reasoning. *)
Lemma tm_config_ok_head :
  forall q tape head,
    tm_config_ok (q, tape, head) ->
    head < length tape.
Proof. intros q tape head [_ [_ Hhead]]. exact Hhead. Qed.

Lemma tm_config_ok_change_state :
  forall q1 q2 tape head,
    tm_config_ok (q1, tape, head) ->
    tm_config_ok (q2, tape, head).
Proof. intros q1 q2 tape head Hok. exact Hok. Qed.

Lemma tm_config_ok_update_write :
  forall q tape head write,
    tm_config_ok (q, tape, head) ->
    write < BASE ->
    tm_config_ok (q, replace_nth tape head write, head).
Proof.
  intros q tape head write Hok Hwrite.
  destruct Hok as [Hdigs [Hlen Hhead]].
  split.
  - apply replace_nth_Forall; [exact Hdigs|exact Hwrite].
  - split.
    + rewrite replace_nth_length. exact Hlen.
    + rewrite replace_nth_length. exact Hhead.
Qed.

Lemma tm_config_ok_update_head :
  forall q tape head head',
    tm_config_ok (q, tape, head) ->
    head' < length tape ->
    tm_config_ok (q, tape, head').
Proof.
  intros q tape head head' Hok Hhead'.
  destruct Hok as [Hdigs [Hlen _]].
  split; [exact Hdigs|].
  split; [exact Hlen|exact Hhead'].
Qed.

(* ----------------------------------------------------------------- *)
(* Step Preservation Facts                                           *)
(* ----------------------------------------------------------------- *)

Lemma tm_step_tape_length :
  forall tm q tape head,
    head < length tape ->
    length (let '(_, tape', _) := tm_step tm (q, tape, head) in tape') = length tape.
Proof.
  intros tm q tape head _.
  unfold tm_step; simpl.
  remember (tm q (nth head tape tm_blank)) as trans.
  destruct trans as [[q' write] move]; simpl.
  apply replace_nth_length.
Qed.

Lemma tm_step_digits_preserved :
  forall tm q tape head,
    tm_config_ok (q, tape, head) ->
    let '(q', write, move) := tm q (nth head tape tm_blank) in
    write < BASE ->
    digits_ok (let '(_, tape', _) := tm_step tm (q, tape, head) in tape').
Proof.
  intros tm q tape head Hok.
  destruct Hok as [Hdigs [_ Hhead]].
  unfold tm_step; simpl.
  remember (tm q (nth head tape tm_blank)) as trans.
  destruct trans as [[q' write] move]; simpl.
  intro Hwrite.
  apply replace_nth_Forall; [exact Hdigs|exact Hwrite].
Qed.

Lemma tm_step_head_preserved :
  forall tm q tape head,
    tm_config_ok (q, tape, head) ->
    let '(q', write, move) := tm q (nth head tape tm_blank) in
    move_head head move < length tape ->
    let '(_, _, head') := tm_step tm (q, tape, head) in head' < length tape.
Proof.
  intros tm q tape head _.
  unfold tm_step; simpl.
  remember (tm q (nth head tape tm_blank)) as trans.
  destruct trans as [[q' write] move]; simpl.
  intro Hmove.
  exact Hmove.
Qed.
