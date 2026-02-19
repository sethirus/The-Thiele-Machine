Require Import List.
Require Import Bool.
Require Import Nat.
Require Import ZArith.
Require Import Arith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.

(* Utility lemma: taking the first n elements of a repeat. *)
(** [firstn_repeat]: formal specification. *)
Lemma firstn_repeat : forall (A:Type) (x:A) n m,
  (* SAFE: Bounded arithmetic operation with explicit domain *)
  firstn n (repeat x m) = repeat x (Init.Nat.min n m).
Proof.
  intros A x n m.
  generalize dependent n.
  induction m as [|m IH]; intros n; simpl.
  - destruct n; reflexivity.
  - destruct n; simpl.
    + reflexivity.
    + f_equal. apply IH.
Qed.

(* Utility lemma: dropping n elements from a repeat. *)
(** [skipn_repeat]: formal specification. *)
Lemma skipn_repeat : forall (A:Type) (x:A) n m,
  skipn n (repeat x m) = repeat x (m - n).
Proof.
  intros A x n m.
  revert m; induction n as [|n IH]; intros m; simpl.
  - now rewrite Nat.sub_0_r.
  - destruct m; simpl; auto.
Qed.

(* --- Section: Turing Machine Definitions --- *)

(* Finite Turing machine described by an explicit rule table. *)
Record TM := {
  tm_accept : nat;
  tm_reject : nat;
  tm_blank  : nat;
  tm_rules  : list (nat * nat * nat * nat * Z)
}.

(* Configuration: state, tape and head position. *)
Definition TMConfig := (nat * list nat * nat)%type. (* state * tape * head *)

(* Lookup the rule matching the current state and symbol. *)
Fixpoint find_rule (rules : list (nat*nat*nat*nat*Z)) (q_cur : nat) (sym_cur : nat)
  : option (nat * nat * Z) :=
  match rules with
  | [] => None
  | (q_rule, sym_rule, q', write, move) :: rest =>
      if andb (Nat.eqb q_rule q_cur) (Nat.eqb sym_rule sym_cur)
      then Some (q', write, move)
      else find_rule rest q_cur sym_cur
  end.

(* A concrete lemma showing equivalence between a δ-function and a single encoded rule. *)
(** [delta_rule_single]: formal specification. *)
Lemma delta_rule_single :
  forall delta q s,
    let '(q',w,m) := delta q s in
    find_rule [(q,s,q',w,m)] q s = Some (q',w,m).
Proof.
  intros delta q s. destruct (delta q s) as [[q' w] m]. simpl.
  rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

(* Execute one TM step according to the rule table. *)
Definition tm_step (tm : TM) (conf : TMConfig) : TMConfig :=
  let '(q, tape, head) := conf in
  if orb (Nat.eqb q tm.(tm_accept)) (Nat.eqb q tm.(tm_reject)) then conf else
  let sym := nth head tape tm.(tm_blank) in
  match find_rule tm.(tm_rules) q sym with
  | None => conf (* Halt if no rule found *)
  | Some (q', write, move) =>
      let tape_ext :=
        if Nat.ltb head (length tape) then tape
        else tape ++ repeat tm.(tm_blank) (head - length tape) in
      let tape' := firstn head tape_ext ++ [write] ++ skipn (S head) tape_ext in
  (* SAFE: Bounded arithmetic operation with explicit domain *)
  (* SAFE: Bounded arithmetic operation with explicit domain *)
      let h' := Z.to_nat (Z.max 0%Z (Z.of_nat head + move)) in
      (q', tape', h')
  end.

(** [tm_step_rule_found_continue]: formal specification. *)
Lemma tm_step_rule_found_continue :
  forall tm q tape head q' write move,
    (Nat.eqb q tm.(tm_accept) || Nat.eqb q tm.(tm_reject)) = false ->
    find_rule tm.(tm_rules) q (nth head tape tm.(tm_blank)) = Some (q', write, move) ->
    tm_step tm ((q, tape), head) =
      let tape_ext :=
        if Nat.ltb head (length tape) then tape
        else tape ++ repeat tm.(tm_blank) (head - length tape) in
      let tape' := firstn head tape_ext ++ [write] ++ skipn (S head) tape_ext in
  (* SAFE: Bounded arithmetic operation with explicit domain *)
  (* SAFE: Bounded arithmetic operation with explicit domain *)
      let h' := Z.to_nat (Z.max 0%Z (Z.of_nat head + move)) in
      (q', tape', h').
Proof.
  intros tm q tape head q' write move Hcontinue Hfind.
  unfold tm_step.
  rewrite Hcontinue.
  simpl.
  rewrite Hfind.
  reflexivity.
Qed.

(** [tm_step_no_rule_continue]: formal specification. *)
Lemma tm_step_no_rule_continue :
  forall tm q tape head,
    (Nat.eqb q tm.(tm_accept) || Nat.eqb q tm.(tm_reject)) = false ->
    find_rule tm.(tm_rules) q (nth head tape tm.(tm_blank)) = None ->
    tm_step tm ((q, tape), head) = ((q, tape), head).
Proof.
  intros tm q tape head Hcontinue Hfind.
  unfold tm_step.
  rewrite Hcontinue.
  simpl.
  rewrite Hfind.
  reflexivity.
Qed.

(** [tm_step_halting_state]: formal specification. *)
Lemma tm_step_halting_state :
  forall tm q tape head,
    (Nat.eqb q tm.(tm_accept) || Nat.eqb q tm.(tm_reject)) = true ->
    tm_step tm ((q, tape), head) = ((q, tape), head).
Proof.
  intros tm q tape head Hhalt.
  unfold tm_step.
  rewrite Hhalt.
  reflexivity.
Qed.

(* Iterate the TM transition n times. *)
Fixpoint tm_step_n (tm : TM) (conf : TMConfig) (n : nat) : TMConfig :=
 match n with
 | 0 => conf
 | S k => tm_step_n tm (tm_step tm conf) k
 end.