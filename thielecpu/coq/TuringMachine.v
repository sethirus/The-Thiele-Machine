(* TuringMachine.v: Classical Turing Machine definition *)

Require Import List.
Require Import ZArith.
Import ListNotations.

Record TM (Symbol State : Type) := {
  tm_states : list State;
  tm_symbols : list Symbol;
  tm_blank : Symbol;
  tm_start : State;
  tm_accept : State;
  tm_reject : State;
  tm_delta : State -> Symbol -> (State * Symbol * Z)
}.

Definition Tape (Symbol : Type) := list Symbol.
Definition TMConfig (Symbol State : Type) := (State * (Tape Symbol) * nat)%type.

Definition tm_step {Symbol State : Type} (tm : TM Symbol State) (conf : TMConfig Symbol State) : TMConfig Symbol State :=
  let '(q, tape, head) := conf in
  let sym :=
    match nth_error tape head with
    | Some s => s
    | None => tm_blank _ _ tm
    end in
  let '(q', write, move) := tm_delta _ _ tm q sym in
  let tape' :=
    match nth_error tape head with
    | Some _ => firstn head tape ++ [write] ++ skipn (S head) tape
    | None =>
        (* Extend tape if head is out of bounds *)
        tape ++ repeat (tm_blank _ _ tm) (Nat.sub head (length tape)) ++ [write]
    end in
  let head' :=
    let h : Z := Z.add (Z.of_nat head) move in
    if Z.ltb h 0 then 0%nat else Z.to_nat h
  in
  (q', tape', head').

(* Example: Simple Turing machine that increments a binary number on the tape *)
Inductive BinSymbol := Zero | One | Blank.
Inductive BinState := QStart | QInc | QHalt.
Require Import Eqdep_dec.

Definition BinState_eq_dec : forall (x y : BinState), {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Open Scope Z_scope.

Definition bin_tm : TM BinSymbol BinState :=
  {| tm_states := (QStart :: QInc :: QHalt :: nil);
     tm_symbols := (Zero :: One :: Blank :: nil);
     tm_blank := Blank;
     tm_start := QStart;
     tm_accept := QHalt;
     tm_reject := QHalt;
     tm_delta := fun st sym =>
       match st, sym with
       | QStart, Blank => (QHalt, Blank, 0%Z)
       | QStart, Zero => (QInc, One, -1%Z)
       | QStart, One => (QStart, Zero, 1%Z)
       | QInc, s => (QHalt, s, 0%Z)
       | QHalt, s => (QHalt, s, 0%Z)
       end
  |}.
(*
  Next steps:
  - Implement tm_step to match standard Turing machine semantics.
  - Prove properties about reachability and halting.
*)
