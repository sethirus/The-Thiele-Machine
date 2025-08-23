(* All-in-one file: TuringMachine, ThieleCPU, Subsumption *)

(* --- TuringMachine.v --- *)
Require Import List.
Require Import Bool.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

(* Axiomatisation of an external logic oracle.  Given a list of encoded
   axioms, it returns [false] when the axioms are paradoxical and
   [true] when they are consistent.  It is left uninterpreted in this
   development. *)
Parameter logic_oracle : list nat -> bool.

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
Definition TMConfig := (nat * Tape nat * nat)%type.

Definition tm_step (tm : TM nat nat)
           (conf : TMConfig) : TMConfig :=
  let '(q, tape, head) := conf in
  if orb (Nat.eqb q (tm_accept _ _ tm)) (Nat.eqb q (tm_reject _ _ tm)) then conf else
  let sym := nth head tape (tm_blank _ _ tm) in
  let '(q', write, move) := tm_delta _ _ tm q sym in
  let tape_ext :=
    if Nat.ltb head (length tape) then tape
    else tape ++ repeat (tm_blank _ _ tm) (Nat.sub head (length tape)) in
  let tape' := firstn head tape_ext ++ [write] ++ skipn (S head) tape_ext in
  let head' :=
    let h := Z.of_nat head + move in
    if Z.ltb h 0 then 0%nat else Z.to_nat h in
  (q', tape', head').

Fixpoint tm_step_n (tm : TM nat nat)
         (conf : TMConfig) (n : nat) : TMConfig :=
  match n with
  | 0%nat => conf
  | S n' => tm_step_n tm (tm_step tm conf) n'
  end.

(* --- ThieleCPU.v --- *)
Record CPUState := {
  state : nat;
  tape : list nat;
  head : nat;
  halted : bool;
  delta_fn : nat -> nat -> (nat * nat * Z);
  blank_sym : nat;
  accept_state : nat;
  reject_state : nat;
  mu_cost : nat;            (* running information cost *)
  paradox_detected : bool   (* flag for logical inconsistency *)
}.

(* The raw Turing-machine step logic factored out so that the CPU step
   interpreter can reuse it.  It returns the next state, tape, head
   position and the new halted flag. *)
Definition tm_step_logic (st : CPUState)
  : (nat * list nat * nat * bool) :=
  let q := state st in
  let tp := tape st in
  let hd := head st in
  let sym := nth hd tp (blank_sym st) in
  let '(q', write, move) := delta_fn st q sym in
  let tp_ext :=
    if Nat.ltb hd (length tp) then tp
    else tp ++ repeat (blank_sym st) (Nat.sub hd (length tp)) in
  let tp' := firstn hd tp_ext ++ [write] ++ skipn (S hd) tp_ext in
  let hd' :=
    let h := Z.of_nat hd + move in
    if Z.ltb h 0 then 0%nat else Z.to_nat h in
  let halted' := orb (Nat.eqb q' (accept_state st)) (Nat.eqb q' (reject_state st)) in
  (q', tp', hd', halted').

(* Instruction set for the Thiele CPU.  [RunTMStep] performs a single
   Turing-machine transition via [tm_step_logic].  [AssertConsistency]
   consults the external oracle to check a set of axioms. *)
Inductive Instr :=
  | RunTMStep : Instr
  | AssertConsistency (axioms : list nat) : Instr.

(* Step interpreter.  It increases [mu_cost] on Turing-machine steps and
   sets [paradox_detected] when the oracle reports an inconsistency. *)
(* Sticky paradox: once set, remains set. *)
Definition step (instr : Instr) (st : CPUState) : CPUState :=
  if paradox_detected st then st else
  match instr with
  | RunTMStep =>
      if halted st then st else
      let '(q', tp', hd', hlt') := tm_step_logic st in
      {| state := q'; tape := tp'; head := hd'; halted := hlt';
         delta_fn := delta_fn st; blank_sym := blank_sym st;
         accept_state := accept_state st; reject_state := reject_state st;
         mu_cost := S (mu_cost st); paradox_detected := paradox_detected st |}
  | AssertConsistency axioms =>
      let consistent := logic_oracle axioms in
      {| state := state st; tape := tape st; head := head st; halted := halted st;
         delta_fn := delta_fn st; blank_sym := blank_sym st;
         accept_state := accept_state st; reject_state := reject_state st;
         mu_cost := mu_cost st; paradox_detected := paradox_detected st || negb consistent |}
  end.

(* Iterate [RunTMStep] a given number of times.  This is used for the
   subsumption theorem which only relies on the Turing-machine part of
   the interpreter. *)
Fixpoint step_n (st : CPUState) (n : nat) : CPUState :=
  match n with
  | 0%nat => st
  | S n' => step_n (step RunTMStep st) n'
  end.

(* --- μ-cost and paradox results --- *)

(* Total information cost: finite when no paradox has been detected,
   infinite (represented by [None]) otherwise. *)
Definition total_mu_cost (st : CPUState) : option nat :=
  if paradox_detected st then None else Some (mu_cost st).

Lemma mu_cost_stable_if_halted :
  forall st n,
    halted st = true -> paradox_detected st = false ->
    total_mu_cost (step_n st n) = total_mu_cost st.
Proof.
  intros st n Hhalt Hpar.
  induction n as [|n IH]; simpl; [reflexivity|].
  unfold step. rewrite Hpar, Hhalt. simpl. exact IH.
Qed.

Lemma mu_cost_strictly_increases :
  forall st,
    halted st = false -> paradox_detected st = false ->
    mu_cost (step RunTMStep st) = S (mu_cost st).
Proof.
  intros st Hhalt Hpar.
  unfold step. rewrite Hpar, Hhalt. simpl.
  destruct (tm_step_logic st) as [[[q' tp'] hd'] hlt'].
  reflexivity.
Qed.

Definition encode_tm_config (tm : TM nat nat)
           (conf : TMConfig) : CPUState :=
  let '(q, tp, hd) := conf in
  {| state := q; tape := tp; head := hd;
     halted := orb (Nat.eqb q (tm_accept _ _ tm)) (Nat.eqb q (tm_reject _ _ tm));
     delta_fn := tm_delta _ _ tm; blank_sym := tm_blank _ _ tm;
     accept_state := tm_accept _ _ tm; reject_state := tm_reject _ _ tm;
     mu_cost := 0%nat; paradox_detected := false |}.

Definition decode_cpu_state (st : CPUState) : TMConfig :=
  (state st, tape st, head st).

(* --- Subsumption.v --- *)

Lemma tm_cpu_simulates_step :
  forall (tm : TM nat nat) (conf : TMConfig),
    decode_cpu_state (step RunTMStep (encode_tm_config tm conf)) = tm_step tm conf.
Proof.
  intros tm [[q tp] hd].
  unfold decode_cpu_state, encode_tm_config, step, tm_step, tm_step_logic; simpl.
  destruct (orb (Nat.eqb q (tm_accept _ _ tm)) (Nat.eqb q (tm_reject _ _ tm))) eqn:Hhalt;
    try rewrite Hhalt; simpl; try reflexivity.
  remember (tm_delta nat nat tm q (nth hd tp (tm_blank nat nat tm))) as delta.
  destruct delta as [[q' write] move].
  destruct (Nat.ltb hd (length tp)); reflexivity.
Qed.

(* A detected paradox implies infinite cost. *)
Theorem cost_of_paradox_is_infinite :
  forall (st : CPUState),
    paradox_detected st = true -> total_mu_cost st = None.
Proof.
  intros st Hpar.
  unfold total_mu_cost.
  rewrite Hpar.
  reflexivity.
Qed.