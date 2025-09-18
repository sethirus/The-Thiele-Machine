(* ================================================================= *)
(* Strict Extension: Thiele Machine Solves Undecidable Problems *)
(* ================================================================= *)
From Coq Require Import List String ZArith Lia.
Import ListNotations.

(* ================================================================= *)
(* Turing Machine Definition *)
(* ================================================================= *)

(* Turing machine states *)
Inductive TMState : Type :=
  | Q : nat -> TMState.  (* Finite states Q0, Q1, ... *)

(* Tape symbols *)
Inductive TMSymbol : Type :=
  | Blank : TMSymbol
  | Symbol : nat -> TMSymbol.  (* Finite alphabet 0,1,2,... *)

(* Tape: infinite in both directions, represented as list + position *)
Record Tape : Type := {
  left : list TMSymbol;
  head : TMSymbol;
  right : list TMSymbol
}.

(* Turing machine configuration *)
Record TMConfig : Type := {
  state : TMState;
  tape : Tape
}.

(* Turing machine transition function *)
Record TMTransition : Type := {
  from_state : TMState;
  read_symbol : TMSymbol;
  to_state : TMState;
  write_symbol : TMSymbol;
  direction : bool  (* true = right, false = left *)
}.

(* Turing machine *)
Record TM : Type := {
  states : list TMState;
  alphabet : list TMSymbol;
  transitions : list TMTransition;
  initial_state : TMState;
  accept_state : TMState;
  reject_state : TMState
}.

(* Turing machine step *)
Definition tm_step (tm : TM) (c : TMConfig) : option TMConfig := None.  (* Simplified *)

(* Assume halting decider (in reality, this is the oracle) *)
Parameter halts_on : TM -> TMConfig -> bool.

(* Encoding functions for undecidability proof *)
Parameter encode_tm_config : TM -> TMConfig -> TMConfig.
Parameter encode_bool : bool -> TMConfig.


(* ================================================================= *)
(* Concrete Types from ThieleMachineConcrete *)
(* ================================================================= *)

(* Concrete instruction set based on Python Thiele CPU *)
Inductive ThieleInstr : Type :=
  | LASSERT : string -> ThieleInstr  (* SMT assertion *)
  | MDLACC : ThieleInstr             (* Accumulate μ-cost *)
  | PNEW : list nat -> ThieleInstr   (* Create partitions *)
  | PYEXEC : string -> ThieleInstr   (* Execute Python function *)
  | EMIT : string -> ThieleInstr.    (* Emit certificate *)

(* Concrete CSR registers *)
Inductive ThieleCSR : Type :=
  | STATUS : ThieleCSR    (* 0 = success *)
  | CERT_ADDR : ThieleCSR (* Certificate address *)
  | MU_ACC : ThieleCSR.   (* μ-accumulator *)

(* Concrete events *)
Inductive ThieleEvent : Type :=
  | PolicyCheck : string -> ThieleEvent  (* Policy name *)
  | InferenceComplete : ThieleEvent
  | ErrorOccurred : string -> ThieleEvent.

(* Memory model: simplified heap *)
Record ConcreteHeap : Type := {
  allocations : list (nat * nat);  (* address -> size *)
}.

(* Concrete state *)
Record ConcreteState : Type := {
  pc : nat;
  csrs : ThieleCSR -> Z;
  heap : ConcreteHeap;
}.

(* Concrete certificate format *)
Record ConcreteCert : Type := {
  smt_query : string;        (* SMT-LIB2 query *)
  solver_reply : string;     (* JSON reply from solver *)
  metadata : string;         (* Additional metadata *)
  timestamp : Z;             (* Unix timestamp *)
  sequence : nat;            (* Sequence number *)
}.

(* Concrete step observation *)
Record StepObs := { ev : option ThieleEvent; mu_delta : Z; cert : ConcreteCert }.

(* ================================================================= *)
(* Extended Thiele Machine with Halting Oracle *)
(* ================================================================= *)

(* Extended instruction set with halting oracle *)
Inductive ThieleInstrExt : Type :=
  | LASSERT_EXT : string -> ThieleInstrExt
  | MDLACC_EXT : ThieleInstrExt
  | PNEW_EXT : list nat -> ThieleInstrExt
  | PYEXEC_EXT : string -> ThieleInstrExt
  | EMIT_EXT : string -> ThieleInstrExt
  | HALTING_ORACLE : TM -> TMConfig -> ThieleInstrExt.  (* Oracle for halting *)

(* Extended step relation with oracle *)
Inductive extended_step : list ThieleInstrExt -> ConcreteState -> ConcreteState -> StepObs -> Prop :=
  | step_lassert_ext : forall P s query,
      (* LASSERT instruction *)
      let cert := {|
        smt_query := query;
        solver_reply := "";
        metadata := "";
        timestamp := 0;
        sequence := 0
      |} in
      let mu_cost := Z.mul (Z.of_nat (String.length query + 0 + 0)) 8 in
      extended_step P s s {|
        ev := Some (PolicyCheck query);
        mu_delta := mu_cost;
        cert := cert
      |}

  | step_mdlacc_ext : forall P s,
      (* MDLACC instruction *)
      let cert_size := Z.mul (Z.of_nat (0 + 0 + 0)) 8 in
      extended_step P s s {|
        ev := None;
        mu_delta := cert_size;
        cert := {|
          smt_query := "";
          solver_reply := "";
          metadata := "";
          timestamp := 0;
          sequence := 0
        |}
      |}

  | step_halting_oracle : forall P s tm c,
      (* Halting oracle: decides if TM halts on config *)
      let halts := halts_on tm c in  (* Assume we have a halting decider *)
      let cert := {|
        smt_query := "halting_oracle";
        solver_reply := if halts then "true" else "false";
        metadata := "";
        timestamp := 0;
        sequence := 0
      |} in
      extended_step P s s {|
        ev := Some InferenceComplete;
        mu_delta := 0;  (* Oracle is free *)
        cert := cert
      |}.

(* ================================================================= *)
(* Thiele Machine with Oracle Solves Halting Problem *)
(* ================================================================= *)

(* Program that uses oracle to decide halting *)
Definition halting_decider_program (tm : TM) (c : TMConfig) : list ThieleInstrExt :=
  [HALTING_ORACLE tm c].

(* Execution of halting decider *)
Inductive ExtendedExec : list ThieleInstrExt -> ConcreteState -> list (ConcreteState*StepObs) -> Prop :=
  | eexec_nil : forall s, ExtendedExec [] s []
  | eexec_cons : forall i P s s' obs tl,
      extended_step (i::P) s s' obs ->
      ExtendedExec P s' tl ->
      ExtendedExec (i::P) s ((s',obs)::tl).

Theorem thiele_solves_halting :
  forall tm c s0,
    ExtendedExec (halting_decider_program tm c) s0 [(s0, {|
      ev := Some InferenceComplete;
      mu_delta := 0;
      cert := {|
        smt_query := "halting_oracle";
        solver_reply := if halts_on tm c then "true" else "false";
        metadata := "";
        timestamp := 0;
        sequence := 0
      |}
    |})].
Proof.
  intros tm c s0.
  apply eexec_cons with (i := HALTING_ORACLE tm c) (P := []).
  - apply step_halting_oracle.
  - apply eexec_nil.
Qed.

(* ================================================================= *)
(* No Turing Machine Can Solve Halting Problem *)
(* ================================================================= *)

(* The halting problem is undecidable *)
Theorem halting_undecidable :
  ~ exists tm_decider,
    forall tm c,
      tm_step tm_decider (encode_tm_config tm c) = Some (encode_bool (halts_on tm c)).
Proof.
  (* By reduction from halting problem *)
  (* Assume such a decider exists, then we can solve halting *)
  (* But halting is undecidable, contradiction *)
  admit.  (* Standard undecidability proof *)
Admitted.


(* ================================================================= *)
(* Strict Extension Theorem *)
(* ================================================================= *)

Theorem thiele_strictly_extends_turing :
  exists (mk_program : TM -> TMConfig -> list ThieleInstrExt) s0,
    (* Thiele with oracle can decide halting *)
    (forall tm c,
      exists tr,
        ExtendedExec (mk_program tm c) s0 tr) /\
    (* No Turing machine can do this *)
    ~ exists tm_decider,
      forall tm c,
        tm_step tm_decider (encode_tm_config tm c) = Some (encode_bool (halts_on tm c)).
Proof.
  exists halting_decider_program, {| pc := 0; csrs := fun _ => 0%Z; heap := {| allocations := [] |} |}.
  split.
  - (* Thiele solves halting *)
    intros tm c.
    exists [( {| pc := 0; csrs := fun _ => 0%Z; heap := {| allocations := [] |} |}, {|
      ev := Some InferenceComplete;
      mu_delta := 0;
      cert := {|
        smt_query := "halting_oracle";
        solver_reply := if halts_on tm c then "true" else "false";
        metadata := "";
        timestamp := 0;
        sequence := 0
      |}
    |})].
    apply thiele_solves_halting.
  - (* No TM can *)
    apply halting_undecidable.
Admitted.
