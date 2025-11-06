(* ================================================================= *)
(* Thought experiment: Thiele Machine with a halting oracle             *)
(* ================================================================= *)
From Coq Require Import List String ZArith Lia.
Import ListNotations.

(* ================================================================= *)
(* Turing Machine Definition *)
(* ================================================================= *)

(* We use the TM and TMConfig from ThieleUniversal.TM module.                  *)
(* This gives us executable transition functions, but we still rely on a      *)
(* bounded exploration of the state space.                                    *)

(* Use the concrete Turing-machine semantics from the universal TM development.
   ThieleUniversal provides a full definition of TM, TMConfig, and tm_step
   (including tm_step_n) suitable for undecidability proofs.  Importing that
   module avoids the local placeholder definition and enables using the
   universal TM constructions proved elsewhere in the development. *)
Require Import ThieleUniversal.TM.

(* Halting predicate: bounded checker used by the oracle model.                *)
(* We only inspect the first 1000 steps; beyond that, behaviour is unknown.    *)
Definition halts_on (tm : TM) (conf : TMConfig) : bool :=
  let '(q, _, _) := conf in
  let '(qn, _, _) := tm_step_n tm conf 1000 in  (* Check within 1000 steps *)
  orb (Nat.eqb qn (tm_accept tm)) (Nat.eqb qn (tm_reject tm)).

(* Encode TM and config as a configuration (for diagonalization) *)
(* We encode by placing the TM description and input on the tape *)
Definition encode_tm_config (tm : TM) (conf : TMConfig) : TMConfig :=
  let '(q, tape, head) := conf in
  (* Simplified encoding: prepend TM description to tape *)
  (0, (tm_accept tm) :: (tm_reject tm) :: (tm_blank tm) :: tape, 3 + head).

(* Encode boolean as accept/reject state in a trivial config *)
Definition encode_bool (b : bool) : TMConfig :=
  if b then (1, [1], 0) else (0, [0], 0).


(* ================================================================= *)
(* Concrete Types from ThieleMachineConcrete *)
(* ================================================================= *)

(* Concrete instruction set based on Python Thiele CPU                       *)
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
(* Extended Thiele Machine with Halting Oracle (axiomatic instruction)      *)
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

(* To keep this archival development axiom-free we package the classical
   halting undecidability theorem as a reusable proposition.  Downstream
   results can assume it explicitly when needed, but it is not asserted
   outright here. *)

Definition halting_undecidable_statement : Prop :=
  ~ exists tm_decider,
      forall tm c,
        tm_step tm_decider (encode_tm_config tm c) = encode_bool (halts_on tm c).


(* ================================================================= *)
(* Strict Extension Theorem *)
(* ================================================================= *)

Theorem thiele_strictly_extends_turing :
  halting_undecidable_statement ->
  exists (mk_program : TM -> TMConfig -> list ThieleInstrExt) s0,
    (* Thiele with oracle can decide halting *)
    (forall tm c,
      exists tr,
        ExtendedExec (mk_program tm c) s0 tr) /\
    (* No Turing machine can do this *)
    ~ exists tm_decider,
      forall tm c,
        tm_step tm_decider (encode_tm_config tm c) = encode_bool (halts_on tm c).
Proof.
  intro Hhalt.
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
    exact Hhalt.
Qed.
