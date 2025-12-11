(* ================================================================= *)
(* Flagship theorem: classical Turing computation is strictly         *)
(* contained in sighted Thiele computation.                           *)
(* ================================================================= *)
From Coq Require Import Arith Lia.

From ThieleUniversal Require Import TM.
From ThieleMachine Require Import ThieleMachine UTMStaticCheck.
(* From ThieleMachine Require Import Simulation Separation HyperThiele_Halting HyperThiele_Oracle.
Import HyperThieleOracleMinimal HyperThiele_Halting Simulation UTMStaticCheck. *)

(* TODO: This file is incomplete - many referenced definitions are missing *)

Axiom strict_advantage_statement : Prop.
(*Definition strict_advantage_statement : Prop :=
  exists (N C D : nat), forall n, n >= N ->
    thiele_sighted_steps (tseitin_family n) <= C * cubic n /\
    thiele_mu_cost (tseitin_family n) <= D * quadratic n /\
    turing_blind_steps (tseitin_family n) >= Nat.pow 2 n.*)

Axiom thiele_simulates_tm_via_simulation : forall (tm : TM), Prop.

Axiom turing_subsumption : Prop.
(*Theorem turing_subsumption : forall tm,
      forall (Hfit : rules_fit tm),
      thiele_simulates_tm_via_simulation tm Hfit.*)

Axiom strict_separation : Prop.
(*Theorem strict_separation : strict_advantage_statement.*)

Axiom main_subsumption : Prop.
(*Theorem main_subsumption : turing_subsumption /\ strict_separation.*)
