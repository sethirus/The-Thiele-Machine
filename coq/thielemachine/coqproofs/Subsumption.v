(* ================================================================= *)
(* Flagship theorem: classical Turing computation is strictly         *)
(* contained in sighted Thiele computation.                           *)
(* ================================================================= *)
From Coq Require Import Arith Lia.

From ThieleUniversal Require Import TM.
From ThieleMachine Require Import ThieleMachine.
From ThieleMachine Require Import Simulation Separation.

Definition strict_advantage_statement : Prop :=
  exists (N C D : nat), forall n, n >= N ->
    thiele_sighted_steps (tseitin_family n) <= C * cubic n /\
    thiele_mu_cost (tseitin_family n) <= D * quadratic n /\
    turing_blind_steps (tseitin_family n) >= Nat.pow 2 n.

Theorem thiele_formally_subsumes_turing :
  (forall tm : TM, thiele_simulates_tm tm) /\
  strict_advantage_statement.
Proof.
  split.
  - apply turing_contained_in_thiele.
  - exact thiele_exponential_separation.
Qed.
