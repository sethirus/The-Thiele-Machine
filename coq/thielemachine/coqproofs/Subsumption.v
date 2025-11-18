(* ================================================================= *)
(* Flagship theorem: classical Turing computation is strictly         *)
(* contained in sighted Thiele computation.                           *)
(* ================================================================= *)
From Coq Require Import Arith Lia.

From ThieleUniversal Require Import TM.
From ThieleMachine Require Import ThieleMachine.
From ThieleMachine Require Import Simulation Separation HyperThiele_Halting HyperThiele_Oracle.
Import HyperThieleOracleMinimal HyperThiele_Halting.

Definition strict_advantage_statement : Prop :=
  exists (N C D : nat), forall n, n >= N ->
    thiele_sighted_steps (tseitin_family n) <= C * cubic n /\
    thiele_mu_cost (tseitin_family n) <= D * quadratic n /\
    turing_blind_steps (tseitin_family n) >= Nat.pow 2 n.

Theorem thiele_formally_subsumes_turing :
  (forall tm : TM
          (Hcat : catalogue_static_check tm = true)
          (Hfit : rules_fit tm),
      thiele_simulates_tm tm Hcat Hfit) /\
  strict_advantage_statement.
Proof.
  split.
  - intros tm Hcat Hfit.
    apply turing_contained_in_thiele; assumption.
  - exact thiele_exponential_separation.
Qed.

Section HyperOracleSubsumption.

  Context (H : Oracle) (Halts : nat -> Prop).
  Hypothesis H_correct : forall e, H e = true <-> Halts e.

  Definition hyper_thiele_halting_statement : Prop :=
    forall e, halting_solver_trace H Halts H_correct e = [true] <-> Halts e.

  Theorem thiele_formally_subsumes_turing_with_hyperoracle :
    (forall tm : TM
            (Hcat : catalogue_static_check tm = true)
            (Hfit : rules_fit tm),
        thiele_simulates_tm tm Hcat Hfit) /\
    strict_advantage_statement /\
    hyper_thiele_halting_statement.
  Proof.
    destruct thiele_formally_subsumes_turing as [Hsim Hsep].
    split; [exact Hsim|].
    split; [exact Hsep|].
    intros e. apply hyper_thiele_decides_halting_trace.
  Qed.

End HyperOracleSubsumption.
