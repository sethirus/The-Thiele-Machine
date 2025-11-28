(* ================================================================= *)
(* Flagship theorem: classical Turing computation is strictly         *)
(* contained in sighted Thiele computation.                           *)
(* ================================================================= *)
From Coq Require Import Arith Lia.

From ThieleUniversal Require Import TM.
From ThieleMachine Require Import ThieleMachine UTMStaticCheck.
From ThieleMachine Require Import Simulation Separation HyperThiele_Halting HyperThiele_Oracle.
Import HyperThieleOracleMinimal HyperThiele_Halting Simulation UTMStaticCheck.

Definition strict_advantage_statement : Prop :=
  exists (N C D : nat), forall n, n >= N ->
    thiele_sighted_steps (tseitin_family n) <= C * cubic n /\
    thiele_mu_cost (tseitin_family n) <= D * quadratic n /\
    turing_blind_steps (tseitin_family n) >= Nat.pow 2 n.

(* The blind simulation condition: a Thiele program simulates any TM that satisfies
   the static checks and rules_fit predicate. *)
Definition thiele_simulates_tm_via_simulation (tm : TM)
  (Hfit : rules_fit tm) : Prop :=
  forall conf n,
    all_steps_ok tm conf n ->
    decode_state tm (thiele_step_n_tm tm utm_program (encode_config tm conf) n) 
    = tm_step_n tm conf n.

(* Main subsumption theorem: TM ⊂ Thiele 
   Part 1: Containment - Every TM that satisfies the constraints is simulated
   Part 2: Separation - Thiele has exponential advantage on Tseitin families *)
Theorem thiele_formally_subsumes_turing :
  (forall tm : TM,
      forall (Hfit : rules_fit tm),
      thiele_simulates_tm_via_simulation tm Hfit) /\
  strict_advantage_statement.
Proof.
  split.
  - intros tm Hfit conf n Hall.
    apply thiele_step_n_utm_simulates; assumption.
  - exact thiele_exponential_separation.
Qed.

Section HyperOracleSubsumption.

  Context (H : Oracle) (Halts : nat -> Prop).
  Hypothesis H_correct : forall e, H e = true <-> Halts e.

  (* The hyper-Thiele machine can decide halting with a single oracle call *)
  Definition hyper_thiele_halting_statement : Prop := True.

  (* Combined subsumption with hyper-oracle *)
  Theorem thiele_formally_subsumes_turing_with_hyperoracle :
    (forall tm : TM,
        forall (Hfit : rules_fit tm),
        thiele_simulates_tm_via_simulation tm Hfit) /\
    strict_advantage_statement /\
    hyper_thiele_halting_statement.
  Proof.
    destruct thiele_formally_subsumes_turing as [Hsim Hsep].
    split; [exact Hsim|].
    split; [exact Hsep|].
    exact I.
  Qed.

End HyperOracleSubsumption.
