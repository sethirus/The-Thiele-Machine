(**
  # ThieleMap – simulation roadmap scaffolding

  This file now references the concrete Thiele and Turing machine
  definitions that already exist in the repository so the remaining proof
  obligations can be stated precisely.  No new theorems are proved here;
  instead we package the key relations and spell out the statements that a
  future mechanisation must supply.  The overarching containment theorem is
  still left admitted so that the roadmap continues to track the work item
  without impacting the checked build.
*)

From Coq Require Import Relations List.
Import ListNotations.

From ThieleMachine.thielemachine.coqproofs Require Import ThieleMachine Simulation.
From ThieleUniversal Require Import TM.
From ThieleMachine.Modular_Proofs Require Import TM_Basics Thiele_Basics Simulation as ModularSimulation.

(** Thiele programs and their small-step relation. *)
Definition ThieleProgram := ThieleMachine.Prog.
Definition ThieleState := ThieleMachine.State.

Definition thiele_step (P : ThieleProgram) : relation ThieleState :=
  fun s s' => exists obs, ThieleMachine.step P s s' obs.

(** Classical Turing machines and their functional step. *)
Definition TuringMachine := ThieleUniversal.TM.
Definition TMConfig := ThieleUniversal.TMConfig.

Definition tm_step_rel (tm : TuringMachine) : relation TMConfig :=
  fun c c' => ThieleUniversal.tm_step tm c = c'.

(** Roadmap placeholder: relate concrete encodings used by the modular bridge. *)
Definition sim_rel (tm : TuringMachine)
  (sem : ModularThieleSemantics ThieleUniversal.tm_step)
  (tp : ThieleProgram) : Prop :=
  True.
(* TODO: tie [tp] to [sem] once the concrete encoding obligations are exposed. *)

Lemma sim_step_placeholder :
  forall tm sem tp,
    sim_rel tm sem tp -> True.
Proof. intros; exact I. Qed.

Lemma sim_run_placeholder :
  forall tm sem tp n,
    sim_rel tm sem tp -> True.
Proof. intros; exact I. Qed.

(** Finite-prefix simulation – discharged. *)
Lemma thiele_simulates_tm_prefix :
  forall (tm : TuringMachine) (conf : TMConfig) (n : nat),
    Simulation.config_ok tm conf ->
    Simulation.rules_fit tm ->
    Simulation.decode_state tm
      (Simulation.thiele_step_n_tm tm Simulation.utm_program
         (Simulation.encode_config tm conf) n)
    = ThieleUniversal.tm_step_n tm conf n.
Proof.
  intros tm conf n Hok Hfit.
  apply Simulation.thiele_step_n_utm_simulates; assumption.
Qed.

(** Target theorem: every Turing machine has a Thiele program simulator. *)
Theorem thiele_simulates_by_tm :
  exists tp : ThieleProgram,
    Simulation.Blind tp /\
    forall (tm : TuringMachine) (conf : TMConfig) (n : nat),
      Simulation.config_ok tm conf ->
      Simulation.rules_fit tm ->
      Simulation.decode_state tm
        (Simulation.thiele_step_n_tm tm tp (Simulation.encode_config tm conf) n)
      = ThieleUniversal.tm_step_n tm conf n.
Proof.
  exists Simulation.utm_program.
  split.
  - exact Simulation.utm_program_blind.
  - intros tm conf n Hok Hfit.
    apply Simulation.thiele_step_n_utm_simulates; assumption.
Qed.

(* End of ThieleMap.v *)
