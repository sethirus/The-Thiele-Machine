(**
  # Canonical Thiele universal interpreter summary

  The historical `ThieleUniversal.v` attempted to repeat the universal
  interpreter proof that now lives—completed and admit-free—in
  `ThieleMachine.Simulation`.  Rather than keep a divergent, unfinished copy,
  this file re-exports the live development and records the concrete bridges
  from the archived CPU artefacts (`UTM_Program`, `UTM_Encode`, …) to the
  abstract Thiele semantics.  Each lemma is a thin wrapper around the mechanised
  theorems so downstream artefacts can cite the results without depending on the
  entire simulation directory.

  The intent is twofold:
  1. Preserve the original namespace for legacy imports that still expect a
     `ThieleUniversal` module.
  2. Emphasise how the concrete bytecode and CPU-state helpers connect to the
     containment proof that shows the Thiele machine subsumes every classical
     Turing machine.
*)

From Coq Require Import List.
From ThieleUniversal Require Import TM UTM_Rules UTM_Program UTM_Encode CPU.
From ThieleMachine Require Import ThieleMachine Simulation ThieleUniversalBridge EncodingBridge.
Export Simulation.

Set Default Goal Selector "!".

Module TU := ThieleUniversal.TM.
Module UCPU := ThieleUniversal.CPU.

(** * Canonical program aliases and invariants *)

Definition thiele_program : Prog := Simulation.utm_program.
Definition cpu_program_words : list nat := ThieleUniversalBridge.program.
Definition cpu_initial_state (tm : TU.TM) (conf : TU.TMConfig) : UCPU.State :=
  Simulation.utm_cpu_state tm conf.

Lemma cpu_program_words_from_archive :
  cpu_program_words =
  flat_map UTM_Encode.encode_instr_words UTM_Program.program_instrs.
Proof. reflexivity. Qed.

Lemma cpu_program_words_fit_window :
  length cpu_program_words <= UTM_Program.RULES_START_ADDR.
Proof. apply Simulation.utm_program_fits. Qed.

Lemma cpu_rules_fit_window :
  forall tm,
    Simulation.rules_fit tm ->
    length (UTM_Encode.encode_rules tm.(TU.tm_rules))
    <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR.
Proof. exact (fun _ Hfit => Hfit). Qed.

Lemma cpu_program_is_blind : Simulation.Blind thiele_program.
Proof. exact Simulation.utm_program_blind. Qed.

Lemma cpu_initial_state_inv :
  forall tm conf,
    Simulation.rules_fit tm ->
    ThieleUniversal.inv (cpu_initial_state tm conf) tm conf.
Proof. apply Simulation.utm_cpu_state_inv_from_rules_fit. Qed.

Lemma cpu_initial_fetch_inv_core :
  forall tm conf,
    Simulation.rules_fit tm ->
    ThieleUniversal.inv_core
      (ThieleUniversal.run_n (cpu_initial_state tm conf) 3) tm conf.
Proof.
  intros tm [[q tape] head] Hfit.
  exact (Simulation.utm_fetch_inv_core tm q tape head Hfit).
Qed.

Lemma cpu_initial_fetch_guard :
  forall tm conf,
    Simulation.rules_fit tm ->
    Simulation.config_ok tm conf ->
    ThieleUniversal.find_rule_start_inv tm conf
      (ThieleUniversal.run_n (cpu_initial_state tm conf) 3).
Proof.
  intros tm [[q tape] head] Hfit Hok.
  unfold Simulation.config_ok, tm_config_ok in Hok.
  simpl in Hok.
  destruct Hok as [_ Hhead].
  apply (Simulation.utm_fetch_establishes_find_rule_start_inv_in_bounds
           tm q tape head); assumption.
Qed.

Lemma cpu_restart_fetch_pc3_cases :
  forall tm conf cpu_find,
    ThieleUniversal.inv_core cpu_find tm conf ->
    ThieleUniversal.find_rule_start_inv tm conf cpu_find ->
    Nat.eqb
      (UCPU.read_reg UCPU.REG_TEMP1 (ThieleUniversal.run_n cpu_find 4)) 0 = false ->
    Nat.eqb
      (UCPU.read_reg UCPU.REG_TEMP1 (ThieleUniversal.run_n cpu_find 6)) 0 = true ->
    Nat.eqb
      (UCPU.read_reg UCPU.REG_TEMP1 (ThieleUniversal.run_n cpu_find 14)) 0 = true ->
    exists steps,
      (steps = 37 \/ steps = 39) /\
      firstn (length ThieleUniversal.program)
        (UCPU.mem (ThieleUniversal.run_n cpu_find steps))
        = ThieleUniversal.program /\
      UCPU.read_reg UCPU.REG_PC (ThieleUniversal.run_n cpu_find steps) = 3.
Proof.
  intros tm conf cpu_find Hcore Hstart Hz4 Hz6 Hz14.
  apply (Simulation.utm_find_rule_restart_fetch_pc3_cases
           tm conf cpu_find Hcore Hstart Hz4 Hz6 Hz14).
Qed.

Lemma cpu_no_rule_preserves_configuration :
  forall tm conf cpu_find,
    Simulation.config_ok tm conf ->
    let '((q, tape), head) := conf in
    let sym := nth head tape tm.(TU.tm_blank) in
    Simulation.find_rule tm.(Simulation.tm_rules) q sym = None ->
    ThieleUniversal.inv_core cpu_find tm conf ->
    ThieleUniversal.find_rule_start_inv tm conf cpu_find ->
    Simulation.rules_fit tm ->
    Simulation.cpu_state_to_tm_config (ThieleUniversal.run_n cpu_find 10) = conf.
Proof.
  intros tm [[q tape] head] cpu_find Hok Hnone Hcore Hstart Hfit.
  apply (Simulation.utm_no_rule_preserves_cpu_config
           tm ((q, tape), head) cpu_find Hok Hnone Hcore Hstart Hfit).
Qed.

(** * Completed simulation theorems *)

Theorem thiele_universal_recap :
  exists tp : ThieleMachine.Prog,
    Simulation.Blind tp /\
    forall (tm : TU.TM) (conf : TU.TMConfig) (n : nat),
      Simulation.config_ok tm conf ->
      Simulation.rules_fit tm ->
      Simulation.decode_state tm
        (Simulation.thiele_step_n_tm tm tp (Simulation.encode_config tm conf) n)
      = TU.tm_step_n tm conf n.
Proof.
  exists Simulation.utm_program.
  split.
  - exact Simulation.utm_program_blind.
  - intros tm conf n Hok Hfit.
    apply Simulation.thiele_step_n_utm_simulates; assumption.
Qed.

Lemma utm_no_rule_preserves_cpu_config_summary :
  forall tm conf cpu_find,
    Simulation.config_ok tm conf ->
    let '((q, tape), head) := conf in
    let sym := nth head tape tm.(Simulation.tm_blank) in
    Simulation.find_rule tm.(Simulation.tm_rules) q sym = None ->
    Simulation.inv_core cpu_find tm conf ->
    Simulation.find_rule_start_inv tm conf cpu_find ->
    Simulation.rules_fit tm ->
    Simulation.cpu_state_to_tm_config (Simulation.run_n cpu_find 10) = conf.
Proof.
  intros tm [[q tape] head] cpu_find Hok Hnone Hcore Hstart Hfit.
  apply (Simulation.utm_no_rule_preserves_cpu_config
           tm ((q, tape), head) cpu_find Hok Hnone Hcore Hstart Hfit).
Qed.

Lemma thiele_prefix_simulation_summary :
  forall tm conf n,
    Simulation.config_ok tm conf ->
    Simulation.rules_fit tm ->
    Simulation.decode_state tm
      (Simulation.thiele_step_n_tm tm Simulation.utm_program
         (Simulation.encode_config tm conf) n)
    = TU.tm_step_n tm conf n.
Proof.
  intros tm conf n Hok Hfit.
  apply Simulation.thiele_step_n_utm_simulates; assumption.
Qed.

(** * Packaged witness for downstream consumers *)

Record interpreter_witness := {
  interpreter_prog : Prog;
  interpreter_blind : Simulation.Blind interpreter_prog;
  interpreter_exact :
    forall tm conf n,
      Simulation.config_ok tm conf ->
      Simulation.rules_fit tm ->
      Simulation.decode_state tm
        (Simulation.thiele_step_n_tm tm interpreter_prog
           (Simulation.encode_config tm conf) n)
      = TU.tm_step_n tm conf n
}.

Definition thiele_universal_witness : interpreter_witness.
Proof.
  refine {| interpreter_prog := thiele_program;
            interpreter_blind := cpu_program_is_blind |}.
  intros tm conf n Hok Hfit.
  apply thiele_prefix_simulation_summary; assumption.
Defined.

Corollary thiele_machine_subsumes_tm :
  forall tm conf n,
    Simulation.config_ok tm conf ->
    Simulation.rules_fit tm ->
    Simulation.decode_state tm
      (Simulation.thiele_step_n_tm tm thiele_universal_witness.(interpreter_prog)
         (Simulation.encode_config tm conf) n)
    = TU.tm_step_n tm conf n.
Proof.
  intros tm conf n Hok Hfit.
  apply thiele_universal_witness.(interpreter_exact); assumption.
Qed.
