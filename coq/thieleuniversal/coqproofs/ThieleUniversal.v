(**
  # Canonical Thiele universal interpreter summary

  This file re-exports the live development from `ThieleMachine.Simulation` and
  records the concrete bridges from the archived CPU artefacts to the abstract
  Thiele semantics.
*)

From Coq Require Import List Lia.
From ThieleUniversal Require Import TM UTM_Rules UTM_Program UTM_Encode CPU.
From ThieleMachine Require Import ThieleMachine Simulation EncodingBridge.
Export Simulation.

Set Default Goal Selector "!".

Module TU := ThieleUniversal.TM.
Module UCPU := ThieleUniversal.CPU.

(** * Canonical program aliases *)

Definition thiele_program : Prog := Simulation.utm_program.

Definition cpu_program_words : list nat :=
  flat_map UTM_Encode.encode_instr_words UTM_Program.program_instrs.

Definition cpu_initial_state (tm : TU.TM) (conf : TU.TMConfig) : UCPU.State :=
  Simulation.utm_cpu_state tm conf.

(** [cpu_rules_fit_window]: formal specification. *)
Lemma cpu_rules_fit_window :
  forall tm,
    Simulation.rules_fit tm ->
    List.length (UTM_Encode.encode_rules tm.(TU.tm_rules))
    <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR.
Proof. exact (fun _ Hfit => Hfit). Qed.

(** [cpu_program_is_blind]: formal specification. *)
Lemma cpu_program_is_blind : Simulation.Blind thiele_program.
Proof. exact Simulation.utm_program_blind. Qed.

(** * Completed simulation theorems

    NOTE: The theorems below use [all_steps_ok] as a precondition, which requires
    that ALL intermediate configurations satisfy [config_ok]. This is a stronger
    requirement than just checking the initial configuration.
    
    The reason is that [tm_step] can produce configurations that violate
    [config_ok] (e.g., head position may exceed SHIFT_LEN). Since the encoding/
    decoding roundtrip only works for valid configurations, we need to ensure
    validity is maintained throughout execution.
    
    For TMs that stay within bounds (e.g., those with bounded tape and head
    movement), [all_steps_ok] can be established from the TM's properties. *)

Theorem thiele_universal_recap :
  exists tp : ThieleMachine.Prog,
    Simulation.Blind tp /\
    forall (tm : TU.TM) (conf : TU.TMConfig) (n : nat),
      Simulation.all_steps_ok tm conf n ->
      Simulation.rules_fit tm ->
      Simulation.decode_state tm
        (Simulation.thiele_step_n_tm tm tp (Simulation.encode_config tm conf) n)
      = TU.tm_step_n tm conf n.
Proof.
  exists Simulation.utm_program.
  split.
  - exact Simulation.utm_program_blind.
  - intros tm conf n Hall Hfit.
    apply Simulation.thiele_step_n_utm_simulates; assumption.
Qed.

(** [thiele_prefix_simulation_summary]: formal specification. *)
Lemma thiele_prefix_simulation_summary :
  forall tm conf n,
    Simulation.all_steps_ok tm conf n ->
    Simulation.rules_fit tm ->
    Simulation.decode_state tm
      (Simulation.thiele_step_n_tm tm Simulation.utm_program
         (Simulation.encode_config tm conf) n)
    = TU.tm_step_n tm conf n.
Proof.
  intros tm conf n Hall Hfit.
  apply Simulation.thiele_step_n_utm_simulates; assumption.
Qed.

(** * Packaged witness for downstream consumers *)

Record interpreter_witness := {
  interpreter_prog : Prog;
  interpreter_blind : Simulation.Blind interpreter_prog;
  interpreter_exact :
    forall tm conf n,
      Simulation.all_steps_ok tm conf n ->
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
  intros tm conf n Hall Hfit.
  apply thiele_prefix_simulation_summary; assumption.
Defined.

(** [thiele_machine_subsumes_tm]: formal specification. *)
Corollary thiele_machine_subsumes_tm :
  forall tm conf n,
    Simulation.all_steps_ok tm conf n ->
    Simulation.rules_fit tm ->
    Simulation.decode_state tm
      (Simulation.thiele_step_n_tm tm thiele_universal_witness.(interpreter_prog)
         (Simulation.encode_config tm conf) n)
    = TU.tm_step_n tm conf n.
Proof.
  intros tm conf n Hall Hfit.
  apply thiele_universal_witness.(interpreter_exact); assumption.
Qed.
