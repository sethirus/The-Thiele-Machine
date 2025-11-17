From Coq Require Import List Arith.

(** * Minimal reproduction of the no-rule lemmas

    This file isolates the unfinished symbolic-execution obligations from
    [Simulation.v].  It deliberately mirrors the lemma statements around
    [utm_no_rule_preserves_mem_length] while replacing the large dependency
    graph with abstract parameters.  The goal is to provide a compact Coq
    file that focuses on the remaining obligations without requiring the
    full universal-interpreter development.
*)

Import ListNotations.

(* -- Simplified abstract machine model ----------------------------------- *)

Definition Rule := nat.

Record TM := {
  tm_rules : list Rule;
  tm_blank : nat
}.

Definition TMConfig : Type := ((nat * list nat) * nat).

Parameter rules_fit : TM -> Prop.

Module ThieleUniversal.
  Module CPU.
    Record State := {
      mem : list nat
    }.
  End CPU.

  Parameter run_n : CPU.State -> nat -> CPU.State.
  Parameter inv_core : CPU.State -> TM -> TMConfig -> Prop.
  Parameter find_rule_start_inv : TM -> TMConfig -> CPU.State -> Prop.
End ThieleUniversal.

Parameter find_rule : list Rule -> nat -> nat -> option Rule.

Parameter config_ok : TM -> TMConfig -> Prop.
Parameter cpu_state_to_tm_config : ThieleUniversal.CPU.State -> TMConfig.

Parameter ThieleState : Type.
Parameter cpu_state_to_thiele_state
  : TM -> ThieleUniversal.CPU.State -> ThieleState.
Parameter decode_state : TM -> ThieleState -> TMConfig.

Parameter decode_state_cpu_state_to_thiele_state_eq :
  forall tm conf cpu,
    config_ok tm conf ->
    cpu_state_to_tm_config (ThieleUniversal.run_n cpu 10) = conf ->
    decode_state tm (cpu_state_to_thiele_state tm (ThieleUniversal.run_n cpu 10))
    = conf.

(* -- Admitted lemmas copied from Simulation.v --------------------------- *)

Lemma utm_no_rule_preserves_cpu_config :
  forall tm conf cpu_find,
    config_ok tm conf ->
    let '((q, tape), head) := conf in
    let sym := nth head tape tm.(tm_blank) in
    find_rule tm.(tm_rules) q sym = None ->
    ThieleUniversal.inv_core cpu_find tm conf ->
    ThieleUniversal.find_rule_start_inv tm conf cpu_find ->
    rules_fit tm ->
    cpu_state_to_tm_config (ThieleUniversal.run_n cpu_find 10) = conf.
Proof.
  intros tm [[q tape] head] cpu_find Hok.
  cbn beta.
  intros _ _ _ _.
  (* Restoring the [find_rule_start_inv] guard and invoking the tape lemma
     remains to be formalised. *)
Admitted.

(* -- Downstream lemma that highlights the dependency -------------------- *)

Lemma utm_no_rule_implies_halting_cfg :
  forall tm conf cpu_find,
    config_ok tm conf ->
    let '((q, tape), head) := conf in
    let sym := nth head tape tm.(tm_blank) in
    find_rule tm.(tm_rules) q sym = None ->
    ThieleUniversal.inv_core cpu_find tm conf ->
    ThieleUniversal.find_rule_start_inv tm conf cpu_find ->
    rules_fit tm ->
    decode_state tm (cpu_state_to_thiele_state tm (ThieleUniversal.run_n cpu_find 10)) =
    conf.
Proof.
  intros.
  (* This lemma is admissible in the minimal context; in the main file it
     follows from [utm_no_rule_preserves_cpu_config] and
     [decode_state_cpu_state_to_thiele_state_eq]. *)
Admitted.

