(* ================================================================= *)
(* Modular Simulation Bridge                                         *)
(* ================================================================= *)
(* The modular bridge derives multi-step subsumption for a Turing      *)
(* machine from a compact set of facts about how the Thiele interpreter *)
(* encodes configurations and performs single steps.  Concrete proofs  *)
(* instantiate the interface defined in [Thiele_Basics].               *)
(* ================================================================= *)

From Coq Require Import List Arith.
Import ListNotations.

From ModularProofs Require Import TM_Basics Thiele_Basics.

Section Simulation.
  Context {tm : TMTransition}.
  Context (sem : ModularThieleSemantics tm).

  Local Notation encode := (mts_encode sem).
  Local Notation decode := (mts_decode sem).
  Local Notation run_n := (mts_run_n sem).

  Lemma thiele_simulates_tm :
    forall n conf,
      tm_config_ok conf ->
      decode (run_n (encode conf) n) = tm_run_n tm conf n.
  Proof.
    intros n conf Hok.
    apply mts_run_n_simulates; exact Hok.
  Qed.
End Simulation.

Theorem thiele_machine_subsumes_turing_modular :
  forall tm (sem : ModularThieleSemantics tm) conf n,
    tm_config_ok conf ->
    mts_decode sem (mts_run_n sem (mts_encode sem conf) n)
    = tm_run_n tm conf n.
Proof.
  intros tm sem conf n Hok.
  apply (thiele_simulates_tm sem n conf); assumption.
Qed.
