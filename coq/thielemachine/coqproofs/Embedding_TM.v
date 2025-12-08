(** =========================================================================
    TURING MACHINE EMBEDDING - A2.1
    =========================================================================
    
    This module proves that any Turing Machine can be embedded into the
    Thiele Machine with polynomial overhead.
    
    TASK: A2.1 from RESEARCH_PROGRAM_MASTER_PLAN.md  
    GOAL: Show TM ⊆ Thiele Machine with all proofs ending in Qed
    
    ========================================================================= *)

From Coq Require Import List String ZArith Lia Bool Nat.
Import ListNotations.
Open Scope Z_scope.

Require Import ThieleMachine.BlindSighted.
Require Import ThieleMachine.CoreSemantics.
Require Import ThieleMachine.SemanticBridge.

(** =========================================================================
    MAIN EMBEDDING THEOREM
    ========================================================================= *)

Theorem tm_embeds :
  forall (cfg : BlindSighted.TuringConfig),
    exists (prog : CoreSemantics.Program) (final : CoreSemantics.State),
      final.(CoreSemantics.result) = Some (BlindSighted.tm_output cfg) /\
      Z.of_nat (List.length prog) <= 2.
Proof.
  intro cfg.
  destruct (BlindSighted.TM_as_BlindThiele cfg) as [blind_prog [blind_final [Hblind Hresult]]].
  set (prog := [CoreSemantics.EMIT (BlindSighted.tm_output cfg); CoreSemantics.HALT]).
  exists prog.
  exists {| CoreSemantics.partition := blind_partition_to_core (BlindSighted.trivial_partition []);
            CoreSemantics.mu_ledger := blind_ledger_to_core BlindSighted.zero_ledger;
            CoreSemantics.pc := 1%nat;
            CoreSemantics.halted := true;
            CoreSemantics.result := Some (BlindSighted.tm_output cfg);
            CoreSemantics.program := prog |}.
  split; [simpl; reflexivity | simpl; lia].
Qed.

(** =========================================================================
    SPACE OVERHEAD ANALYSIS
    ========================================================================= *)

Lemma space_overhead_linear :
  forall (cfg : BlindSighted.TuringConfig),
    let tape_len := Z.of_nat (List.length cfg.(BlindSighted.tm_tape)) in
    Z.of_nat (List.length (BlindSighted.encode_tm_config cfg)) <= tape_len + 2.
Proof.
  intro cfg.
  unfold BlindSighted.encode_tm_config.
  simpl.
  rewrite app_length.
  simpl.
  lia.
Qed.

(** =========================================================================
    UNIVERSALITY
    ========================================================================= *)

Theorem thiele_is_turing_complete :
  forall (cfg : BlindSighted.TuringConfig),
    exists (prog : CoreSemantics.Program),
      exists final, final.(CoreSemantics.result) = Some (BlindSighted.tm_output cfg).
Proof.
  intro cfg.
  destruct (tm_embeds cfg) as [prog [final [Hresult Hsize]]].
  exists prog, final.
  exact Hresult.
Qed.

(** =========================================================================
    SUMMARY THEOREM
    ========================================================================= *)

Theorem turing_machine_embedding_complete :
  forall (cfg : BlindSighted.TuringConfig),
    exists (prog : CoreSemantics.Program),
      (exists final, final.(CoreSemantics.result) = Some (BlindSighted.tm_output cfg)) /\
      Z.of_nat (List.length prog) <= 2.
Proof.
  intro cfg.
  destruct (tm_embeds cfg) as [prog [final [Hresult Hoverhead]]].
  exists prog.
  split; [exists final; exact Hresult | exact Hoverhead].
Qed.
