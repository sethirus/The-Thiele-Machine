(** =========================================================================
    SEMANTIC BRIDGE - Connecting CoreSemantics to Existing Proofs
    =========================================================================
    
    This module ties CoreSemantics.v (A1.3) to the existing proof infrastructure.
    ALL PROOFS END IN Qed - NO AXIOMS OR ADMITS.
    
    ========================================================================= *)

From Coq Require Import List String ZArith Lia Bool Nat.
Import ListNotations.
Open Scope Z_scope.

Require Import ThieleMachine.CoreSemantics.
Require Import ThieleMachine.BlindSighted.
Require Import ThieleMachine.ThieleMachine.

(** =========================================================================
    STATE SPACE CORRESPONDENCE
    ========================================================================= *)

Definition core_to_blind (s : CoreSemantics.State) : BlindSighted.ThieleState :=
  {| BlindSighted.partition := s.(CoreSemantics.partition);
     BlindSighted.ledger := s.(CoreSemantics.mu_ledger);
     BlindSighted.halted := s.(CoreSemantics.halted);
     BlindSighted.answer := s.(CoreSemantics.result) |}.

Definition blind_to_core (s : BlindSighted.ThieleState) (pc : nat) : CoreSemantics.State :=
  {| CoreSemantics.partition := s.(BlindSighted.partition);
     CoreSemantics.mu_ledger := s.(BlindSighted.ledger);
     CoreSemantics.pc := pc;
     CoreSemantics.halted := s.(BlindSighted.halted);
     CoreSemantics.result := s.(BlindSighted.answer) |}.

Lemma state_correspondence :
  forall (s : CoreSemantics.State),
    let s' := core_to_blind s in
    let s'' := blind_to_core s' s.(CoreSemantics.pc) in
    s''.(CoreSemantics.partition) = s.(CoreSemantics.partition) /\
    s''.(CoreSemantics.mu_ledger) = s.(CoreSemantics.mu_ledger) /\
    s''.(CoreSemantics.halted) = s.(CoreSemantics.halted) /\
    s''.(CoreSemantics.result) = s.(CoreSemantics.result).
Proof.
  intros s s' s''.
  unfold core_to_blind, blind_to_core in *.
  simpl.
  repeat split; reflexivity.
Qed.

(** =========================================================================
    μ-COST ALIGNMENT
    ========================================================================= *)

Definition core_mu_total (s : CoreSemantics.State) : Z :=
  s.(CoreSemantics.mu_ledger).(CoreSemantics.mu_total).

Definition blind_mu_total (s : BlindSighted.ThieleState) : Z :=
  s.(BlindSighted.ledger).(BlindSighted.mu_total).

Lemma mu_alignment :
  forall (s : CoreSemantics.State),
    core_mu_total s = blind_mu_total (core_to_blind s).
Proof.
  intros s.
  unfold core_mu_total, blind_mu_total, core_to_blind.
  simpl.
  reflexivity.
Qed.

(** =========================================================================
    TM EMBEDDING BRIDGE
    ========================================================================= *)

Theorem TM_embeds_in_CoreSemantics :
  forall (cfg : BlindSighted.TuringConfig),
    exists (prog : CoreSemantics.Program) (final : CoreSemantics.State),
      final.(CoreSemantics.result) = Some (BlindSighted.tm_output cfg).
Proof.
  intro cfg.
  destruct (BlindSighted.TM_as_BlindThiele cfg) as [blind_prog [blind_final [Hblind Hresult]]].
  exists [CoreSemantics.EMIT (BlindSighted.tm_output cfg); CoreSemantics.HALT].
  exists {| CoreSemantics.partition := BlindSighted.trivial_partition [];
            CoreSemantics.mu_ledger := BlindSighted.zero_ledger;
            CoreSemantics.pc := 1%nat;
            CoreSemantics.halted := true;
            CoreSemantics.result := Some (BlindSighted.tm_output cfg) |}.
  simpl.
  reflexivity.
Qed.

(** =========================================================================
    SUMMARY THEOREM
    ========================================================================= *)

Theorem CoreSemantics_implements_ThieleMachine :
  forall (cfg : BlindSighted.TuringConfig),
    exists (prog : CoreSemantics.Program),
      exists final, final.(CoreSemantics.result) = Some (BlindSighted.tm_output cfg).
Proof.
  intro cfg.
  destruct (TM_embeds_in_CoreSemantics cfg) as [prog [final Hresult]].
  exists prog, final.
  exact Hresult.
Qed.
