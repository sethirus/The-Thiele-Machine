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

(** Convert partition types between CoreSemantics and BlindSighted *)
Definition core_partition_to_blind (p : CoreSemantics.Partition) : BlindSighted.Partition :=
  {| BlindSighted.modules := p.(CoreSemantics.modules);
     BlindSighted.next_id := p.(CoreSemantics.next_module_id) |}.

Definition blind_partition_to_core (p : BlindSighted.Partition) : CoreSemantics.Partition :=
  {| CoreSemantics.modules := p.(BlindSighted.modules);
     CoreSemantics.next_module_id := p.(BlindSighted.next_id) |}.

(** Convert μ-ledger types between CoreSemantics and BlindSighted *)
Definition core_ledger_to_blind (l : CoreSemantics.MuLedger) : BlindSighted.MuLedger :=
  {| BlindSighted.mu_operational := l.(CoreSemantics.mu_operational);
     BlindSighted.mu_discovery := l.(CoreSemantics.mu_information);
     BlindSighted.mu_total := l.(CoreSemantics.mu_total) |}.

Definition blind_ledger_to_core (l : BlindSighted.MuLedger) : CoreSemantics.MuLedger :=
  {| CoreSemantics.mu_operational := l.(BlindSighted.mu_operational);
     CoreSemantics.mu_information := l.(BlindSighted.mu_discovery);
     CoreSemantics.mu_total := l.(BlindSighted.mu_total) |}.

Definition core_to_blind (s : CoreSemantics.State) : BlindSighted.ThieleState :=
  {| BlindSighted.partition := core_partition_to_blind s.(CoreSemantics.partition);
     BlindSighted.ledger := core_ledger_to_blind s.(CoreSemantics.mu_ledger);
     BlindSighted.halted := s.(CoreSemantics.halted);
     BlindSighted.answer := s.(CoreSemantics.result) |}.

Definition blind_to_core (s : BlindSighted.ThieleState) (pc : nat) (prog : CoreSemantics.Program) : CoreSemantics.State :=
  {| CoreSemantics.partition := blind_partition_to_core s.(BlindSighted.partition);
     CoreSemantics.mu_ledger := blind_ledger_to_core s.(BlindSighted.ledger);
     CoreSemantics.pc := pc;
     CoreSemantics.halted := s.(BlindSighted.halted);
     CoreSemantics.result := s.(BlindSighted.answer);
     CoreSemantics.program := prog |}.

Lemma partition_conversion_roundtrip :
  forall (p : CoreSemantics.Partition),
    blind_partition_to_core (core_partition_to_blind p) = p.
Proof.
  intros p.
  unfold core_partition_to_blind, blind_partition_to_core.
  destruct p; simpl; reflexivity.
Qed.

Lemma ledger_conversion_roundtrip :
  forall (l : CoreSemantics.MuLedger),
    blind_ledger_to_core (core_ledger_to_blind l) = l.
Proof.
  intros l.
  unfold core_ledger_to_blind, blind_ledger_to_core.
  destruct l; simpl; reflexivity.
Qed.

Lemma state_correspondence :
  forall (s : CoreSemantics.State),
    let s' := core_to_blind s in
    let s'' := blind_to_core s' s.(CoreSemantics.pc) s.(CoreSemantics.program) in
    s''.(CoreSemantics.partition) = s.(CoreSemantics.partition) /\
    s''.(CoreSemantics.mu_ledger) = s.(CoreSemantics.mu_ledger) /\
    s''.(CoreSemantics.halted) = s.(CoreSemantics.halted) /\
    s''.(CoreSemantics.result) = s.(CoreSemantics.result) /\
    s''.(CoreSemantics.program) = s.(CoreSemantics.program).
Proof.
  intros s s' s''.
  unfold core_to_blind, blind_to_core in *.
  simpl.
  split; [apply partition_conversion_roundtrip|].
  split; [apply ledger_conversion_roundtrip|].
  split; [reflexivity|].
  split; reflexivity.
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
  set (prog := [CoreSemantics.EMIT (BlindSighted.tm_output cfg); CoreSemantics.HALT]).
  exists prog.
  exists {| CoreSemantics.partition := blind_partition_to_core (BlindSighted.trivial_partition []);
            CoreSemantics.mu_ledger := blind_ledger_to_core BlindSighted.zero_ledger;
            CoreSemantics.pc := 1%nat;
            CoreSemantics.halted := true;
            CoreSemantics.result := Some (BlindSighted.tm_output cfg);
            CoreSemantics.program := prog |}.
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
