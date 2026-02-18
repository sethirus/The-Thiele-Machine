(** * Embedding a reversible wave model into the Thiele VM

    This optional study mirrors the reversible lattice gas but focuses on a
    simple left/right propagating wave.  The embedding is abstract: any VM
    trace that simulates one [wave_step] with zero-cost instructions inherits
    the energy/momentum conservation laws and the µ-constancy/zero
    irreversibility guarantees provided by the ledger. *)

From Coq Require Import List Lia.
From Physics Require Import WaveModel.
From Kernel Require Import VMState VMStep MuLedgerConservation SimulationProof.
From ThieleManifold Require Import ThieleManifoldBridge PhysicsIsomorphism.

Import ListNotations.

