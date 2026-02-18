(** * Embedding the reversible lattice gas into the Thiele VM

    This optional study connects the discrete physics model from
    [Physics.DiscreteModel] to the verified VM semantics.  The encoding and
    compiled trace stay abstract; once a simulation lemma is available, the
    conservation laws and irreversibility bounds transport automatically. *)

From Coq Require Import List Lia.
From Physics Require Import DiscreteModel.
From Kernel Require Import VMState VMStep MuLedgerConservation SimulationProof.
From ThieleManifold Require Import ThieleManifoldBridge PhysicsIsomorphism.

Import ListNotations.


