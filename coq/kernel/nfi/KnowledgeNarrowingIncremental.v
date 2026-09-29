(** KnowledgeNarrowingIncremental: what an observer learns during a run.

    [KnowledgeNarrowing] compares the whole candidate set [Omega] with what
    the observer knows after a run. What the observer sees includes the
    first window, so a candidate set that the first window already splits
    narrows before any step runs. The incremental reading compares knowledge
    after the empty trace with knowledge after the trace: only what the run
    itself taught.

    The question it poses is how small a machine can teach an observer for
    free. A machine teaches for free when its prices meet the squeeze price,
    a trace of total cost zero runs, and the observer ends up with fewer
    candidates than it started with. [free_incremental_narrowing_with n]
    says a machine with exactly [n] states does this. *)

From Coq Require Import List Arith.PeanoNat.
Import ListNotations.
From Kernel Require Import PermanentCertification PermanentRecordPricing.
From Kernel Require Import KnowledgeNarrowing.

(** The drop in what the observer knows across the run, from the empty
    trace to [t], is paid for by the trace. *)
Definition incremental_observer_narrowing_priced
    {S I : Type} (step : S -> I -> S) (cost : I -> nat)
    {O : Type} (obs : S -> O) (obs_eq_dec : forall a b : O, {a = b} + {a <> b})
  : Prop :=
  forall Omega t s0,
    NoDup Omega -> In s0 Omega ->
    Nat.log2_up (length (knowledge step obs obs_eq_dec Omega [] s0)) -
    Nat.log2_up (length (knowledge step obs obs_eq_dec Omega t s0))
      <= trace_cost cost t.

(** A machine with exactly [n] states, priced by the squeeze price, on which
    a zero-cost trace strictly narrows what an observer knows. *)
Definition free_incremental_narrowing_with (n : nat) : Prop :=
  exists (S I O : Type) (all : list S) (step : S -> I -> S) (cost : I -> nat)
         (eq_dec : forall a b : S, {a = b} + {a <> b})
         (obs : S -> O) (obs_eq_dec : forall a b : O, {a = b} + {a <> b})
         (Omega : list S) (t : list I) (s0 : S),
    finite_states all /\ length all = n /\
    compression_priced step cost eq_dec /\
    NoDup Omega /\ In s0 Omega /\
    trace_cost cost t = 0 /\
    length (knowledge step obs obs_eq_dec Omega t s0) <
    length (knowledge step obs obs_eq_dec Omega [] s0).
