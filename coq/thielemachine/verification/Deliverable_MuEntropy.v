From Coq Require Import QArith.
Open Scope Q_scope.

From ThieleMachine Require Export InfoTheory.

(** Deliverable: μ-cost split into description-length + Shannon-style entropy.

    The underlying definitions and proofs live in [ThieleMachine.InfoTheory].
    This file exists to provide a stable, user-facing entrypoint.
*)

Module DeliverableMuEntropy.

(* Re-exported definitions (for quick discovery):
   - question_cost
   - state_reduction_entropy
   - information_cost
   - mu_cost
   - shannon_entropy

   Re-exported key theorems:
   - mu_bounds_shannon_entropy
   - mu_cost_nonnegative
   - information_equals_shannon_reduction
*)

End DeliverableMuEntropy.
