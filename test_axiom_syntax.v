(** Test file to verify Variable→Axiom conversion syntax is correct *)

From Coq Require Import Reals Arith.

(** Test 1: Simple Axiom declaration (like in TsirelsonBoundProof.v) *)
Axiom sqrt2 : R.

(** Test 2: Axiom with universally quantified variables (like in MuInformationTheoreticBounds.v) *)
Axiom partition_bound : forall (n num_partitions : nat),
  (num_partitions > 0)%nat ->
  exists (required_mu : nat),
    (required_mu >= Nat.log2 num_partitions)%nat.

(** Test 3: Function type Axiom (like in QuantumBoundComplete.v) *)
Axiom VMState : Type.
Axiom some_function : nat -> VMState -> nat.

(** All syntax matches our Variable→Axiom conversions and is valid in Coq 8.18.0 *)
Theorem test_compiles : True.
Proof. trivial. Qed.
