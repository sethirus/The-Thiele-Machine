(* test_vscoq.v - VSCoq integration test *)
(* This file verifies basic Coq compilation works in VSCode. *)

Require Import Coq.Init.Datatypes.

Definition test_value : nat := 42.

Theorem test_reflexivity : test_value = 42.
Proof.
  reflexivity.
Qed.

(* End of VSCoq test file *)
