From Coq Require Import List Arith Bool Nat.
Import ListNotations.

From ThieleMachine Require Import HyperThiele_Oracle ThieleMachine Oracle PartitionLogic.
Import HyperThieleOracleMinimal ThieleMachine.ThieleMachine.

Module HyperThiele_Halting.

  (**
    # HyperThiele halting oracle – experimental only

    The statements in this module assume a perfect halting oracle for the
    minimal HyperThiele language.  None of the lemmas below are part of the
    `make -C coq core` target; they live behind the dedicated ``make oracle``
    entry point so downstream work cannot accidentally rely on the hypothesis.
  *)


End HyperThiele_Halting.

(* End of HyperThiele_Halting.v *)
