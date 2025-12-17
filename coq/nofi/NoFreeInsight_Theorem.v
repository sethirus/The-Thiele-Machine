From Coq Require Import Arith.PeanoNat.

Require Import NoFI.NoFreeInsight_Interface.

(** * No-Free-Insight theorem (functor)

    This file proves the theorem for *any* system satisfying the interface.
    It contains **no `Axiom`** and **no `Admitted`**.
*)

Module NoFreeInsight (X : NO_FREE_INSIGHT_SYSTEM).
  Theorem no_free_insight :
    forall tr s0 s1 strength weak,
      X.clean_start s0 ->
      X.run tr s0 = Some s1 ->
      X.strictly_stronger strength weak ->
      X.certifies s1 strength ->
      X.structure_event tr s0.
  Proof.
    intros tr s0 s1 strength weak Hclean Hrun Hstrict Hcert.
    eapply X.no_free_insight_contract; eauto.
  Qed.
End NoFreeInsight.
