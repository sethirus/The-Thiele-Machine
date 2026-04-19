From Coq Require Import Arith.PeanoNat.

Require Import NoFI.NoFreeInsight_Interface.

(** No-Free-Insight theorem functor.

  This file packages the generic theorem for any system satisfying the
  interface in NoFreeInsight_Interface.v. There is no extra theory here and
  no hidden axiom layer. The whole point is that once an instance proves the
  interface obligations, the no-free-insight theorem drops out immediately.
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
