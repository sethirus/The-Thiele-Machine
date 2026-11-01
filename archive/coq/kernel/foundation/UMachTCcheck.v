(** UMachTCcheck.v: the condition "the host must be Thiele-complete", against
    the bare cheat of UMachCheatSmall.v.

    A Thiele-complete machine has three pairwise different moves of price
    exactly 1 (a CHECK, a COMMIT and a CERTIFY of clause (d)).  The bare
    cheat has one move of positive price (GSTEP1), so it is not
    Thiele-complete.  The condition is easily met by a host that still steps
    the guest with price-0 moves: see UMachHybrid.v.                       *)

From Coq Require Import List Arith Lia Bool.
Require Minimal.ThieleComplete.
Module TC := Minimal.ThieleComplete.
Require Import Kernel.UMachCheatSmall.

Theorem tc_three_paid : forall M, TC.thiele_complete M ->
  exists a b c : TC.m_move M,
    TC.m_cost M a = 1 /\ TC.m_cost M b = 1 /\ TC.m_cost M c = 1 /\
    a <> b /\ b <> c /\ a <> c.
Proof.
  intros M [I [_ [_ [[Hcost _] Hnv]]]].
  destruct Hnv as (cl & chk & cmt & crt & Hk1 & Hk2 & Hk3 & _).
  exists chk, cmt, crt.
  rewrite !Hcost. unfold TC.record_move. rewrite Hk1, Hk2, Hk3.
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [| split]; intros E; subst.
  - rewrite Hk1 in Hk2. discriminate.
  - rewrite Hk2 in Hk3. discriminate.
  - rewrite Hk1 in Hk3. discriminate.
Qed.

Definition cheat_machine : TC.machine := TC.mk_machine cst cmove cexec ccost cmir.

Theorem cheat_not_thiele_complete : ~ TC.thiele_complete cheat_machine.
Proof.
  intros H. destruct (tc_three_paid _ H) as (a & b & c & Ha & Hb & _ & Hab & _).
  simpl in a, b, Ha, Hb.
  destruct a; simpl in Ha; try discriminate.
  destruct b; simpl in Hb; try discriminate.
  apply Hab. reflexivity.
Qed.

Print Assumptions tc_three_paid.
Print Assumptions cheat_not_thiele_complete.
