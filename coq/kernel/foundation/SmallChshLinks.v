(** SmallChshLinks.v: the CHSH check on the small machine as an instance of
    the book's CertificationSystem record.

    SmallChshMachine.v fills the property language of the machine of
    EarnedMulti.v with one property, small_chsh_PCHSH, whose checker is the
    integer CHSH check of SmallChshCheck.v. This file reads that machine as
    a CertificationSystem, with no new assumptions:

      - the machine over PCHSH is a CertificationSystem, so the trace floor
        of universal_nfi_any_substrate holds for it
                                       [small_chsh_cs, small_chsh_cs_floor];
      - a run from a clean start that raises the flag pays at least 3 on the
        record, and in the same run the counter that was committed held a
        tally that passes the check, whose pinned matrix is positive
        semidefinite, and whose score obeys the Tsirelson bound
                                       [small_chsh_certified_floor];
      - the chain CHECK, COMMIT, CERTIFY on any counter lists exactly 3 on
        the record, the floor of the run that certifies a passing tally
                                       [small_chsh_chain_cost].              *)

From Coq Require Import List Arith Lia Reals.
Import ListNotations.
From Kernel Require Import UniversalCertificationCost.
Require Kernel.UniversalInterpreterLinks.
Require Kernel.SmallChshCheck.
Require Kernel.SmallChshMachine.
Require Minimal.EarnedMulti.
Module M := Minimal.EarnedMulti.
Module L := Kernel.UniversalInterpreterLinks.
Module S := Kernel.SmallChshMachine.
Module K := Kernel.SmallChshCheck.

(* The machine of EarnedMulti.v with the one property PCHSH, read as a
   CertificationSystem. *)
Definition small_chsh_cs : CertificationSystem :=
  L.multi_cs S.small_chsh_prop_eqb S.small_chsh_eval.

(* Any trace that raises the flag costs at least 1 on the record. *)
Theorem small_chsh_cs_floor : forall (tr : list (@M.instr S.small_chsh_prop))
    (s0 : @M.state S.small_chsh_prop),
  M.cert s0 = false ->
  M.cert (M.run S.small_chsh_prop_eqb S.small_chsh_eval tr s0) = true ->
  cs_total_cost small_chsh_cs tr >= 1.
Proof.
  intros tr s0 H0 H1.
  unfold small_chsh_cs. rewrite L.multi_cs_cost.
  exact (@L.multi_cs_floor S.small_chsh_prop S.small_chsh_prop_eqb S.small_chsh_eval tr s0 H0 H1).
Qed.

(* A run from a clean start that raises the flag pays at least 3 on the
   record; its committed counter held a passing tally, and that tally's
   score obeys the Tsirelson bound. *)
Theorem small_chsh_certified_floor : forall (tr : list (@M.instr S.small_chsh_prop))
    (s0 : @M.state S.small_chsh_prop),
  M.clean_start s0 ->
  M.cert (M.run S.small_chsh_prop_eqb S.small_chsh_eval tr s0) = true ->
  cs_total_cost small_chsh_cs tr >= 3 /\
  exists pre1 c mid1 mid2 post,
    tr = pre1 ++ M.CHECK S.small_chsh_PCHSH c :: mid1
           ++ M.COMMIT S.small_chsh_PCHSH c :: mid2 ++ M.CERTIFY :: post /\
    let t := S.small_chsh_tally_of
               (M.vals (M.core_of (M.run S.small_chsh_prop_eqb S.small_chsh_eval pre1 s0)) c) in
    K.small_chsh_check t = true /\
    (K.small_chsh_score t * K.small_chsh_score t <= 8)%R /\
    (Rabs (K.small_chsh_score t) <= 2 * sqrt 2)%R.
Proof.
  intros tr s0 H0 H1. split.
  - unfold small_chsh_cs. rewrite L.multi_cs_cost.
    destruct (M.multi_certified_run_min_cost S.small_chsh_prop_eqb S.small_chsh_prop_eqb_eq
                S.small_chsh_eval s0 tr H0 H1) as [H3 _].
    exact H3.
  - destruct (S.small_chsh_flag_implies_tsirelson s0 tr H0 H1)
      as [pre1 [c [mid1 [mid2 [post [Htr [Hck [_ [Hsq [Habs _]]]]]]]]]].
    exists pre1, c, mid1, mid2, post. split; [exact Htr |].
    cbv zeta. repeat split; assumption.
Qed.

(* The chain CHECK, COMMIT, CERTIFY on any counter pays exactly 3 on the
   record, whether or not its check passes. *)
Theorem small_chsh_chain_cost : forall c : nat,
  cs_total_cost small_chsh_cs (S.small_chsh_chain c) = 3.
Proof.
  intros c. unfold small_chsh_cs. rewrite L.multi_cs_cost. reflexivity.
Qed.

Print Assumptions small_chsh_cs.
Print Assumptions small_chsh_cs_floor.
Print Assumptions small_chsh_certified_floor.
Print Assumptions small_chsh_chain_cost.
