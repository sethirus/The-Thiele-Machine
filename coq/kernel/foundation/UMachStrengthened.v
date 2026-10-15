(** UMachStrengthened.v: the pieces of the strengthened definition D+ that U and
    U_P meet, each a closed Coq theorem.

    D+ = book clauses (1)-(3)                       [U_meets_weak, UP_meets_weak]
       + (c) earned and tied: every rise of the host flag stands on the
             host's own CHECK, COMMIT (same claim, untouched), CERTIFY, and
             the checked claim is the guest's own justification
                                                    [universal_earned,
                                                     presented_universal_earned]
       + (d) register host: the host is EarnedMulti / EarnedMultiPriced over
             some property language (base = INC/DEC/HALT on registers, record
             moves CHECK/COMMIT/CERTIFY(/PAY) that leave the registers alone
             and either advance or trap), loaded clean, decoded from
             registers                              [U_host, UP_host are such
                                                     by definition; content:
                                                     checker_blind,
                                                     pchecker_blind and the
                                                     corollaries below]       *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.UMachCheatSmall.
Require Import Kernel.UMachCheatPresented.
Require Import Kernel.UMachMeetsU.
Require Import Kernel.UMachMeetsUP.
Require Import Kernel.UMachInert.
Require Import Minimal.UniversalCodes.
Require Import Kernel.UniversalBridge.
Require Import Kernel.UniversalLayout.
Require Import Kernel.UniversalSim.
Require Import Kernel.UniversalRun.
Require Kernel.UniversalPCodes.
Require Kernel.UniversalPSim.
Require Kernel.UniversalPLayout.
Require Kernel.UniversalPRun.
Require Kernel.PresentedUniversal.
Require Minimal.EarnedMulti.
Require Minimal.EarnedMultiPriced.

(* U's register trajectory is the same under its real checker heval and
   under the checker that says yes to everything, at every step before a
   trap: U's CHECKs do no computing for the base. *)
Corollary U_checker_free : forall P x y n,
  Minimal.EarnedMulti.err (Minimal.EarnedMulti.core_of
     (Minimal.EarnedMulti.run_prog hprop_eqb heval n U (hload P x y))) = false ->
  Minimal.EarnedMulti.err (Minimal.EarnedMulti.core_of
     (Minimal.EarnedMulti.run_prog hprop_eqb (fun _ _ => true) n U (hload P x y))) = false ->
  bsame (Minimal.EarnedMulti.core_of (Minimal.EarnedMulti.run_prog hprop_eqb heval n U (hload P x y)))
        (Minimal.EarnedMulti.core_of
           (Minimal.EarnedMulti.run_prog hprop_eqb (fun _ _ => true) n U (hload P x y))).
Proof.
  intros P x y n H1 H2. apply checker_blind; [| exact H1 | exact H2].
  split; [| split]; reflexivity.
Qed.

(* The same for U_P, whose checker runs a guest's reading routine. *)
Corollary UP_checker_free : forall P x y n,
  Minimal.EarnedMultiPriced.err (Minimal.EarnedMultiPriced.core_of
     (Minimal.EarnedMultiPriced.pu_run_prog UniversalPCodes.pu_hprop_eqb UniversalPCodes.pu_heval n
        UniversalPLayout.U_P (UniversalPSim.pu_hload P x y))) = false ->
  Minimal.EarnedMultiPriced.err (Minimal.EarnedMultiPriced.core_of
     (Minimal.EarnedMultiPriced.pu_run_prog UniversalPCodes.pu_hprop_eqb (fun _ _ => true) n
        UniversalPLayout.U_P (UniversalPSim.pu_hload P x y))) = false ->
  pbsame (Minimal.EarnedMultiPriced.core_of
     (Minimal.EarnedMultiPriced.pu_run_prog UniversalPCodes.pu_hprop_eqb UniversalPCodes.pu_heval n
        UniversalPLayout.U_P (UniversalPSim.pu_hload P x y)))
   (Minimal.EarnedMultiPriced.core_of
     (Minimal.EarnedMultiPriced.pu_run_prog UniversalPCodes.pu_hprop_eqb (fun _ _ => true) n
        UniversalPLayout.U_P (UniversalPSim.pu_hload P x y))).
Proof.
  intros P x y n H1 H2. apply pchecker_blind; [| exact H1 | exact H2].
  split; [| split]; reflexivity.
Qed.

(* The loads are clean (no facts, empty channel, flag down; ledger 0). *)
Lemma U_load_clean : forall P x y,
  Minimal.EarnedMulti.clean_start (hload P x y) /\ Minimal.EarnedMulti.mu (hload P x y) = 0.
Proof. intros. split; [apply Minimal.EarnedMulti.multi_start_clean | reflexivity]. Qed.

Lemma UP_load_clean : forall P x y,
  Minimal.EarnedMultiPriced.pu_clean_start (UniversalPSim.pu_hload P x y) /\
  Minimal.EarnedMultiPriced.mu (UniversalPSim.pu_hload P x y) = 0.
Proof. intros. split; [apply Minimal.EarnedMultiPriced.pu_multi_start_clean | reflexivity]. Qed.

Print Assumptions U_meets_weak.
Print Assumptions UP_meets_weak.
Print Assumptions universal_earned.
Print Assumptions PresentedUniversal.presented_universal_earned.
Print Assumptions universal_thiele_complete_over.
Print Assumptions UniversalPRun.pu_universal_thiele_complete_over.
Print Assumptions U_checker_free.
Print Assumptions UP_checker_free.
Print Assumptions U_load_clean.
Print Assumptions UP_load_clean.
Print Assumptions cheat_is_universal.
Print Assumptions pcheat_is_universal.
