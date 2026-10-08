(** NecSU.v: the fixed program U on the host with a counter for every
    number (UniversalRun.v, UniversalInterpreterLinks.v) pushed to its
    limit.

    - "The host's flag-raising run of U costs at least 1 on the system
      built from Thiele-completeness" improves to at least 3: that system
      agrees cost for cost with the host's own, where the floor is 3.
    - The floor 3 is attained by U: on the three-instruction guest CHECK,
      COMMIT, CERTIFY of "A is at least 0", from every start, U halts with
      its flag up and its ledger exactly 3.
    - "In between matching points the host ledger lies between the guest's
      ledger at m and at m + 1" improves to: every host ledger value IS a
      guest ledger value, because a guest step costs at most 1.
    - The bound m <= n of "U keeps pace" is attained at m = 0 by the
      loaded host itself.                                                 *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Kernel Require Import UniversalCertificationCost.
Require Kernel.UniversalLayout Kernel.UniversalSim Kernel.UniversalRun.
Require Import Kernel.UniversalInterpreterLinks.
Require Minimal.EarnedCore Minimal.EarnedMulti Minimal.UniversalCodes.
Module E := Minimal.EarnedCore.
Module M := Minimal.EarnedMulti.
Module C := Minimal.UniversalCodes.
Module R := Kernel.UniversalRun.

(* ================================================================= *)
(* 1. The floor on the Thiele-complete system is 3, not 1.            *)
(* ================================================================= *)

Theorem nec_s_U_complete_floor_three : forall (P : list E.instr) (x y n : nat),
  M.cert (R.hrun P x y n) = true ->
  cs_total_cost interp_complete_cs
    (M.trace_of C.hprop_eqb C.heval n Kernel.UniversalLayout.U (Kernel.UniversalSim.hload P x y))
  >= 3.
Proof.
  intros P x y n Hc.
  rewrite (proj2 (interp_complete_agrees _ (Kernel.UniversalSim.hload P x y))).
  apply interp_U_certified_floor. exact Hc.
Qed.

(* ================================================================= *)
(* 2. The floor 3 is attained by U.                                   *)
(* ================================================================= *)

Lemma nec_s_witness_halts : forall x y,
  E.halted E.witness (E.core_of (R.grun E.witness x y 3)) /\
  E.cert (R.grun E.witness x y 3) = true /\ E.mu (R.grun E.witness x y 3) = 3.
Proof.
  intros x y. unfold R.grun. cbn.
  unfold E.cexec, E.check_ok, E.commit_ok, E.certify_ok, E.claim, E.fact_eqb; cbn.
  repeat split.
Qed.

Theorem nec_s_U_floor_three_attained : forall x y, exists n,
  M.halted Kernel.UniversalLayout.U (M.core_of (R.hrun E.witness x y n)) /\
  M.cert (R.hrun E.witness x y n) = true /\ M.mu (R.hrun E.witness x y n) = 3 /\
  cs_total_cost interp_cs
    (M.trace_of C.hprop_eqb C.heval n Kernel.UniversalLayout.U
       (Kernel.UniversalSim.hload E.witness x y)) = 3.
Proof.
  intros x y. destruct (nec_s_witness_halts x y) as [Hh [Hc Hm]].
  destruct (proj1 (R.universal_halting E.witness x y) (ex_intro _ 3 Hh)) as [n Hn].
  destruct (R.universal_output E.witness x y 3 n Hh Hn) as [_ [_ [_ [Hmu Hce]]]].
  exists n. split; [exact Hn |]. split; [rewrite Hce; exact Hc |].
  split; [rewrite Hmu; exact Hm |].
  unfold interp_cs. rewrite multi_cs_cost.
  pose proof (M.multi_mu_conservation_program C.hprop_eqb C.heval n
                Kernel.UniversalLayout.U (Kernel.UniversalSim.hload E.witness x y)) as Hc2.
  change (M.run_prog C.hprop_eqb C.heval n Kernel.UniversalLayout.U
            (Kernel.UniversalSim.hload E.witness x y)) with (R.hrun E.witness x y n) in Hc2.
  rewrite Hmu, Hm in Hc2. simpl in Hc2. lia.
Qed.

(* ================================================================= *)
(* 3. Every host ledger value is a guest ledger value.                *)
(* ================================================================= *)

Lemma nec_s_grun_mu_step : forall P x y m,
  E.mu (R.grun P x y (S m)) <= E.mu (R.grun P x y m) + 1.
Proof.
  intros P x y m. unfold R.grun. rewrite R.grun_succ, E.step_mu.
  destruct (E.next_instr P _) as [[] |]; simpl; lia.
Qed.

Theorem nec_s_host_ledger_is_guest_ledger : forall P x y n, exists m,
  M.mu (R.hrun P x y n) = E.mu (R.grun P x y m).
Proof.
  intros P x y n. destruct (proj2 (R.universal_ledger_exact P x y) n) as [m [H1 H2]].
  pose proof (nec_s_grun_mu_step P x y m).
  destruct (Nat.eq_dec (M.mu (R.hrun P x y n)) (E.mu (R.grun P x y m))) as [E | E].
  - exists m. exact E.
  - exists (S m). lia.
Qed.

(* ================================================================= *)
(* 4. m <= n is attained at m = 0.                                    *)
(* ================================================================= *)

Theorem nec_s_U_sim_bound_attained : forall P x y,
  Kernel.UniversalSim.rel P (R.grun P x y 0) (R.hrun P x y 0).
Proof.
  intros P x y. exists [], None. apply Kernel.UniversalSim.hload_rel.
Qed.

Print Assumptions nec_s_U_complete_floor_three.
Print Assumptions nec_s_U_floor_three_attained.
Print Assumptions nec_s_host_ledger_is_guest_ledger.
Print Assumptions nec_s_U_sim_bound_attained.

(* ================================================================= *)
(* 5. The earned host flag needs the loaded clean start.              *)
(* ================================================================= *)

(* From a host state whose flag is already up, U's run of 0 steps has its
   flag up and an empty trace, so no earned chain: the loaded start is
   what makes universal_earned true. *)
Theorem nec_s_U_earned_needs_load :
  let s := @M.mkst C.hprop (M.start_core (fun _ => 0)) 0 true in
  M.cert (M.run_prog C.hprop_eqb C.heval 0 Kernel.UniversalLayout.U s) = true /\
  M.trace_of C.hprop_eqb C.heval 0 Kernel.UniversalLayout.U s = [].
Proof. split; reflexivity. Qed.

Print Assumptions nec_s_U_earned_needs_load.
