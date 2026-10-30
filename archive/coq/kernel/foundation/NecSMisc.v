(** NecSMisc.v: the remaining rows of "The smallest honest machine".

    - Unearned steps trap: "if COMMIT would not pass it traps" is an iff,
      and so is the same for CERTIFY.
    - The small machine runs the eight-state machine only on live states:
      each of the three conjuncts of "live" (trap down, the fact "A >= 0"
      about A's current version in the table, a commitment on the channel)
      is necessary for the step-for-step window theorem; and the paid
      certification through the window attains its bound of 1.
    - A counter beside a Turing machine changes nothing, and the converse
      fails as strongly as it can: the configuration determines nothing
      about the counter (a looping machine keeps its configuration while
      the counter grows without bound); the cost bound 2 per step of the
      cost certificate is attained.                                       *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.EarnedCore.
Require Minimal.FragmentSmall.
Module F := Minimal.FragmentSmall.
From Kernel Require Import ProperSubsumption.

(* ================================================================= *)
(* 1. Unearned steps trap, exactly.                                   *)
(* ================================================================= *)

Theorem nec_s_commit_traps_iff : forall k p c,
  err (cexec k (COMMIT p c)) = true <-> commit_ok k p c = false.
Proof.
  intros k p c. unfold cexec. destruct (err k) eqn:He.
  - unfold commit_ok. rewrite He. simpl. split; auto.
  - destruct (commit_ok k p c) eqn:Hc; simpl; [rewrite He | ]; split; congruence.
Qed.

Theorem nec_s_certify_traps_iff : forall s,
  err (core_of (exec s CERTIFY)) = true <-> certify_ok (core_of s) = false.
Proof.
  intros [k m r]. simpl. unfold cexec. destruct (err k) eqn:He.
  - unfold certify_ok. rewrite He. simpl. split; auto.
  - destruct (certify_ok k) eqn:Hc; simpl; [rewrite He |]; split; congruence.
Qed.

(* ================================================================= *)
(* 2. The eight-state machine needs live states.                      *)
(* ================================================================= *)

Definition nec_s_g0 : fact := mkfact (PGe 0) CA 0.
Definition nec_s_ch : option fact := Some nec_s_g0.

(* Trap up, the other two conjuncts hold. *)
Definition nec_s_frag_trapped : state :=
  mkst (mkcore 0 0 0 0 1 [nec_s_g0] nec_s_ch true) 0 false.
(* No commitment on the channel, the other two hold. *)
Definition nec_s_frag_nochan : state :=
  mkst (mkcore 0 0 0 0 1 [nec_s_g0] None false) 0 false.
(* No fact in the table, the other two hold. *)
Definition nec_s_frag_nofact : state :=
  mkst (mkcore 0 0 0 0 1 [] nec_s_ch false) 0 false.

Theorem nec_s_frag_needs_live :
  (In (claim (core_of nec_s_frag_trapped) F.frag_q CA) (facts (core_of nec_s_frag_trapped)) /\
   chan (core_of nec_s_frag_trapped) <> None /\
   F.frag_window (run (F.frag_compile F.FStamp) nec_s_frag_trapped)
     <> F.frag_step (F.frag_window nec_s_frag_trapped) F.FStamp) /\
  (err (core_of nec_s_frag_nochan) = false /\
   In (claim (core_of nec_s_frag_nochan) F.frag_q CA) (facts (core_of nec_s_frag_nochan)) /\
   F.frag_window (run (F.frag_compile F.FStamp) nec_s_frag_nochan)
     <> F.frag_step (F.frag_window nec_s_frag_nochan) F.FStamp) /\
  (err (core_of nec_s_frag_nofact) = false /\ chan (core_of nec_s_frag_nofact) <> None /\
   F.frag_window (run (F.frag_compile (F.FJump F.FS0)) nec_s_frag_nofact)
     <> F.frag_step (F.frag_window nec_s_frag_nofact) (F.FJump F.FS0)).
Proof.
  vm_compute. repeat split; try (left; reflexivity); discriminate.
Qed.

(* The paid certification through the window attains its bound of 1. *)
Theorem nec_s_frag_toll_attained :
  let s := run F.frag_setup (start 0 0) in
  F.frag_live s /\ cert s = false /\
  cert (run (F.frag_compile_all [F.FStamp]) s) = true /\
  mu (run (F.frag_compile_all [F.FStamp]) s) = mu s + 1.
Proof.
  intro s. destruct (F.frag_setup_live 0 0) as [Hl _]. split; [exact Hl |].
  vm_compute. auto.
Qed.

(* ================================================================= *)
(* 3. The counter beside a Turing machine.                            *)
(* ================================================================= *)

Import ProperSubsumption.

(* A machine that writes w where it stands, stays, and keeps its state. *)
Definition nec_s_loop (w : Symbol) : TM_Delta :=
  fun _ _ => Some {| tm_write := w; tm_move := Stay; tm_next := 0 |}.
Definition nec_s_c0 : TM_Config := {| tm_state := 0; tm_tape := empty_tape |}.

Lemma nec_s_loop_blank_run : forall n m,
  thiele_run n (nec_s_loop blank) {| th_tm_config := nec_s_c0; th_mu := m |}
  = {| th_tm_config := nec_s_c0; th_mu := m + n |}.
Proof.
  induction n as [| n IH]; intro m; [simpl; rewrite Nat.add_0_r; reflexivity |].
  cbn [thiele_run].
  replace (thiele_step (nec_s_loop blank) {| th_tm_config := nec_s_c0; th_mu := m |})
    with (Some {| th_tm_config := nec_s_c0; th_mu := m + 1 |}) by reflexivity.
  rewrite IH. f_equal. lia.
Qed.

(* The configuration determines nothing about the counter. *)
Theorem nec_s_tm_ledger_not_function_of_config :
  ~ exists g : TM_Config -> nat,
      forall n, g (th_tm_config (thiele_run n (nec_s_loop blank) (lift_config nec_s_c0)))
                = th_mu (thiele_run n (nec_s_loop blank) (lift_config nec_s_c0)).
Proof.
  intros [g Hg]. pose proof (Hg 0) as H0. pose proof (Hg 1) as H1.
  unfold lift_config in *. rewrite nec_s_loop_blank_run in H0, H1. simpl in H0, H1.
  congruence.
Qed.

Definition nec_s_c1 : TM_Config :=
  {| tm_state := 0; tm_tape := {| tape_left := []; tape_head := 1; tape_right := [] |} |}.

Lemma nec_s_loop_one_run : forall n m,
  thiele_run n (nec_s_loop 1) {| th_tm_config := nec_s_c1; th_mu := m |}
  = {| th_tm_config := nec_s_c1; th_mu := m + 2 * n |}.
Proof.
  induction n as [| n IH]; intro m; [simpl; f_equal; lia |].
  cbn [thiele_run].
  replace (thiele_step (nec_s_loop 1) {| th_tm_config := nec_s_c1; th_mu := m |})
    with (Some {| th_tm_config := nec_s_c1; th_mu := m + 2 |}) by reflexivity.
  rewrite IH. f_equal. lia.
Qed.

(* The bound mu <= mu0 + fuel * (step_cost + 1) is attained for every fuel. *)
Theorem nec_s_tm_cost_bound_attained : forall n,
  th_mu (thiele_run n (nec_s_loop 1) {| th_tm_config := nec_s_c1; th_mu := 0 |})
  = 0 + n * (step_cost + 1).
Proof. intro n. rewrite nec_s_loop_one_run. unfold step_cost. simpl. lia. Qed.

Print Assumptions nec_s_commit_traps_iff.
Print Assumptions nec_s_certify_traps_iff.
Print Assumptions nec_s_frag_needs_live.
Print Assumptions nec_s_frag_toll_attained.
Print Assumptions nec_s_tm_ledger_not_function_of_config.
Print Assumptions nec_s_tm_cost_bound_attained.
