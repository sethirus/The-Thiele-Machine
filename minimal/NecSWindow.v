(** NecSWindow.v: the small machine's separation, oracle, order, version,
    trap and table results pushed to their limit.

    - Same window, different record holds from EVERY clean untrapped start,
      not only start(0, 0); and two runs can even agree on the window, both
      versions and the ledger while disagreeing on the flag, so the flag is
      not a function of the window and the ledger together.
    - No function of the window gives the ledger, from ANY state at all.
    - No function of the window gives the flag, from a state with the flag
      down, EXACTLY when some run from that state raises it.
    - From a clean start, a window oracle for the flag or for "would COMMIT
      A is at least 0 pass" exists exactly when the start is trapped.
    - Of the six orders of CHECK, COMMIT, CERTIFY only CHECK; COMMIT;
      CERTIFY certifies, from every start.
    - COMMIT compares versions, not values: it refuses a claim that is true
      again but was checked on an older version; a variant of the machine
      without versions commits and certifies a false claim.
    - The trap-down hypothesis of the simulation theorem is necessary.
    - The toll and the floor do not need the flag to be permanent.
    - The table bound 16 is attained.                                    *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.EarnedCore.
From Minimal Require Import NecSClean.

Definition nec_s_G : prop := PGe 0.

(* ================================================================= *)
(* 1. Separation from every clean untrapped start.                    *)
(* ================================================================= *)

Definition nec_s_idle_trap : list instr :=
  [CHECK nec_s_G CA; CHECK nec_s_G CA; CHECK nec_s_G CA; COMMIT (PGe 1) CB].
Definition nec_s_idle_paid : list instr :=
  [CHECK nec_s_G CA; CHECK nec_s_G CA; CHECK nec_s_G CA].

Theorem nec_s_separation_any_clean_start : forall s0,
  clean_start s0 -> err (core_of s0) = false ->
  let A := run witness s0 in
  let B := run nec_s_idle_trap s0 in
  window (core_of A) = window (core_of B) /\
  ver (core_of A) CA = ver (core_of B) CA /\
  ver (core_of A) CB = ver (core_of B) CB /\
  mu A <> mu B /\ cert A <> cert B /\
  facts (core_of A) <> facts (core_of B) /\
  commit_ok (core_of A) nec_s_G CA <> commit_ok (core_of B) nec_s_G CA.
Proof.
  intros [[a b u v p fs ch e] m r] [Hf [Hch Hc]] He. simpl in *. subst.
  unfold witness, nec_s_idle_trap, nec_s_G. simpl.
  unfold cexec, check_ok, commit_ok, certify_ok, claim, fact_eqb; simpl.
  rewrite !Nat.eqb_refl. simpl.
  repeat split; try discriminate; try lia; try (rewrite Nat.eqb_refl; discriminate).
Qed.

Theorem nec_s_same_ledger_different_flag : forall s0,
  clean_start s0 -> err (core_of s0) = false ->
  let A := run witness s0 in
  let B := run nec_s_idle_paid s0 in
  window (core_of A) = window (core_of B) /\
  ver (core_of A) CA = ver (core_of B) CA /\
  ver (core_of A) CB = ver (core_of B) CB /\
  mu A = mu B /\ cert A = true /\ cert B = false.
Proof.
  intros [[a b u v p fs ch e] m r] [Hf [Hch Hc]] He. simpl in *. subst.
  unfold witness, nec_s_idle_paid, nec_s_G. simpl.
  unfold cexec, check_ok, commit_ok, certify_ok, claim, fact_eqb; simpl.
  rewrite !Nat.eqb_refl. simpl.
  repeat split.
Qed.

(* The flag is not a function of the window, both versions and the ledger. *)
Theorem nec_s_no_flag_oracle_even_with_ledger : forall s0,
  clean_start s0 -> err (core_of s0) = false ->
  ~ exists g : mconf -> nat -> nat -> nat -> bool,
      forall tr, let k := core_of (run tr s0) in
        g (window k) (ver k CA) (ver k CB) (mu (run tr s0)) = cert (run tr s0).
Proof.
  intros s0 H0 He [g Hg].
  destruct (nec_s_same_ledger_different_flag s0 H0 He) as [Hw [Ha [Hb [Hm [HA HB]]]]].
  pose proof (Hg witness) as G1. pose proof (Hg nec_s_idle_paid) as G2. cbv zeta in G1, G2.
  rewrite Hw, Ha, Hb, Hm in G1. congruence.
Qed.

(* ================================================================= *)
(* 2. Oracles.                                                        *)
(* ================================================================= *)

(* No function of the window gives the ledger, from any state at all. *)
Theorem nec_s_no_mu_oracle_any_state : forall s0,
  ~ exists g : mconf -> nat,
      forall tr, g (window (core_of (run tr s0))) = mu (run tr s0).
Proof.
  intros s0 [g Hg].
  pose proof (Hg []) as H1.
  pose proof (Hg [CHECK nec_s_G CA; INC CA; DEC CA (pc (core_of s0))]) as H2.
  assert (Hw : window (core_of (run [CHECK nec_s_G CA; INC CA; DEC CA (pc (core_of s0))] s0))
               = window (core_of s0)).
  { destruct s0 as [[a b u v p fs ch e] m r]. destruct e; [reflexivity |].
    unfold nec_s_G. simpl. unfold cexec, check_ok; simpl.
    destruct (length fs <? fact_cap); reflexivity. }
  rewrite Hw in H2. simpl in H1, H2. rewrite H1 in H2. lia.
Qed.

Lemma nec_s_total_cost_decs : forall n c j, total_cost (repeat (DEC c j) n) = 0.
Proof. induction n; intros; simpl; auto. Qed.

(* From an untrapped state, increments and decrements reach any window
   for free, without touching the flag. *)
Lemma nec_s_reach_window : forall s w,
  err (core_of s) = false ->
  exists tr, window (core_of (run tr s)) = w /\ cert (run tr s) = cert s /\
             total_cost tr = 0.
Proof.
  intros s [p1 [a1 b1]] He.
  set (a := val (core_of s) CA). set (b := val (core_of s) CB).
  exists (repeat (DEC CA 1) a ++ repeat (DEC CB 1) b ++ repeat (INC CA) (S a1)
          ++ repeat (INC CB) b1 ++ [DEC CA p1]).
  rewrite !run_app.
  destruct (nec_s_run_decs a s CA 1 He ltac:(unfold a; lia))
    as [V1a [V1o [E1 C1]]].
  set (s1 := run (repeat (DEC CA 1) a) s) in *.
  assert (V1b : val (core_of s1) CB = b) by (apply V1o; discriminate).
  destruct (nec_s_run_decs b s1 CB 1 E1 ltac:(lia)) as [V2b [V2o [E2 C2]]].
  set (s2 := run (repeat (DEC CB 1) b) s1) in *.
  assert (V2a : val (core_of s2) CA = 0) by (rewrite V2o by discriminate; unfold a in V1a; lia).
  destruct (nec_s_run_incs (S a1) s2 CA E2) as [_ [V3a [V3o [_ [_ [E3 C3]]]]]].
  set (s3 := run (repeat (INC CA) (S a1)) s2) in *.
  assert (V3b : val (core_of s3) CB = 0) by (rewrite V3o by discriminate; lia).
  destruct (nec_s_run_incs b1 s3 CB E3) as [_ [V4b [V4o [_ [_ [E4 C4]]]]]].
  set (s4 := run (repeat (INC CB) b1) s3) in *.
  assert (V4a : val (core_of s4) CA = S a1) by (rewrite V4o by discriminate; lia).
  destruct (nec_s_dec_step s4 CA p1 a1 E4 V4a) as [V5a [V5o [P5 [_ C5]]]].
  split; [| split].
  - simpl. unfold window.
    change (ca (cexec (core_of s4) (DEC CA p1))) with (val (core_of (exec s4 (DEC CA p1))) CA).
    change (cb (cexec (core_of s4) (DEC CA p1))) with (val (core_of (exec s4 (DEC CA p1))) CB).
    change (pc (cexec (core_of s4) (DEC CA p1))) with (pc (core_of (exec s4 (DEC CA p1)))).
    rewrite V5a, P5, V5o by discriminate. f_equal. f_equal. lia.
  - change (cert (exec s4 (DEC CA p1)) = cert s). rewrite C5, C4, C3, C2, C1. reflexivity.
  - rewrite !total_cost_app, nec_s_total_cost_decs, nec_s_total_cost_decs,
      nec_s_total_cost_incs, nec_s_total_cost_incs. reflexivity.
Qed.

(* With the flag down: a window oracle for the flag exists exactly when no
   run raises the flag. *)
Theorem nec_s_cert_oracle_iff : forall s0,
  cert s0 = false ->
  ((exists g : mconf -> bool,
      forall tr, g (window (core_of (run tr s0))) = cert (run tr s0)) <->
   (forall tr, cert (run tr s0) = false)).
Proof.
  intros s0 Hc0. split.
  - intros [g Hg] tr. destruct (cert (run tr s0)) eqn:H1; [| reflexivity].
    exfalso. destruct (err (core_of s0)) eqn:He.
    + destruct (nec_s_run_trapped tr s0 He) as [_ Hc]. congruence.
    + destruct (nec_s_reach_window s0 (window (core_of (run tr s0))) He)
        as [tr' [Hw [Hc _]]].
      pose proof (Hg tr) as G1. pose proof (Hg tr') as G2.
      rewrite Hw in G2. congruence.
  (* SAFE: when the flag never rises, the constant-false oracle is the intended window function. *)
  - intro H. exists (fun _ => false). intro tr. symmetry. apply H.
Qed.

Corollary nec_s_clean_cert_oracle_iff_trapped : forall s0,
  clean_start s0 ->
  ((exists g : mconf -> bool,
      forall tr, g (window (core_of (run tr s0))) = cert (run tr s0)) <->
   err (core_of s0) = true).
Proof.
  intros s0 H0. pose proof H0 as [_ [_ Hc0]].
  rewrite (nec_s_cert_oracle_iff s0 Hc0).
  pose proof (nec_s_clean_certifiable_iff_untrapped s0 H0) as Hiff. split.
  - intro H. destruct (err (core_of s0)) eqn:He; [reflexivity |].
    destruct (proj2 Hiff eq_refl) as [tr Htr]. congruence.
  - intros He tr. destruct (cert (run tr s0)) eqn:Htr; [| reflexivity].
    assert (err (core_of s0) = false) by (apply Hiff; exists tr; exact Htr). congruence.
Qed.

Theorem nec_s_clean_commit_oracle_iff_trapped : forall s0,
  clean_start s0 ->
  ((exists g : mconf -> bool,
      forall tr, g (window (core_of (run tr s0))) = commit_ok (core_of (run tr s0)) nec_s_G CA)
   <-> err (core_of s0) = true).
Proof.
  intros s0 H0. split.
  - intros [g Hg]. destruct (err (core_of s0)) eqn:He; [reflexivity | exfalso].
    destruct (nec_s_separation_any_clean_start s0 H0 He) as [Hw [_ [_ [_ [_ [_ Hk]]]]]].
    pose proof (Hg witness) as G1. pose proof (Hg nec_s_idle_trap) as G2.
    rewrite Hw in G1. congruence.
  (* SAFE: from a trapped start the flag never rises, so the constant-false oracle is the intended window function. *)
  - intro He. exists (fun _ => false). intro tr.
    destruct (nec_s_run_trapped tr s0 He) as [Hk _]. rewrite Hk.
    unfold commit_ok. rewrite He. reflexivity.
Qed.

(* ================================================================= *)
(* 3. Order: CHECK, then COMMIT, then CERTIFY, and no other order.    *)
(* ================================================================= *)

Definition nec_s_orders : list (list instr) :=
  [ [CHECK nec_s_G CA; COMMIT nec_s_G CA; CERTIFY];
    [CHECK nec_s_G CA; CERTIFY; COMMIT nec_s_G CA];
    [COMMIT nec_s_G CA; CHECK nec_s_G CA; CERTIFY];
    [COMMIT nec_s_G CA; CERTIFY; CHECK nec_s_G CA];
    [CERTIFY; CHECK nec_s_G CA; COMMIT nec_s_G CA];
    [CERTIFY; COMMIT nec_s_G CA; CHECK nec_s_G CA] ].

Theorem nec_s_only_order_certifies : forall a b l,
  In l nec_s_orders -> (cert (run l (start a b)) = true <-> l = witness).
Proof.
  intros a b l Hin.
  repeat (destruct Hin as [<- | Hin]; [vm_compute; split; intro H; congruence |]).
  destruct Hin.
Qed.

(* ================================================================= *)
(* 4. Versions: COMMIT compares versions, and without versions the    *)
(*    machine commits a false claim.                                  *)
(* ================================================================= *)

(* A claim checked, then the counter moved away and back: the claim is
   true again, yet COMMIT refuses it, because its fact is about version 0
   and the counter is at version 2. *)
Theorem nec_s_commit_refuses_true_stale :
  let k := core_of (run [CHECK PZero CA; INC CA; DEC CA 3] (start 0 0)) in
  val k CA = 0 /\ holds PZero (val k CA) /\ In (mkfact PZero CA 0) (facts k) /\
  ver k CA = 2 /\ commit_ok k PZero CA = false.
Proof. vm_compute. repeat split. left. reflexivity. Qed.

(* The same machine with versions erased after every step. *)
Definition nec_s_nv (k : core) : core :=
  mkcore (ca k) (cb k) 0 0 (pc k) (facts k) (chan k) (err k).
Definition nec_s_exec_nv (s : state) (i : instr) : state :=
  mkst (nec_s_nv (cexec (core_of s) i)) (mu s + cost i) (cert s || fires (core_of s) i).
Fixpoint nec_s_run_nv (tr : list instr) (s : state) : state :=
  match tr with [] => s | i :: rest => nec_s_run_nv rest (nec_s_exec_nv s i) end.

Definition nec_s_stale_commit_run : list instr :=
  [CHECK PZero CA; INC CA; COMMIT PZero CA; CERTIFY].

(* The real machine refuses: the COMMIT traps and the flag stays down. *)
Theorem nec_s_versioned_refuses :
  let s := run nec_s_stale_commit_run (start 0 0) in
  cert s = false /\ err (core_of s) = true.
Proof. vm_compute. split; reflexivity. Qed.

(* The versionless variant commits "A is 0" while A is 1 and certifies. *)
Theorem nec_s_versionless_unsound :
  let s := nec_s_run_nv nec_s_stale_commit_run (start 0 0) in
  cert s = true /\ mu s = 3 /\ chan (core_of s) = Some (mkfact PZero CA 0) /\
  ~ holds PZero (val (core_of s) CA).
Proof. vm_compute. repeat split. discriminate. Qed.

(* ================================================================= *)
(* 5. The simulation needs the trap down.                             *)
(* ================================================================= *)

Definition nec_s_trapped_core : core := mkcore 0 0 0 0 1 [] None true.

Theorem nec_s_simulation_needs_trap_down :
  ~ (forall M k, mstep M (window k) = None <-> halted (compile M) k) /\
  ~ (forall n M k, window (core_run n (compile M) k) = mrun n M (window k)).
Proof.
  split.
  - intro H. pose proof (proj2 (H [MINC CA] nec_s_trapped_core) eq_refl) as Hm.
    vm_compute in Hm. discriminate.
  - intro H. pose proof (H 1 [MINC CA] nec_s_trapped_core) as Hm.
    vm_compute in Hm. discriminate.
Qed.

(* ================================================================= *)
(* 6. The toll does not need permanence.                              *)
(* ================================================================= *)

(* The same machine with a flag that HALT lowers. *)
Definition nec_s_exec_drop (s : state) (i : instr) : state :=
  mkst (cexec (core_of s) i) (mu s + cost i)
       (match i with HALT => false | _ => cert s || fires (core_of s) i end).
Fixpoint nec_s_run_drop (tr : list instr) (s : state) : state :=
  match tr with [] => s | i :: rest => nec_s_run_drop rest (nec_s_exec_drop s i) end.

Theorem nec_s_toll_without_permanence :
  (forall s i, cert s = false -> cert (nec_s_exec_drop s i) = true ->
     i = CERTIFY /\ certify_ok (core_of s) = true /\ cost i >= 1) /\
  (forall tr s, cert s = false -> cert (nec_s_run_drop tr s) = true -> total_cost tr >= 1) /\
  (forall s i, mu (nec_s_exec_drop s i) = mu s + cost i) /\
  ~ (forall s i, cert s = true -> cert (nec_s_exec_drop s i) = true).
Proof.
  assert (Hstep : forall s i, cert s = false -> cert (nec_s_exec_drop s i) = true ->
     i = CERTIFY /\ certify_ok (core_of s) = true /\ cost i >= 1).
  { intros s i H0 H1. simpl in H1.
    destruct i; simpl in H1; try discriminate; rewrite H0 in H1; simpl in H1;
      try discriminate.
    repeat split; auto. }
  split; [exact Hstep |]. split; [| split; [reflexivity |]].
  - induction tr as [| i tr IH]; intros s H0 H1; simpl in *; [congruence |].
    destruct (cert (nec_s_exec_drop s i)) eqn:Hm.
    + destruct (Hstep s i H0 Hm) as [_ [_ Hc]]. lia.
    + pose proof (IH _ Hm H1). lia.
  - intro H. specialize (H nec_s_flag_up HALT eq_refl). discriminate.
Qed.

(* ================================================================= *)
(* 7. The table bound 16 is attained.                                 *)
(* ================================================================= *)

Theorem nec_s_table_bound_attained :
  let k := core_of (run (repeat (CHECK nec_s_G CA) 16) (start 0 0)) in
  length (facts k) = 16 /\ err k = false /\
  err (cexec k (CHECK nec_s_G CA)) = true /\
  facts (cexec k (CHECK nec_s_G CA)) = facts k.
Proof. vm_compute. repeat split. Qed.

Print Assumptions nec_s_separation_any_clean_start.
Print Assumptions nec_s_same_ledger_different_flag.
Print Assumptions nec_s_no_flag_oracle_even_with_ledger.
Print Assumptions nec_s_no_mu_oracle_any_state.
Print Assumptions nec_s_cert_oracle_iff.
Print Assumptions nec_s_clean_cert_oracle_iff_trapped.
Print Assumptions nec_s_clean_commit_oracle_iff_trapped.
Print Assumptions nec_s_only_order_certifies.
Print Assumptions nec_s_commit_refuses_true_stale.
Print Assumptions nec_s_versioned_refuses.
Print Assumptions nec_s_versionless_unsound.
Print Assumptions nec_s_simulation_needs_trap_down.
Print Assumptions nec_s_toll_without_permanence.
Print Assumptions nec_s_table_bound_attained.

(* ================================================================= *)
(* 8. Refused forever: what the refusal needs.                        *)
(* ================================================================= *)

(* Dropped-stronger: no clean start is needed; from every state with the
   flag down, the program at line 1 and A not zero, the program never
   raises the flag. *)
Theorem nec_s_refused_from_any_flag_down_state : forall s n,
  cert s = false -> pc (core_of s) = 1 -> val (core_of s) CA <> 0 ->
  cert (run_prog n earned_run s) = false.
Proof.
  intros [[a b u v p fs ch e] m r] n Hc Hp Ha. simpl in *. subst r p.
  destruct e.
  - rewrite run_prog_trapped by reflexivity. reflexivity.
  - destruct a as [| a]; [contradiction |]. destruct n as [| n]; [reflexivity |].
    simpl. rewrite run_prog_trapped by reflexivity. reflexivity.
Qed.

(* After the failed CHECK the machine is trapped, and NO continuation at
   all, stored program or free trace, changes its core or raises its flag:
   there is no instruction that clears the trap. *)
Theorem nec_s_refused_any_continuation : forall a b tr,
  a <> 0 ->
  let s := run_prog 1 earned_run (start a b) in
  err (core_of s) = true /\ cert (run tr s) = false /\ core_of (run tr s) = core_of s.
Proof.
  intros a b tr Ha s.
  assert (He : err (core_of s) = true).
  { unfold s. destruct a as [| a]; [contradiction | reflexivity]. }
  destruct (nec_s_run_trapped tr s He) as [Hk Hc].
  split; [exact He |]. split; [rewrite Hc; unfold s; destruct a; [contradiction | reflexivity] | exact Hk].
Qed.

Print Assumptions nec_s_refused_from_any_flag_down_state.
Print Assumptions nec_s_refused_any_continuation.
