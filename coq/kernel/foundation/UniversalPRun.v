(** UniversalPRun.v: whole runs of the fixed host program U_P.

    This file is the priced counterpart of UniversalRun.v: the host is the
    machine of EarnedMultiPriced.v (with PAY), the guest is the priced
    machine of EarnedPriced.v over the universal property language
    cg_uprop (UniversalPCodes.v), every name carries the prefix pu_, and
    the host program is U_P.

    For every priced guest program P over cg_uprop and every start (x, y),
    grun P x y m is the guest after m steps from E.start x y, and
    hrun P x y n is the host after n steps of U_P from hload P x y.

      pu_U_simulation             every guest step count m has a matching host
                               step count n >= m with rel, or both machines
                               have stopped and pu_rel_halt holds
      pu_universal_halting        the guest halts iff the host halts
      pu_universal_output         at halting, pu_RA and pu_RB hold the guest
                               counters, and the trap latches, the ledgers
                               and the flags are equal
      pu_universal_flag_iff       the guest's flag ever rises iff the host's
                               flag ever rises
      pu_universal_ledger_exact   at matching points the host ledger equals the
                               guest ledger, and every host prefix's ledger
                               lies between the guest ledger at some m and
                               at m + 1
      pu_universal_earned         a raised host flag stands on the host's own
                               chain: a passing CHECK PSlot (pu_SLOT c k), a
                               passing COMMIT PSlot (pu_SLOT c k) of the same
                               claim with the slot untouched between, and the
                               CERTIFY that raised the flag; when checked,
                               the slot held pair (pcode p) v with p true of
                               v; and the guest's own run contains its chain
                               CHECK p c, COMMIT p c, CERTIFY on the same p
                               and c, with v the value of guest counter c at
                               its CHECK
      pu_universal_thiele_complete  the host machine (EarnedMultiPriced with the
                               property PSlot), read with its INC/DEC moves as
                               the base, CHECK, COMMIT, CERTIFY as the record
                               moves and PAY as a check of the empty claim
                               (as in PricedComplete.v), meets
                               thiele_complete of ThieleComplete.v

    Dependencies: the Coq standard library, the vendored
    coq-undecidability library, EarnedGeneric.v, EarnedPriced.v,
    EarnedMultiPriced.v, CompilerChecker.v, ThieleComplete.v, UniversalPCodes.v, UniversalPBridge.v,
    UniversalPBlocks.v, UniversalPLayout.v, UniversalPPhases.v and
    UniversalPSim.v. No axioms, no Admitted.                               *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the universal interpreter U_P of UniversalPRun.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library and files under minimal/. Its link to the abstract record (the
   host machine meeting thiele_complete of ThieleComplete.v, and every
   computably presented machine run on U_P) lives in UniversalPRun.v and
   PresentedUniversal.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UniversalPCodes Kernel.UniversalPBridge Kernel.UniversalPBlocks
  Kernel.UniversalPLayout Kernel.UniversalPPhases Kernel.UniversalPSim.
Require Minimal.ThieleComplete.
Module TC := Minimal.ThieleComplete.

Local Notation hstate := (@M.pu_state pu_hprop).
Local Notation hinstr := (@M.pu_instr pu_hprop).
Local Notation hrun_prog := (M.pu_run_prog pu_hprop_eqb pu_heval).
Local Notation hrun_l := (M.pu_run pu_hprop_eqb pu_heval).
Local Notation htrace := (M.pu_trace_of pu_hprop_eqb pu_heval).
Local Notation hexec := (M.pu_exec pu_hprop_eqb pu_heval).

(* ================================================================= *)
(* Host runs of U_P.                                                    *)
(* ================================================================= *)

Lemma pu_hmu_mono : forall d s, M.mu s <= M.mu (hrun_prog d U_P s).
Proof. intros d s. rewrite M.pu_multi_mu_conservation_program. lia. Qed.

Lemma pu_hmu_le : forall a b s, a <= b -> M.mu (hrun_prog a U_P s) <= M.mu (hrun_prog b U_P s).
Proof.
  intros a b s H. replace b with (a + (b - a)) by lia.
  rewrite M.pu_multi_run_prog_add. apply pu_hmu_mono.
Qed.

Lemma pu_hcert_mono : forall d s, M.cert s = true -> M.cert (hrun_prog d U_P s) = true.
Proof.
  induction d as [| d IH]; intros s H; [exact H |]. cbn [M.pu_run_prog]. apply IH.
  unfold M.pu_step. destruct (M.pu_next_instr U_P (M.core_of s)); [| exact H].
  apply M.pu_multi_cert_permanent, H.
Qed.

Lemma pu_hcert_le : forall a b s, a <= b ->
  M.cert (hrun_prog a U_P s) = true -> M.cert (hrun_prog b U_P s) = true.
Proof.
  intros a b s H Hc. replace b with (a + (b - a)) by lia.
  rewrite M.pu_multi_run_prog_add. apply pu_hcert_mono, Hc.
Qed.

Lemma pu_hhalted_stay : forall a b s, a <= b ->
  M.pu_halted U_P (M.core_of (hrun_prog a U_P s)) -> hrun_prog b U_P s = hrun_prog a U_P s.
Proof.
  intros a b s H Hh. replace b with (a + (b - a)) by lia.
  rewrite M.pu_multi_run_prog_add. apply M.pu_multi_run_prog_halted, Hh.
Qed.

Lemma pu_hhalted_unique : forall a b s,
  M.pu_halted U_P (M.core_of (hrun_prog a U_P s)) -> M.pu_halted U_P (M.core_of (hrun_prog b U_P s)) ->
  hrun_prog a U_P s = hrun_prog b U_P s.
Proof.
  intros a b s Ha Hb. destruct (le_ge_dec a b) as [H | H].
  - symmetry. apply pu_hhalted_stay; assumption.
  - apply pu_hhalted_stay; assumption.
Qed.

(* A stretch of a run that pays nothing leaves the channel alone: the
   channel changes only at a COMMIT, which costs 1. *)
Lemma pu_hchan_const : forall d s,
  M.mu (hrun_prog d U_P s) = M.mu s -> M.chan (M.core_of (hrun_prog d U_P s)) = M.chan (M.core_of s).
Proof.
  induction d as [| d IH]; intros s H; [reflexivity |]. cbn [M.pu_run_prog] in *.
  unfold M.pu_step in *. destruct (M.pu_next_instr U_P (M.core_of s)) as [i |] eqn:Hn.
  - pose proof (pu_hmu_mono d (hexec s i)) as Hm.
    assert (Hmi : M.mu (hexec s i) = M.mu s + M.pu_cost i) by reflexivity.
    assert (Hc : M.pu_cost i = 0) by lia.
    rewrite IH by lia. simpl.
    destruct (M.pu_multi_chan_step pu_hprop_eqb pu_heval (M.core_of s) i) as [E | [p [c [-> _]]]];
      [exact E | discriminate Hc].
  - apply IH. exact H.
Qed.

(* A prefix of a host trace runs to the state after that many steps. *)
Lemma pu_htrace_prefix : forall n s l1 l2,
  htrace n U_P s = l1 ++ l2 -> hrun_l l1 s = hrun_prog (length l1) U_P s.
Proof.
  induction n as [| n IH]; intros s l1 l2 H.
  - destruct l1; [reflexivity | discriminate H].
  - destruct l1 as [| a l1]; [reflexivity |]. cbn [M.pu_trace_of] in H.
    destruct (M.pu_next_instr U_P (M.core_of s)) as [i |] eqn:Hn; [| discriminate H].
    injection H as -> H. cbn [M.pu_run M.pu_run_prog length].
    unfold M.pu_step. rewrite Hn. apply (IH _ _ l2 H).
Qed.

(* Equal versions of one register at two points of a host run mean equal
   values. *)
Lemma pu_hsame_point : forall a b s r,
  hver (hrun_prog a U_P s) r = hver (hrun_prog b U_P s) r ->
  hv (hrun_prog a U_P s) r = hv (hrun_prog b U_P s) r.
Proof.
  assert (K : forall a b s r, a <= b ->
    hver (hrun_prog a U_P s) r = hver (hrun_prog b U_P s) r ->
    hv (hrun_prog a U_P s) r = hv (hrun_prog b U_P s) r).
  { intros a b s r H Hv. replace b with (a + (b - a)) in * by lia.
    rewrite M.pu_multi_run_prog_add in *. set (s1 := hrun_prog a U_P s) in *.
    rewrite M.pu_multi_run_prog_trace in *.
    symmetry. apply pu_run_same_ver_same_val. symmetry. exact Hv. }
  intros a b s r Hv. destruct (le_ge_dec a b) as [H | H]; [apply K; assumption |].
  symmetry. apply K; [exact H | symmetry; exact Hv].
Qed.

(* ================================================================= *)
(* Guest runs.                                                        *)
(* ================================================================= *)

Lemma pu_grun_succ : forall m P s, E.run_prog (S m) P s = E.step P (E.run_prog m P s).
Proof.
  induction m as [| m IH]; intros P s; [reflexivity |].
  change (E.run_prog (S (S m)) P s) with (E.run_prog (S m) P (E.step P s)).
  rewrite IH. reflexivity.
Qed.

Lemma pu_grun_add : forall a b P s, E.run_prog (a + b) P s = E.run_prog b P (E.run_prog a P s).
Proof. induction a as [| a IH]; intros b P s; [reflexivity | apply IH]. Qed.

Lemma pu_gstep_halted : forall P g, E.halted P (E.core_of g) -> E.step P g = g.
Proof. intros P g H. unfold E.step. unfold E.halted in H. rewrite H. reflexivity. Qed.

Lemma pu_gtrace_prefix : forall n P s l1 l2,
  E.trace_of n P s = l1 ++ l2 -> E.run l1 s = E.run_prog (length l1) P s.
Proof.
  induction n as [| n IH]; intros P s l1 l2 H.
  - destruct l1; [reflexivity | discriminate H].
  - destruct l1 as [| a l1]; [reflexivity |]. cbn [E.trace_of] in H.
    destruct (E.next_instr P (E.core_of s)) as [i |] eqn:Hn; [| discriminate H].
    injection H as -> H. cbn [E.run E.run_prog length].
    unfold E.step. rewrite Hn. apply (IH _ _ _ l2 H).
Qed.

Lemma pu_gtrace_succ : forall m P s,
  E.trace_of (S m) P s =
  E.trace_of m P s ++
  match E.next_instr P (E.core_of (E.run_prog m P s)) with Some i => [i] | None => [] end.
Proof.
  induction m as [| m IH]; intros P s.
  - simpl. destruct (E.next_instr P (E.core_of s)); reflexivity.
  - replace (E.trace_of (S (S m)) P s) with
      (match E.next_instr P (E.core_of s) with
       | None => [] | Some i => i :: E.trace_of (S m) P (E.exec s i) end) by reflexivity.
    replace (E.trace_of (S m) P s) with
      (match E.next_instr P (E.core_of s) with
       | None => [] | Some i => i :: E.trace_of m P (E.exec s i) end) by reflexivity.
    replace (E.run_prog (S m) P s) with (E.run_prog m P (E.step P s)) by reflexivity.
    unfold E.step.
    destruct (E.next_instr P (E.core_of s)) as [i |] eqn:Hn.
    + rewrite IH. reflexivity.
    + rewrite E.run_prog_halted by exact Hn. rewrite Hn. reflexivity.
Qed.

Lemma pu_grun_same_ver : forall tr s c,
  E.ver (E.core_of (E.run tr s)) c = E.ver (E.core_of s) c ->
  E.val (E.core_of (E.run tr s)) c = E.val (E.core_of s) c.
Proof.
  induction tr as [| i tr IH]; intros s c H; [reflexivity |]. cbn [E.run] in *.
  pose proof (E.ver_mono (E.core_of s) i c) as H1.
  pose proof (E.ver_mono_run tr (E.exec s i) c) as H2.
  change (E.core_of (E.exec s i)) with (E.cexec (E.core_of s) i) in *.
  assert (E1 : E.ver (E.cexec (E.core_of s) i) c = E.ver (E.core_of s) c) by lia.
  rewrite IH; [apply E.ver_same_val, E1 | exact (eq_trans H (eq_sym E1))].
Qed.

Lemma pu_gsame_point : forall P a b s c,
  E.ver (E.core_of (E.run_prog a P s)) c = E.ver (E.core_of (E.run_prog b P s)) c ->
  E.val (E.core_of (E.run_prog a P s)) c = E.val (E.core_of (E.run_prog b P s)) c.
Proof.
  assert (K : forall P a b s c, a <= b ->
    E.ver (E.core_of (E.run_prog a P s)) c = E.ver (E.core_of (E.run_prog b P s)) c ->
    E.val (E.core_of (E.run_prog a P s)) c = E.val (E.core_of (E.run_prog b P s)) c).
  { intros P a b s c H Hv. replace b with (a + (b - a)) in * by lia.
    rewrite pu_grun_add in *. set (s1 := E.run_prog a P s) in *.
    rewrite E.run_prog_trace in *.
    symmetry. apply pu_grun_same_ver. symmetry. exact Hv. }
  intros P a b s c Hv. destruct (le_ge_dec a b) as [H | H]; [apply K; assumption |].
  symmetry. apply K; [exact H | symmetry; exact Hv].
Qed.

Lemma pu_gnext_fetch : forall P k i,
  E.err k = false -> E.next_instr P k = Some i -> E.fetch P (E.pc k) = Some i.
Proof.
  intros P k i He H. unfold E.next_instr in H. rewrite He in H.
  destruct (E.fetch P (E.pc k)) as [[] |]; congruence.
Qed.

(* ================================================================= *)
(* Matching points.                                                   *)
(* ================================================================= *)

Definition pu_grun (P : list E.instr) (x y m : nat) : E.state := E.run_prog m P (E.start x y).
Definition pu_hrun (P : list E.instr) (x y n : nat) : hstate := hrun_prog n U_P (pu_hload P x y).

Lemma pu_hrun_add : forall P x y a b, pu_hrun P x y (a + b) = hrun_prog b U_P (pu_hrun P x y a).
Proof. intros. unfold pu_hrun. apply M.pu_multi_run_prog_add. Qed.

Lemma pu_grun_halted_succ : forall P x y m,
  E.halted P (E.core_of (pu_grun P x y m)) -> pu_grun P x y (S m) = pu_grun P x y m.
Proof. intros. unfold pu_grun. rewrite pu_grun_succ. apply pu_gstep_halted. assumption. Qed.

(* A record's host fact had its version and value together at some point
   of the host run, and its guest fact at some point of the guest run. *)
Definition pu_hwit (P : list E.instr) (x y : nat) (r : pu_srec) : Prop :=
  exists t, hver (pu_hrun P x y t) (pu_SLOT (pu_r_c r) (pu_r_k r)) = pu_r_hv r /\
            hv (pu_hrun P x y t) (pu_SLOT (pu_r_c r) (pu_r_k r)) = pu_pair (pu_pcode (pu_r_p r)) (pu_r_v r).

Definition pu_gwit (P : list E.instr) (x y : nat) (r : pu_srec) : Prop :=
  exists t, E.ver (E.core_of (pu_grun P x y t)) (pu_r_c r) = pu_r_gv r /\
            E.val (E.core_of (pu_grun P x y t)) (pu_r_c r) = pu_r_v r.

Lemma pu_sim_points : forall P x y m, exists N sg rho,
  ((pu_rel_with P sg rho (pu_grun P x y m) (pu_hrun P x y N) /\ m <= N) \/
   pu_rel_halt P (pu_grun P x y m) (pu_hrun P x y N)) /\
  (forall n, n <= N -> exists m', m' <= m /\
     E.mu (pu_grun P x y m') <= M.mu (pu_hrun P x y n) <= E.mu (pu_grun P x y (S m'))) /\
  (forall r, In r sg -> pu_hwit P x y r /\ pu_gwit P x y r).
Proof.
  intros P x y m. induction m as [| m IH].
  - exists 0, [], None. split; [left; split; [apply pu_hload_rel | lia] |].
    split; [| intros r []].
    intros n Hn. exists 0. split; [lia |]. replace n with 0 by lia.
    unfold pu_hrun. simpl. lia.
  - destruct IH as [N [sg [rho [[[R Hle] | RH] [Hbr Hw]]]]].
    + assert (Hg : pu_grun P x y (S m) = E.step P (pu_grun P x y m))
        by (unfold pu_grun; apply pu_grun_succ).
      destruct (pu_U_step_with P sg rho _ _ R)
        as [[Hh [h' [[d Hd] RH']]] | [Hnh [d [h' [Hd [[sg' [rho' [R' Hnew]]] | [Herr RH']]]]]]].
      * (* the guest has stopped *)
        assert (Hh' : pu_hrun P x y (N + d) = h') by (rewrite pu_hrun_add; exact Hd).
        exists (N + d), [], None. split; [right; rewrite pu_grun_halted_succ, Hh'; assumption |].
        split; [| intros r []].
        intros n Hn. destruct (le_lt_dec n N) as [H | H].
        { destruct (Hbr n H) as [m' [Hm' Hb]]. exists m'. split; [lia | exact Hb]. }
        exists m. split; [lia |].
        rewrite (pu_grun_halted_succ P x y m Hh).
        pose proof (pu_hmu_le N n (pu_hload P x y) (Nat.lt_le_incl _ _ H)) as M1.
        pose proof (pu_hmu_le n (N + d) (pu_hload P x y) Hn) as M2.
        fold (pu_hrun P x y N) (pu_hrun P x y n) (pu_hrun P x y (N + d)) in M1, M2.
        rewrite Hh' in M2.
        destruct RH' as [_ [_ [_ [_ [_ [HM _]]]]]].
        pose proof (pu_rw_mu _ _ _ _ _ R). lia.
      * (* a related step *)
        assert (Hh' : pu_hrun P x y (N + S d) = h') by (rewrite pu_hrun_add; exact Hd).
        exists (N + S d), sg', rho'. split; [left; split; [rewrite Hg, Hh'; exact R' | lia] |].
        split.
        { intros n Hn. destruct (le_lt_dec n N) as [H | H].
          { destruct (Hbr n H) as [m' [Hm' Hb]]. exists m'. split; [lia | exact Hb]. }
          exists m. split; [lia |].
          pose proof (pu_hmu_le N n (pu_hload P x y) (Nat.lt_le_incl _ _ H)) as M1.
          pose proof (pu_hmu_le n (N + S d) (pu_hload P x y) Hn) as M2.
          fold (pu_hrun P x y N) (pu_hrun P x y n) (pu_hrun P x y (N + S d)) in M1, M2.
          rewrite Hh' in M2. rewrite Hg.
          pose proof (pu_rw_mu _ _ _ _ _ R). pose proof (pu_rw_mu _ _ _ _ _ R'). lia. }
        intros r Hin. destruct (Hnew r Hin) as [Hold | Hcur]; [exact (Hw r Hold) |].
        destruct (pu_rw_recs _ _ _ _ _ R' r Hin) as [_ [Hsl [_ [_ [Hiff [Hc _]]]]]].
        split.
        { exists (N + S d). rewrite Hh'. split; [symmetry; apply Hiff, Hcur | exact Hsl]. }
        { exists (S m). rewrite Hg. split; [symmetry; exact Hcur | symmetry; apply Hc, Hcur]. }
      * (* a trap *)
        assert (Hh' : pu_hrun P x y (N + S d) = h') by (rewrite pu_hrun_add; exact Hd).
        exists (N + S d), [], None. split; [right; rewrite Hg, Hh'; exact RH' |].
        split; [| intros r []].
        intros n Hn. destruct (le_lt_dec n N) as [H | H].
        { destruct (Hbr n H) as [m' [Hm' Hb]]. exists m'. split; [lia | exact Hb]. }
        exists m. split; [lia |].
        pose proof (pu_hmu_le N n (pu_hload P x y) (Nat.lt_le_incl _ _ H)) as M1.
        pose proof (pu_hmu_le n (N + S d) (pu_hload P x y) Hn) as M2.
        fold (pu_hrun P x y N) (pu_hrun P x y n) (pu_hrun P x y (N + S d)) in M1, M2.
        rewrite Hh' in M2. rewrite Hg.
        destruct RH' as [_ [_ [_ [_ [_ [HM _]]]]]].
        pose proof (pu_rw_mu _ _ _ _ _ R). lia.
    + (* both stopped already *)
      exists N, [], None. split; [right; rewrite pu_grun_halted_succ; [exact RH | apply RH] |].
      split; [| intros r []].
      intros n Hn. destruct (Hbr n Hn) as [m' [Hm' Hb]]. exists m'. split; [lia | exact Hb].
Qed.

Theorem pu_U_simulation : forall P x y m, exists n,
  (pu_rel P (pu_grun P x y m) (pu_hrun P x y n) /\ m <= n) \/ pu_rel_halt P (pu_grun P x y m) (pu_hrun P x y n).
Proof.
  intros P x y m. destruct (pu_sim_points P x y m) as [N [sg [rho [[[R Hle] | RH] _]]]].
  - exists N. left. split; [exists sg, rho; exact R | exact Hle].
  - exists N. right. exact RH.
Qed.

(* A stopped guest has a related stopped host. *)
Lemma pu_halt_point : forall P x y m, E.halted P (E.core_of (pu_grun P x y m)) ->
  exists N, pu_rel_halt P (pu_grun P x y m) (pu_hrun P x y N).
Proof.
  intros P x y m Hh. destruct (pu_sim_points P x y m) as [N [sg [rho [[[R _] | RH] _]]]].
  - destruct (pu_U_step_with P sg rho _ _ R) as [[_ [h' [[d Hd] RH']]] | [Hn _]];
      [| contradiction].
    exists (N + d). rewrite pu_hrun_add, Hd. exact RH'.
  - exists N. exact RH.
Qed.

Theorem pu_universal_halting : forall P x y,
  (exists m, E.halted P (E.core_of (pu_grun P x y m))) <->
  (exists n, M.pu_halted U_P (M.core_of (pu_hrun P x y n))).
Proof.
  intros P x y. split.
  - intros [m Hh]. destruct (pu_halt_point P x y m Hh) as [N RH]. exists N. apply RH.
  - intros [n Hh]. destruct (pu_sim_points P x y n) as [N [sg [rho [[[R Hle] | RH] _]]]].
    + exfalso. apply (pu_rel_host_running P sg rho _ _ R).
      unfold pu_hrun in *. rewrite (pu_hhalted_stay n N (pu_hload P x y) Hle Hh). exact Hh.
    + exists n. apply RH.
Qed.

Theorem pu_universal_output : forall P x y m n,
  E.halted P (E.core_of (pu_grun P x y m)) -> M.pu_halted U_P (M.core_of (pu_hrun P x y n)) ->
  hv (pu_hrun P x y n) pu_RA = E.ca (E.core_of (pu_grun P x y m)) /\
  hv (pu_hrun P x y n) pu_RB = E.cb (E.core_of (pu_grun P x y m)) /\
  herr (pu_hrun P x y n) = E.err (E.core_of (pu_grun P x y m)) /\
  M.mu (pu_hrun P x y n) = E.mu (pu_grun P x y m) /\
  M.cert (pu_hrun P x y n) = E.cert (pu_grun P x y m).
Proof.
  intros P x y m n Hg Hh. destruct (pu_halt_point P x y m Hg) as [N RH].
  assert (E : pu_hrun P x y n = pu_hrun P x y N).
  { unfold pu_hrun in *. apply pu_hhalted_unique; [exact Hh | apply RH]. }
  rewrite E. destruct RH as [_ [_ [Ha [Hb [He [Hm [Hc _]]]]]]]. auto.
Qed.

Theorem pu_universal_flag_iff : forall P x y,
  (exists m, E.cert (pu_grun P x y m) = true) <-> (exists n, M.cert (pu_hrun P x y n) = true).
Proof.
  intros P x y. split.
  - intros [m Hm]. destruct (pu_sim_points P x y m) as [N [sg [rho [[[R _] | RH] _]]]].
    + exists N. rewrite (pu_rw_cert _ _ _ _ _ R). exact Hm.
    + exists N. destruct RH as [_ [_ [_ [_ [_ [_ [Hc _]]]]]]]. rewrite Hc. exact Hm.
  - intros [n Hn]. destruct (pu_sim_points P x y n) as [N [sg [rho [[[R Hle] | RH] _]]]].
    + exists n. rewrite <- (pu_rw_cert _ _ _ _ _ R). unfold pu_hrun in *.
      apply (pu_hcert_le n N); assumption.
    + exists n. destruct RH as [_ [Hh [_ [_ [_ [_ [Hc _]]]]]]]. rewrite <- Hc.
      unfold pu_hrun in *. destruct (le_ge_dec n N) as [H | H].
      * apply (pu_hcert_le n N); assumption.
      * rewrite <- (pu_hhalted_stay N n (pu_hload P x y) H Hh). exact Hn.
Qed.

Theorem pu_universal_ledger_exact : forall P x y,
  (forall m, exists n,
     ((pu_rel P (pu_grun P x y m) (pu_hrun P x y n) /\ m <= n) \/
      pu_rel_halt P (pu_grun P x y m) (pu_hrun P x y n)) /\
     M.mu (pu_hrun P x y n) = E.mu (pu_grun P x y m)) /\
  (forall n, exists m,
     E.mu (pu_grun P x y m) <= M.mu (pu_hrun P x y n) <= E.mu (pu_grun P x y (S m))).
Proof.
  intros P x y. split.
  - intro m. destruct (pu_sim_points P x y m) as [N [sg [rho [[[R Hle] | RH] _]]]].
    + exists N. split; [left; split; [exists sg, rho; exact R | exact Hle] |].
      exact (pu_rw_mu _ _ _ _ _ R).
    + exists N. split; [right; exact RH |]. apply RH.
  - intro n. destruct (pu_sim_points P x y n) as [N [sg [rho [[[R Hle] | RH] [Hbr _]]]]].
    + destruct (Hbr n Hle) as [m' [_ Hb]]. exists m'. exact Hb.
    + destruct (le_ge_dec n N) as [H | H].
      * destruct (Hbr n H) as [m' [_ Hb]]. exists m'. exact Hb.
      * exists n. destruct RH as [Hg [Hh [_ [_ [_ [Hm _]]]]]].
        unfold pu_hrun in *. rewrite (pu_hhalted_stay N n (pu_hload P x y) H Hh), Hm.
        rewrite (pu_grun_halted_succ P x y n Hg). lia.
Qed.

(* ================================================================= *)
(* Earned certification, host and guest.                              *)
(* ================================================================= *)

Lemma pu_cert_switch : forall (f : nat -> bool) m,
  f 0 = false -> f m = true -> exists m0, f m0 = false /\ f (S m0) = true.
Proof.
  intros f m H0. induction m as [| m IH]; intro Hm; [congruence |].
  destruct (f m) eqn:E; [apply IH; reflexivity | exists m; auto].
Qed.

Theorem pu_universal_earned : forall P x y n,
  M.cert (pu_hrun P x y n) = true ->
  exists c k p v pre1 mid1 mid2 post,
    k < 16 /\
    htrace n U_P (pu_hload P x y) =
      pre1 ++ M.CHECK PSlot (pu_SLOT c k) :: mid1 ++ M.COMMIT PSlot (pu_SLOT c k) :: mid2 ++
      M.CERTIFY :: post /\
    M.pu_check_ok pu_heval (M.core_of (hrun_l pre1 (pu_hload P x y))) PSlot (pu_SLOT c k) = true /\
    M.pu_commit_ok pu_hprop_eqb
      (M.core_of (hrun_l (pre1 ++ M.CHECK PSlot (pu_SLOT c k) :: mid1) (pu_hload P x y)))
      PSlot (pu_SLOT c k) = true /\
    M.pu_certify_ok (M.core_of (hrun_l (pre1 ++ M.CHECK PSlot (pu_SLOT c k) :: mid1 ++
                                     M.COMMIT PSlot (pu_SLOT c k) :: mid2) (pu_hload P x y))) = true /\
    hver (hrun_l pre1 (pu_hload P x y)) (pu_SLOT c k) =
      hver (hrun_l (pre1 ++ M.CHECK PSlot (pu_SLOT c k) :: mid1) (pu_hload P x y)) (pu_SLOT c k) /\
    M.pu_untouched pu_hprop_eqb pu_heval (hrun_l (pre1 ++ [M.CHECK PSlot (pu_SLOT c k)]) (pu_hload P x y))
      mid1 (pu_SLOT c k) /\
    hv (hrun_l pre1 (pu_hload P x y)) (pu_SLOT c k) = pu_pair (pu_pcode p) v /\ E.holds p v /\
    exists m gpre gmid1 gmid2 gpost,
      E.trace_of m P (E.start x y) =
        gpre ++ E.CHECK p c :: gmid1 ++ E.COMMIT p c :: gmid2 ++ E.CERTIFY :: gpost /\
      E.check_ok (E.core_of (E.run gpre (E.start x y))) p c = true /\
      E.commit_ok (E.core_of (E.run (gpre ++ E.CHECK p c :: gmid1) (E.start x y))) p c = true /\
      E.certify_ok (E.core_of (E.run (gpre ++ E.CHECK p c :: gmid1 ++ E.COMMIT p c :: gmid2)
                                     (E.start x y))) = true /\
      E.ver (E.core_of (E.run gpre (E.start x y))) c =
        E.ver (E.core_of (E.run (gpre ++ E.CHECK p c :: gmid1) (E.start x y))) c /\
      E.untouched (E.run (gpre ++ [E.CHECK p c]) (E.start x y)) gmid1 c /\
      E.val (E.core_of (E.run gpre (E.start x y))) c = v.
Proof.
  intros P x y n Hc.
  set (h0 := pu_hload P x y). set (g0 := E.start x y).
  (* The guest certifies, and its flag rises at some step m0. *)
  destruct (proj2 (pu_universal_flag_iff P x y) (ex_intro _ n Hc)) as [m Hm].
  destruct (pu_cert_switch (fun m => E.cert (pu_grun P x y m)) m eq_refl Hm) as [m0 [Hc0 Hc1]].
  simpl in Hc0, Hc1.
  destruct (pu_sim_points P x y m0) as [N0 [sg [rho [[[R _] | RH] [_ Hwit]]]]].
  2:{ exfalso. rewrite (pu_grun_halted_succ P x y m0 (proj1 RH)) in Hc1. congruence. }
  set (g := pu_grun P x y m0) in *.
  pose proof (pu_rw_err _ _ _ _ _ R) as He.
  assert (Hgs : pu_grun P x y (S m0) = E.step P g) by (unfold g, pu_grun; apply pu_grun_succ).
  rewrite Hgs in Hc1. unfold E.step in Hc1.
  destruct (E.next_instr P (E.core_of g)) as [i |] eqn:Hni; [| congruence].
  destruct (E.only_certify_certifies g i Hc0 Hc1) as [-> Hgok].
  pose proof (pu_gnext_fetch P _ _ He Hni) as Hgf.
  (* The guest channel names a record r0 of sg. *)
  assert (Hr0 : exists r0, rho = Some r0).
  { unfold E.certify_ok in Hgok. rewrite (pu_rw_gchan _ _ _ _ _ R) in Hgok.
    destruct rho as [r0 |]; [exists r0; reflexivity | rewrite He in Hgok; discriminate]. }
  destruct Hr0 as [r0 Hrho].
  pose proof (pu_rw_rho _ _ _ _ _ R r0 Hrho) as Hin0.
  destruct (Hwit r0 Hin0) as [[tau [Hwv Hwval]] [sig [Hgv Hgval]]].
  destruct (pu_rw_recs _ _ _ _ _ R r0 Hin0) as [Hk0 _].
  set (c := pu_r_c r0) in *. set (k := pu_r_k r0) in *.
  set (p := pu_r_p r0) in *. set (v := pu_r_v r0) in *.
  (* The host's CERTIFY phase from the matching point N0. *)
  assert (Hhf : E.fetch P (hv (pu_hrun P x y N0) pu_GPC) = Some E.CERTIFY)
    by (rewrite (pu_rw_gpc _ _ _ _ _ R); exact Hgf).
  assert (Hhc : M.chan (M.core_of (pu_hrun P x y N0)) = Some (pu_hfact r0))
    by (rewrite (pu_rw_hchan _ _ _ _ _ R), Hrho; reflexivity).
  destruct (pu_phase_certify_pass P (pu_hrun P x y N0) (pu_hfact r0) (pu_rw_head _ _ _ _ _ R) Hhf Hhc)
    as [h1 [[d Hd] [_ [_ [_ [_ [HM1 [HR1 _]]]]]]]].
  assert (Hh1 : pu_hrun P x y (N0 + d) = h1) by (rewrite pu_hrun_add; exact Hd).
  assert (Hcert0 : M.cert (pu_hrun P x y N0) = false) by (rewrite (pu_rw_cert _ _ _ _ _ R); exact Hc0).
  (* The host's first raising CERTIFY. *)
  assert (Hrn : M.cert (hrun_l (htrace n U_P h0) h0) = true)
    by (rewrite <- M.pu_multi_run_prog_trace; exact Hc).
  destruct (M.pu_multi_cert_first pu_hprop_eqb pu_heval h0 _ eq_refl Hrn)
    as [pre [post [Htr [Hpre Hok]]]].
  set (t := length pre).
  assert (Ht : hrun_l pre h0 = pu_hrun P x y t) by exact (pu_htrace_prefix n h0 pre _ Htr).
  assert (Ht1 : hrun_l (pre ++ [M.CERTIFY]) h0 = pu_hrun P x y (S t)).
  { rewrite (pu_htrace_prefix n h0 (pre ++ [M.CERTIFY]) post);
      [rewrite app_length; simpl; unfold pu_hrun, t; f_equal; lia |].
    rewrite Htr, <- app_assoc. reflexivity. }
  rewrite M.pu_multi_run_snoc, (M.pu_multi_exec_certify_pass pu_hprop_eqb pu_heval _ Hok) in Ht1.
  rewrite Ht in Hpre, Ht1.
  assert (HcS : M.cert (pu_hrun P x y (S t)) = true) by (rewrite <- Ht1; reflexivity).
  assert (HmS : M.mu (pu_hrun P x y (S t)) = M.mu (pu_hrun P x y t) + 1) by (rewrite <- Ht1; reflexivity).
  assert (Hlo : N0 <= t).
  { destruct (le_lt_dec N0 t) as [H | H]; [exact H | exfalso].
    pose proof (pu_hcert_le (S t) N0 h0 H HcS) as X.
    change (M.cert (pu_hrun P x y N0) = true) in X. congruence. }
  assert (Hhi : S t <= N0 + d).
  { destruct (le_lt_dec (S t) (N0 + d)) as [H | H]; [exact H | exfalso].
    assert (X : M.cert (pu_hrun P x y (N0 + d)) = true) by (rewrite Hh1; exact HR1).
    pose proof (pu_hcert_le (N0 + d) t h0 ltac:(lia) X) as Y.
    change (M.cert (pu_hrun P x y t) = true) in Y. congruence. }
  assert (Hmu : M.mu (pu_hrun P x y t) = M.mu (pu_hrun P x y N0)).
  { pose proof (pu_hmu_le N0 t h0 Hlo) as M1. pose proof (pu_hmu_le (S t) (N0 + d) h0 Hhi) as M2.
    change (M.mu (pu_hrun P x y N0) <= M.mu (pu_hrun P x y t)) in M1.
    change (M.mu (pu_hrun P x y (S t)) <= M.mu (pu_hrun P x y (N0 + d))) in M2.
    rewrite Hh1 in M2. lia. }
  assert (Hch : M.chan (M.core_of (hrun_l pre h0)) = Some (pu_hfact r0)).
  { rewrite Ht. rewrite <- Hhc. replace t with (N0 + (t - N0)) in * by lia.
    rewrite pu_hrun_add in *. apply pu_hchan_const. exact Hmu. }
  (* The host chain, from the host's own record rules. *)
  destruct (M.pu_multi_chan_origin pu_hprop_eqb pu_heval h0 pre (pu_hfact r0) eq_refl Hch)
    as [preC [p' [R' [mid2 [HpreC [Hcm Hf]]]]]].
  destruct p'.
  unfold pu_hfact, M.pu_claim in Hf.
  assert (HR' : R' = pu_SLOT c k) by (apply (f_equal M.f_reg) in Hf; symmetry; exact Hf).
  assert (HvC : hver (hrun_l preC h0) R' = pu_r_hv r0)
    by (apply (f_equal M.f_ver) in Hf; symmetry; exact Hf).
  subst R'.
  destruct (M.pu_multi_earned_commitment_provenance pu_hprop_eqb pu_hprop_eqb_eq pu_heval h0 preC
              PSlot (pu_SLOT c k) (M.pu_multi_start_clean _) Hcm)
    as [pre1 [mid1 [HpreC1 [Hck [_ [_ [Hv1 Hun]]]]]]].
  subst pre preC.
  assert (Hlist : htrace n U_P h0 =
    pre1 ++ M.CHECK PSlot (pu_SLOT c k) :: mid1 ++ M.COMMIT PSlot (pu_SLOT c k) :: mid2 ++
    M.CERTIFY :: post) by (rewrite Htr; repeat (rewrite <- app_assoc; simpl); reflexivity).
  assert (Hp1 : hrun_l pre1 h0 = pu_hrun P x y (length pre1))
    by exact (pu_htrace_prefix n h0 pre1 _ Hlist).
  (* The slot value at the host CHECK is the record's pair. *)
  assert (Hval : hv (hrun_l pre1 h0) (pu_SLOT c k) = pu_pair (pu_pcode p) v).
  { rewrite Hp1. rewrite <- Hwval. apply pu_hsame_point.
    change (hver (pu_hrun P x y (length pre1)) (pu_SLOT c k) = hver (pu_hrun P x y tau) (pu_SLOT c k)).
    rewrite <- Hp1, Hv1, HvC. symmetry. exact Hwv. }
  assert (Hholds : E.holds p v).
  { unfold M.pu_check_ok in Hck. apply andb_true_iff in Hck as [Hck _].
    apply andb_true_iff in Hck as [_ Hck]. rewrite Hval, pu_heval_pair in Hck.
    apply E.eval_iff, Hck. }
  (* The guest chain, from the guest's own record rules. *)
  assert (Hgch : E.chan (E.core_of (E.run (E.trace_of m0 P g0) g0)) = Some (pu_gfact r0)).
  { rewrite <- E.run_prog_trace. change (E.chan (E.core_of g) = Some (pu_gfact r0)).
    rewrite (pu_rw_gchan _ _ _ _ _ R), Hrho. reflexivity. }
  destruct (E.chan_origin g0 _ _ eq_refl Hgch) as [gpreC [p'' [c'' [gmid2 [HgC [Hgcm Hgf']]]]]].
  unfold E.claim in Hgf'. apply pu_gfact_eq in Hgf' as [Hp'' [Hc'' Hv'']].
  fold p in Hp''. fold c in Hc''. subst p'' c''.
  destruct (E.earned_commitment_provenance g0 gpreC p c (E.start_clean x y) Hgcm)
    as [gpre [gmid1 [HgC1 [Hgck [_ [_ [Hgv1 Hgun]]]]]]].
  subst gpreC.
  assert (Hglist : E.trace_of (S m0) P g0 =
    gpre ++ E.CHECK p c :: gmid1 ++ E.COMMIT p c :: gmid2 ++ [E.CERTIFY]).
  { rewrite pu_gtrace_succ. change (E.run_prog m0 P g0) with g. rewrite Hni, HgC.
    repeat (rewrite <- app_assoc; simpl). reflexivity. }
  assert (Hgp : E.run gpre g0 = pu_grun P x y (length gpre))
    by exact (pu_gtrace_prefix (S m0) P g0 gpre _ Hglist).
  assert (Hgvalue : E.val (E.core_of (E.run gpre g0)) c = v).
  { rewrite Hgp. rewrite <- Hgval. unfold pu_grun. apply pu_gsame_point.
    change (E.ver (E.core_of (pu_grun P x y (length gpre))) c =
            E.ver (E.core_of (pu_grun P x y sig)) c).
    rewrite <- Hgp, Hgv1, Hgv.
    symmetry. exact Hv''. }
  exists c, k, p, v, pre1, mid1, mid2, post.
  split; [exact Hk0 |]. split; [exact Hlist |]. split; [exact Hck |].
  split; [exact Hcm |].
  split.
  { replace (pre1 ++ M.CHECK PSlot (pu_SLOT c k) :: mid1 ++ M.COMMIT PSlot (pu_SLOT c k) :: mid2)
      with (((pre1 ++ M.CHECK PSlot (pu_SLOT c k) :: mid1) ++ M.COMMIT PSlot (pu_SLOT c k) :: mid2))
      by (repeat (rewrite <- app_assoc; simpl); reflexivity).
    exact Hok. }
  split; [exact Hv1 |].
  split; [exact Hun |]. split; [exact Hval |]. split; [exact Hholds |].
  exists (S m0), gpre, gmid1, gmid2, [].
  split; [exact Hglist |]. split; [exact Hgck |]. split; [exact Hgcm |].
  split; [| split; [exact Hgv1 | split; [exact Hgun | exact Hgvalue]]].
  replace (gpre ++ E.CHECK p c :: gmid1 ++ E.COMMIT p c :: gmid2)
    with ((gpre ++ E.CHECK p c :: gmid1) ++ E.COMMIT p c :: gmid2)
    by (rewrite <- app_assoc; reflexivity).
  rewrite <- HgC, <- E.run_prog_trace. exact Hgok.
Qed.

(* ================================================================= *)
(* The host machine is Thiele-complete.                               *)
(* ================================================================= *)

(* The host machine of ThieleComplete.v: states and instructions of
   EarnedMulti with the property PSlot, one instruction per move, cost
   and flag as in EarnedMulti. *)
Definition pu_host_machine : TC.machine :=
  TC.mk_machine hstate hinstr hexec (@M.pu_cost pu_hprop) (@M.cert pu_hprop).

Lemma pu_run_host : forall tr s, TC.run pu_host_machine tr s = hrun_l tr s.
Proof. induction tr; intros; simpl; auto. Qed.

(* U's run from hload is a run of pu_host_machine. *)
Lemma pu_U_run_on_host_machine : forall P x y n,
  TC.run pu_host_machine (htrace n U_P (pu_hload P x y)) (pu_hload P x y) = pu_hrun P x y n.
Proof. intros. rewrite pu_run_host. unfold pu_hrun. symmetry. apply M.pu_multi_run_prog_trace. Qed.

Definition pu_hreg_of (r : TC.reg) : nat := match r with TC.RA => 0 | TC.RB => 1 end.

Definition pu_host_compile (i : TC.cm_instr) : hinstr :=
  match i with
  | TC.CINC r => M.INC (pu_hreg_of r)
  | TC.CDEC r j => M.DEC (pu_hreg_of r) j
  end.

Definition pu_host_window (s : hstate) : TC.cm_conf := (hpc s, (hv s 0, hv s 1)).

Definition pu_host_load (a b : nat) : hstate :=
  M.pu_start (fun r => if Nat.eqb r 0 then a else if Nat.eqb r 1 then b else 0).

Lemma pu_host_sim : forall (s : hstate) i, herr s = false ->
  pu_host_window (hexec s (pu_host_compile i)) = TC.cm_exec i (pu_host_window s) /\
  herr (hexec s (pu_host_compile i)) = false.
Proof.
  intros [[vs vr pc f ch e] m c] i He. simpl in He. subst e.
  unfold pu_host_window. destruct i as [[|] | [|] j]; simpl;
    unfold M.pu_cexec, M.pu_write, M.pu_goto, M.pu_upd; simpl.
  - split; reflexivity.
  - split; reflexivity.
  - destruct (vs 0) eqn:E; simpl; rewrite ?E; split; reflexivity.
  - destruct (vs 1) eqn:E; simpl; rewrite ?E; split; reflexivity.
Qed.

Definition pu_host_base : TC.universal_base pu_host_machine :=
  TC.mk_ub pu_host_machine pu_host_window (fun s => herr s = false) pu_host_compile pu_host_load
    (fun a b => eq_refl) (fun a b => eq_refl) pu_host_sim.

(* Claims: Some (p, r) is "p holds of register r"; None is the empty
   claim of PAY, which means nothing, is never checked true, and is kept
   by every change. PAY reads as a check of the empty claim, as in
   PricedComplete.v: it costs 1 like a record move, and it can never start
   an earned chain. *)
Definition pu_host_kind (i : hinstr) : TC.kind (option (pu_hprop * nat)) :=
  match i with
  | M.CHECK p r => TC.KCheck (Some (p, r))
  | M.COMMIT p r => TC.KCommit (Some (p, r))
  | M.CERTIFY => TC.KCertify
  | M.PAY => TC.KCheck None
  | _ => TC.KBase
  end.

Definition pu_host_meaning (c : option (pu_hprop * nat)) (s : hstate) : Prop :=
  match c with Some pr => pu_hholds (fst pr) (hv s (snd pr)) | None => False end.

Definition pu_host_check (s : hstate) (c : option (pu_hprop * nat)) : bool :=
  match c with
  | Some pr => M.pu_check_ok pu_heval (M.core_of s) (fst pr) (snd pr)
  | None => false
  end.

Definition pu_host_same (c : option (pu_hprop * nat)) (s t : hstate) : Prop :=
  match c with
  | Some pr => hver s (snd pr) = hver t (snd pr) /\ hv s (snd pr) = hv t (snd pr)
  | None => True
  end.

Definition pu_host_interface : TC.thiele_interface pu_host_machine :=
  TC.mk_ti pu_host_machine pu_host_base (option (pu_hprop * nat)) pu_host_kind
    pu_host_meaning pu_host_check pu_host_same M.pu_clean_start (@M.mu pu_hprop).

Lemma pu_host_untouched_prefix : forall s mid r, M.pu_untouched pu_hprop_eqb pu_heval s mid r ->
  forall t1 t2, mid = t1 ++ t2 ->
  hver (hrun_l t1 s) r = hver s r /\ hv (hrun_l t1 s) r = hv s r.
Proof.
  intros s mid r Hu t1. induction t1 as [| i t1 IH] using rev_ind; intros t2 Hmid;
    [simpl; auto |].
  destruct (IH (i :: t2)) as [Hv Hw]; [rewrite Hmid, <- app_assoc; reflexivity |].
  destruct (Hu t1 i t2) as [Hv' Hw']; [rewrite Hmid, <- app_assoc; reflexivity |].
  rewrite M.pu_multi_run_snoc. simpl. rewrite Hv', Hw'. auto.
Qed.

Lemma pu_host_chain_holds : forall s0 tr,
  M.pu_clean_start s0 -> M.cert (hrun_l tr s0) = true ->
  TC.earned_chain pu_host_interface s0 tr.
Proof.
  intros s0 tr H0 H1. pose proof H0 as [_ [Hch Hc0]].
  destruct (M.pu_multi_cert_first pu_hprop_eqb pu_heval s0 tr Hc0 H1) as [pre [post [Htr [Hpre Hok]]]].
  pose proof Hok as Hset. unfold M.pu_certify_ok in Hset.
  apply andb_true_iff in Hset as [_ Hset].
  destruct (M.chan (M.core_of (hrun_l pre s0))) as [f |] eqn:Hf; [| discriminate].
  destruct (M.pu_multi_chan_origin pu_hprop_eqb pu_heval s0 pre f Hch Hf)
    as [preC [p [c [mid2 [HpreC [Hcm _]]]]]].
  destruct (M.pu_multi_earned_commitment_provenance pu_hprop_eqb pu_hprop_eqb_eq pu_heval
              s0 preC p c H0 Hcm)
    as [pre1 [mid1 [Hpre1 [Hck [_ [_ [_ Hun]]]]]]].
  assert (Hlist : pre1 ++ M.CHECK p c :: mid1 ++ M.COMMIT p c :: mid2 = pre)
    by (rewrite HpreC, Hpre1; TC.list_eq).
  exists pre1, (Some (p, c)), (M.CHECK p c), mid1, (M.COMMIT p c), mid2, M.CERTIFY, post.
  split; [rewrite Htr, <- Hlist; TC.list_eq |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [rewrite pu_run_host; exact Hck |].
  split.
  { intros t1 t2 Hm. rewrite !pu_run_host. simpl.
    replace (pre1 ++ M.CHECK p c :: t1) with ((pre1 ++ [M.CHECK p c]) ++ t1)
      by (rewrite <- app_assoc; reflexivity).
    rewrite M.pu_multi_run_app.
    destruct (pu_host_untouched_prefix _ _ _ Hun t1 t2 Hm) as [Hv Hw].
    rewrite Hv, Hw, M.pu_multi_run_snoc. simpl.
    rewrite M.pu_multi_ver_check, M.pu_multi_val_check. split; reflexivity. }
  assert (Hl2 : pre1 ++ M.CHECK p c :: mid1 ++ M.COMMIT p c :: mid2 ++ [M.CERTIFY]
                = pre ++ [M.CERTIFY]) by (rewrite <- Hlist; TC.list_eq).
  assert (Hup : M.cert (hrun_l (pre ++ [M.CERTIFY]) s0) = true)
    by (rewrite M.pu_multi_run_snoc; simpl; rewrite Hpre; exact Hok).
  rewrite <- Hl2 in Hup. rewrite <- Hlist in Hpre.
  split; rewrite pu_run_host; assumption.
Qed.

Lemma pu_host_chain_iff : forall a b,
  M.cert (hrun_l [M.CHECK PSlot 0; M.COMMIT PSlot 0; M.CERTIFY] (pu_host_load a b)) = true <->
  pu_hholds PSlot a.
Proof.
  intros a b. rewrite <- pu_heval_iff.
  change (hrun_l [M.CHECK PSlot 0; M.COMMIT PSlot 0; M.CERTIFY] (pu_host_load a b))
    with (hexec (hexec (hexec (pu_host_load a b) (M.CHECK PSlot 0)) (M.COMMIT PSlot 0))
            M.CERTIFY).
  destruct (pu_heval PSlot a) eqn:Ev.
  - assert (Hck : M.pu_check_ok pu_heval (M.core_of (pu_host_load a b)) PSlot 0 = true)
      by (unfold M.pu_check_ok; simpl; rewrite Ev; reflexivity).
    rewrite (M.pu_multi_exec_check_pass pu_hprop_eqb pu_heval (pu_host_load a b) PSlot 0 Hck).
    set (k1 := M.pu_record_fact (M.core_of (pu_host_load a b))
                 (M.pu_claim (M.core_of (pu_host_load a b)) PSlot 0)).
    assert (Hcm : M.pu_commit_ok pu_hprop_eqb k1 PSlot 0 = true).
    { apply (M.pu_multi_commit_ok_iff pu_hprop_eqb pu_hprop_eqb_eq). split; [reflexivity |].
      left. reflexivity. }
    set (s1 := M.mkst k1 (M.mu (pu_host_load a b) + 1) (M.cert (pu_host_load a b))).
    rewrite (M.pu_multi_exec_commit_pass pu_hprop_eqb pu_hprop_eqb_eq pu_heval s1 PSlot 0 Hcm).
    split; reflexivity.
  - assert (Hck : M.pu_check_ok pu_heval (M.core_of (pu_host_load a b)) PSlot 0 = false)
      by (unfold M.pu_check_ok; simpl; rewrite Ev; reflexivity).
    rewrite (M.pu_multi_exec_check_fail pu_hprop_eqb pu_heval (pu_host_load a b) PSlot 0 eq_refl Hck).
    split; intro H; discriminate H.
Qed.

Lemma pu_hholds_one : pu_hholds PSlot 1.
Proof. vm_compute. reflexivity. Qed.

Lemma pu_hholds_zero : ~ pu_hholds PSlot 0.
Proof. vm_compute. intros []. Qed.

Theorem pu_host_thiele_complete_with : TC.thiele_complete_with pu_host_interface.
Proof.
  split; [| split; [| split]].
  - split; [intros [[|] | [|] j]; reflexivity |].
    split; [intros a b; apply M.pu_multi_start_clean |]. split.
    + intros s m Hk. destruct m; simpl in Hk; try discriminate; simpl;
        apply orb_false_r.
    + intros s m H. apply M.pu_multi_cert_permanent, H.
  - split; [intros s [_ [_ H]]; exact H |]. split.
    + intros s0 tr H0 H1. apply pu_host_chain_holds; [exact H0 |].
      rewrite <- pu_run_host. exact H1.
    + split.
      * intros s [[p r] |] H; simpl in *; [| discriminate H]. unfold M.pu_check_ok in H.
        apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
        apply pu_heval_iff, H.
      * intros [[p r] |] s t Hs H; simpl in *; [| contradiction H].
        destruct Hs as [_ Hsame]. rewrite <- Hsame. exact H.
  - split; [intros []; reflexivity | intros s m; reflexivity].
  - exists (Some (PSlot, 0)), (M.CHECK PSlot 0), (M.COMMIT PSlot 0), M.CERTIFY.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [| split; [exists 1, 0; exact pu_hholds_one | exists 0, 0; exact pu_hholds_zero]].
    intros a b. unfold TC.load. simpl TC.ti_meaning. rewrite pu_run_host.
    apply pu_host_chain_iff.
Qed.

Theorem pu_universal_thiele_complete : TC.thiele_complete pu_host_machine.
Proof. exists pu_host_interface. exact pu_host_thiele_complete_with. Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions pu_sim_points.
Print Assumptions pu_U_simulation.
Print Assumptions pu_halt_point.
Print Assumptions pu_universal_halting.
Print Assumptions pu_universal_output.
Print Assumptions pu_universal_flag_iff.
Print Assumptions pu_universal_ledger_exact.
Print Assumptions pu_universal_earned.
Print Assumptions pu_U_run_on_host_machine.
Print Assumptions pu_host_thiele_complete_with.
Print Assumptions pu_universal_thiele_complete.
