(** UniversalRun.v: whole runs of the fixed host program U.

    For every guest program P of the small machine and every start (x, y),
    grun P x y m is the guest after m steps from E.start x y, and
    hrun P x y n is the host after n steps of U from hload P x y.

      universal_simulation     every guest step count m has a matching host
                               step count n >= m with rel, or both machines
                               have stopped and rel_halt holds
      universal_halting        the guest halts iff the host halts
      universal_output         at halting, RA and RB hold the guest
                               counters, and the trap latches, the ledgers
                               and the flags are equal
      universal_flag_iff       the guest's flag ever rises iff the host's
                               flag ever rises
      universal_ledger_exact   at matching points the host ledger equals the
                               guest ledger, and every host prefix's ledger
                               lies between the guest ledger at some m and
                               at m + 1
      universal_earned         a raised host flag stands on the host's own
                               chain: a passing CHECK PSlot (SLOT c k), a
                               passing COMMIT PSlot (SLOT c k) of the same
                               claim with the slot untouched between, and the
                               CERTIFY that raised the flag; when checked,
                               the slot held pair (pcode p) v with p true of
                               v; and the guest's own run contains its chain
                               CHECK p c, COMMIT p c, CERTIFY on the same p
                               and c, with v the value of guest counter c at
                               its CHECK
      universal_thiele_complete  the host machine (EarnedMulti with the
                               property PSlot), read with its INC/DEC moves as
                               the base and CHECK, COMMIT, CERTIFY as the
                               record moves, meets thiele_complete of
                               ThieleComplete.v

    Dependencies: the Coq standard library, the vendored
    coq-undecidability library, EarnedCore.v, EarnedGeneric.v,
    EarnedMulti.v, ThieleComplete.v, UniversalCodes.v, UniversalBridge.v,
    UniversalBlocks.v, UniversalLayout.v, UniversalPhases.v and
    UniversalSim.v. No axioms, no Admitted.                               *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.UniversalCodes Minimal.UniversalBridge Minimal.UniversalBlocks
  Minimal.UniversalLayout Minimal.UniversalPhases Minimal.UniversalSim.
Require Minimal.ThieleComplete.
Module TC := Minimal.ThieleComplete.

Local Notation hstate := (@M.state hprop).
Local Notation hinstr := (@M.instr hprop).
Local Notation hrun_prog := (M.run_prog hprop_eqb heval).
Local Notation hrun_l := (M.run hprop_eqb heval).
Local Notation htrace := (M.trace_of hprop_eqb heval).
Local Notation hexec := (M.exec hprop_eqb heval).

(* ================================================================= *)
(* Host runs of U.                                                    *)
(* ================================================================= *)

Lemma hmu_mono : forall d s, M.mu s <= M.mu (hrun_prog d U s).
Proof. intros d s. rewrite M.multi_mu_conservation_program. lia. Qed.

Lemma hmu_le : forall a b s, a <= b -> M.mu (hrun_prog a U s) <= M.mu (hrun_prog b U s).
Proof.
  intros a b s H. replace b with (a + (b - a)) by lia.
  rewrite M.multi_run_prog_add. apply hmu_mono.
Qed.

Lemma hcert_mono : forall d s, M.cert s = true -> M.cert (hrun_prog d U s) = true.
Proof.
  induction d as [| d IH]; intros s H; [exact H |]. cbn [M.run_prog]. apply IH.
  unfold M.step. destruct (M.next_instr U (M.core_of s)); [| exact H].
  apply M.multi_cert_permanent, H.
Qed.

Lemma hcert_le : forall a b s, a <= b ->
  M.cert (hrun_prog a U s) = true -> M.cert (hrun_prog b U s) = true.
Proof.
  intros a b s H Hc. replace b with (a + (b - a)) by lia.
  rewrite M.multi_run_prog_add. apply hcert_mono, Hc.
Qed.

Lemma hhalted_stay : forall a b s, a <= b ->
  M.halted U (M.core_of (hrun_prog a U s)) -> hrun_prog b U s = hrun_prog a U s.
Proof.
  intros a b s H Hh. replace b with (a + (b - a)) by lia.
  rewrite M.multi_run_prog_add. apply M.multi_run_prog_halted, Hh.
Qed.

Lemma hhalted_unique : forall a b s,
  M.halted U (M.core_of (hrun_prog a U s)) -> M.halted U (M.core_of (hrun_prog b U s)) ->
  hrun_prog a U s = hrun_prog b U s.
Proof.
  intros a b s Ha Hb. destruct (le_ge_dec a b) as [H | H].
  - symmetry. apply hhalted_stay; assumption.
  - apply hhalted_stay; assumption.
Qed.

(* A stretch of a run that pays nothing leaves the channel alone: the
   channel changes only at a COMMIT, which costs 1. *)
Lemma hchan_const : forall d s,
  M.mu (hrun_prog d U s) = M.mu s -> M.chan (M.core_of (hrun_prog d U s)) = M.chan (M.core_of s).
Proof.
  induction d as [| d IH]; intros s H; [reflexivity |]. cbn [M.run_prog] in *.
  unfold M.step in *. destruct (M.next_instr U (M.core_of s)) as [i |] eqn:Hn.
  - pose proof (hmu_mono d (hexec s i)) as Hm.
    assert (Hmi : M.mu (hexec s i) = M.mu s + M.cost i) by reflexivity.
    assert (Hc : M.cost i = 0) by lia.
    rewrite IH by lia. simpl.
    destruct (M.multi_chan_step hprop_eqb heval (M.core_of s) i) as [E | [p [c [-> _]]]];
      [exact E | discriminate Hc].
  - apply IH. exact H.
Qed.

(* A prefix of a host trace runs to the state after that many steps. *)
Lemma htrace_prefix : forall n s l1 l2,
  htrace n U s = l1 ++ l2 -> hrun_l l1 s = hrun_prog (length l1) U s.
Proof.
  induction n as [| n IH]; intros s l1 l2 H.
  - destruct l1; [reflexivity | discriminate H].
  - destruct l1 as [| a l1]; [reflexivity |]. cbn [M.trace_of] in H.
    destruct (M.next_instr U (M.core_of s)) as [i |] eqn:Hn; [| discriminate H].
    injection H as -> H. cbn [M.run M.run_prog length].
    unfold M.step. rewrite Hn. apply (IH _ _ l2 H).
Qed.

(* Equal versions of one register at two points of a host run mean equal
   values. *)
Lemma hsame_point : forall a b s r,
  hver (hrun_prog a U s) r = hver (hrun_prog b U s) r ->
  hv (hrun_prog a U s) r = hv (hrun_prog b U s) r.
Proof.
  assert (K : forall a b s r, a <= b ->
    hver (hrun_prog a U s) r = hver (hrun_prog b U s) r ->
    hv (hrun_prog a U s) r = hv (hrun_prog b U s) r).
  { intros a b s r H Hv. replace b with (a + (b - a)) in * by lia.
    rewrite M.multi_run_prog_add in *. set (s1 := hrun_prog a U s) in *.
    rewrite M.multi_run_prog_trace in *.
    symmetry. apply run_same_ver_same_val. symmetry. exact Hv. }
  intros a b s r Hv. destruct (le_ge_dec a b) as [H | H]; [apply K; assumption |].
  symmetry. apply K; [exact H | symmetry; exact Hv].
Qed.

(* ================================================================= *)
(* Guest runs.                                                        *)
(* ================================================================= *)

Lemma grun_succ : forall m P s, E.run_prog (S m) P s = E.step P (E.run_prog m P s).
Proof.
  induction m as [| m IH]; intros P s; [reflexivity |].
  change (E.run_prog (S (S m)) P s) with (E.run_prog (S m) P (E.step P s)).
  rewrite IH. reflexivity.
Qed.

Lemma grun_add : forall a b P s, E.run_prog (a + b) P s = E.run_prog b P (E.run_prog a P s).
Proof. induction a as [| a IH]; intros b P s; [reflexivity | apply IH]. Qed.

Lemma gstep_halted : forall P g, E.halted P (E.core_of g) -> E.step P g = g.
Proof. intros P g H. unfold E.step. unfold E.halted in H. rewrite H. reflexivity. Qed.

Lemma gtrace_prefix : forall n P s l1 l2,
  E.trace_of n P s = l1 ++ l2 -> E.run l1 s = E.run_prog (length l1) P s.
Proof.
  induction n as [| n IH]; intros P s l1 l2 H.
  - destruct l1; [reflexivity | discriminate H].
  - destruct l1 as [| a l1]; [reflexivity |]. cbn [E.trace_of] in H.
    destruct (E.next_instr P (E.core_of s)) as [i |] eqn:Hn; [| discriminate H].
    injection H as -> H. cbn [E.run E.run_prog length].
    unfold E.step. rewrite Hn. apply (IH _ _ _ l2 H).
Qed.

Lemma gtrace_succ : forall m P s,
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

Lemma grun_same_ver : forall tr s c,
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

Lemma gsame_point : forall P a b s c,
  E.ver (E.core_of (E.run_prog a P s)) c = E.ver (E.core_of (E.run_prog b P s)) c ->
  E.val (E.core_of (E.run_prog a P s)) c = E.val (E.core_of (E.run_prog b P s)) c.
Proof.
  assert (K : forall P a b s c, a <= b ->
    E.ver (E.core_of (E.run_prog a P s)) c = E.ver (E.core_of (E.run_prog b P s)) c ->
    E.val (E.core_of (E.run_prog a P s)) c = E.val (E.core_of (E.run_prog b P s)) c).
  { intros P a b s c H Hv. replace b with (a + (b - a)) in * by lia.
    rewrite grun_add in *. set (s1 := E.run_prog a P s) in *.
    rewrite E.run_prog_trace in *.
    symmetry. apply grun_same_ver. symmetry. exact Hv. }
  intros P a b s c Hv. destruct (le_ge_dec a b) as [H | H]; [apply K; assumption |].
  symmetry. apply K; [exact H | symmetry; exact Hv].
Qed.

Lemma gnext_fetch : forall P k i,
  E.err k = false -> E.next_instr P k = Some i -> E.fetch P (E.pc k) = Some i.
Proof.
  intros P k i He H. unfold E.next_instr in H. rewrite He in H.
  destruct (E.fetch P (E.pc k)) as [[] |]; congruence.
Qed.

(* ================================================================= *)
(* Matching points.                                                   *)
(* ================================================================= *)

Definition grun (P : list E.instr) (x y m : nat) : E.state := E.run_prog m P (E.start x y).
Definition hrun (P : list E.instr) (x y n : nat) : hstate := hrun_prog n U (hload P x y).

Lemma hrun_add : forall P x y a b, hrun P x y (a + b) = hrun_prog b U (hrun P x y a).
Proof. intros. unfold hrun. apply M.multi_run_prog_add. Qed.

Lemma grun_halted_succ : forall P x y m,
  E.halted P (E.core_of (grun P x y m)) -> grun P x y (S m) = grun P x y m.
Proof. intros. unfold grun. rewrite grun_succ. apply gstep_halted. assumption. Qed.

(* A record's host fact had its version and value together at some point
   of the host run, and its guest fact at some point of the guest run. *)
Definition hwit (P : list E.instr) (x y : nat) (r : srec) : Prop :=
  exists t, hver (hrun P x y t) (SLOT (r_c r) (r_k r)) = r_hv r /\
            hv (hrun P x y t) (SLOT (r_c r) (r_k r)) = pair (pcode (r_p r)) (r_v r).

Definition gwit (P : list E.instr) (x y : nat) (r : srec) : Prop :=
  exists t, E.ver (E.core_of (grun P x y t)) (r_c r) = r_gv r /\
            E.val (E.core_of (grun P x y t)) (r_c r) = r_v r.

Lemma sim_points : forall P x y m, exists N sg rho,
  ((rel_with P sg rho (grun P x y m) (hrun P x y N) /\ m <= N) \/
   rel_halt P (grun P x y m) (hrun P x y N)) /\
  (forall n, n <= N -> exists m', m' <= m /\
     E.mu (grun P x y m') <= M.mu (hrun P x y n) <= E.mu (grun P x y (S m'))) /\
  (forall r, In r sg -> hwit P x y r /\ gwit P x y r).
Proof.
  intros P x y m. induction m as [| m IH].
  - exists 0, [], None. split; [left; split; [apply hload_rel | lia] |].
    split; [| intros r []].
    intros n Hn. exists 0. split; [lia |]. replace n with 0 by lia.
    unfold hrun. simpl. lia.
  - destruct IH as [N [sg [rho [[[R Hle] | RH] [Hbr Hw]]]]].
    + assert (Hg : grun P x y (S m) = E.step P (grun P x y m))
        by (unfold grun; apply grun_succ).
      destruct (U_step_with P sg rho _ _ R)
        as [[Hh [h' [[d Hd] RH']]] | [Hnh [d [h' [Hd [[sg' [rho' [R' Hnew]]] | [Herr RH']]]]]]].
      * (* the guest has stopped *)
        assert (Hh' : hrun P x y (N + d) = h') by (rewrite hrun_add; exact Hd).
        exists (N + d), [], None. split; [right; rewrite grun_halted_succ, Hh'; assumption |].
        split; [| intros r []].
        intros n Hn. destruct (le_lt_dec n N) as [H | H].
        { destruct (Hbr n H) as [m' [Hm' Hb]]. exists m'. split; [lia | exact Hb]. }
        exists m. split; [lia |].
        rewrite (grun_halted_succ P x y m Hh).
        pose proof (hmu_le N n (hload P x y) (Nat.lt_le_incl _ _ H)) as M1.
        pose proof (hmu_le n (N + d) (hload P x y) Hn) as M2.
        fold (hrun P x y N) (hrun P x y n) (hrun P x y (N + d)) in M1, M2.
        rewrite Hh' in M2.
        destruct RH' as [_ [_ [_ [_ [_ [HM _]]]]]].
        pose proof (rw_mu _ _ _ _ _ R). lia.
      * (* a related step *)
        assert (Hh' : hrun P x y (N + S d) = h') by (rewrite hrun_add; exact Hd).
        exists (N + S d), sg', rho'. split; [left; split; [rewrite Hg, Hh'; exact R' | lia] |].
        split.
        { intros n Hn. destruct (le_lt_dec n N) as [H | H].
          { destruct (Hbr n H) as [m' [Hm' Hb]]. exists m'. split; [lia | exact Hb]. }
          exists m. split; [lia |].
          pose proof (hmu_le N n (hload P x y) (Nat.lt_le_incl _ _ H)) as M1.
          pose proof (hmu_le n (N + S d) (hload P x y) Hn) as M2.
          fold (hrun P x y N) (hrun P x y n) (hrun P x y (N + S d)) in M1, M2.
          rewrite Hh' in M2. rewrite Hg.
          pose proof (rw_mu _ _ _ _ _ R). pose proof (rw_mu _ _ _ _ _ R'). lia. }
        intros r Hin. destruct (Hnew r Hin) as [Hold | Hcur]; [exact (Hw r Hold) |].
        destruct (rw_recs _ _ _ _ _ R' r Hin) as [_ [Hsl [_ [_ [Hiff [Hc _]]]]]].
        split.
        { exists (N + S d). rewrite Hh'. split; [symmetry; apply Hiff, Hcur | exact Hsl]. }
        { exists (S m). rewrite Hg. split; [symmetry; exact Hcur | symmetry; apply Hc, Hcur]. }
      * (* a trap *)
        assert (Hh' : hrun P x y (N + S d) = h') by (rewrite hrun_add; exact Hd).
        exists (N + S d), [], None. split; [right; rewrite Hg, Hh'; exact RH' |].
        split; [| intros r []].
        intros n Hn. destruct (le_lt_dec n N) as [H | H].
        { destruct (Hbr n H) as [m' [Hm' Hb]]. exists m'. split; [lia | exact Hb]. }
        exists m. split; [lia |].
        pose proof (hmu_le N n (hload P x y) (Nat.lt_le_incl _ _ H)) as M1.
        pose proof (hmu_le n (N + S d) (hload P x y) Hn) as M2.
        fold (hrun P x y N) (hrun P x y n) (hrun P x y (N + S d)) in M1, M2.
        rewrite Hh' in M2. rewrite Hg.
        destruct RH' as [_ [_ [_ [_ [_ [HM _]]]]]].
        pose proof (rw_mu _ _ _ _ _ R). lia.
    + (* both stopped already *)
      exists N, [], None. split; [right; rewrite grun_halted_succ; [exact RH | apply RH] |].
      split; [| intros r []].
      intros n Hn. destruct (Hbr n Hn) as [m' [Hm' Hb]]. exists m'. split; [lia | exact Hb].
Qed.

Theorem universal_simulation : forall P x y m, exists n,
  (rel P (grun P x y m) (hrun P x y n) /\ m <= n) \/ rel_halt P (grun P x y m) (hrun P x y n).
Proof.
  intros P x y m. destruct (sim_points P x y m) as [N [sg [rho [[[R Hle] | RH] _]]]].
  - exists N. left. split; [exists sg, rho; exact R | exact Hle].
  - exists N. right. exact RH.
Qed.

(* A stopped guest has a related stopped host. *)
Lemma halt_point : forall P x y m, E.halted P (E.core_of (grun P x y m)) ->
  exists N, rel_halt P (grun P x y m) (hrun P x y N).
Proof.
  intros P x y m Hh. destruct (sim_points P x y m) as [N [sg [rho [[[R _] | RH] _]]]].
  - destruct (U_step_with P sg rho _ _ R) as [[_ [h' [[d Hd] RH']]] | [Hn _]];
      [| contradiction].
    exists (N + d). rewrite hrun_add, Hd. exact RH'.
  - exists N. exact RH.
Qed.

Theorem universal_halting : forall P x y,
  (exists m, E.halted P (E.core_of (grun P x y m))) <->
  (exists n, M.halted U (M.core_of (hrun P x y n))).
Proof.
  intros P x y. split.
  - intros [m Hh]. destruct (halt_point P x y m Hh) as [N RH]. exists N. apply RH.
  - intros [n Hh]. destruct (sim_points P x y n) as [N [sg [rho [[[R Hle] | RH] _]]]].
    + exfalso. apply (rel_host_running P sg rho _ _ R).
      unfold hrun in *. rewrite (hhalted_stay n N (hload P x y) Hle Hh). exact Hh.
    + exists n. apply RH.
Qed.

Theorem universal_output : forall P x y m n,
  E.halted P (E.core_of (grun P x y m)) -> M.halted U (M.core_of (hrun P x y n)) ->
  hv (hrun P x y n) RA = E.ca (E.core_of (grun P x y m)) /\
  hv (hrun P x y n) RB = E.cb (E.core_of (grun P x y m)) /\
  herr (hrun P x y n) = E.err (E.core_of (grun P x y m)) /\
  M.mu (hrun P x y n) = E.mu (grun P x y m) /\
  M.cert (hrun P x y n) = E.cert (grun P x y m).
Proof.
  intros P x y m n Hg Hh. destruct (halt_point P x y m Hg) as [N RH].
  assert (E : hrun P x y n = hrun P x y N).
  { unfold hrun in *. apply hhalted_unique; [exact Hh | apply RH]. }
  rewrite E. destruct RH as [_ [_ [Ha [Hb [He [Hm [Hc _]]]]]]]. auto.
Qed.

Theorem universal_flag_iff : forall P x y,
  (exists m, E.cert (grun P x y m) = true) <-> (exists n, M.cert (hrun P x y n) = true).
Proof.
  intros P x y. split.
  - intros [m Hm]. destruct (sim_points P x y m) as [N [sg [rho [[[R _] | RH] _]]]].
    + exists N. rewrite (rw_cert _ _ _ _ _ R). exact Hm.
    + exists N. destruct RH as [_ [_ [_ [_ [_ [_ [Hc _]]]]]]]. rewrite Hc. exact Hm.
  - intros [n Hn]. destruct (sim_points P x y n) as [N [sg [rho [[[R Hle] | RH] _]]]].
    + exists n. rewrite <- (rw_cert _ _ _ _ _ R). unfold hrun in *.
      apply (hcert_le n N); assumption.
    + exists n. destruct RH as [_ [Hh [_ [_ [_ [_ [Hc _]]]]]]]. rewrite <- Hc.
      unfold hrun in *. destruct (le_ge_dec n N) as [H | H].
      * apply (hcert_le n N); assumption.
      * rewrite <- (hhalted_stay N n (hload P x y) H Hh). exact Hn.
Qed.

Theorem universal_ledger_exact : forall P x y,
  (forall m, exists n,
     ((rel P (grun P x y m) (hrun P x y n) /\ m <= n) \/
      rel_halt P (grun P x y m) (hrun P x y n)) /\
     M.mu (hrun P x y n) = E.mu (grun P x y m)) /\
  (forall n, exists m,
     E.mu (grun P x y m) <= M.mu (hrun P x y n) <= E.mu (grun P x y (S m))).
Proof.
  intros P x y. split.
  - intro m. destruct (sim_points P x y m) as [N [sg [rho [[[R Hle] | RH] _]]]].
    + exists N. split; [left; split; [exists sg, rho; exact R | exact Hle] |].
      exact (rw_mu _ _ _ _ _ R).
    + exists N. split; [right; exact RH |]. apply RH.
  - intro n. destruct (sim_points P x y n) as [N [sg [rho [[[R Hle] | RH] [Hbr _]]]]].
    + destruct (Hbr n Hle) as [m' [_ Hb]]. exists m'. exact Hb.
    + destruct (le_ge_dec n N) as [H | H].
      * destruct (Hbr n H) as [m' [_ Hb]]. exists m'. exact Hb.
      * exists n. destruct RH as [Hg [Hh [_ [_ [_ [Hm _]]]]]].
        unfold hrun in *. rewrite (hhalted_stay N n (hload P x y) H Hh), Hm.
        rewrite (grun_halted_succ P x y n Hg). lia.
Qed.

(* ================================================================= *)
(* Earned certification, host and guest.                              *)
(* ================================================================= *)

Lemma cert_switch : forall (f : nat -> bool) m,
  f 0 = false -> f m = true -> exists m0, f m0 = false /\ f (S m0) = true.
Proof.
  intros f m H0. induction m as [| m IH]; intro Hm; [congruence |].
  destruct (f m) eqn:E; [apply IH; reflexivity | exists m; auto].
Qed.

Theorem universal_earned : forall P x y n,
  M.cert (hrun P x y n) = true ->
  exists c k p v pre1 mid1 mid2 post,
    k < 16 /\
    htrace n U (hload P x y) =
      pre1 ++ M.CHECK PSlot (SLOT c k) :: mid1 ++ M.COMMIT PSlot (SLOT c k) :: mid2 ++
      M.CERTIFY :: post /\
    M.check_ok heval (M.core_of (hrun_l pre1 (hload P x y))) PSlot (SLOT c k) = true /\
    M.commit_ok hprop_eqb
      (M.core_of (hrun_l (pre1 ++ M.CHECK PSlot (SLOT c k) :: mid1) (hload P x y)))
      PSlot (SLOT c k) = true /\
    M.certify_ok (M.core_of (hrun_l (pre1 ++ M.CHECK PSlot (SLOT c k) :: mid1 ++
                                     M.COMMIT PSlot (SLOT c k) :: mid2) (hload P x y))) = true /\
    hver (hrun_l pre1 (hload P x y)) (SLOT c k) =
      hver (hrun_l (pre1 ++ M.CHECK PSlot (SLOT c k) :: mid1) (hload P x y)) (SLOT c k) /\
    M.untouched hprop_eqb heval (hrun_l (pre1 ++ [M.CHECK PSlot (SLOT c k)]) (hload P x y))
      mid1 (SLOT c k) /\
    hv (hrun_l pre1 (hload P x y)) (SLOT c k) = pair (pcode p) v /\ E.holds p v /\
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
  set (h0 := hload P x y). set (g0 := E.start x y).
  (* The guest certifies, and its flag rises at some step m0. *)
  destruct (proj2 (universal_flag_iff P x y) (ex_intro _ n Hc)) as [m Hm].
  destruct (cert_switch (fun m => E.cert (grun P x y m)) m eq_refl Hm) as [m0 [Hc0 Hc1]].
  simpl in Hc0, Hc1.
  destruct (sim_points P x y m0) as [N0 [sg [rho [[[R _] | RH] [_ Hwit]]]]].
  2:{ exfalso. rewrite (grun_halted_succ P x y m0 (proj1 RH)) in Hc1. congruence. }
  set (g := grun P x y m0) in *.
  pose proof (rw_err _ _ _ _ _ R) as He.
  assert (Hgs : grun P x y (S m0) = E.step P g) by (unfold g, grun; apply grun_succ).
  rewrite Hgs in Hc1. unfold E.step in Hc1.
  destruct (E.next_instr P (E.core_of g)) as [i |] eqn:Hni; [| congruence].
  destruct (E.only_certify_certifies g i Hc0 Hc1) as [-> Hgok].
  pose proof (gnext_fetch P _ _ He Hni) as Hgf.
  (* The guest channel names a record r0 of sg. *)
  assert (Hr0 : exists r0, rho = Some r0).
  { unfold E.certify_ok in Hgok. rewrite (rw_gchan _ _ _ _ _ R) in Hgok.
    destruct rho as [r0 |]; [exists r0; reflexivity | rewrite He in Hgok; discriminate]. }
  destruct Hr0 as [r0 Hrho].
  pose proof (rw_rho _ _ _ _ _ R r0 Hrho) as Hin0.
  destruct (Hwit r0 Hin0) as [[tau [Hwv Hwval]] [sig [Hgv Hgval]]].
  destruct (rw_recs _ _ _ _ _ R r0 Hin0) as [Hk0 _].
  set (c := r_c r0) in *. set (k := r_k r0) in *.
  set (p := r_p r0) in *. set (v := r_v r0) in *.
  (* The host's CERTIFY phase from the matching point N0. *)
  assert (Hhf : E.fetch P (hv (hrun P x y N0) GPC) = Some E.CERTIFY)
    by (rewrite (rw_gpc _ _ _ _ _ R); exact Hgf).
  assert (Hhc : M.chan (M.core_of (hrun P x y N0)) = Some (hfact r0))
    by (rewrite (rw_hchan _ _ _ _ _ R), Hrho; reflexivity).
  destruct (phase_certify_pass P (hrun P x y N0) (hfact r0) (rw_head _ _ _ _ _ R) Hhf Hhc)
    as [h1 [[d Hd] [_ [_ [_ [_ [HM1 [HR1 _]]]]]]]].
  assert (Hh1 : hrun P x y (N0 + d) = h1) by (rewrite hrun_add; exact Hd).
  assert (Hcert0 : M.cert (hrun P x y N0) = false) by (rewrite (rw_cert _ _ _ _ _ R); exact Hc0).
  (* The host's first raising CERTIFY. *)
  assert (Hrn : M.cert (hrun_l (htrace n U h0) h0) = true)
    by (rewrite <- M.multi_run_prog_trace; exact Hc).
  destruct (M.multi_cert_first hprop_eqb heval h0 _ eq_refl Hrn)
    as [pre [post [Htr [Hpre Hok]]]].
  set (t := length pre).
  assert (Ht : hrun_l pre h0 = hrun P x y t) by exact (htrace_prefix n h0 pre _ Htr).
  assert (Ht1 : hrun_l (pre ++ [M.CERTIFY]) h0 = hrun P x y (S t)).
  { rewrite (htrace_prefix n h0 (pre ++ [M.CERTIFY]) post);
      [rewrite app_length; simpl; unfold hrun, t; f_equal; lia |].
    rewrite Htr, <- app_assoc. reflexivity. }
  rewrite M.multi_run_snoc, (M.multi_exec_certify_pass hprop_eqb heval _ Hok) in Ht1.
  rewrite Ht in Hpre, Ht1.
  assert (HcS : M.cert (hrun P x y (S t)) = true) by (rewrite <- Ht1; reflexivity).
  assert (HmS : M.mu (hrun P x y (S t)) = M.mu (hrun P x y t) + 1) by (rewrite <- Ht1; reflexivity).
  assert (Hlo : N0 <= t).
  { destruct (le_lt_dec N0 t) as [H | H]; [exact H | exfalso].
    pose proof (hcert_le (S t) N0 h0 H HcS) as X.
    change (M.cert (hrun P x y N0) = true) in X. congruence. }
  assert (Hhi : S t <= N0 + d).
  { destruct (le_lt_dec (S t) (N0 + d)) as [H | H]; [exact H | exfalso].
    assert (X : M.cert (hrun P x y (N0 + d)) = true) by (rewrite Hh1; exact HR1).
    pose proof (hcert_le (N0 + d) t h0 ltac:(lia) X) as Y.
    change (M.cert (hrun P x y t) = true) in Y. congruence. }
  assert (Hmu : M.mu (hrun P x y t) = M.mu (hrun P x y N0)).
  { pose proof (hmu_le N0 t h0 Hlo) as M1. pose proof (hmu_le (S t) (N0 + d) h0 Hhi) as M2.
    change (M.mu (hrun P x y N0) <= M.mu (hrun P x y t)) in M1.
    change (M.mu (hrun P x y (S t)) <= M.mu (hrun P x y (N0 + d))) in M2.
    rewrite Hh1 in M2. lia. }
  assert (Hch : M.chan (M.core_of (hrun_l pre h0)) = Some (hfact r0)).
  { rewrite Ht. rewrite <- Hhc. replace t with (N0 + (t - N0)) in * by lia.
    rewrite hrun_add in *. apply hchan_const. exact Hmu. }
  (* The host chain, from the host's own record rules. *)
  destruct (M.multi_chan_origin hprop_eqb heval h0 pre (hfact r0) eq_refl Hch)
    as [preC [p' [R' [mid2 [HpreC [Hcm Hf]]]]]].
  destruct p'.
  unfold hfact, M.claim in Hf.
  assert (HR' : R' = SLOT c k) by (apply (f_equal M.f_reg) in Hf; symmetry; exact Hf).
  assert (HvC : hver (hrun_l preC h0) R' = r_hv r0)
    by (apply (f_equal M.f_ver) in Hf; symmetry; exact Hf).
  subst R'.
  destruct (M.multi_earned_commitment_provenance hprop_eqb hprop_eqb_eq heval h0 preC
              PSlot (SLOT c k) (M.multi_start_clean _) Hcm)
    as [pre1 [mid1 [HpreC1 [Hck [_ [_ [Hv1 Hun]]]]]]].
  subst pre preC.
  assert (Hlist : htrace n U h0 =
    pre1 ++ M.CHECK PSlot (SLOT c k) :: mid1 ++ M.COMMIT PSlot (SLOT c k) :: mid2 ++
    M.CERTIFY :: post) by (rewrite Htr; repeat (rewrite <- app_assoc; simpl); reflexivity).
  assert (Hp1 : hrun_l pre1 h0 = hrun P x y (length pre1))
    by exact (htrace_prefix n h0 pre1 _ Hlist).
  (* The slot value at the host CHECK is the record's pair. *)
  assert (Hval : hv (hrun_l pre1 h0) (SLOT c k) = pair (pcode p) v).
  { rewrite Hp1. rewrite <- Hwval. apply hsame_point.
    change (hver (hrun P x y (length pre1)) (SLOT c k) = hver (hrun P x y tau) (SLOT c k)).
    rewrite <- Hp1, Hv1, HvC. symmetry. exact Hwv. }
  assert (Hholds : E.holds p v).
  { unfold M.check_ok in Hck. apply andb_true_iff in Hck as [Hck _].
    apply andb_true_iff in Hck as [_ Hck]. rewrite Hval, heval_pair in Hck.
    apply E.eval_iff, Hck. }
  (* The guest chain, from the guest's own record rules. *)
  assert (Hgch : E.chan (E.core_of (E.run (E.trace_of m0 P g0) g0)) = Some (gfact r0)).
  { rewrite <- E.run_prog_trace. change (E.chan (E.core_of g) = Some (gfact r0)).
    rewrite (rw_gchan _ _ _ _ _ R), Hrho. reflexivity. }
  destruct (E.chan_origin g0 _ _ eq_refl Hgch) as [gpreC [p'' [c'' [gmid2 [HgC [Hgcm Hgf']]]]]].
  unfold E.claim in Hgf'. apply gfact_eq in Hgf' as [Hp'' [Hc'' Hv'']].
  fold p in Hp''. fold c in Hc''. subst p'' c''.
  destruct (E.earned_commitment_provenance g0 gpreC p c (E.start_clean x y) Hgcm)
    as [gpre [gmid1 [HgC1 [Hgck [_ [_ [Hgv1 Hgun]]]]]]].
  subst gpreC.
  assert (Hglist : E.trace_of (S m0) P g0 =
    gpre ++ E.CHECK p c :: gmid1 ++ E.COMMIT p c :: gmid2 ++ [E.CERTIFY]).
  { rewrite gtrace_succ. change (E.run_prog m0 P g0) with g. rewrite Hni, HgC.
    repeat (rewrite <- app_assoc; simpl). reflexivity. }
  assert (Hgp : E.run gpre g0 = grun P x y (length gpre))
    by exact (gtrace_prefix (S m0) P g0 gpre _ Hglist).
  assert (Hgvalue : E.val (E.core_of (E.run gpre g0)) c = v).
  { rewrite Hgp. rewrite <- Hgval. unfold grun. apply gsame_point.
    change (E.ver (E.core_of (grun P x y (length gpre))) c =
            E.ver (E.core_of (grun P x y sig)) c).
    rewrite <- Hgp, Hgv1, Hgv.
    symmetry. exact Hv''. }
  exists c, k, p, v, pre1, mid1, mid2, post.
  split; [exact Hk0 |]. split; [exact Hlist |]. split; [exact Hck |].
  split; [exact Hcm |].
  split.
  { replace (pre1 ++ M.CHECK PSlot (SLOT c k) :: mid1 ++ M.COMMIT PSlot (SLOT c k) :: mid2)
      with (((pre1 ++ M.CHECK PSlot (SLOT c k) :: mid1) ++ M.COMMIT PSlot (SLOT c k) :: mid2))
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
Definition host_machine : TC.machine :=
  TC.mk_machine hstate hinstr hexec (@M.cost hprop) (@M.cert hprop).

Lemma run_host : forall tr s, TC.run host_machine tr s = hrun_l tr s.
Proof. induction tr; intros; simpl; auto. Qed.

(* U's run from hload is a run of host_machine. *)
Lemma U_run_on_host_machine : forall P x y n,
  TC.run host_machine (htrace n U (hload P x y)) (hload P x y) = hrun P x y n.
Proof. intros. rewrite run_host. unfold hrun. symmetry. apply M.multi_run_prog_trace. Qed.

Definition hreg_of (r : TC.reg) : nat := match r with TC.RA => 0 | TC.RB => 1 end.

Definition host_compile (i : TC.cm_instr) : hinstr :=
  match i with
  | TC.CINC r => M.INC (hreg_of r)
  | TC.CDEC r j => M.DEC (hreg_of r) j
  end.

Definition host_window (s : hstate) : TC.cm_conf := (hpc s, (hv s 0, hv s 1)).

Definition host_load (a b : nat) : hstate :=
  M.start (fun r => if Nat.eqb r 0 then a else if Nat.eqb r 1 then b else 0).

Lemma host_sim : forall (s : hstate) i, herr s = false ->
  host_window (hexec s (host_compile i)) = TC.cm_exec i (host_window s) /\
  herr (hexec s (host_compile i)) = false.
Proof.
  intros [[vs vr pc f ch e] m c] i He. simpl in He. subst e.
  unfold host_window. destruct i as [[|] | [|] j]; simpl;
    unfold M.cexec, M.write, M.goto, M.upd; simpl.
  - split; reflexivity.
  - split; reflexivity.
  - destruct (vs 0) eqn:E; simpl; rewrite ?E; split; reflexivity.
  - destruct (vs 1) eqn:E; simpl; rewrite ?E; split; reflexivity.
Qed.

Definition host_base : TC.universal_base host_machine :=
  TC.mk_ub host_machine host_window (fun s => herr s = false) host_compile host_load
    (fun a b => eq_refl) (fun a b => eq_refl) host_sim.

Definition host_kind (i : hinstr) : TC.kind (hprop * nat) :=
  match i with
  | M.CHECK p r => TC.KCheck (p, r)
  | M.COMMIT p r => TC.KCommit (p, r)
  | M.CERTIFY => TC.KCertify
  | _ => TC.KBase
  end.

Definition host_interface : TC.thiele_interface host_machine :=
  TC.mk_ti host_machine host_base (hprop * nat) host_kind
    (fun pr s => hholds (fst pr) (hv s (snd pr)))
    (fun s pr => M.check_ok heval (M.core_of s) (fst pr) (snd pr))
    (fun pr s t => hver s (snd pr) = hver t (snd pr) /\ hv s (snd pr) = hv t (snd pr))
    M.clean_start (@M.mu hprop).

Lemma host_untouched_prefix : forall s mid r, M.untouched hprop_eqb heval s mid r ->
  forall t1 t2, mid = t1 ++ t2 ->
  hver (hrun_l t1 s) r = hver s r /\ hv (hrun_l t1 s) r = hv s r.
Proof.
  intros s mid r Hu t1. induction t1 as [| i t1 IH] using rev_ind; intros t2 Hmid;
    [simpl; auto |].
  destruct (IH (i :: t2)) as [Hv Hw]; [rewrite Hmid, <- app_assoc; reflexivity |].
  destruct (Hu t1 i t2) as [Hv' Hw']; [rewrite Hmid, <- app_assoc; reflexivity |].
  rewrite M.multi_run_snoc. simpl. rewrite Hv', Hw'. auto.
Qed.

Lemma host_chain_holds : forall s0 tr,
  M.clean_start s0 -> M.cert (hrun_l tr s0) = true ->
  TC.earned_chain host_interface s0 tr.
Proof.
  intros s0 tr H0 H1. pose proof H0 as [_ [Hch Hc0]].
  destruct (M.multi_cert_first hprop_eqb heval s0 tr Hc0 H1) as [pre [post [Htr [Hpre Hok]]]].
  pose proof Hok as Hset. unfold M.certify_ok in Hset.
  apply andb_true_iff in Hset as [_ Hset].
  destruct (M.chan (M.core_of (hrun_l pre s0))) as [f |] eqn:Hf; [| discriminate].
  destruct (M.multi_chan_origin hprop_eqb heval s0 pre f Hch Hf)
    as [preC [p [c [mid2 [HpreC [Hcm _]]]]]].
  destruct (M.multi_earned_commitment_provenance hprop_eqb hprop_eqb_eq heval
              s0 preC p c H0 Hcm)
    as [pre1 [mid1 [Hpre1 [Hck [_ [_ [_ Hun]]]]]]].
  assert (Hlist : pre1 ++ M.CHECK p c :: mid1 ++ M.COMMIT p c :: mid2 = pre)
    by (rewrite HpreC, Hpre1; TC.list_eq).
  exists pre1, (p, c), (M.CHECK p c), mid1, (M.COMMIT p c), mid2, M.CERTIFY, post.
  split; [rewrite Htr, <- Hlist; TC.list_eq |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [rewrite run_host; exact Hck |].
  split.
  { intros t1 t2 Hm. rewrite !run_host. simpl.
    replace (pre1 ++ M.CHECK p c :: t1) with ((pre1 ++ [M.CHECK p c]) ++ t1)
      by (rewrite <- app_assoc; reflexivity).
    rewrite M.multi_run_app.
    destruct (host_untouched_prefix _ _ _ Hun t1 t2 Hm) as [Hv Hw].
    rewrite Hv, Hw, M.multi_run_snoc. simpl.
    rewrite M.multi_ver_check, M.multi_val_check. split; reflexivity. }
  assert (Hl2 : pre1 ++ M.CHECK p c :: mid1 ++ M.COMMIT p c :: mid2 ++ [M.CERTIFY]
                = pre ++ [M.CERTIFY]) by (rewrite <- Hlist; TC.list_eq).
  assert (Hup : M.cert (hrun_l (pre ++ [M.CERTIFY]) s0) = true)
    by (rewrite M.multi_run_snoc; simpl; rewrite Hpre; exact Hok).
  rewrite <- Hl2 in Hup. rewrite <- Hlist in Hpre.
  split; rewrite run_host; assumption.
Qed.

Lemma host_chain_iff : forall a b,
  M.cert (hrun_l [M.CHECK PSlot 0; M.COMMIT PSlot 0; M.CERTIFY] (host_load a b)) = true <->
  hholds PSlot a.
Proof.
  intros a b. rewrite <- heval_iff.
  change (hrun_l [M.CHECK PSlot 0; M.COMMIT PSlot 0; M.CERTIFY] (host_load a b))
    with (hexec (hexec (hexec (host_load a b) (M.CHECK PSlot 0)) (M.COMMIT PSlot 0))
            M.CERTIFY).
  destruct (heval PSlot a) eqn:Ev.
  - assert (Hck : M.check_ok heval (M.core_of (host_load a b)) PSlot 0 = true)
      by (unfold M.check_ok; simpl; rewrite Ev; reflexivity).
    rewrite (M.multi_exec_check_pass hprop_eqb heval (host_load a b) PSlot 0 Hck).
    set (k1 := M.record_fact (M.core_of (host_load a b))
                 (M.claim (M.core_of (host_load a b)) PSlot 0)).
    assert (Hcm : M.commit_ok hprop_eqb k1 PSlot 0 = true).
    { apply (M.multi_commit_ok_iff hprop_eqb hprop_eqb_eq). split; [reflexivity |].
      left. reflexivity. }
    set (s1 := M.mkst k1 (M.mu (host_load a b) + 1) (M.cert (host_load a b))).
    rewrite (M.multi_exec_commit_pass hprop_eqb hprop_eqb_eq heval s1 PSlot 0 Hcm).
    split; reflexivity.
  - assert (Hck : M.check_ok heval (M.core_of (host_load a b)) PSlot 0 = false)
      by (unfold M.check_ok; simpl; rewrite Ev; reflexivity).
    rewrite (M.multi_exec_check_fail hprop_eqb heval (host_load a b) PSlot 0 eq_refl Hck).
    split; intro H; discriminate H.
Qed.

Lemma hholds_one : hholds PSlot 1.
Proof. vm_compute. reflexivity. Qed.

Lemma hholds_zero : ~ hholds PSlot 0.
Proof. vm_compute. intros []. Qed.

Theorem host_thiele_complete_with : TC.thiele_complete_with host_interface.
Proof.
  split; [| split; [| split]].
  - split; [intros [[|] | [|] j]; reflexivity |].
    split; [intros a b; apply M.multi_start_clean |]. split.
    + intros s m Hk. destruct m; simpl in Hk; try discriminate; simpl;
        apply orb_false_r.
    + intros s m H. apply M.multi_cert_permanent, H.
  - split; [intros s [_ [_ H]]; exact H |]. split.
    + intros s0 tr H0 H1. apply host_chain_holds; [exact H0 |].
      rewrite <- run_host. exact H1.
    + split.
      * intros s [p r] H. simpl in *. unfold M.check_ok in H.
        apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
        apply heval_iff, H.
      * intros [p r] s t [_ Hsame] H. simpl in *. rewrite <- Hsame. exact H.
  - split; [intros []; reflexivity | intros s m; reflexivity].
  - exists (PSlot, 0), (M.CHECK PSlot 0), (M.COMMIT PSlot 0), M.CERTIFY.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    split; [| split; [exists 1, 0; exact hholds_one | exists 0, 0; exact hholds_zero]].
    intros a b. unfold TC.load. simpl TC.ti_meaning. rewrite run_host.
    apply host_chain_iff.
Qed.

Theorem universal_thiele_complete : TC.thiele_complete host_machine.
Proof. exists host_interface. exact host_thiele_complete_with. Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions sim_points.
Print Assumptions universal_simulation.
Print Assumptions halt_point.
Print Assumptions universal_halting.
Print Assumptions universal_output.
Print Assumptions universal_flag_iff.
Print Assumptions universal_ledger_exact.
Print Assumptions universal_earned.
Print Assumptions U_run_on_host_machine.
Print Assumptions host_thiele_complete_with.
Print Assumptions universal_thiele_complete.
