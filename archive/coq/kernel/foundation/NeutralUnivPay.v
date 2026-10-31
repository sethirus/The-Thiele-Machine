(** NeutralUnivPay.v: is PAY needed?

      pay_line          (neutral, any host) if the guest has paid while its
                        record is down, the host's run has executed, before
                        the matching time, a record move that either trapped
                        or sits on a line that (N3) marks as non-raising,
                        i.e. a record move that raises from NO untrapped state
                        at that line: a PAY in function;
      cnh_only_pay      on the canonical neutral host the only record move that
                        never raises is PAY (MARK r raises when r >= 1, TICK
                        always): there PAY is needed as a move;
      commit_pay_loop   on U's host (EarnedMulti: CHECK, COMMIT, CERTIFY and no
                        PAY), the four-line loop
                            l: DEC t (l+2);  l+2: COMMIT p Z;  l+3: INC W;  l+4: DEC W l
                        with one claim p about an untouched register Z held in
                        the table pays exactly the value of register t, never
                        raises the record, never traps, and leaves every
                        register but t (and the work register W) alone: the
                        "32 payments" ceiling of the small machine is not a
                        ceiling for a host without PAY.                      *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Kernel.NeutralUnivCanon.
Require Minimal.EarnedMulti.
Module EM := Minimal.EarnedMulti.

(* ================================================================= *)
(* Neutral: a PAY in function.                                        *)
(* ================================================================= *)

Theorem pay_line : forall (C : gclass) (H : host) (R : reg_host H) (P : hP H) (raise : nat -> bool)
  (h0 : hS H) (i : gi C) n m s,
  line_raise H R P raise ->
  (forall s m, hflag H s = true -> hflag H (hstep H s m) = true) ->
  hflag H (hr P h0 n) = glat i m -> glat i m = false ->
  hl P h0 n = gledger i m + s -> gledger i m >= 1 ->
  exists k mv, k < n /\ hnext H P (hr P h0 k) = Some mv /\ b_kind R mv = RRec /\
    (b_err R (hr P h0 (S k)) = true \/
     (raise (b_pc R (hr P h0 k)) = false /\
      forall s' m', b_err R s' = false -> b_pc R s' = b_pc R (hr P h0 k) ->
        hnext H P s' = Some m' -> b_kind R m' = RRec ->
        b_err R (hstep H s' m') = true \/ hflag H (hstep H s' m') = hflag H s')).
Proof.
  intros C H R P ra h0 i n m s HL Hperm Hf Hg Hl Hp.
  destruct (pay_needed C H P h0 i R n m s Hperm Hf Hg Hl Hp) as (k & mv & Hk & Hn & Hkind & Hdown).
  exists k, mv. split; [exact Hk |]. split; [exact Hn |]. split; [exact Hkind |].
  destruct (b_err R (hr P h0 k)) eqn:Ek.
  - left. rewrite hr_succ, Hn. destruct (b_stuck H R _ mv Ek) as [T _]. exact T.
  - rewrite hr_succ, Hn in Hdown |- *.
    destruct (HL _ mv Ek Hn Hkind) as [T | A]; [left; exact T |].
    right. rewrite Hdown in A. symmetry in A. apply orb_false_iff in A as [_ Ar].
    split; [exact Ar |]. intros s' m' E' Hp' Hn' Hk'.
    destruct (HL s' m' E' Hn' Hk') as [T | A']; [left; exact T | right].
    rewrite A', Hp', Ar. apply orb_false_r.
Qed.

(* ================================================================= *)
(* On CNH only PAY never raises.                                      *)
(* ================================================================= *)

Theorem cnh_only_pay : forall m, ckind m = RRec ->
  (forall s, cflag s = false -> cflag (cstep s m) = false) -> m = CPay.
Proof.
  intros [r | r j | | r | |] K Hn; simpl in K; try discriminate; [| | reflexivity].
  - specialize (Hn (mkcs 1 (fun _ => 1) false 0)). discriminate (Hn eq_refl).
  - specialize (Hn (mkcs 1 (fun _ => 0) false 0)). discriminate (Hn eq_refl).
Qed.

(* ================================================================= *)
(* U's host pays without PAY.                                         *)
(* ================================================================= *)

Section Commit.
Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Hypothesis prop_eqb_eq : forall p q, prop_eqb p q = true <-> p = q.
Variable eval : prop -> nat -> bool.

Local Notation run_prog := (EM.run_prog prop_eqb eval).

Variables (P : list (@EM.instr prop)) (l t W Z : nat) (p : prop).
Hypothesis Ht : EM.fetch P l = Some (EM.DEC t (l + 2)).
Hypothesis Hc : EM.fetch P (l + 2) = Some (EM.COMMIT p Z).
Hypothesis Hi : EM.fetch P (l + 3) = Some (EM.INC W).
Hypothesis Hd : EM.fetch P (l + 4) = Some (EM.DEC W l).
Hypothesis Dtw : t <> W.
Hypothesis Dtz : t <> Z.
Hypothesis Dwz : W <> Z.

Lemma upd_eq : forall (g : nat -> nat) r v, EM.upd g r v r = v.
Proof. intros. unfold EM.upd. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma upd_neq : forall (g : nat -> nat) r v x, x <> r -> EM.upd g r v x = g x.
Proof. intros. unfold EM.upd. rewrite (proj2 (Nat.eqb_neq x r) H). reflexivity. Qed.

Definition held (s : @EM.state prop) : Prop :=
  In (EM.claim (EM.core_of s) p Z) (EM.facts (EM.core_of s)).

Lemma step_at : forall s i, EM.err (EM.core_of s) = false -> EM.fetch P (EM.pc (EM.core_of s)) = Some i ->
  i <> EM.HALT -> EM.step prop_eqb eval P s = EM.exec prop_eqb eval s i.
Proof.
  intros s i E F Hh. unfold EM.step, EM.next_instr. rewrite E, F. destruct i; try reflexivity. congruence.
Qed.

Theorem commit_pay_loop : forall k s,
  EM.pc (EM.core_of s) = l -> EM.err (EM.core_of s) = false ->
  EM.vals (EM.core_of s) t = k -> EM.vals (EM.core_of s) W = 0 -> held s ->
  let s' := run_prog (4 * k + 1) P s in
  EM.pc (EM.core_of s') = S l /\ EM.err (EM.core_of s') = false /\
  EM.mu s' = EM.mu s + k /\ EM.cert s' = EM.cert s /\
  EM.vals (EM.core_of s') t = 0 /\ EM.vals (EM.core_of s') W = 0 /\
  (forall x, x <> t -> EM.vals (EM.core_of s') x = EM.vals (EM.core_of s) x) /\
  EM.vers (EM.core_of s') Z = EM.vers (EM.core_of s) Z /\ EM.facts (EM.core_of s') = EM.facts (EM.core_of s).
Proof.
  induction k as [| k IH]; intros s Hp He Hv Hw Hh s'.
  - unfold s'. simpl. rewrite (step_at s _ He (eq_ind_r (fun x => EM.fetch P x = _) Ht Hp)) by discriminate.
    destruct s as [[vs vr pc f ch e] mu ce]. simpl in *. subst pc e.
    unfold EM.exec, EM.cexec. simpl. rewrite Hv. simpl.
    repeat split; try reflexivity; try lia; auto. rewrite orb_false_r. reflexivity.
  - destruct s as [[vs vr pc f ch e] mu ce]. simpl in Hp, He, Hv, Hw. subst pc e.
    unfold held in Hh. simpl in Hh.
    (* DEC t (l+2), t > 0 *)
    set (s1 := EM.exec prop_eqb eval (EM.mkst (EM.mkcore vs vr l f ch false) mu ce) (EM.DEC t (l + 2))).
    assert (E1 : s1 = EM.mkst (EM.mkcore (EM.upd vs t k) (EM.upd vr t (S (vr t))) (l + 2) f ch false) mu ce).
    { unfold s1, EM.exec, EM.cexec. simpl. rewrite Hv. simpl. rewrite orb_false_r, Nat.add_0_r. reflexivity. }
    (* COMMIT p Z *)
    assert (Hcl : EM.claim (EM.core_of s1) p Z = EM.claim (EM.mkcore vs vr l f ch false) p Z).
    { rewrite E1. unfold EM.claim. simpl. unfold EM.upd. destruct (Nat.eqb Z t) eqn:Q; [apply Nat.eqb_eq in Q; congruence | reflexivity]. }
    set (s2 := EM.exec prop_eqb eval s1 (EM.COMMIT p Z)).
    assert (E2 : s2 = EM.mkst (EM.mkcore (EM.upd vs t k) (EM.upd vr t (S (vr t))) (S (l + 2)) f
                                (Some (EM.claim (EM.core_of s1) p Z)) false) (S mu) ce).
    assert (Hcl' : EM.claim (EM.mkcore (EM.upd vs t k) (EM.upd vr t (S (vr t))) (l + 2) f ch false) p Z =
                   EM.claim (EM.mkcore vs vr l f ch false) p Z).
    { unfold EM.claim. simpl. unfold EM.upd. rewrite (proj2 (Nat.eqb_neq Z t) (not_eq_sym Dtz)). reflexivity. }
    { unfold s2. rewrite E1. unfold EM.exec, EM.cexec, EM.commit_ok. simpl.
      assert (Hin : existsb (EM.fact_eqb prop_eqb (EM.claim (EM.mkcore (EM.upd vs t k) (EM.upd vr t (S (vr t))) (l + 2) f ch false) p Z)) f = true).
      { apply existsb_exists. exists (EM.claim (EM.mkcore vs vr l f ch false) p Z). split; [exact Hh |].
        rewrite Hcl'. apply (EM.multi_fact_eqb_eq prop_eqb prop_eqb_eq). reflexivity. }
      rewrite Hin. simpl. rewrite orb_false_r. f_equal. lia. }
    (* INC W *)
    set (s3 := EM.exec prop_eqb eval s2 (EM.INC W)).
    (* DEC W l *)
    set (s4 := EM.exec prop_eqb eval s3 (EM.DEC W l)).
    assert (E4 : EM.core_of s4 = EM.mkcore (EM.upd (EM.upd (EM.upd vs t k) W 1) W 0)
                   (EM.upd (EM.upd (EM.upd vr t (S (vr t))) W (S (EM.upd vr t (S (vr t)) W)))
                      W (S (EM.upd (EM.upd vr t (S (vr t))) W (S (EM.upd vr t (S (vr t)) W)) W)))
                   l f (Some (EM.claim (EM.core_of s1) p Z)) false /\
                 EM.mu s4 = S mu /\ EM.cert s4 = ce).
    { unfold s4, s3. rewrite E2. unfold EM.exec, EM.cexec. simpl.
      rewrite upd_eq, (upd_neq vs t k W (not_eq_sym Dtw)), Hw. simpl.
      rewrite !orb_false_r, !Nat.add_0_r. split; [reflexivity | split; reflexivity]. }
    assert (R4 : run_prog 4 P (EM.mkst (EM.mkcore vs vr l f ch false) mu ce) = s4).
    { simpl. rewrite (step_at (EM.mkst (EM.mkcore vs vr l f ch false) mu ce) _ eq_refl Ht) by discriminate. fold s1.
      assert (P1 : EM.pc (EM.core_of s1) = l + 2) by (rewrite E1; reflexivity).
      assert (Er1 : EM.err (EM.core_of s1) = false) by (rewrite E1; reflexivity).
      rewrite (step_at s1 _ Er1 (eq_trans (f_equal (EM.fetch P) P1) Hc)) by discriminate.
      fold s2.
      assert (P2 : EM.pc (EM.core_of s2) = l + 3) by (rewrite E2; simpl; lia).
      assert (Er2 : EM.err (EM.core_of s2) = false) by (rewrite E2; reflexivity).
      rewrite (step_at s2 _ Er2 (eq_trans (f_equal (EM.fetch P) P2) Hi)) by discriminate.
      fold s3.
      assert (E3pc : EM.pc (EM.core_of s3) = l + 4).
      { unfold s3. rewrite E2. unfold EM.exec, EM.cexec. simpl. lia. }
      assert (E3err : EM.err (EM.core_of s3) = false).
      { unfold s3. rewrite E2. reflexivity. }
      rewrite (step_at s3 _ E3err (eq_trans (f_equal (EM.fetch P) E3pc) Hd)) by discriminate.
      reflexivity. }
    destruct E4 as (C4 & M4 & K4).
    assert (Hh4 : held s4).
    { unfold held. rewrite C4. simpl.
      replace (EM.claim (EM.mkcore (EM.upd (EM.upd (EM.upd vs t k) W 1) W 0) _ l f _ false) p Z)
        with (EM.claim (EM.mkcore vs vr l f ch false) p Z); [exact Hh |].
      unfold EM.claim. simpl. unfold EM.upd.
      rewrite (proj2 (Nat.eqb_neq Z W) (not_eq_sym Dwz)), (proj2 (Nat.eqb_neq Z t) (not_eq_sym Dtz)).
      reflexivity. }
    assert (V4 : forall x, EM.vals (EM.core_of s4) x = if Nat.eqb x t then k else vs x).
    { intros x. rewrite C4. simpl. unfold EM.upd.
      destruct (Nat.eqb x W) eqn:Q1; destruct (Nat.eqb x t) eqn:Q2; try reflexivity.
      - apply Nat.eqb_eq in Q1, Q2. congruence.
      - apply Nat.eqb_eq in Q1. subst x. rewrite Hw. reflexivity. }
    destruct (IH s4) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
    + rewrite C4. reflexivity.
    + rewrite C4. reflexivity.
    + rewrite V4, Nat.eqb_refl. reflexivity.
    + rewrite V4. rewrite (proj2 (Nat.eqb_neq W t) (not_eq_sym Dtw)). exact Hw.
    + exact Hh4.
    + unfold s'. replace (4 * S k + 1) with (4 + (4 * k + 1)) by lia.
      rewrite (EM.multi_run_prog_add prop_eqb eval). rewrite R4.
      split; [exact A1 |]. split; [exact A2 |]. split; [rewrite A3, M4; simpl; lia |].
      split; [rewrite A4, K4; reflexivity |]. split; [exact A5 |]. split; [exact A6 |].
      split.
      * intros x Hx. rewrite A7 by exact Hx. rewrite V4. rewrite (proj2 (Nat.eqb_neq x t) Hx). reflexivity.
      * split; [rewrite A8, C4; simpl; unfold EM.upd;
                rewrite (proj2 (Nat.eqb_neq Z W) (not_eq_sym Dwz)), (proj2 (Nat.eqb_neq Z t) (not_eq_sym Dtz));
                reflexivity |].
        rewrite A9, C4. reflexivity.
Qed.

End Commit.

Print Assumptions pay_line.
Print Assumptions cnh_only_pay.
Print Assumptions commit_pay_loop.
