(** NeutralUnivGstep.v: the bare GSTEP cheat of UMachCheatSmall.v against the neutral
    definition.

    The guests of UMachCheatSmall.small_class (every small-machine program from
    every clean start) are neutral-complete guests: the small machine is
    Thiele-complete (ThieleComplete.earned_core_thiele_complete), hence
    neutral-complete (NeutralComplete.thiele_complete_neutral), and its
    record is permanent.  The cheat host (PEEK, BR, GSTEP0, GSTEP1, STOP and
    a five-line loop) meets

      (N1) with the halted state matched and (N2) in order, with surcharge 0
           and any observation at all            [gstep_meets_N1_N2]
      the suggested neutral "earned again" (every rise of its record made
           by its own paid move, at a point where the guest's record
           rises, and never otherwise)           [gstep_meets_naive]

    and fails (N4): it is no register host under any register reading
    [gstep_not_reg] (the proof of UMachRegHost.cheat_not_reg_host, redone against
    NeutralUnivBase.reg_host).                                                      *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Kernel.UMachCheatSmall.
Require Minimal.ThieleComplete.
Require Minimal.NeutralComplete.

Theorem small_guests_nc : NeutralComplete.neutral_complete Minimal.ThieleComplete.earned_machine.
Proof. apply NeutralComplete.thiele_complete_neutral, Minimal.ThieleComplete.earned_core_thiele_complete. Qed.

Lemma small_perm : forall (i : sinst) s m, gread small_class i s = true -> gread small_class i (gstep small_class i s m) = true.
Proof.
  intros i s m H. change (E.cert (E.exec s m) = true). change (E.cert s = true) in H.
  rewrite E.cert_latch, H. reflexivity.
Qed.

Lemma cheat_perm : forall s m, hflag cheat_host s = true -> hflag cheat_host (hstep cheat_host s m) = true.
Proof.
  intros [pc r P g mir er] m H. simpl in *. subst mir. unfold cexec. simpl.
  destruct er; [reflexivity |]. destruct m; simpl; try reflexivity.
  - destruct (E.next_instr P (E.core_of g)) as [i |]; [destruct (Nat.eqb (E.cost i) 0) |]; reflexivity.
  - destruct (E.next_instr P (E.core_of g)) as [i |]; [destruct (Nat.eqb (E.cost i) 1) |]; reflexivity.
Qed.

Section Meets.
Variable Obs : gi small_class -> Type.
Variable obs : forall i, gS small_class i -> Obs i.

Definition gdec (i : sinst) (h : cst) : Obs i := obs i (cg h).

Theorem gstep_meets_N1_N2 : forall i,
  halt_clause small_class cheat_host Obs obs 0 CHEAT (cload i) i (gdec i) /\
  in_order small_class cheat_host Obs obs 0 CHEAT (cload i) i (gdec i) (fun m => 4 * m).
Proof.
  intros i. destruct (cheat_is_universal Obs obs) as (P0 & ld & dc & _).
  split; [split |].
  - (* clause (1): from cheat_is_universal's proof, redone *)
    unfold clause1. split.
    + intros [n Hn].
      destruct (live_or_stop i (S n)) as [Hl | (m0 & _ & Hs & _)]; [| exists m0; exact Hs].
      exfalso. destruct (points i n (fun k Hk => Hl k ltac:(lia))) as (r & Hh & _).
      rewrite <- (hr_stopped_stays cheat_host CHEAT (cload i) n (4 * n)) in Hn by (lia || exact Hn).
      rewrite Hh in Hn. discriminate.
    + intros [m Hm].
      destruct (live_or_stop i (S m)) as [Hl | (m0 & _ & Hs & Hl0)].
      { exfalso. exact (Hl m ltac:(lia) Hm). }
      destruct (points i m0 Hl0) as (r & Hh & _).
      exists (4 * m0 + 2). rewrite (hr_add cheat_host CHEAT), Hh.
      simpl in Hs. rewrite (hr_cons _ _ PEEK) by reflexivity.
      rewrite (ex_peek_stop 1 r _ _ _ Hs).
      rewrite (hr_cons _ _ (BR 3 5 7)) by reflexivity. rewrite ex_br. reflexivity.
  - (* the halted state matches the guest's last state *)
    intros m0 Hl0 Hs. destruct (points i m0 Hl0) as (r & Hh & Hle).
    exists (4 * m0 + 2).
    assert (E : hr (H:=cheat_host) CHEAT (cload i) (4 * m0 + 2) =
                mkc 7 2 (fst (fst i)) (grun (C:=small_class) i m0)
                    (E.cert (grun (C:=small_class) i m0)) false).
    { rewrite (hr_add cheat_host CHEAT), Hh. simpl in Hs.
      rewrite (hr_cons _ _ PEEK) by reflexivity. rewrite (ex_peek_stop 1 r _ _ _ Hs).
      rewrite (hr_cons _ _ (BR 3 5 7)) by reflexivity. rewrite ex_br. reflexivity. }
    assert (L : hl (H:=cheat_host) CHEAT (cload i) (4 * m0 + 2) = gledger (C:=small_class) i m0).
    { rewrite (hl_add cheat_host CHEAT), Hh, Hle. simpl in Hs.
      rewrite (hl_cons _ _ PEEK) by reflexivity. rewrite (ex_peek_stop 1 r _ _ _ Hs).
      rewrite (hl_cons _ _ (BR 3 5 7)) by reflexivity. rewrite ex_br. simpl. lia. }
    split.
    + change (cnext CHEAT (hr (H:=cheat_host) CHEAT (cload i) (4 * m0 + 2)) = None).
      rewrite E. reflexivity.
    + unfold match_at, gdec. rewrite E, L. split; [reflexivity |].
      split; [simpl; symmetry; apply glat_cert | exists 0; split; lia].
  - split; [intros; lia |]. intros m Hl. destruct (points i m Hl) as (r & Hh & Hle).
    unfold match_at, gdec. rewrite Hle, Hh. split; [reflexivity |].
    split; [simpl; symmetry; apply glat_cert |]. exists 0. split; lia.
Qed.

(* The suggested neutral form of "earned again" holds for the cheat. *)
Theorem gstep_meets_naive : forall (i : gi small_class) n,
  hflag cheat_host (hr (H:=cheat_host) CHEAT (cload i) n) = false -> hflag cheat_host (hr (H:=cheat_host) CHEAT (cload i) (S n)) = true ->
  (exists mv, hnext cheat_host CHEAT (hr (H:=cheat_host) CHEAT (cload i) n) = Some mv /\ hcost cheat_host mv >= 1) /\
  ((n < 4 * 0 /\ glat (C:=small_class) i 0 = true) \/
   (exists m, live_before (C:=small_class) i (S m) /\ 4 * m <= n < 4 * S m /\
              glat (C:=small_class) i m = false /\ glat (C:=small_class) i (S m) = true)).
Proof.
  intros i. destruct (gstep_meets_N1_N2 i) as [H1 H2].
  exact (naive_rise_free small_class cheat_host Obs obs 0 CHEAT (cload i) i (gdec i) (fun m => 4 * m)
           cheat_perm H1 H2).
Qed.

End Meets.

(* ================================================================= *)
(* It is no register host, under any reading.                         *)
(* ================================================================= *)

Definition s_at (P : list UMachCheatSmall.E.instr) (err : bool) : cst := mkc 3 0 P (UMachCheatSmall.E.start 0 0) false err.

Lemma cheat_untrapped_live : forall (R : reg_host cheat_host) P, b_err R (s_at P false) = false.
Proof.
  intros R P. destruct (b_err R (s_at P false)) eqn:E; [| reflexivity].
  pose proof (b_next_err cheat_host R [PEEK; PEEK; GSTEP0] (s_at P false) E) as X.
  discriminate X.
Qed.

Theorem gstep_not_reg : reg_host cheat_host -> False.
Proof.
  intros R.
  pose proof (b_cost cheat_host R GSTEP0) as Hc. simpl in Hc.
  set (sp := s_at [UMachCheatSmall.E.CERTIFY] false).
  assert (Ep : b_err R sp = false) by apply cheat_untrapped_live.
  assert (Tp : hstep cheat_host sp GSTEP0 = s_at [UMachCheatSmall.E.CERTIFY] true) by reflexivity.
  assert (Fix : forall m, hstep cheat_host (s_at [UMachCheatSmall.E.CERTIFY] true) m = s_at [UMachCheatSmall.E.CERTIFY] true)
    by (intros m; reflexivity).
  destruct (b_kind R GSTEP0) as [r | r j | |] eqn:K.
  - destruct (b_inc cheat_host R sp GSTEP0 r Ep K) as (E1 & _ & _).
    rewrite Tp in E1.
    destruct (b_inc cheat_host R _ GSTEP0 r E1 K) as (_ & P2 & _).
    rewrite Fix in P2. lia.
  - destruct (b_dec cheat_host R sp GSTEP0 r j Ep K) as (E1 & _).
    rewrite Tp in E1.
    destruct (b_dec cheat_host R _ GSTEP0 r j E1 K) as (_ & D2).
    rewrite Fix in D2. destruct (b_reg R (s_at [UMachCheatSmall.E.CERTIFY] true) r) as [| n] eqn:V.
    + destruct D2 as [P2 _]. lia.
    + destruct D2 as [_ R2]. specialize (R2 r). unfold upd in R2.
      rewrite Nat.eqb_refl, V in R2. lia.
  - set (sf := s_at [UMachCheatSmall.E.INC UMachCheatSmall.E.CA] false).
    assert (Ef : b_err R sf = false) by apply cheat_untrapped_live.
    destruct (b_halt cheat_host R sf GSTEP0 K) as (E2 & P2 & _).
    pose proof (b_next cheat_host R [PEEK; PEEK; GSTEP0; STOP] _ _ E2 P2) as N.
    discriminate N.
  - lia.
Qed.

Print Assumptions small_guests_nc.
Print Assumptions gstep_meets_N1_N2.
Print Assumptions gstep_meets_naive.
Print Assumptions gstep_not_reg.
