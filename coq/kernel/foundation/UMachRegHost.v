(** UMachRegHost.v: the register-host condition, stated for ANY host, not
    only for the book's machines.  A register host is a UMachDef host whose state shows a line,
    a register file and a trap bit, such that

      - every move is a counter move (INC r, DEC r j, HALT) of price 0 or a
        record move of price 1;
      - counter moves act on (line, registers) exactly as the Shepherdson-
        Sturgis register machine does, and keep the trap down;
      - a record move leaves every register alone and either traps or goes
        to the next line (whatever else it does to the rest of the state);
      - a trapped state stays trapped and its line and registers stay put;
      - the program's next move depends only on the line and the trap, and
        a trapped state has none.

    Theorem rh_base_determined: in a register host, two runs of the same
    program from states with the same line and registers have the same
    line and registers at every step before either traps, WHATEVER the rest
    of the two states holds (fact tables, flags, an oracle, a whole guest
    machine stepped by record moves).  So everything a register host's run
    computes into its registers, and so everything a decode that reads
    registers can see, is computed by counter moves.

    U's host and U_P's host (with their real checkers) are register hosts
    [U_host_RH, UP_host_RH].                                               *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.UMachCheatSmall.
Require Import Kernel.UMachMeetsU.
Require Import Kernel.UMachMeetsUP.
Require Import Minimal.UniversalCodes.
Require Import Kernel.UniversalPCodes.
Require Minimal.EarnedMulti.
Require Minimal.EarnedMultiPriced.
Module M := Minimal.EarnedMulti.
Module MP := Minimal.EarnedMultiPriced.

Inductive rkind : Type := RInc (r : nat) | RDec (r j : nat) | RHalt | RRec.

Definition upd (f : nat -> nat) (r v : nat) : nat -> nat := fun x => if Nat.eqb x r then v else f x.

Record reg_host (H : host) : Type := mk_rh {
  b_pc : hS H -> nat;
  b_reg : hS H -> nat -> nat;
  b_err : hS H -> bool;
  b_kind : hI H -> rkind;
  b_cost : forall m, hcost H m = match b_kind m with RRec => 1 | _ => 0 end;
  b_stuck : forall s m, b_err s = true ->
    b_err (hstep H s m) = true /\ b_pc (hstep H s m) = b_pc s /\
    (forall x, b_reg (hstep H s m) x = b_reg s x);
  b_inc : forall s m r, b_err s = false -> b_kind m = RInc r ->
    b_err (hstep H s m) = false /\ b_pc (hstep H s m) = S (b_pc s) /\
    (forall x, b_reg (hstep H s m) x = upd (b_reg s) r (S (b_reg s r)) x);
  b_dec : forall s m r j, b_err s = false -> b_kind m = RDec r j ->
    b_err (hstep H s m) = false /\
    match b_reg s r with
    | 0 => b_pc (hstep H s m) = S (b_pc s) /\ (forall x, b_reg (hstep H s m) x = b_reg s x)
    | S n => b_pc (hstep H s m) = j /\ (forall x, b_reg (hstep H s m) x = upd (b_reg s) r n x)
    end;
  b_halt : forall s m, b_kind m = RHalt ->
    b_err (hstep H s m) = b_err s /\ b_pc (hstep H s m) = b_pc s /\
    (forall x, b_reg (hstep H s m) x = b_reg s x);
  b_rec : forall s m, b_err s = false -> b_kind m = RRec ->
    (forall x, b_reg (hstep H s m) x = b_reg s x) /\
    (b_err (hstep H s m) = true \/ b_pc (hstep H s m) = S (b_pc s));
  b_next : forall P s1 s2, b_err s1 = b_err s2 -> b_pc s1 = b_pc s2 -> hnext H P s1 = hnext H P s2;
  b_next_err : forall P s, b_err s = true -> hnext H P s = None
}.

Arguments b_pc {H} _ _.
Arguments b_reg {H} _ _ _.
Arguments b_err {H} _ _.
Arguments b_kind {H} _ _.

Section Determined.
Variable H : host.
Variable R : reg_host H.

Definition bsame (s1 s2 : hS H) : Prop :=
  b_pc R s1 = b_pc R s2 /\ forall x, b_reg R s1 x = b_reg R s2 x.

Lemma err_back : forall P n s, b_err R (hr P s n) = false -> b_err R s = false.
Proof.
  intros P n s Hf. destruct (b_err R s) eqn:E; [| reflexivity]. exfalso.
  rewrite (hr_stop H P s n (b_next_err H R P s E)) in Hf. congruence.
Qed.

Lemma one : forall s1 s2 m, bsame s1 s2 -> b_err R s1 = false -> b_err R s2 = false ->
  b_err R (hstep H s1 m) = false -> b_err R (hstep H s2 m) = false ->
  bsame (hstep H s1 m) (hstep H s2 m).
Proof.
  intros s1 s2 m [Hp Hr] E1 E2 F1 F2.
  destruct (b_kind R m) as [r | r j | |] eqn:K.
  - destruct (b_inc H R s1 m r E1 K) as (_ & P1 & R1).
    destruct (b_inc H R s2 m r E2 K) as (_ & P2 & R2).
    split; [lia |]. intros x. rewrite R1, R2. unfold upd. rewrite !Hr. reflexivity.
  - destruct (b_dec H R s1 m r j E1 K) as (_ & D1).
    destruct (b_dec H R s2 m r j E2 K) as (_ & D2).
    rewrite <- (Hr r) in D2. destruct (b_reg R s1 r) as [| n].
    + destruct D1 as [P1 R1]; destruct D2 as [P2 R2].
      split; [lia |]. intros x. rewrite R1, R2. apply Hr.
    + destruct D1 as [P1 R1]; destruct D2 as [P2 R2].
      split; [lia |]. intros x. rewrite R1, R2. unfold upd. rewrite Hr. reflexivity.
  - destruct (b_halt H R s1 m K) as (_ & P1 & R1).
    destruct (b_halt H R s2 m K) as (_ & P2 & R2).
    split; [lia |]. intros x. rewrite R1, R2. apply Hr.
  - destruct (b_rec H R s1 m E1 K) as (R1 & [T1 | P1]); [congruence |].
    destruct (b_rec H R s2 m E2 K) as (R2 & [T2 | P2]); [congruence |].
    split; [lia |]. intros x. rewrite R1, R2. apply Hr.
Qed.

Theorem rh_base_determined : forall P n s1 s2,
  bsame s1 s2 ->
  b_err R (hr P s1 n) = false -> b_err R (hr P s2 n) = false ->
  bsame (hr P s1 n) (hr P s2 n).
Proof.
  intros P n. induction n as [| n IH]; intros s1 s2 B F1 F2; [exact B |].
  pose proof (err_back P (S n) s1 F1) as E1. pose proof (err_back P (S n) s2 F2) as E2.
  simpl in F1, F2 |- *.
  assert (N : hnext H P s1 = hnext H P s2) by (apply (b_next H R); [congruence | apply B]).
  rewrite <- N in F2 |- *.
  destruct (hnext H P s1) as [m |]; [| exact B].
  apply IH; [| exact F1 | exact F2].
  apply one; auto.
  - exact (err_back P n _ F1).
  - exact (err_back P n _ F2).
Qed.

End Determined.

(* ================================================================= *)
(* U's host and U_P's host are register hosts.                        *)
(* ================================================================= *)

Definition ukind (i : @M.instr hprop) : rkind :=
  match i with M.INC r => RInc r | M.DEC r j => RDec r j | M.HALT => RHalt | _ => RRec end.

Definition U_host_RH : reg_host U_host.
Proof.
  refine (mk_rh U_host (fun s => M.pc (M.core_of s)) (fun s => M.vals (M.core_of s))
            (fun s => M.err (M.core_of s)) ukind _ _ _ _ _ _ _ _).
  - intros [r | r j | | p r | p r |]; reflexivity.
  - intros s m E. simpl. unfold M.cexec. rewrite E. auto.
  - intros s m r E K. destruct m; simpl in K; try discriminate. injection K as ->.
    simpl. unfold M.cexec. rewrite E. simpl. auto.
  - intros s m r j E K. destruct m; simpl in K; try discriminate. injection K as -> ->.
    simpl. unfold M.cexec. rewrite E. destruct (M.vals (M.core_of s) r); simpl; auto.
  - intros s m K. destruct m; simpl in K; try discriminate.
    simpl. unfold M.cexec. destruct (M.err (M.core_of s)) eqn:E; simpl; repeat split; auto.
  - intros s m E K. simpl. unfold M.cexec. rewrite E.
    destruct m; simpl in K; try discriminate.
    + destruct (M.check_ok heval (M.core_of s) p r); simpl; auto.
    + destruct (M.commit_ok hprop_eqb (M.core_of s) p r); simpl; auto.
    + destruct (M.certify_ok (M.core_of s)); simpl; auto.
  - intros P s1 s2 E Pc. simpl. unfold M.next_instr. rewrite E, Pc. reflexivity.
  - intros P s E. simpl. unfold M.next_instr. rewrite E. reflexivity.
Defined.

Definition pkind (i : @MP.pu_instr pu_hprop) : rkind :=
  match i with MP.INC r => RInc r | MP.DEC r j => RDec r j | MP.HALT => RHalt | _ => RRec end.

Definition UP_host_RH : reg_host UP_host.
Proof.
  refine (mk_rh UP_host (fun s => MP.pc (MP.core_of s)) (fun s => MP.vals (MP.core_of s))
            (fun s => MP.err (MP.core_of s)) pkind _ _ _ _ _ _ _ _).
  - intros [r | r j | | p r | p r | |]; reflexivity.
  - intros s m E. simpl. unfold MP.pu_cexec. rewrite E. auto.
  - intros s m r E K. destruct m; simpl in K; try discriminate. injection K as ->.
    simpl. unfold MP.pu_cexec. rewrite E. simpl. auto.
  - intros s m r j E K. destruct m; simpl in K; try discriminate. injection K as -> ->.
    simpl. unfold MP.pu_cexec. rewrite E. destruct (MP.vals (MP.core_of s) r); simpl; auto.
  - intros s m K. destruct m; simpl in K; try discriminate.
    simpl. unfold MP.pu_cexec. destruct (MP.err (MP.core_of s)) eqn:E; simpl; repeat split; auto.
  - intros s m E K. simpl. unfold MP.pu_cexec. rewrite E.
    destruct m; simpl in K; try discriminate.
    + destruct (MP.pu_check_ok pu_heval (MP.core_of s) p r); simpl; auto.
    + destruct (MP.pu_commit_ok pu_hprop_eqb (MP.core_of s) p r); simpl; auto.
    + destruct (MP.pu_certify_ok (MP.core_of s)); simpl; auto.
    + simpl. auto.
  - intros P s1 s2 E Pc. simpl. unfold MP.pu_next_instr. rewrite E, Pc. reflexivity.
  - intros P s E. simpl. unfold MP.pu_next_instr. rewrite E. reflexivity.
Defined.


(* ================================================================= *)
(* The cheat host of UMachCheatSmall.v is not a register host, under ANY   *)
(* choice of line, registers and trap bit: GSTEP0 has price 0, so it   *)
(* would have to be a counter move, and no counter move can both trap  *)
(* (as GSTEP0 does on a paid guest instruction) and move the line (as  *)
(* it does on a free one).                                             *)
(* ================================================================= *)

Definition s_at (P : list UMachCheatSmall.E.instr) (err : bool) : cst := mkc 3 0 P (UMachCheatSmall.E.start 0 0) false err.

Lemma gstep_host_untrapped_live : forall (R : reg_host cheat_host) P, b_err R (s_at P false) = false.
Proof.
  intros R P. destruct (b_err R (s_at P false)) eqn:E; [| reflexivity].
  pose proof (b_next_err cheat_host R [PEEK; PEEK; GSTEP0] (s_at P false) E) as X.
  discriminate X.
Qed.

Theorem cheat_not_reg_host : reg_host cheat_host -> False.
Proof.
  intros R.
  pose proof (b_cost cheat_host R GSTEP0) as Hc. simpl in Hc.
  (* a paid guest instruction: GSTEP0 traps *)
  set (sp := s_at [UMachCheatSmall.E.CERTIFY] false).
  assert (Ep : b_err R sp = false) by apply gstep_host_untrapped_live.
  assert (Tp : hstep cheat_host sp GSTEP0 = s_at [UMachCheatSmall.E.CERTIFY] true) by reflexivity.
  (* a trapped cheat state is a fixed point of every move *)
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
  - (* RHalt: the line could not move, yet GSTEP0 moves it on a free guest instruction *)
    set (sf := s_at [UMachCheatSmall.E.INC UMachCheatSmall.E.CA] false).
    assert (Ef : b_err R sf = false) by apply gstep_host_untrapped_live.
    destruct (b_halt cheat_host R sf GSTEP0 K) as (E2 & P2 & _).
    pose proof (b_next cheat_host R [PEEK; PEEK; GSTEP0; STOP] _ _ E2 P2) as N.
    discriminate N.
  - lia.
Qed.

Print Assumptions cheat_not_reg_host.

Print Assumptions rh_base_determined.
Print Assumptions U_host_RH.
Print Assumptions UP_host_RH.
