(** NeutralUnivBase.v: the generic register-host part of UMachRegHost.v,
    stated in a file of its own so that it can be used without importing the
    presented cheat host (whose large state type would make every host too
    large to be read as a ThieleComplete.machine), together with
    live_or_stop_gen of UMachPresented.v. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   states the register-host record over the hosts of UMachDef.v and imports
   only UMachDef.v and the Coq standard library. NeutralUnivDef.v connects
   it to the small machine's definitions in ThieleComplete.v and
   NeutralComplete.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.

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


Lemma live_or_stop_gen : forall (C : gclass) (i : gi C) n,
  live_before i n \/
  exists m0, m0 < n /\ gnext C i (grun i m0) = None /\ live_before i m0.
Proof.
  intros C i n. induction n as [| n IH].
  - left. intros k Hk. lia.
  - destruct IH as [Hl | (m0 & Hm & Hs & Hl)].
    + destruct (gnext C i (grun i n)) eqn:E.
      * left. intros k Hk. destruct (Nat.eq_dec k n) as [-> | Hne].
        { unfold grun in E. rewrite E. discriminate. }
        apply Hl. lia.
      * right. exists n. auto.
    + right. exists m0. split; [lia | auto].
Qed.


Print Assumptions rh_base_determined.
