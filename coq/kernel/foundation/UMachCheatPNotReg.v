(** UMachCheatPNotReg.v: the U_P cheat of UMachCheatPresented.v (one fixed host and
    14-line program meeting the in-order rendering of the plain definition
    for every presented machine with surcharge bound 1) is not a register
    host (UMachRegHost.reg_host), under ANY choice of line, registers and trap
    bit.  As for the small cheat (UMachRegHost.cheat_not_reg_host): GMOVE0 has
    price 0, so it would have to be a counter move; a counter move from an
    untrapped state lands untrapped and then must move the line or a
    register, but GMOVE0 traps on a paid driver move, and a trapped state is
    a fixed point of every move; and GMOVE0 cannot be HALT-like because it
    moves the line on a free driver move.                                 *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.UMachRegHost.
Require Import Kernel.UMachCheatPresented.
Require Import Minimal.Presented.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

(* Two one-move presented machines: every move costs 1, or every move costs 0. *)
Lemma paid_toll : forall (s : bool) (i : unit), s = false -> true = true -> 1 >= 1.
Proof. intros. lia. Qed.

Definition sys1 : T.CertificationSystem :=
  T.mk_cert_system bool unit (fun _ _ => true) (fun _ => 1) (fun s => s) paid_toll.

Lemma free_toll : forall (s : bool) (i : unit), s = false -> s = true -> 0 >= 1.
Proof. intros s i H1 H2. congruence. Qed.

Definition sys0 : T.CertificationSystem :=
  T.mk_cert_system bool unit (fun s _ => s) (fun _ => 0) (fun s => s) free_toll.

Lemma bcode : forall b : bool, Some (Nat.eqb (if b then 1 else 0) 1) = Some b.
Proof. intros []; reflexivity. Qed.

Lemma ucode : forall u : unit, Some tt = Some u.
Proof. intros []; reflexivity. Qed.

Definition M1 : presented_machine :=
  mk_presented sys1 (fun _ => Some tt) (fun b => if b then 1 else 0) (fun n => Some (Nat.eqb n 1))
    (fun _ => 0) (fun _ => Some tt) bcode ucode.

Definition M0 : presented_machine :=
  mk_presented sys0 (fun _ => Some tt) (fun b => if b then 1 else 0) (fun n => Some (Nat.eqb n 1))
    (fun _ => 0) (fun _ => Some tt) bcode ucode.

Definition Q3 : list pmove := [PEEKR; PEEKR; GMOVE0].

Theorem pcheat_not_reg_host : reg_host pcheat_host -> False.
Proof.
  intros R.
  pose proof (b_cost pcheat_host R GMOVE0) as Hc. simpl in Hc.
  set (sp := mkp 3 0 M1 false false false).
  assert (Ep : b_err R sp = false).
  { destruct (b_err R sp) eqn:E; [| reflexivity].
    pose proof (b_next_err pcheat_host R Q3 sp E) as X. discriminate X. }
  set (tp := mkp 3 0 M1 false false true).
  assert (Tp : hstep pcheat_host sp GMOVE0 = tp) by reflexivity.
  assert (Fix : forall m, hstep pcheat_host tp m = tp) by (intros m; reflexivity).
  destruct (b_kind R GMOVE0) as [r | r j | |] eqn:K.
  - destruct (b_inc pcheat_host R sp GMOVE0 r Ep K) as (E1 & _ & _). rewrite Tp in E1.
    destruct (b_inc pcheat_host R tp GMOVE0 r E1 K) as (_ & P2 & _). rewrite Fix in P2. lia.
  - destruct (b_dec pcheat_host R sp GMOVE0 r j Ep K) as (E1 & _). rewrite Tp in E1.
    destruct (b_dec pcheat_host R tp GMOVE0 r j E1 K) as (_ & D2). rewrite Fix in D2.
    destruct (b_reg R tp r) as [| n] eqn:V.
    + destruct D2 as [P2 _]. lia.
    + destruct D2 as [_ R2]. specialize (R2 r). unfold upd in R2.
      rewrite Nat.eqb_refl, V in R2. lia.
  - set (sf := mkp 3 0 M0 false false false).
    destruct (b_halt pcheat_host R sf GMOVE0 K) as (E2 & P2 & _).
    pose proof (b_next pcheat_host R Q3 _ _ E2 P2) as N. discriminate N.
  - lia.
Qed.

Print Assumptions pcheat_not_reg_host.
