(** NeutralUnivSmuggle.v: the decode clause, as neutral_universal states it,
    lets the decode carry the guest.

    Class Cs: the CNH program [INC 0; INC 9; DEC 9 1] from register 0 = a
    (it counts register 0 up forever, never marks, never halts).  The host
    program [INC 5; INC 9; DEC 9 1] is loaded with ALL REGISTERS ZERO for
    every guest, so its run is the same for every guest [smuggle_blind];
    the decode  a, rho |-> a + rho 5  supplies the guest.  It meets every
    clause of neutral_universal with surcharge 0 [smuggle_universal].

    What stops it: a decode fixed with the class (the guest's own state
    coding read from fixed registers), not chosen per instance by the host;
    U and U_P meet that form (U_dec, UP_dec read fixed registers through the
    guest's own coding).  On a class with a halting guest and one that does
    not halt, or a raising guest and one that does not, no host blind to
    the guest can meet (N1) or (N2)'s record clause, so the smuggle needs a
    class whose halting and record are the same for all its guests.       *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   tests the decode clause of NeutralUnivDef.v on the canonical host of
   NeutralUnivCanon.v. Those two files connect it to ThieleComplete.v and
   NeutralComplete.v; it uses no name of the foundation chain directly. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Kernel.NeutralUnivCanon.
Require Import Kernel.NeutralUnivTools.

Definition Qs : list cmove := [CInc 0; CInc 9; CDec 9 1].
Definition Cs : gclass := cnh_class nat (fun _ => Qs) (fun a => ctpl (cregs2 a 0)).
Definition sobs (a : nat) (s : cst) : nat := creg s 0.

Definition Ps : list cmove := [CInc 5; CInc 9; CDec 9 1].
Definition scode (a : nat) : nat -> nat := fun _ => 0.
Definition sdec (a : nat) (rho : nat -> nat) : nat := a + rho 5.

Definition sinv (a : nat) (g h : cst) : Prop :=
  cpc g = cpc h /\ creg g 9 = creg h 9 /\
  ((cpc g = 1 /\ creg g 9 = 0) \/ (cpc g = 2 /\ creg g 9 = 0) \/ (cpc g = 3 /\ creg g 9 = 1)) /\
  creg g 0 = a + creg h 5 /\ cflag g = false /\ cflag h = false /\ cled g = 0 /\ cled h = 0.

Lemma sinv_step : forall a g h, sinv a g h ->
  exists m m', cnext Qs g = Some m /\ cnext Ps h = Some m' /\ ccost m = 0 /\ ccost m' = 0 /\
    sinv a (cstep g m) (cstep h m').
Proof.
  intros a [p r f l] [q u e d] (Hp & H9 & Hl & H0 & Hf & He & Hd & Hd'). simpl in *.
  subst q f e l d. unfold cnext, cfetch.
  destruct Hl as [[-> R9] | [[-> R9] | [-> R9]]]; simpl.
  - eexists; eexists. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    unfold sinv; simpl; unfold upd; simpl. repeat split; lia.
  - eexists; eexists. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    unfold sinv; simpl; unfold upd; simpl. repeat split; lia.
  - assert (U9 : u 9 = 1) by lia.
    eexists; eexists. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    unfold sinv; simpl. rewrite R9, U9. unfold upd; simpl. repeat split; lia.
Qed.

Lemma smuggle_run : forall a n g h, sinv a g h ->
  sinv a (gr (C:=Cs) (i:=a) g n) (hr (H:=CNH) Ps h n) /\
  gl (C:=Cs) (i:=a) g n = 0 /\ hl (H:=CNH) Ps h n = 0 /\
  gnext Cs a (gr (C:=Cs) (i:=a) g n) <> None /\ hnext CNH Ps (hr (H:=CNH) Ps h n) <> None.
Proof.
  intros a n. induction n as [| n IH]; intros g h I.
  - destruct (sinv_step a g h I) as (m & m' & Hg & Hh & _ & _ & _).
    simpl. change (cnext Qs g <> None /\ cnext Ps h <> None) with (cnext Qs g <> None /\ cnext Ps h <> None).
    split; [exact I |]. split; [reflexivity |]. split; [reflexivity |]. rewrite Hg, Hh. split; discriminate.
  - destruct (sinv_step a g h I) as (m & m' & Hg & Hh & Cg & Ch & I').
    simpl. change (gnext Cs a g) with (cnext Qs g). change (hnext CNH Ps h) with (cnext Ps h).
    rewrite Hg, Hh. change (gstep Cs a g m) with (cstep g m). change (hstep CNH h m') with (cstep h m').
    change (gcost Cs a m) with (ccost m). change (hcost CNH m') with (ccost m').
    rewrite Cg, Ch. destruct (IH _ _ I') as (A & B & C' & D & E). auto.
Qed.

Lemma smuggle_start : forall a, sinv a (ctpl (cregs2 a 0)) (ctpl (scode a)).
Proof.
  intros a. unfold sinv; simpl. split; [reflexivity |]. split; [reflexivity |].
  split; [left; split; reflexivity |]. split; [unfold scode; lia |]. repeat split.
Qed.

Theorem smuggle_universal : neutral_universal Cs CNH (fun _ => nat) sobs 0.
Proof.
  exists Ps, cnh_reg, (fun l => tick_at (cfetch Ps l)), ctpl, scode, sdec.
  split; [exact cnh_host_nc |].
  split; [apply cnh_line_raise_nomark; intros [| [| [| [| l]]]] r; simpl; try discriminate; destruct l; discriminate |].
  split; [exact ctpl_clean |].
  intros a. pose proof (fun n => smuggle_run a n _ _ (smuggle_start a)) as L.
  assert (M : forall m, match_at Cs CNH (fun _ => nat) sobs 0 Ps (ctpl (scode a)) a
                          (fun h => sdec a (b_reg cnh_reg h)) m m).
  { intros m. destruct (L m) as ((_ & _ & _ & R0 & Fg & Fh & _) & Gl & Hl & _).
    split; [| split].
    - unfold sdec, sobs, grun. simpl. symmetry. exact R0.
    - change (cflag (hr (H:=CNH) Ps (ctpl (scode a)) m) = glat (C:=Cs) a m). rewrite Fh.
      rewrite (glat_read Cs a (fun s m => cnh_perm s m)). symmetry. exact Fg.
    - exists 0. split; [lia |]. unfold gledger. rewrite Hl. simpl. rewrite Gl. reflexivity. }
  split; [split |].
  - split; intros [n Hn]; exfalso; destruct (L n) as (_ & _ & _ & D & E); [exact (E Hn) | exact (D Hn)].
  - intros m0 _ Hs. exfalso. destruct (L m0) as (_ & _ & _ & D & _). exact (D Hs).
  - exists (fun m => m). split; [intros; lia | intros m _; apply M].
Qed.

(* The host's run does not depend on the guest. *)
Theorem smuggle_blind : forall a a' n,
  hr (H:=CNH) Ps (ctpl (scode a)) n = hr (H:=CNH) Ps (ctpl (scode a')) n.
Proof. reflexivity. Qed.

Print Assumptions smuggle_universal.
Print Assumptions smuggle_blind.
