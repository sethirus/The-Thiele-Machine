(** NeutralUnivCanon.v: the canonical neutral register host, and an honest neutral
    universal machine with surcharge 0 for a class of guests that raise
    their record for a total ledger of 1.

    CNH ("canonical neutral host"): a register machine (registers nat -> nat,
    INC r, DEC r j, HALT, all at price 0) with three record moves at price 1:
      MARK r   record := record || (register r >= 1), next line;
      TICK     record := true, next line;
      PAY      next line (the record untouched).
    It never traps.  It is the lift (NeutralComplete.v, section 5) of the
    register machine with the events "r >= 1", "true", "false", made
    program-driven (each mark goes to the next line).

      cnh_nc            CNH is neutral-complete (its base: INC/DEC on
                        registers 0, 1; its distinction: MARK 0);
      cnh_reg           CNH is a register host;
      lockstep_universal  a host run in lockstep with every guest of a class
                        meets (N1) and (N2) with f = id and surcharge 0;
      down_universal    the honest host program [DEC 0 1; TICK; HALT] on CNH
                        is a neutral universal machine (all of N0-N5) with
                        surcharge 0 for the class Cdown of guests
                        "count register 0 down, then MARK 1" (each of which
                        raises its record with ledger exactly 1, the case in
                        which U_P pays 3, a surcharge of 2).               *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Minimal.ThieleComplete.
Require Import Minimal.NeutralComplete.

(* ================================================================= *)
(* 1. The canonical neutral host.                                     *)
(* ================================================================= *)

Inductive cmove : Type :=
| CInc (r : nat) | CDec (r j : nat) | CHalt | CMark (r : nat) | CTick | CPay.

Record cst : Type := mkcs { cpc : nat; creg : nat -> nat; cflag : bool; cled : nat }.

Definition ccost (m : cmove) : nat :=
  match m with CMark _ | CTick | CPay => 1 | _ => 0 end.

Definition cstep (s : cst) (m : cmove) : cst :=
  match m with
  | CInc r => mkcs (S (cpc s)) (upd (creg s) r (S (creg s r))) (cflag s) (cled s)
  | CDec r j =>
      match creg s r with
      | 0 => mkcs (S (cpc s)) (creg s) (cflag s) (cled s)
      | S n => mkcs j (upd (creg s) r n) (cflag s) (cled s)
      end
  | CHalt => s
  | CMark r => mkcs (S (cpc s)) (creg s) (cflag s || Nat.leb 1 (creg s r)) (S (cled s))
  | CTick => mkcs (S (cpc s)) (creg s) true (S (cled s))
  | CPay => mkcs (S (cpc s)) (creg s) (cflag s) (S (cled s))
  end.

Lemma ctoll : forall s m, cflag s = false -> cflag (cstep s m) = true -> ccost m >= 1.
Proof.
  intros [p r f l] m H0 H1. simpl in H0. subst f.
  destruct m as [x | x j | | x | |]; simpl in *; try lia; try discriminate.
  destruct (r x); simpl in H1; discriminate.
Qed.

Definition cfetch (P : list cmove) (n : nat) : option cmove :=
  match n with 0 => None | S k => nth_error P k end.

Definition cnext (P : list cmove) (s : cst) : option cmove :=
  match cfetch P (cpc s) with Some CHalt => None | o => o end.

Definition CNH : host := mk_host cst cmove cstep ccost cflag ctoll (list cmove) cnext.

Definition ckind (m : cmove) : rkind :=
  match m with CInc r => RInc r | CDec r j => RDec r j | CHalt => RHalt | _ => RRec end.

Definition cnh_reg : reg_host CNH.
Proof.
  refine (mk_rh CNH cpc creg (fun _ => false) ckind _ _ _ _ _ _ _ _).
  - intros [r | r j | | r | |]; reflexivity.
  - intros s m E. discriminate E.
  - intros s m r _ K. destruct m; simpl in K; try discriminate. injection K as ->.
    simpl. auto.
  - intros s m r j _ K. destruct m; simpl in K; try discriminate. injection K as -> ->.
    simpl. destruct (creg s r); simpl; auto.
  - intros s m K. destruct m; simpl in K; try discriminate. simpl. auto.
  - intros s m _ K. destruct m; simpl in K; try discriminate; simpl; auto.
  - intros P s1 s2 _ Hp. simpl. unfold cnext. rewrite Hp. reflexivity.
  - intros P s E. discriminate E.
Defined.

(* Counter moves leave the record alone. *)
Lemma cnh_counter_blind : forall s m, ckind m <> RRec -> cflag (cstep s m) = cflag s.
Proof.
  intros s [r | r j | | r | |] K; simpl; try reflexivity; try (exfalso; apply K; reflexivity).
  destruct (creg s r); reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* CNH is neutral-complete.                                           *)
(* ----------------------------------------------------------------- *)

Definition creg_of (r : reg) : nat := match r with RA => 0 | RB => 1 end.

Definition ccompile (i : cm_instr) : cmove :=
  match i with CINC r => CInc (creg_of r) | CDEC r j => CDec (creg_of r) j end.

Definition cwin (s : cst) : cm_conf := (cpc s, (creg s 0, creg s 1)).

Definition cregs2 (a b : nat) : nat -> nat := fun x => match x with 0 => a | 1 => b | _ => 0 end.

Definition cload (a b : nat) : cst := mkcs 1 (cregs2 a b) false 0.

Definition cnh_base : universal_base (hmach CNH).
Proof.
  refine (mk_ub (hmach CNH) cwin (fun _ => True) ccompile cload _ _ _).
  - intros a b. reflexivity.
  - intros a b. exact I.
  - intros [p r f l] i _. split; [| exact I].
    destruct i as [[|] | [|] j]; simpl; unfold cwin, upd; simpl; try reflexivity.
    + destruct (r 0) eqn:E; simpl; rewrite ?E; reflexivity.
    + destruct (r 1) eqn:E; simpl; rewrite ?E; reflexivity.
Defined.

Definition cnh_iface : neutral_interface (hmach CNH) :=
  mk_ni (hmach CNH) cnh_base (fun m => is_counter (ckind m)) cled.

Theorem cnh_nc : neutral_complete_with cnh_iface.
Proof.
  split; [| split; [| split]].
  - split; [intros [[|] | [|] j]; reflexivity |]. split.
    + intros s m Hb. simpl in Hb. simpl. apply cnh_counter_blind.
      destruct (ckind m); simpl in Hb; congruence.
    + intros [p r f l] m H. simpl in H. subst f. destruct m as [x | x j | | x | |]; simpl; auto.
      destruct (r x); reflexivity.
  - intros a b. reflexivity.
  - split.
    + intros [r | r j | | r | |]; reflexivity.
    + intros [p r f l] [x | x j | | x | |]; simpl; try lia. destruct (r x); simpl; lia.
  - exists [CMark 0], 1, 0, 0, 0. split; reflexivity.
Qed.

Theorem cnh_host_nc : host_nc CNH cnh_reg.
Proof. exists cnh_iface. split; [exact cnh_nc | intros m; reflexivity]. Qed.

(* ================================================================= *)
(* 2. Lockstep hosts meet (N1) and (N2) with surcharge 0.             *)
(* ================================================================= *)

Section Lockstep.
Variable C : gclass.
Variable H : host.
Variable Obs : gi C -> Type.
Variable obs : forall i, gS C i -> Obs i.
Variable P : hP H.
Variable h0 : hS H.
Variable i : gi C.
Variable decode : hS H -> Obs i.
Hypothesis Hgp : forall s m, gread C i s = true -> gread C i (gstep C i s m) = true.
Hypothesis Lhalt : forall n, hnext H P (hr P h0 n) = None <-> gnext C i (grun i n) = None.
Hypothesis Ldec : forall n, decode (hr P h0 n) = obs i (grun i n).
Hypothesis Lflag : forall n, hflag H (hr P h0 n) = gread C i (grun i n).
Hypothesis Lled : forall n, hl P h0 n = gledger i n.

Theorem lockstep_universal :
  halt_clause C H Obs obs 0 P h0 i decode /\ in_order C H Obs obs 0 P h0 i decode (fun m => m).
Proof.
  assert (M : forall m, match_at C H Obs obs 0 P h0 i decode m m).
  { intros m. split; [apply Ldec |]. split; [rewrite Lflag; symmetry; apply glat_read, Hgp |].
    exists 0. split; [lia | rewrite Lled; lia]. }
  split; [split |].
  - split; intros [n Hn]; exists n; apply Lhalt; exact Hn.
  - intros m0 _ Hs. exists m0. split; [apply Lhalt, Hs | apply M].
  - split; [intros; lia | intros m _; apply M].
Qed.

End Lockstep.

(* ================================================================= *)
(* 3. The countdown class and its honest host.                        *)
(* ================================================================= *)

(* Guests: CNH programs [DEC 0 1; MARK 1; HALT] from registers (x, 1). *)
Definition Qd : list cmove := [CDec 0 1; CMark 1; CHalt].

Definition dcode (x : nat) : nat -> nat := cregs2 x 1.

Definition ctpl (rho : nat -> nat) : cst := mkcs 1 rho false 0.

Definition Cdown : gclass :=
  mk_gclass nat (fun _ => cst) (fun _ => cmove) (fun _ => cnext Qd) (fun _ => cstep)
    (fun _ => ccost) (fun _ => cflag) (fun _ => ctoll) (fun x => ctpl (dcode x)).

Definition dobs (x : nat) (s : cst) : nat * nat := (creg s 0, creg s 1).

(* The host program: TICK where the guest has MARK 1. *)
Definition Pd : list cmove := [CDec 0 1; CTick; CHalt].

Lemma down_step : forall s, creg s 1 = 1 ->
  match cnext Pd s, cnext Qd s with
  | None, None => True
  | Some a, Some b => cstep s a = cstep s b /\ creg (cstep s a) 1 = 1 /\ ccost a = ccost b
  | _, _ => False
  end.
Proof.
  intros [p r f l] H1. simpl in H1. unfold cnext, cfetch. simpl.
  destruct p as [| [| [| [| p]]]]; simpl; auto.
  - destruct (r 0) eqn:E; simpl; repeat split; auto; unfold upd; simpl; exact H1.
  - rewrite H1. simpl. rewrite orb_true_r. auto.
  - destruct p; simpl; auto.
Qed.

Lemma down_lockstep : forall n s, creg s 1 = 1 ->
  hr (H:=CNH) Pd s n = gr (C:=Cdown) (i:=0) s n /\
  hl (H:=CNH) Pd s n = gl (C:=Cdown) (i:=0) s n /\ creg (hr (H:=CNH) Pd s n) 1 = 1.
Proof.
  induction n as [| n IH]; intros s H1; [auto |].
  pose proof (down_step s H1) as D. simpl.
  change (hnext CNH Pd s) with (cnext Pd s). change (gnext Cdown 0 s) with (cnext Qd s).
  destruct (cnext Pd s) as [a |], (cnext Qd s) as [b |]; try contradiction; [| auto].
  destruct D as (E & H1' & Ec).
  change (hstep CNH s a) with (cstep s a). change (gstep Cdown 0 s b) with (cstep s b).
  change (hcost CNH a) with (ccost a). change (gcost Cdown 0 b) with (ccost b).
  destruct (IH (cstep s a) H1') as (A & B & C').
  rewrite <- E. rewrite A, B, Ec. rewrite A in C'. auto.
Qed.

(* The guest class does not depend on the instance index for its steps. *)
Lemma down_gr_any : forall (x : nat) s n, gr (C:=Cdown) (i:=x) s n = gr (C:=Cdown) (i:=0) s n.
Proof. intros x s n. revert s. induction n; intros s; simpl; [reflexivity |]. destruct (cnext Qd s); auto. Qed.

Lemma down_gl_any : forall (x : nat) s n, gl (C:=Cdown) (i:=x) s n = gl (C:=Cdown) (i:=0) s n.
Proof. intros x s n. revert s. induction n; intros s; simpl; [reflexivity |]. destruct (cnext Qd s); auto. Qed.

Definition draise (l : nat) : bool := Nat.eqb l 2.

Lemma down_line_raise : line_raise CNH cnh_reg Pd draise.
Proof.
  intros [p r f l] m _ Hn K. right. simpl in *. unfold cnext, cfetch in Hn.
  destruct p as [| [| [| [| p]]]]; simpl in Hn; try discriminate.
  - injection Hn as <-. discriminate K.
  - injection Hn as <-. simpl. rewrite orb_true_r. reflexivity.
  - destruct p; discriminate Hn.
Qed.

Lemma ctpl_clean : clean_template CNH cnh_reg ctpl.
Proof. repeat split. Qed.

Theorem down_universal : neutral_universal Cdown CNH (fun _ => (nat * nat)%type) dobs 0.
Proof.
  exists Pd, cnh_reg, draise, ctpl, dcode, (fun _ rho => (rho 0, rho 1)).
  split; [exact cnh_host_nc |]. split; [exact down_line_raise |]. split; [exact ctpl_clean |].
  intros x. assert (H1 : creg (ctpl (dcode x)) 1 = 1) by reflexivity.
  assert (L : forall n, hr (H:=CNH) Pd (ctpl (dcode x)) n = grun (C:=Cdown) x n /\
                        hl (H:=CNH) Pd (ctpl (dcode x)) n = gledger (C:=Cdown) x n).
  { intros n. destruct (down_lockstep n _ H1) as (A & B & _).
    change (grun (C:=Cdown) x n) with (gr (C:=Cdown) (i:=x) (ctpl (dcode x)) n).
    change (gledger (C:=Cdown) x n) with (gl (C:=Cdown) (i:=x) (ctpl (dcode x)) n).
    rewrite (down_gr_any x), (down_gl_any x). split; [exact A | exact B]. }
  destruct (lockstep_universal Cdown CNH (fun _ => (nat * nat)%type) dobs Pd (ctpl (dcode x)) x
              (fun h => (creg h 0, creg h 1)))
    as [Hh Ho].
  - intros s m Hs. simpl in *. destruct s as [p r f l]; simpl in Hs; subst f.
    destruct m as [y | y j | | y | |]; simpl; auto. destruct (r y); reflexivity.
  - intros n. rewrite (proj1 (L n)). change (hnext CNH Pd) with (cnext Pd).
    change (gnext Cdown x) with (cnext Qd).
    pose proof (down_step (grun (C:=Cdown) x n)) as D.
    assert (Hr : creg (grun (C:=Cdown) x n) 1 = 1).
    { rewrite <- (proj1 (L n)). exact (proj2 (proj2 (down_lockstep n _ H1))). }
    specialize (D Hr). set (g := grun (C:=Cdown) x n) in *.
    destruct (cnext Pd g) eqn:E1, (cnext Qd g) eqn:E2; try contradiction; split; intros; first [reflexivity | congruence].
  - intros n. rewrite (proj1 (L n)). reflexivity.
  - intros n. rewrite (proj1 (L n)). reflexivity.
  - intros n. exact (proj2 (L n)).
  - split; [exact Hh |]. exists (fun m => m). exact Ho.
Qed.

(* Each guest of the class raises its record with a total ledger of 1:
   from x = 0 the guest's record is up after 2 steps, its ledger 1. *)
Example down_unit_raise :
  gread Cdown 0 (grun (C:=Cdown) 0 2) = true /\ gledger (C:=Cdown) 0 2 = 1.
Proof. split; reflexivity. Qed.

Print Assumptions cnh_nc.
Print Assumptions cnh_host_nc.
Print Assumptions lockstep_universal.
Print Assumptions down_universal.
