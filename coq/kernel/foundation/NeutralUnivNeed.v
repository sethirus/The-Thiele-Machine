(** NeutralUnivNeed.v: each clause of neutral_universal is needed.  For each clause,
    a host and program that meet the other clauses and fail it, on the
    one-guest class C1 = Cdown at x = 1 (or, for the load clause, a one-guest
    class whose record is up at its start).

      need_N0      a host without a conditional mark (only TICK, PAY):
                   everything but (N0), whose distinction fails;
      need_N1      a program that loops after its TICK: everything but (N1);
      need_order   a program that shows the guest's states backwards:
                   halting, decode, record, ledger at some time for every
                   guest step, and the rest; no increasing choice exists;
      need_decode  observation (line, A, B): every other clause, but no
                   decode from registers works with any increasing times;
      need_record  a program that PAYs instead of TICKs;
      need_ledger  a program with one PAY too many (surcharge 1 > K = 0);
      need_clean   a load with the record already up meets everything with
                   surcharge 0 but the load clause; with the load clause the
                   surcharge at that guest's start is at least 1, and 1 is
                   attained (up_floor, up_attained);
      need_N4      a hybrid host whose free primitive GEX fetches, decodes
                   and executes the guest's next instruction from the
                   registers: it meets everything with a register reading
                   that only drops the counter-move requirement, and it is
                   no register host under any reading.

    (N3) is needed: NeutralUnivMirror.v (oracle_y, mirror_y).                      *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Kernel.NeutralUnivCanon.
Require Import Kernel.NeutralUnivTools.
Require Import Minimal.ThieleComplete.
Require Import Minimal.NeutralComplete.

Definition C1 : gclass := cnh_class unit (fun _ => Qd) (fun _ => ctpl (dcode 1)).
Definition O2 : unit -> Type := fun _ => (nat * nat)%type.
Definition o2 (u : unit) (s : cst) : nat * nat := (creg s 0, creg s 1).
Definition d2 (rho : nat -> nat) : nat * nat := (rho 0, rho 1).

Lemma C1_stop : gnext C1 tt (grun (C:=C1) tt 3) = None.
Proof. reflexivity. Qed.
Lemma C1_live : forall m, live_before (C:=C1) tt m -> m <= 3.
Proof. intros m Hl. exact (live_bound C1 tt 3 m C1_stop Hl). Qed.
Lemma C1_stop_only : forall m, live_before (C:=C1) tt m -> gnext C1 tt (grun (C:=C1) tt m) = None -> m = 3.
Proof.
  intros m Hl Hs. pose proof (C1_live m Hl). destruct m as [| [| [| [|]]]]; try lia; discriminate Hs.
Qed.

(* A unit-class tactic: finite case analysis on the guest step. *)
Ltac fin_match := split; [reflexivity |]; split; [reflexivity |]; exists 0; split; [lia | reflexivity].

(* ================================================================= *)
(* (N1) is needed: a program that loops after the TICK.               *)
(* ================================================================= *)

Definition Ploop : list cmove := [CDec 0 1; CTick; CInc 9; CDec 9 3].

Lemma Ploop_nomark : forall l r, cfetch Ploop l <> Some (CMark r).
Proof. intros [| [| [| [| [| l]]]]] r; simpl; try discriminate. destruct l; discriminate. Qed.

Lemma Ploop_runs : forall n, hnext CNH Ploop (hr (H:=CNH) Ploop (ctpl (dcode 1)) n) <> None.
Proof.
  assert (Inv : forall n s, (cpc s = 3 /\ creg s 9 = 0) \/ (cpc s = 4 /\ creg s 9 = 1) ->
                  hnext CNH Ploop (hr (H:=CNH) Ploop s n) <> None).
  { induction n as [| n IH]; intros [p r f l] H.
    - simpl in *. unfold cnext, cfetch. destruct H as [[-> _] | [-> _]]; simpl; discriminate.
    - simpl in H. destruct H as [[-> H9] | [-> H9]].
      + simpl. apply IH. right. simpl. unfold upd. simpl. rewrite H9. auto.
      + simpl. rewrite H9. apply IH. left. simpl. unfold upd. simpl. auto. }
  intros n. destruct n as [| [| [| n]]]; try (simpl; discriminate).
  replace (S (S (S n))) with (3 + n) by lia. rewrite hr_add. apply Inv. left. split; reflexivity.
Qed.

Theorem need_N1 :
  line_raise CNH cnh_reg Ploop (fun l => tick_at (cfetch Ploop l)) /\
  in_order C1 CNH O2 o2 0 Ploop (ctpl (dcode 1)) tt (fun h => d2 (b_reg cnh_reg h)) (fun m => m) /\
  ~ clause1 C1 CNH Ploop (ctpl (dcode 1)) tt.
Proof.
  split; [exact (cnh_line_raise_nomark Ploop Ploop_nomark) |]. split.
  - split; [intros; lia |]. intros m Hl. pose proof (C1_live m Hl).
    destruct m as [| [| [| [|]]]]; try lia; fin_match.
  - intros [_ H]. destruct (H (ex_intro _ 3 C1_stop)) as [n Hn]. exact (Ploop_runs n Hn).
Qed.

(* ================================================================= *)
(* (N2), order, is needed.                                            *)
(* ================================================================= *)

Definition Prev : list cmove := [CDec 0 5; CInc 5; CTick; CHalt; CInc 3; CInc 9; CDec 9 1].
Definition drev (rho : nat -> nat) : nat * nat := (if Nat.eqb (rho 5) 0 then rho 3 else 0, rho 1).

Lemma Prev_nomark : forall l r, cfetch Prev l <> Some (CMark r).
Proof. intros [| [| [| [| [| [| [| [| l]]]]]]]] r; simpl; try discriminate. destruct l; discriminate. Qed.

Lemma Prev_halt : forall n, 7 <= n -> hr (H:=CNH) Prev (ctpl (dcode 1)) n = hr (H:=CNH) Prev (ctpl (dcode 1)) 7.
Proof. intros n Hn. apply (hr_stopped_stays CNH Prev); [exact Hn | reflexivity]. Qed.

Definition rmatch (n m : nat) : Prop :=
  match_at C1 CNH O2 o2 0 Prev (ctpl (dcode 1)) tt (fun h => drev (b_reg cnh_reg h)) n m.

Lemma rmatch_late : forall n m, 7 <= n -> rmatch n m -> m = 3 \/ m > 3.
Proof.
  intros n m Hn [_ [Hf _]]. rewrite (Prev_halt n Hn) in Hf.
  destruct m as [| [| [|]]]; [discriminate Hf | discriminate Hf | discriminate Hf | lia].
Qed.

Theorem need_order :
  line_raise CNH cnh_reg Prev (fun l => tick_at (cfetch Prev l)) /\
  halt_clause C1 CNH O2 o2 0 Prev (ctpl (dcode 1)) tt (fun h => drev (b_reg cnh_reg h)) /\
  (forall m, live_before (C:=C1) tt m -> exists n, rmatch n m) /\
  ~ exists f, in_order C1 CNH O2 o2 0 Prev (ctpl (dcode 1)) tt (fun h => drev (b_reg cnh_reg h)) f.
Proof.
  split; [exact (cnh_line_raise_nomark Prev Prev_nomark) |]. split; [split |]; [| | split].
  - split; intros _; [exists 3; exact C1_stop | exists 7; reflexivity].
  - intros m0 Hl Hs. rewrite (C1_stop_only m0 Hl Hs). exists 7. split; [reflexivity | fin_match].
  - intros m Hl. pose proof (C1_live m Hl).
    destruct m as [| [| [| [|]]]]; try lia; [exists 2 | exists 0 | exists 0 | exists 7]; fin_match.
  - intros [f [Hinc Hm]].
    assert (L3 : live_before (C:=C1) tt 3) by (intros k Hk; destruct k as [| [| [|]]]; try lia; discriminate).
    assert (L2 : live_before (C:=C1) tt 2) by (intros k Hk; apply L3; lia).
    assert (L1 : live_before (C:=C1) tt 1) by (intros k Hk; apply L3; lia).
    assert (L0 : live_before (C:=C1) tt 0) by (intros k Hk; lia).
    pose proof (Hinc 0 L1) as I0. pose proof (Hinc 1 L2) as I1. pose proof (Hm 0 L0) as M0.
    pose proof (Hm 1 L1) as M1. pose proof (Hm 2 L2) as M2.
    (* the times that match step 0 are 2..5; step 1: 0, 1, 6; step 2: 0, 1, 6 *)
    assert (A0 : 2 <= f 0).
    { destruct (le_lt_dec 2 (f 0)) as [h | h]; [exact h |]. exfalso.
      destruct M0 as [D _]. destruct (f 0) as [| [|]]; [discriminate D | discriminate D | lia]. }
    assert (A1 : f 1 = 6).
    { destruct (le_lt_dec 7 (f 1)) as [h | h].
      - exfalso. destruct (rmatch_late (f 1) 1 h M1); lia.
      - destruct M1 as [D _]. destruct (f 1) as [| [| [| [| [| [| [|]]]]]]]; try lia;
          try discriminate D; reflexivity. }
    assert (h : 7 <= f 2) by lia. destruct (rmatch_late (f 2) 2 h M2); lia.
Qed.

(* ================================================================= *)
(* (N2), decode, is needed: observe (line, A, B).                     *)
(* ================================================================= *)

Definition O3 : unit -> Type := fun _ => (nat * nat * nat)%type.
Definition o3 (u : unit) (s : cst) : nat * nat * nat := (cpc s, creg s 0, creg s 1).

Theorem need_decode :
  line_raise CNH cnh_reg Pd draise /\
  (exists f, (forall m, live_before (C:=C1) tt (S m) -> f m < f (S m)) /\
     forall m, live_before (C:=C1) tt m ->
       hflag CNH (hr (H:=CNH) Pd (ctpl (dcode 1)) (f m)) = glat (C:=C1) tt m /\
       hl (H:=CNH) Pd (ctpl (dcode 1)) (f m) = gledger (C:=C1) tt m) /\
  ~ exists (dec : (nat -> nat) -> nat * nat * nat) f,
      in_order C1 CNH O3 o3 0 Pd (ctpl (dcode 1)) tt (fun h => dec (b_reg cnh_reg h)) f.
Proof.
  split; [exact down_line_raise |]. split.
  - exists (fun m => m). split; [intros; lia |]. intros m Hl. pose proof (C1_live m Hl).
    destruct m as [| [| [| [|]]]]; try lia; split; reflexivity.
  - intros (dec & f & Hinc & Hm).
    assert (L3 : live_before (C:=C1) tt 3) by (intros k Hk; destruct k as [| [| [|]]]; try lia; discriminate).
    assert (L2 : live_before (C:=C1) tt 2) by (intros k Hk; apply L3; lia).
    assert (L1 : live_before (C:=C1) tt 1) by (intros k Hk; apply L3; lia).
    pose proof (Hinc 0 L1). pose proof (Hinc 1 L2) as I1.
    destruct (Hm 1 L1) as [D1 _]. destruct (Hm 2 L2) as [D2 [F2 _]].
    (* times with the record down: 0, 1, 2 *)
    assert (T2 : f 2 <= 2).
    { destruct (le_lt_dec (f 2) 2) as [h | h]; [exact h |]. exfalso.
      assert (E : hr (H:=CNH) Pd (ctpl (dcode 1)) (f 2) = hr (H:=CNH) Pd (ctpl (dcode 1)) 3).
      { destruct (f 2) as [| [| [| k]]]; try lia. destruct k; [reflexivity |].
        apply (hr_stopped_stays CNH Pd); [lia | reflexivity]. }
      rewrite E in F2. discriminate F2. }
    assert (E1 : f 1 = 1) by lia. assert (E2 : f 2 = 2) by lia.
    rewrite E1 in D1. rewrite E2 in D2. simpl in D1, D2.
    (* the register files at times 1 and 2 are the same *)
    change (dec (upd (cregs2 1 1) 0 0) = (1, 0, 1)) in D1.
    change (dec (upd (cregs2 1 1) 0 0) = (2, 0, 1)) in D2.
    rewrite D1 in D2. discriminate D2.
Qed.

(* ================================================================= *)
(* (N2), record and ledger, are needed.                               *)
(* ================================================================= *)

Definition Ppay : list cmove := [CDec 0 1; CPay; CHalt].

Theorem need_record :
  line_raise CNH cnh_reg Ppay (fun l => tick_at (cfetch Ppay l)) /\
  (forall m, live_before (C:=C1) tt m ->
     d2 (b_reg cnh_reg (hr (H:=CNH) Ppay (ctpl (dcode 1)) m)) = o2 tt (grun (C:=C1) tt m) /\
     hl (H:=CNH) Ppay (ctpl (dcode 1)) m = gledger (C:=C1) tt m) /\
  ~ exists n, hflag CNH (hr (H:=CNH) Ppay (ctpl (dcode 1)) n) = glat (C:=C1) tt 3.
Proof.
  split; [apply cnh_line_raise_nomark; intros [| [| [| [| l]]]] r; simpl; try discriminate; destruct l; discriminate |].
  split.
  - intros m Hl. pose proof (C1_live m Hl). destruct m as [| [| [| [|]]]]; try lia; split; reflexivity.
  - intros [n Hn]. assert (Hf : forall n s, cflag s = false -> cflag (hr (H:=CNH) Ppay s n) = false).
    { induction n0 as [| n0 IH]; intros s Hs; [exact Hs |]. simpl. change (hnext CNH Ppay s) with (cnext Ppay s).
      destruct (cnext Ppay s) as [m |] eqn:E; [| exact Hs]. apply IH.
      destruct s as [p r f l]; simpl in Hs; subst f. unfold cnext, cfetch in E. simpl in E.
      destruct p as [| [| [| [| p]]]]; simpl in E; try discriminate.
      - injection E as <-. simpl. destruct (r 0); reflexivity.
      - injection E as <-. reflexivity.
      - destruct p; discriminate. }
    change (cflag (hr (H:=CNH) Ppay (ctpl (dcode 1)) n) = glat (C:=C1) tt 3) in Hn.
    rewrite (Hf n (ctpl (dcode 1)) eq_refl) in Hn. discriminate Hn.
Qed.

Definition Pextra : list cmove := [CDec 0 1; CPay; CTick; CHalt].

Theorem need_ledger :
  line_raise CNH cnh_reg Pextra (fun l => tick_at (cfetch Pextra l)) /\
  in_order C1 CNH O2 o2 1 Pextra (ctpl (dcode 1)) tt (fun h => d2 (b_reg cnh_reg h))
    (fun m => match m with 3 => 4 | _ => m end) /\
  ~ exists f, in_order C1 CNH O2 o2 0 Pextra (ctpl (dcode 1)) tt (fun h => d2 (b_reg cnh_reg h)) f.
Proof.
  split; [apply cnh_line_raise_nomark; intros [| [| [| [| [| l]]]]] r; simpl; try discriminate; destruct l; discriminate |].
  split.
  - split; [intros m Hl; pose proof (C1_live (S m) Hl); destruct m as [| [| [|]]]; simpl; lia |].
    intros m Hl. pose proof (C1_live m Hl). destruct m as [| [| [| [|]]]]; try lia; try fin_match.
    split; [reflexivity |]. split; [reflexivity |]. exists 1. split; [lia | reflexivity].
  - intros [f [_ Hm]].
    assert (L3 : live_before (C:=C1) tt 3) by (intros k Hk; destruct k as [| [| [|]]]; try lia; discriminate).
    destruct (Hm 3 L3) as [_ [F [s [Hs L]]]].
    assert (Hs0 : s = 0) by lia. subst s.
    (* the record is up only from time 4 on, where the ledger is 2 *)
    assert (G : forall n, hflag CNH (hr (H:=CNH) Pextra (ctpl (dcode 1)) n) = true ->
                  hl (H:=CNH) Pextra (ctpl (dcode 1)) n = 2).
    { intros n Hn. destruct n as [| [| [| [| n]]]]; try discriminate Hn.
      replace (S (S (S (S n)))) with (4 + n) by lia. rewrite hl_add.
      rewrite (hl_stop CNH Pextra _ n) by reflexivity. reflexivity. }
    rewrite (G _ F) in L. discriminate L.
Qed.

(* ================================================================= *)
(* (N5) is needed: a load with the record already up.                 *)
(* ================================================================= *)

(* One guest, record up at its start: [DEC 0 1; HALT] from (1, 1). *)
Definition Qu : list cmove := [CDec 0 1; CHalt].
Definition Cup : gclass := cnh_class unit (fun _ => Qu) (fun _ => mkcs 1 (dcode 1) true 0).

Lemma Cup_stop : gnext Cup tt (grun (C:=Cup) tt 2) = None.
Proof. reflexivity. Qed.
Lemma Cup_live : forall m, live_before (C:=Cup) tt m -> m <= 2.
Proof. intros m Hl. exact (live_bound Cup tt 2 m Cup_stop Hl). Qed.

Definition uptpl (rho : nat -> nat) : cst := mkcs 1 rho true 0.

Theorem need_clean :
  line_raise CNH cnh_reg Qu (fun l => tick_at (cfetch Qu l)) /\
  halt_clause Cup CNH O2 o2 0 Qu (uptpl (dcode 1)) tt (fun h => d2 (b_reg cnh_reg h)) /\
  in_order Cup CNH O2 o2 0 Qu (uptpl (dcode 1)) tt (fun h => d2 (b_reg cnh_reg h)) (fun m => m) /\
  ~ clean_template CNH cnh_reg uptpl.
Proof.
  split; [apply cnh_line_raise_nomark; intros [| [| [| l]]] r; simpl; try discriminate; destruct l; discriminate |].
  split; [split |].
  - split; intros _; [exists 2; exact Cup_stop | exists 2; reflexivity].
  - intros m0 Hl Hs. assert (m0 = 2).
    { pose proof (Cup_live m0 Hl). destruct m0 as [| [| [|]]]; try lia; discriminate Hs. }
    subst m0. exists 2. split; [reflexivity | fin_match].
  - split; [split; [intros; lia |] |].
    + intros m Hl. pose proof (Cup_live m Hl). destruct m as [| [| [|]]]; try lia; fin_match.
    + intros (_ & _ & _ & Hf). specialize (Hf (fun _ => 0)). discriminate Hf.
Qed.

(* With a clean load, every host pays at least 1 by the first matching
   time of a guest whose record is up at its start. *)
Theorem up_floor : forall (H : host) (P : hP H) (R : reg_host H) (tpl : (nat -> nat) -> hS H) rho dec f K,
  clean_template H R tpl ->
  in_order Cup H O2 o2 K P (tpl rho) tt (fun h => dec (b_reg R h)) f ->
  exists s, s >= 1 /\ hl P (tpl rho) (f 0) = gledger (C:=Cup) tt 0 + s.
Proof.
  intros H P R tpl rho dec f K [_ [_ [_ Hfl]]] [_ Hm].
  destruct (Hm 0 (fun k Hk => ltac:(lia))) as [_ [F [s [_ L]]]].
  exists s. split; [| exact L].
  pose proof (surcharge_floor_one Cup H P (tpl rho) tt (f 0) 0 s (Hfl rho) F eq_refl L) as X.
  simpl in X. lia.
Qed.

(* And 1 is attained by an honest program: TICK first, then the guest. *)
Definition Pup : list cmove := [CTick; CDec 0 2; CHalt].

Theorem up_attained :
  line_raise CNH cnh_reg Pup (fun l => tick_at (cfetch Pup l)) /\
  halt_clause Cup CNH O2 o2 1 Pup (ctpl (dcode 1)) tt (fun h => d2 (b_reg cnh_reg h)) /\
  in_order Cup CNH O2 o2 1 Pup (ctpl (dcode 1)) tt (fun h => d2 (b_reg cnh_reg h)) (fun m => S m) /\
  (forall m, live_before (C:=Cup) tt m ->
     hl (H:=CNH) Pup (ctpl (dcode 1)) (S m) = gledger (C:=Cup) tt m + 1).
Proof.
  split; [apply cnh_line_raise_nomark; intros [| [| [| [| l]]]] r; simpl; try discriminate; destruct l; discriminate |].
  assert (M : forall m, m <= 2 -> match_at Cup CNH O2 o2 1 Pup (ctpl (dcode 1)) tt
                                       (fun h => d2 (b_reg cnh_reg h)) (S m) m).
  { intros m Hm. destruct m as [| [| [|]]]; try lia;
      (split; [reflexivity |]); (split; [reflexivity |]); (exists 1; split; [lia | reflexivity]). }
  split; [split |]; [| | split].
  - split; intros _; [exists 2; exact Cup_stop | exists 3; reflexivity].
  - intros m0 Hl Hs. assert (m0 = 2).
    { pose proof (Cup_live m0 Hl). destruct m0 as [| [| [|]]]; try lia; discriminate Hs. }
    subst m0. exists 3. split; [reflexivity | apply M; lia].
  - split; [intros; lia | intros m Hl; apply M, Cup_live, Hl].
  - intros m Hl. pose proof (Cup_live m Hl). destruct m as [| [| [|]]]; try lia; reflexivity.
Qed.

(* ================================================================= *)
(* (N0) is needed: a host with no conditional mark.                   *)
(* ================================================================= *)

Inductive tmove : Type := TInc (r : nat) | TDec (r j : nat) | THalt | TTick | TPay.

Definition tc (m : tmove) : cmove :=
  match m with TInc r => CInc r | TDec r j => CDec r j | THalt => CHalt | TTick => CTick | TPay => CPay end.

Definition tstep (s : cst) (m : tmove) : cst := cstep s (tc m).
Definition tcost (m : tmove) : nat := ccost (tc m).
Lemma ttoll : forall s m, cflag s = false -> cflag (tstep s m) = true -> tcost m >= 1.
Proof. intros s m. apply ctoll. Qed.

Definition tnext (P : list tmove) (s : cst) : option tmove :=
  match (match cpc s with 0 => None | S k => nth_error P k end) with Some THalt => None | o => o end.

Definition CNT : host := mk_host cst tmove tstep tcost cflag ttoll (list tmove) tnext.

Definition cnt_reg : reg_host CNT.
Proof.
  refine (mk_rh CNT cpc creg (fun _ => false) (fun m => ckind (tc m)) _ _ _ _ _ _ _ _).
  - intros [r | r j | | |]; reflexivity.
  - intros s m E. discriminate E.
  - intros s m r _ K. destruct m; simpl in K; try discriminate. injection K as ->. simpl. auto.
  - intros s m r j _ K. destruct m; simpl in K; try discriminate. injection K as -> ->.
    simpl. unfold tstep. simpl. destruct (creg s r); simpl; auto.
  - intros s m K. destruct m; simpl in K; try discriminate. simpl. auto.
  - intros s m _ K. destruct m; simpl in K; try discriminate; simpl; auto.
  - intros P s1 s2 _ Hp. simpl. unfold tnext. rewrite Hp. reflexivity.
  - intros P s E. discriminate E.
Defined.

Fixpoint ticks (tr : list tmove) : bool :=
  match tr with [] => false | TTick :: _ => true | _ :: r => ticks r end.

Lemma cnt_record_run : forall tr s, cflag s = false -> cflag (run (hmach CNT) tr s) = ticks tr.
Proof.
  induction tr as [| m tr IH]; intros s H; [exact H |].
  destruct m as [r | r j | | |]; simpl.
  - apply IH. exact H.
  - apply IH. unfold tstep. simpl. destruct (creg s r); exact H.
  - apply IH. exact H.
  - assert (E : forall l t, cflag t = true -> cflag (run (hmach CNT) l t) = true).
    { induction l as [| a l IHl]; intros t Ht; [exact Ht |]. simpl. apply IHl.
      unfold tstep. apply cnh_perm. exact Ht. }
    apply E. reflexivity.
  - apply IH. exact H.
Qed.

Theorem cnt_not_nc : ~ neutral_complete (hmach CNT).
Proof.
  intros [J [_ [Hs [_ [tr [a [b [a' [b' [H1 H2]]]]]]]]]].
  change (cflag (run (hmach CNT) tr (nload J a b)) = true) in H1.
  change (cflag (run (hmach CNT) tr (nload J a' b')) = false) in H2.
  rewrite (cnt_record_run tr _ (Hs a b)) in H1. rewrite (cnt_record_run tr _ (Hs a' b')) in H2.
  congruence.
Qed.

Definition Pt : list tmove := [TDec 0 1; TTick; THalt].

Lemma cnt_hr : forall n, hr (H:=CNT) Pt (ctpl (dcode 1)) n = hr (H:=CNH) Pd (ctpl (dcode 1)) n /\
                         hl (H:=CNT) Pt (ctpl (dcode 1)) n = hl (H:=CNH) Pd (ctpl (dcode 1)) n.
Proof.
  intros n. destruct n as [| [| [| [| n]]]]; split; reflexivity.
Qed.

Theorem need_N0 :
  ~ host_nc CNT cnt_reg /\
  line_raise CNT cnt_reg Pt draise /\ clean_template CNT cnt_reg ctpl /\
  halt_clause C1 CNT O2 o2 0 Pt (ctpl (dcode 1)) tt (fun h => d2 (b_reg cnt_reg h)) /\
  in_order C1 CNT O2 o2 0 Pt (ctpl (dcode 1)) tt (fun h => d2 (b_reg cnt_reg h)) (fun m => m).
Proof.
  split; [intros [J [HJ _]]; exact (cnt_not_nc (ex_intro _ J HJ)) |].
  split.
  { intros [p r f l] m _ Hn K. right. simpl in *. unfold tnext in Hn.
    destruct p as [| [| [| [| p]]]]; simpl in Hn; try discriminate.
    - injection Hn as <-. discriminate K.
    - injection Hn as <-. simpl. rewrite orb_true_r. reflexivity.
    - destruct p; discriminate Hn. }
  split; [repeat split |].
  assert (M : forall m, m <= 3 -> match_at C1 CNT O2 o2 0 Pt (ctpl (dcode 1)) tt
                                     (fun h => d2 (b_reg cnt_reg h)) m m).
  { intros m Hm. unfold match_at. destruct (cnt_hr m) as [A B]. rewrite A, B.
    destruct m as [| [| [| [|]]]]; try lia; fin_match. }
  split; [split |].
  - split; intros _; [exists 3; exact C1_stop | exists 3; reflexivity].
  - intros m0 Hl Hs. rewrite (C1_stop_only m0 Hl Hs). exists 3. split; [reflexivity | apply M; lia].
  - split; [intros; lia | intros m Hl; apply M, C1_live, Hl].
Qed.

(* ================================================================= *)
(* (N4) is needed: the hybrid host.                                   *)
(* ================================================================= *)

(* CNH plus GEX, a free primitive that fetches the guest's instruction at
   the guest line kept in register 2 (guest program Qd), decodes it and,
   if it is a DEC, executes it on the registers (the host line stays);
   on a MARK or HALT it moves the host to its next line; on no
   instruction it does nothing. *)
Inductive xmove : Type := XC (m : cmove) | GEX.

Definition gex (s : cst) : cst :=
  match cfetch Qd (creg s 2) with
  | Some (CDec r j) =>
      match creg s r with
      | 0 => mkcs (cpc s) (upd (creg s) 2 (S (creg s 2))) (cflag s) (cled s)
      | S n => mkcs (cpc s) (upd (upd (creg s) r n) 2 j) (cflag s) (cled s)
      end
  | Some _ => mkcs (S (cpc s)) (creg s) (cflag s) (cled s)
  | None => s
  end.

Definition xstep (s : cst) (m : xmove) : cst := match m with XC c => cstep s c | GEX => gex s end.
Definition xcost (m : xmove) : nat := match m with XC c => ccost c | GEX => 0 end.

Lemma gex_flag : forall s, cflag (gex s) = cflag s.
Proof.
  intros s. unfold gex. destruct (cfetch Qd (creg s 2)) as [[] |]; try reflexivity.
  destruct (creg s r); reflexivity.
Qed.

Lemma xtoll : forall s m, cflag s = false -> cflag (xstep s m) = true -> xcost m >= 1.
Proof. intros s [c |] H0 H1; simpl in *; [exact (ctoll s c H0 H1) | rewrite gex_flag in H1; congruence]. Qed.

Definition xnext (P : list xmove) (s : cst) : option xmove :=
  match (match cpc s with 0 => None | S k => nth_error P k end) with Some (XC CHalt) => None | o => o end.

Definition HX : host := mk_host cst xmove xstep xcost cflag xtoll (list xmove) xnext.

(* A register reading without the counter-move requirement. *)
Record rview (H : host) : Type := mk_rv {
  v_pc : hS H -> nat; v_reg : hS H -> nat -> nat; v_err : hS H -> bool;
  v_next : forall P s1 s2, v_err s1 = v_err s2 -> v_pc s1 = v_pc s2 -> hnext H P s1 = hnext H P s2;
  v_rec : forall s m, hcost H m = 1 -> v_err s = false ->
            (forall x, v_reg (hstep H s m) x = v_reg s x) /\
            (v_err (hstep H s m) = true \/ v_pc (hstep H s m) = S (v_pc s));
  v_cost : forall m, hcost H m <= 1 }.

Definition hx_view : rview HX.
Proof.
  refine (mk_rv HX cpc creg (fun _ => false) _ _ _).
  - intros P s1 s2 _ Hp. simpl. unfold xnext. rewrite Hp. reflexivity.
  - intros s [[r | r j | | r | |] |] Hc _; simpl in Hc; try discriminate; simpl; auto.
  - intros [[] |]; simpl; lia.
Defined.

Definition hx_base : universal_base (hmach HX).
Proof.
  refine (mk_ub (hmach HX) cwin (fun _ => True) (fun i => XC (ccompile i)) cload _ _ _).
  - intros a b. reflexivity.
  - intros a b. exact I.
  - intros s i _. split; [| exact I]. exact (proj1 (ub_sim cnh_base s i I)).
Defined.

Definition hx_iface : neutral_interface (hmach HX) :=
  mk_ni (hmach HX) hx_base (fun m => Nat.eqb (xcost m) 0) cled.

Theorem hx_nc : neutral_complete_with hx_iface.
Proof.
  split; [| split; [| split]].
  - split; [intros [[|] | [|] j]; reflexivity |]. split.
    + intros s [c |] Hb; simpl in *; [| apply gex_flag].
      apply cnh_counter_blind. destruct c; simpl in *; discriminate.
    + intros s [c |] H; simpl in *; [apply cnh_perm, H | rewrite gex_flag; exact H].
  - intros a b. reflexivity.
  - split.
    + intros [[r | r j | | r | |] |]; reflexivity.
    + intros [p r f l] [[x | x j | | x | |] |]; simpl; try lia.
      * destruct (r x); simpl; lia.
      * unfold gex. simpl. destruct (cfetch Qd (r 2)) as [[] |]; simpl; try lia.
        destruct (r r0); simpl; lia.
  - exists [XC (CMark 0)], 1, 0, 0, 0. split; reflexivity.
Qed.

Definition xcode : nat -> nat := fun x => match x with 0 => 1 | 1 => 1 | 2 => 1 | _ => 0 end.
Definition PX : list xmove := [GEX; XC CTick; XC CHalt].
Definition xf (m : nat) : nat := match m with 3 => 4 | _ => m end.

Theorem hx_not_reg : reg_host HX -> False.
Proof.
  intros R. apply (not_counter HX R GEX eq_refl).
  - exists (mkcs 1 (fun _ => 0) false 0), PX. split; [reflexivity | discriminate].
  - exists (mkcs 1 (fun x => match x with 2 => 2 | _ => 0 end) false 0), PX.
    split; [simpl; discriminate | discriminate].
Qed.

Theorem need_N4 :
  neutral_complete_with hx_iface /\
  (forall m, hcost HX m = 0 -> m_cost (hmach HX) m = 0) /\
  (forall s m, v_err HX hx_view s = false -> hnext HX PX s = Some m -> hcost HX m = 1 ->
     hflag HX (hstep HX s m) = hflag HX s || Nat.eqb (v_pc HX hx_view s) 2) /\
  halt_clause C1 HX O2 o2 0 PX (mkcs 1 xcode false 0) tt (fun h => d2 (v_reg HX hx_view h)) /\
  in_order C1 HX O2 o2 0 PX (mkcs 1 xcode false 0) tt (fun h => d2 (v_reg HX hx_view h)) xf /\
  ~ inhabited (reg_host HX).
Proof.
  split; [exact hx_nc |]. split; [intros m H; exact H |]. split.
  { intros [p r f l] m _ Hn Hc. simpl in *. unfold xnext in Hn.
    destruct p as [| [| [| [| p]]]]; simpl in Hn; try discriminate.
    - injection Hn as <-. discriminate Hc.
    - injection Hn as <-. simpl. rewrite orb_true_r. reflexivity.
    - destruct p; discriminate Hn. }
  assert (M : forall m, m <= 3 -> match_at C1 HX O2 o2 0 PX (mkcs 1 xcode false 0) tt
                                     (fun h => d2 (v_reg HX hx_view h)) (xf m) m).
  { intros m Hm. destruct m as [| [| [| [|]]]]; try lia; fin_match. }
  split; [split |]; [| | split; [| intros [R]; exact (hx_not_reg R)]].
  - split; intros _; [exists 3; exact C1_stop | exists 4; reflexivity].
  - intros m0 Hl Hs. rewrite (C1_stop_only m0 Hl Hs). exists 4. split; [reflexivity | apply (M 3); lia].
  - split; [intros m Hl; pose proof (C1_live (S m) Hl); destruct m as [| [| [|]]]; simpl; lia |].
    intros m Hl. apply M, C1_live, Hl.
Qed.

Print Assumptions need_N1.
Print Assumptions need_order.
Print Assumptions need_decode.
Print Assumptions need_record.
Print Assumptions need_ledger.
Print Assumptions need_clean.
Print Assumptions up_floor.
Print Assumptions up_attained.
Print Assumptions cnt_not_nc.
Print Assumptions need_N0.
Print Assumptions hx_not_reg.
Print Assumptions need_N4.
