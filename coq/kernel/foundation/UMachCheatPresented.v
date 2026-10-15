(** UMachCheatPresented.v: the cheat for U_P's class.  One fixed host and one
    fixed 14-line program run every computably presented Thiele machine
    (in fact every presented machine; the presentation is never used) and
    meet UMachDef.universal_thiele (the in-order form of the plain definition)
    with surcharge bound 1 over the whole class, and exactly 0 at every
    matching point when the reading starts at no.  The load is CLEAN (flag
    down, ledger 0, as U_P's load is).  U_P's proved bound is 3 (2 when the
    reading starts at no).

    And U_P meets the weak (order-free) form with K = 3, from the
    presented_universal theorems of PresentedUniversal.v.                        *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Minimal.Presented.
Require Import Kernel.Presentation.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

(* ================================================================= *)
(* Generic: a guest is live up to n, or it stopped at a first m0 < n. *)
(* ================================================================= *)

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

Lemma glatch_read : forall (C : gclass) (i : gi C) s n, gread C i (gr s n) = true -> glatch s n = true.
Proof.
  intros C i s [| n] H; [exact H |].
  change (glatch s (S n)) with (glatch s n || gread C i (gr s (S n))).
  rewrite H. apply orb_true_r.
Qed.

(* ================================================================= *)
(* U_P's class: computably presented machines with a start.           *)
(* ================================================================= *)

Definition pinst : Type :=
  { Mp : presented_machine & (cg_presentation Mp * T.cs_state (pm_sys Mp))%type }.

Definition presented_class : gclass :=
  mk_gclass pinst
    (fun i => T.cs_state (pm_sys (projT1 i)))
    (fun i => T.cs_instr (pm_sys (projT1 i)))
    (fun i => pm_next (projT1 i))
    (fun i => T.cs_step (pm_sys (projT1 i)))
    (fun i => T.cs_cost (pm_sys (projT1 i)))
    (fun i => T.cs_cert (pm_sys (projT1 i)))
    (fun i => T.cs_cert_costs (pm_sys (projT1 i)))
    (fun i => snd (projT2 i)).

(* ================================================================= *)
(* The cheat host.                                                    *)
(* ================================================================= *)

Inductive pmove : Type :=
| PEEKR                 (* r := 1 if the guest's reading is yes and the flag is down *)
| BRR (j0 j1 : nat)     (* pc := j_r                                               *)
| LATCH                 (* price 1: flag := flag || reading                        *)
| PEEK                  (* r := 0 if the driver says stop, else price + 1          *)
| DECJ (j : nat)        (* if r = 0 then pc := j else r := r - 1                   *)
| JMP (j : nat)
| PAY                   (* price 1, nothing else                                   *)
| GMOVE0                (* the driver's move if its price is 0, else trap          *)
| GMOVE1                (* price 1: the driver's move if its price is >= 1, else trap;
                           flag := flag || reading of the new state                *)
| STOP.

Definition pcost (m : pmove) : nat :=
  match m with LATCH | PAY | GMOVE1 => 1 | _ => 0 end.

Record pst : Type := mkp {
  ppc : nat; pr : nat; pM : presented_machine; ps : T.cs_state (pm_sys pM);
  pmir : bool; perr : bool }.

Definition pexec (h : pst) (m : pmove) : pst :=
  if perr h then h else
  let M := pM h in
  match m with
  | PEEKR => mkp (S (ppc h)) (if T.cs_cert (pm_sys M) (ps h) && negb (pmir h) then 1 else 0)
                 M (ps h) (pmir h) false
  | BRR j0 j1 => mkp (match pr h with 0 => j0 | _ => j1 end) (pr h) M (ps h) (pmir h) false
  | LATCH => mkp (S (ppc h)) (pr h) M (ps h) (pmir h || T.cs_cert (pm_sys M) (ps h)) false
  | PEEK => mkp (S (ppc h))
                (match pm_next M (ps h) with None => 0 | Some mv => S (T.cs_cost (pm_sys M) mv) end)
                M (ps h) (pmir h) false
  | DECJ j => match pr h with
              | 0 => mkp j 0 M (ps h) (pmir h) false
              | S r => mkp (S (ppc h)) r M (ps h) (pmir h) false
              end
  | JMP j => mkp j (pr h) M (ps h) (pmir h) false
  | PAY => mkp (S (ppc h)) (pr h) M (ps h) (pmir h) false
  | GMOVE0 =>
      match pm_next M (ps h) with
      | Some mv => if Nat.eqb (T.cs_cost (pm_sys M) mv) 0
                   then mkp (S (ppc h)) (pr h) M (T.cs_step (pm_sys M) (ps h) mv) (pmir h) false
                   else mkp (ppc h) (pr h) M (ps h) (pmir h) true
      | None => mkp (ppc h) (pr h) M (ps h) (pmir h) true
      end
  | GMOVE1 =>
      match pm_next M (ps h) with
      | Some mv => if Nat.leb 1 (T.cs_cost (pm_sys M) mv)
                   then mkp (S (ppc h)) (pr h) M (T.cs_step (pm_sys M) (ps h) mv)
                            (pmir h || T.cs_cert (pm_sys M) (T.cs_step (pm_sys M) (ps h) mv)) false
                   else mkp (ppc h) (pr h) M (ps h) (pmir h) true
      | None => mkp (ppc h) (pr h) M (ps h) (pmir h) true
      end
  | STOP => h
  end.

Theorem pcheat_toll : forall h m, pmir h = false -> pmir (pexec h m) = true -> pcost m >= 1.
Proof.
  intros [pc r M s mir er] m H0 H1. simpl in H0. subst mir.
  unfold pexec in H1. simpl in H1. destruct er; [discriminate |].
  destruct m; simpl; try lia; exfalso;
  repeat match goal with
         | H : context [match ?x with _ => _ end] |- _ => destruct x; simpl in H
         end; discriminate.
Qed.

Definition pnext (Q : list pmove) (h : pst) : option pmove :=
  if perr h then None else
  match nth_error Q (pred (ppc h)) with Some STOP => None | o => if Nat.eqb (ppc h) 0 then None else o end.

Definition pcheat_host : host :=
  mk_host pst pmove pexec pcost pmir pcheat_toll (list pmove) pnext.

(* The one fixed program. *)
Definition PB : list pmove :=
  [PEEKR; BRR 4 3; LATCH;                                  (* 1-3  start block   *)
   PEEK; DECJ 14; DECJ 12; DECJ 10; PAY; JMP 7;            (* 4-9  peek and pay  *)
   GMOVE1; JMP 4; GMOVE0; JMP 4; STOP].                    (* 10-14              *)

Definition pload (i : pinst) : pst := mkp 1 0 (projT1 i) (snd (projT2 i)) false false.

(* ================================================================= *)
(* Stepping lemmas.                                                   *)
(* ================================================================= *)

Lemma hr_cons : forall Q h m n, pnext Q h = Some m ->
  hr (H:=pcheat_host) Q h (S n) = hr (H:=pcheat_host) Q (pexec h m) n.
Proof. intros Q h m n E. simpl. change (hnext pcheat_host) with pnext. rewrite E. reflexivity. Qed.

Lemma hl_cons : forall Q h m n, pnext Q h = Some m ->
  hl (H:=pcheat_host) Q h (S n) = pcost m + hl (H:=pcheat_host) Q (pexec h m) n.
Proof. intros Q h m n E. simpl. change (hnext pcheat_host) with pnext. rewrite E. reflexivity. Qed.

Ltac stp m := rewrite (hr_cons _ _ m), (hl_cons _ _ m) by reflexivity.

(* The PAY loop: at line 7 with r = k, 3k+1 moves pay k and reach line 10. *)
Lemma pay_loop : forall k M s mir,
  hr (H:=pcheat_host) PB (mkp 7 k M s mir false) (3 * k + 1) = mkp 10 0 M s mir false /\
  hl (H:=pcheat_host) PB (mkp 7 k M s mir false) (3 * k + 1) = k.
Proof.
  induction k as [| k IH]; intros M s mir.
  - simpl. split; reflexivity.
  - replace (3 * S k + 1) with (S (S (S (3 * k + 1)))) by lia.
    stp (DECJ 10). cbn [pexec perr pr ppc pM ps pmir].
    stp PAY. cbn [pexec perr pr ppc pM ps pmir].
    stp (JMP 7). cbn [pexec perr pr ppc pM ps pmir].
    destruct (IH M s mir) as [A B]. rewrite A, B. split; [reflexivity | simpl; lia].
Qed.

Definition roundlen (M : presented_machine) (s : T.cs_state (pm_sys M)) : nat :=
  match pm_next M s with
  | None => 0
  | Some mv => if Nat.eqb (T.cs_cost (pm_sys M) mv) 0 then 5 else 3 * T.cs_cost (pm_sys M) mv + 3
  end.

(* One round from line 4: one driven move of M, paid exactly. *)
Lemma round : forall M s r mv,
  pm_next M s = Some mv ->
  let s' := T.cs_step (pm_sys M) s mv in
  forall mir, (T.cs_cert (pm_sys M) s' = true -> T.cs_cost (pm_sys M) mv = 0 -> mir = true) ->
  hr (H:=pcheat_host) PB (mkp 4 r M s mir false) (roundlen M s) =
    mkp 4 0 M s' (mir || T.cs_cert (pm_sys M) s') false /\
  hl (H:=pcheat_host) PB (mkp 4 r M s mir false) (roundlen M s) = T.cs_cost (pm_sys M) mv.
Proof.
  intros M s r mv Hn s' mir Hm. unfold roundlen. rewrite Hn.
  destruct (T.cs_cost (pm_sys M) mv) as [| c] eqn:Hc.
  - simpl Nat.eqb. cbv iota.
    stp PEEK. cbn [pexec perr pr ppc pM ps pmir]. rewrite ?Hn, ?Hc. cbn [pexec perr pr ppc pM ps pmir].
    stp (DECJ 14). cbn [pexec perr pr ppc pM ps pmir].
    stp (DECJ 12). cbn [pexec perr pr ppc pM ps pmir].
    stp GMOVE0. cbn [pexec perr pr ppc pM ps pmir]. rewrite ?Hn, ?Hc. cbn [pexec perr pr ppc pM ps pmir]. simpl Nat.eqb.
    cbv iota.
    stp (JMP 4). cbn [pexec perr pr ppc pM ps pmir].
    simpl. fold s'.
    destruct (T.cs_cert (pm_sys M) s') eqn:Hr.
    + rewrite (Hm eq_refl eq_refl). split; reflexivity.
    + rewrite orb_false_r. split; reflexivity.
  - replace (if Nat.eqb (S c) 0 then 5 else 3 * S c + 3) with (S (S (S (3 * c + 1 + 2)))) by
      (simpl; lia).
    stp PEEK. cbn [pexec perr pr ppc pM ps pmir]. rewrite ?Hn, ?Hc. cbn [pexec perr pr ppc pM ps pmir].
    stp (DECJ 14). cbn [pexec perr pr ppc pM ps pmir].
    stp (DECJ 12). cbn [pexec perr pr ppc pM ps pmir].
    rewrite (hr_add pcheat_host PB), (hl_add pcheat_host PB).
    destruct (pay_loop c M s mir) as [A B]. rewrite A, B.
    stp GMOVE1. cbn [pexec perr pr ppc pM ps pmir]. rewrite ?Hn, ?Hc. cbn [pexec perr pr ppc pM ps pmir].
    simpl Nat.leb. cbv iota.
    stp (JMP 4). cbn [pexec perr pr ppc pM ps pmir].
    simpl. fold s'. split; [reflexivity | lia].
Qed.

(* ================================================================= *)
(* Matching points.                                                   *)
(* ================================================================= *)

Definition start_len (i : pinst) : nat :=
  if T.cs_cert (pm_sys (projT1 i)) (snd (projT2 i)) then 3 else 2.
Definition start_fee (i : pinst) : nat :=
  if T.cs_cert (pm_sys (projT1 i)) (snd (projT2 i)) then 1 else 0.

Fixpoint fpt (i : pinst) (m : nat) : nat :=
  match m with
  | 0 => start_len i
  | S m' => fpt i m' + roundlen (projT1 i) (grun (C:=presented_class) i m')
  end.

Lemma start_block : forall i,
  hr (H:=pcheat_host) PB (pload i) (start_len i) =
    mkp 4 (start_fee i) (projT1 i) (snd (projT2 i)) (glat (C:=presented_class) i 0) false /\
  hl (H:=pcheat_host) PB (pload i) (start_len i) = start_fee i.
Proof.
  intros [M [pc s0]]. unfold start_len, start_fee, pload, glat. simpl projT1; simpl projT2.
  simpl snd. simpl glatch. simpl gstart. simpl gread.
  destruct (T.cs_cert (pm_sys M) s0) eqn:Hr;
    cbn; rewrite ?Hr; cbn; rewrite ?Hr; cbn; rewrite ?Hr; cbn; split; reflexivity.
Qed.

Lemma points : forall (i : pinst) m, live_before (C:=presented_class) i m ->
  exists r,
    hr (H:=pcheat_host) PB (pload i) (fpt i m) =
      mkp 4 r (projT1 i) (grun (C:=presented_class) i m) (glat (C:=presented_class) i m) false /\
    hl (H:=pcheat_host) PB (pload i) (fpt i m) = gledger (C:=presented_class) i m + start_fee i.
Proof.
  intros i m. induction m as [| m IH]; intros Hl.
  - exists (start_fee i). simpl fpt. destruct (start_block i) as [A B]. rewrite A, B.
    split; reflexivity.
  - destruct IH as (r & Hh & Hle). { intros k Hk. apply Hl. lia. }
    assert (Hn : gnext presented_class i (grun (C:=presented_class) i m) <> None) by (apply Hl; lia).
    destruct (gnext presented_class i (grun (C:=presented_class) i m)) as [mv |] eqn:Ej;
      [| congruence].
    simpl in Ej.
    destruct (round (projT1 i) (grun (C:=presented_class) i m) r mv Ej
                (glat (C:=presented_class) i m)) as [R1 R2].
    { intros Hr Hc.
      destruct (T.cs_cert (pm_sys (projT1 i)) (grun (C:=presented_class) i m)) eqn:H0.
      - unfold glat. apply (glatch_read presented_class i). exact H0.
      - pose proof (T.cs_cert_costs (pm_sys (projT1 i)) _ mv H0 Hr) as X. lia. }
    exists 0. simpl fpt. rewrite (hr_add pcheat_host PB), (hl_add pcheat_host PB), Hh, R1, R2, Hle.
    unfold grun, gledger, glat.
    rewrite (gr_succ presented_class i m), (gl_succ presented_class i m).
    fold (grun (C:=presented_class) i m). simpl gnext. rewrite Ej.
    split; [| simpl; lia].
    change (glatch (gstart presented_class i) (S m)) with
      (glatch (gstart presented_class i) m ||
       gread presented_class i (gr (gstart presented_class i) (S m))).
    rewrite (gr_succ presented_class i m). fold (grun (C:=presented_class) i m).
    simpl gnext. rewrite Ej. reflexivity.
Qed.

Lemma fpt_ge : forall i m, live_before (C:=presented_class) i m -> m <= fpt i m.
Proof.
  intros i m. induction m as [| m IH]; intros Hl; [lia |].
  simpl. assert (Hn : gnext presented_class i (grun (C:=presented_class) i m) <> None) by (apply Hl; lia).
  unfold roundlen. simpl in Hn.
  destruct (pm_next (projT1 i) (grun (C:=presented_class) i m)); [| congruence].
  destruct (Nat.eqb _ 0); specialize (IH (fun k Hk => Hl k ltac:(lia))); lia.
Qed.

(* ================================================================= *)
(* The theorem.                                                       *)
(* ================================================================= *)

Definition pobs (i : pinst) (s : T.cs_state (pm_sys (projT1 i))) : option (T.cs_state (pm_sys (projT1 i))) :=
  Some s.

(* Decode through the machine's own state code, as U_P's decode does. *)
Definition pdecode (i : pinst) (h : pst) : option (T.cs_state (pm_sys (projT1 i))) :=
  pm_sdec (projT1 i) (pm_scode (pM h) (ps h)).

Theorem pcheat_is_universal :
  universal_thiele presented_class pcheat_host
    (fun i => option (T.cs_state (pm_sys (projT1 i)))) pobs 1.
Proof.
  exists PB, pload, pdecode. intros i. split; [| split].
  - unfold clause1. split.
    + intros [n Hn].
      destruct (live_or_stop_gen presented_class i (S n)) as [Hl | (m0 & _ & Hs & _)];
        [| exists m0; exact Hs].
      exfalso. assert (Hl' : live_before (C:=presented_class) i n) by (intros k Hk; apply Hl; lia).
      destruct (points i n Hl') as (r & Hh & _).
      rewrite <- (hr_stopped_stays pcheat_host PB (pload i) n (fpt i n)) in Hn
        by (apply fpt_ge, Hl' || exact Hn).
      rewrite Hh in Hn. discriminate.
    + intros [m Hm].
      destruct (live_or_stop_gen presented_class i (S m)) as [Hl | (m0 & _ & Hs & Hl0)].
      { exfalso. exact (Hl m ltac:(lia) Hm). }
      destruct (points i m0 Hl0) as (r & Hh & _).
      exists (fpt i m0 + 2). rewrite (hr_add pcheat_host PB), Hh. simpl in Hs.
      rewrite (hr_cons _ _ PEEK) by reflexivity.
      cbn [pexec perr pr ppc pM ps pmir]. rewrite Hs.
      rewrite (hr_cons _ _ (DECJ 14)) by reflexivity. reflexivity.
  - exists (fpt i). split.
    + intros m Hl. simpl. unfold roundlen.
      assert (Hn : gnext presented_class i (grun (C:=presented_class) i m) <> None) by (apply Hl; lia).
      simpl in Hn. destruct (pm_next (projT1 i) _); [| congruence].
      destruct (Nat.eqb _ 0); lia.
    + intros m Hl. destruct (points i m Hl) as (r & Hh & Hle).
      unfold match_at. simpl hP in *. rewrite Hle, Hh. split; [| split].
      * unfold pdecode, pobs. simpl. apply pm_sdec_scode.
      * reflexivity.
      * exists (start_fee i). split; [unfold start_fee; destruct (T.cs_cert _ _); lia | lia].
  - intros n. apply clause3_free.
Qed.

(* Surcharge 0 at every matching point when the reading starts at no. *)
Theorem pcheat_exact_when_no_at_start : forall i m,
  T.cs_cert (pm_sys (projT1 i)) (snd (projT2 i)) = false ->
  live_before (C:=presented_class) i m ->
  hl (H:=pcheat_host) PB (pload i) (fpt i m) = gledger (C:=presented_class) i m /\
  pmir (hr (H:=pcheat_host) PB (pload i) (fpt i m)) = glat (C:=presented_class) i m.
Proof.
  intros i m H0 Hl. destruct (points i m Hl) as (r & Hh & Hle).
  rewrite Hle, Hh. unfold start_fee. rewrite H0. split; [lia | reflexivity].
Qed.

(* No host at all, with a load whose flag is down, can do better than 1
   on a guest whose reading is yes at the start: clause (2) at m = 0 needs
   the flag up while M's ledger is 0, and raising it costs at least 1. *)
Theorem one_is_forced : forall (Hh : host) (P : hP Hh) (h0 : hS Hh) n,
  hflag Hh h0 = false -> hflag Hh (hr P h0 n) = true -> hl P h0 n >= 1.
Proof.
  intros Hh P h0 n. revert h0. induction n as [| n IH]; intros h0 H0 H1; simpl in *; [congruence |].
  destruct (hnext Hh P h0) as [m |] eqn:E; [| congruence].
  destruct (hflag Hh (hstep Hh h0 m)) eqn:F.
  - pose proof (htoll Hh h0 m H0 F). lia.
  - pose proof (IH _ F H1). lia.
Qed.

Print Assumptions pcheat_toll.
Print Assumptions pcheat_is_universal.
Print Assumptions pcheat_exact_when_no_at_start.
Print Assumptions one_is_forced.
