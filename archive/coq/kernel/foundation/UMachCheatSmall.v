(** UMachCheatSmall.v: a host with a built-in guest step (PEEK, GSTEP0, GSTEP1)
    and a five-line loop is a universal Thiele machine, in the sense of
    UMachDef.universal_thiele (the strong, in-order form of the plain definition),
    for the class U serves (every small-machine program P from every clean
    start (x, y)), with surcharge 0 and decode the identity (or any
    observation at all).  *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.
Require Import Kernel.UMachDef.

(* ================================================================= *)
(* The guest class of U: small-machine programs from clean starts.    *)
(* ================================================================= *)

Definition sinst : Type := (list E.instr * nat * nat)%type.

Definition small_class : gclass :=
  mk_gclass sinst (fun _ => E.state) (fun _ => E.instr)
    (fun i s => E.next_instr (fst (fst i)) (E.core_of s))
    (fun _ => E.exec) (fun _ => E.cost) (fun _ => E.cert)
    (fun _ => E.a2)
    (fun i => E.start (snd (fst i)) (snd i)).

(* ================================================================= *)
(* The cheat host.                                                    *)
(* ================================================================= *)

Inductive cmove : Type :=
| PEEK                      (* r := 2 if the guest has stopped, else its next price *)
| BR (j0 j1 j2 : nat)       (* pc := j_r                                            *)
| GSTEP0                    (* one guest step if its price is 0, else trap          *)
| GSTEP1                    (* one guest step if its price is 1, else trap          *)
| STOP.

Definition ccost (m : cmove) : nat := match m with GSTEP1 => 1 | _ => 0 end.

Record cst : Type := mkc {
  cpc : nat; cr : nat; cP : list E.instr; cg : E.state; cmir : bool; cerr : bool }.

Definition peek (h : cst) : nat :=
  match E.next_instr (cP h) (E.core_of (cg h)) with None => 2 | Some i => E.cost i end.

Definition cexec (h : cst) (m : cmove) : cst :=
  if cerr h then h else
  match m with
  | PEEK => mkc (S (cpc h)) (peek h) (cP h) (cg h) (cmir h) false
  | BR j0 j1 j2 =>
      mkc (match cr h with 0 => j0 | 1 => j1 | _ => j2 end) (cr h) (cP h) (cg h) (cmir h) false
  | GSTEP0 =>
      match E.next_instr (cP h) (E.core_of (cg h)) with
      | Some i => if Nat.eqb (E.cost i) 0
                  then mkc (S (cpc h)) (cr h) (cP h) (E.exec (cg h) i) (cmir h) false
                  else mkc (cpc h) (cr h) (cP h) (cg h) (cmir h) true
      | None => mkc (cpc h) (cr h) (cP h) (cg h) (cmir h) true
      end
  | GSTEP1 =>
      match E.next_instr (cP h) (E.core_of (cg h)) with
      | Some i => if Nat.eqb (E.cost i) 1
                  then mkc (S (cpc h)) (cr h) (cP h) (E.exec (cg h) i)
                           (cmir h || (negb (E.cert (cg h)) && E.cert (E.exec (cg h) i))) false
                  else mkc (cpc h) (cr h) (cP h) (cg h) (cmir h) true
      | None => mkc (cpc h) (cr h) (cP h) (cg h) (cmir h) true
      end
  | STOP => h
  end.

(* The toll, on every state and move: the flag (the mirror) rises only in
   a GSTEP1, which costs 1. *)
Theorem cheat_toll : forall h m, cmir h = false -> cmir (cexec h m) = true -> ccost m >= 1.
Proof.
  intros [pc r P g mir er] m H0 H1. simpl in H0. subst mir.
  unfold cexec in H1. simpl in H1. destruct er; [simpl in H1; discriminate |].
  destruct m; simpl in H1; try discriminate; simpl; try lia.
  destruct (E.next_instr P (E.core_of g)) as [i |]; [| discriminate].
  destruct (Nat.eqb (E.cost i) 0); discriminate.
Qed.

Definition cnext (Q : list cmove) (h : cst) : option cmove :=
  if cerr h then None else
  match E.fetch Q (cpc h) with Some STOP => None | o => o end.

Definition cheat_host : host :=
  mk_host cst cmove cexec ccost cmir cheat_toll (list cmove) cnext.

(* The one fixed program. *)
Definition CHEAT : list cmove :=
  [PEEK; BR 3 5 7; GSTEP0; BR 1 1 1; GSTEP1; BR 1 1 1; STOP].

Definition cload (i : sinst) : cst :=
  mkc 1 0 (fst (fst i)) (E.start (snd (fst i)) (snd i)) false false.

(* ================================================================= *)
(* One round: four host moves per guest step.                         *)
(* ================================================================= *)

Lemma cert_exec_cost0 : forall g i, E.cost i = 0 -> E.cert (E.exec g i) = E.cert g.
Proof.
  intros g i Hc. rewrite E.cert_latch. destruct i; simpl in Hc; try discriminate;
  simpl; apply orb_false_r.
Qed.

Lemma ex_peek : forall pc r P g mir i, E.next_instr P (E.core_of g) = Some i ->
  cexec (mkc pc r P g mir false) PEEK = mkc (S pc) (E.cost i) P g mir false.
Proof. intros. unfold cexec, peek. simpl cerr. cbv iota beta. simpl. rewrite H. reflexivity. Qed.

Lemma ex_peek_stop : forall pc r P g mir, E.next_instr P (E.core_of g) = None ->
  cexec (mkc pc r P g mir false) PEEK = mkc (S pc) 2 P g mir false.
Proof. intros. unfold cexec, peek. simpl. rewrite H. reflexivity. Qed.

Lemma ex_g0 : forall pc r P g mir i, E.next_instr P (E.core_of g) = Some i -> E.cost i = 0 ->
  cexec (mkc pc r P g mir false) GSTEP0 = mkc (S pc) r P (E.exec g i) mir false.
Proof. intros. unfold cexec. simpl. rewrite H, H0. reflexivity. Qed.

Lemma ex_g1 : forall pc r P g mir i, E.next_instr P (E.core_of g) = Some i -> E.cost i = 1 ->
  cexec (mkc pc r P g mir false) GSTEP1 =
  mkc (S pc) r P (E.exec g i) (mir || (negb (E.cert g) && E.cert (E.exec g i))) false.
Proof. intros. unfold cexec. simpl. rewrite H, H0. reflexivity. Qed.

Lemma ex_br : forall pc r P g mir j0 j1 j2,
  cexec (mkc pc r P g mir false) (BR j0 j1 j2) =
  mkc (match r with 0 => j0 | 1 => j1 | _ => j2 end) r P g mir false.
Proof. reflexivity. Qed.

Lemma hr_cons : forall Q h m n, cnext Q h = Some m ->
  hr (H:=cheat_host) Q h (S n) = hr (H:=cheat_host) Q (cexec h m) n.
Proof. intros Q h m n E. simpl. change (hnext cheat_host) with cnext. rewrite E. reflexivity. Qed.

Lemma hl_cons : forall Q h m n, cnext Q h = Some m ->
  hl (H:=cheat_host) Q h (S n) = ccost m + hl (H:=cheat_host) Q (cexec h m) n.
Proof. intros Q h m n E. simpl. change (hnext cheat_host) with cnext. rewrite E. reflexivity. Qed.

Lemma round : forall r P g i,
  E.next_instr P (E.core_of g) = Some i ->
  hr (H:=cheat_host) CHEAT (mkc 1 r P g (E.cert g) false) 4 =
    mkc 1 (E.cost i) P (E.exec g i) (E.cert (E.exec g i)) false /\
  hl (H:=cheat_host) CHEAT (mkc 1 r P g (E.cert g) false) 4 = E.cost i.
Proof.
  intros r P g i Hn.
  assert (Hc : E.cost i = 0 \/ E.cost i = 1) by (destruct i; simpl; auto).
  destruct Hc as [Hc | Hc].
  - rewrite (hr_cons _ _ PEEK), (hl_cons _ _ PEEK) by reflexivity.
    rewrite (ex_peek 1 r P g (E.cert g) i Hn), Hc.
    rewrite (hr_cons _ _ (BR 3 5 7)), (hl_cons _ _ (BR 3 5 7)) by reflexivity.
    rewrite ex_br.
    rewrite (hr_cons _ _ GSTEP0), (hl_cons _ _ GSTEP0) by reflexivity.
    rewrite (ex_g0 3 0 P g (E.cert g) i Hn Hc).
    rewrite (hr_cons _ _ (BR 1 1 1)), (hl_cons _ _ (BR 1 1 1)) by reflexivity.
    rewrite ex_br. simpl.
    pose proof (cert_exec_cost0 g i Hc) as Hx. simpl in Hx. rewrite Hx.
    split; reflexivity.
  - rewrite (hr_cons _ _ PEEK), (hl_cons _ _ PEEK) by reflexivity.
    rewrite (ex_peek 1 r P g (E.cert g) i Hn), Hc.
    rewrite (hr_cons _ _ (BR 3 5 7)), (hl_cons _ _ (BR 3 5 7)) by reflexivity.
    rewrite ex_br.
    rewrite (hr_cons _ _ GSTEP1), (hl_cons _ _ GSTEP1) by reflexivity.
    rewrite (ex_g1 5 1 P g (E.cert g) i Hn Hc).
    rewrite (hr_cons _ _ (BR 1 1 1)), (hl_cons _ _ (BR 1 1 1)) by reflexivity.
    rewrite ex_br. simpl.
    destruct (E.cert g), (E.fires (E.core_of g) i); split; reflexivity.
Qed.

(* ================================================================= *)
(* The guest side.                                                    *)
(* ================================================================= *)

Lemma glat_cert : forall (i : sinst) m, glat (C:=small_class) i m = E.cert (grun (C:=small_class) i m).
Proof.
  intros i m. induction m as [| m IH]; [reflexivity |].
  unfold glat, grun in *.
  change (glatch (gstart small_class i) (S m)) with
    (glatch (gstart small_class i) m || gread small_class i (gr (gstart small_class i) (S m))).
  rewrite IH, (gr_succ small_class i m).
  change (gread small_class i) with E.cert.
  destruct (gnext small_class i (gr (gstart small_class i) m)) as [j |].
  - change (gstep small_class i) with E.exec. rewrite E.cert_latch.
    destruct (E.cert _); reflexivity.
  - destruct (E.cert _); reflexivity.
Qed.

Lemma live_or_stop : forall (i : sinst) n,
  live_before (C:=small_class) i n \/
  exists m0, m0 < n /\ gnext small_class i (grun (C:=small_class) i m0) = None /\
             live_before (C:=small_class) i m0.
Proof.
  intros i n. induction n as [| n IH].
  - left. intros k Hk. lia.
  - destruct IH as [Hl | (m0 & Hm & Hs & Hl)].
    + destruct (gnext small_class i (grun (C:=small_class) i n)) eqn:E.
      * left. intros k Hk. destruct (Nat.eq_dec k n) as [-> | Hne].
        { unfold grun in E. rewrite E. discriminate. }
        apply Hl. lia.
      * right. exists n. auto.
    + right. exists m0. split; [lia | auto].
Qed.

(* ================================================================= *)
(* Matching points.                                                   *)
(* ================================================================= *)

Lemma points : forall (i : sinst) m, live_before (C:=small_class) i m ->
  exists r,
    hr (H:=cheat_host) CHEAT (cload i) (4 * m) =
      mkc 1 r (fst (fst i)) (grun (C:=small_class) i m)
          (E.cert (grun (C:=small_class) i m)) false /\
    hl (H:=cheat_host) CHEAT (cload i) (4 * m) = gledger (C:=small_class) i m.
Proof.
  intros i m. induction m as [| m IH]; intros Hl.
  - exists 0. split; reflexivity.
  - destruct IH as (r & Hh & Hle).
    { intros k Hk. apply Hl. lia. }
    assert (Hn : gnext small_class i (grun (C:=small_class) i m) <> None) by (apply Hl; lia).
    destruct (gnext small_class i (grun (C:=small_class) i m)) as [j |] eqn:Ej;
      [| congruence].
    simpl in Ej.
    destruct (round r (fst (fst i)) (grun (C:=small_class) i m) j Ej) as [R1 R2].
    exists (E.cost j).
    replace (4 * S m) with (4 * m + 4) by lia.
    rewrite (hr_add cheat_host CHEAT), (hl_add cheat_host CHEAT), Hh, R1, R2, Hle.
    unfold grun, gledger. rewrite (gr_succ small_class i m), (gl_succ small_class i m).
    fold (grun (C:=small_class) i m). simpl gnext. rewrite Ej. simpl. split; reflexivity.
Qed.

(* ================================================================= *)
(* The theorem.                                                       *)
(* ================================================================= *)

Theorem cheat_is_universal :
  forall (Obs : gi small_class -> Type) (obs : forall i, gS small_class i -> Obs i),
  universal_thiele small_class cheat_host Obs obs 0.
Proof.
  intros Obs obs.
  exists CHEAT, cload, (fun i h => obs i (cg h)). intros i. split; [| split].
  - (* (1) halting *)
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
  - (* (2) in order, decoded, latch, ledger exact *)
    exists (fun m => 4 * m). split; [intros; lia |].
    intros m Hl. destruct (points i m Hl) as (r & Hh & Hle).
    unfold match_at. simpl hP in *. rewrite Hle, Hh. split; [reflexivity |].
    split; [simpl; symmetry; apply glat_cert |].
    exists 0. split; lia.
  - (* (3) *)
    intros n. apply clause3_free.
Qed.

Print Assumptions cheat_toll.
Print Assumptions cheat_is_universal.
