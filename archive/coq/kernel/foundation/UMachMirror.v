(** UMachMirror.v: the "mirror" cheat.  The bare cheat of UMachCheatSmall.v with its
    one paid move GSTEP1 split into three paid moves of the host, MCHECK,
    MCOMMIT, MCERTIFY (price 1 each): MCHECK carries out the guest's next
    instruction when it is a CHECK (else traps the host), MCOMMIT when it
    is a COMMIT, MCERTIFY when it is a CERTIFY; only MCERTIFY touches the
    host's flag (flag := flag || the guest's flag after the step).  The
    unpaid guest instructions are still carried out by the built-in GSTEP0.

    mirror_is_universal: it meets the in-order rendering of
      the plain definition for U's class with surcharge 0.
    mirror_trace: at matching time 4m the host's own trace is the image of
      the guest's trace under  i |-> [MPEEK; MBR; op i; JMP], with
      op (CHECK p c) = MCHECK, op (COMMIT p c) = MCOMMIT, op CERTIFY = MCERTIFY.
    mirror_earned: whenever the host flag is up at a matching time, the
      host's own trace contains its own MCHECK, MCOMMIT, MCERTIFY, in that
      order, executed on a guest CHECK p c that passed, a guest COMMIT p c
      that passed with counter c untouched since the CHECK, and a guest
      CERTIFY that passed: the shape of universal_earned for U.
    mirror_not_reg_host: it is not a register host (GSTEP0 still traps on
      a paid guest instruction).                                          *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.
Require Import Kernel.UMachDef.
Require Import Kernel.UMachCheatSmall.
Require Import Kernel.UMachRegHost.

Inductive mmove : Type :=
| MPEEK                          (* r := kind of the guest's next instruction *)
| MBR (j0 j1 j2 j3 j4 : nat)     (* pc := j_r                                   *)
| MGSTEP0                        (* a guest INC/DEC, else trap                  *)
| MCHECK                         (* price 1: a guest CHECK, else trap           *)
| MCOMMIT                        (* price 1: a guest COMMIT, else trap          *)
| MCERTIFY                       (* price 1: a guest CERTIFY, else trap; flag   *)
| MSTOP.

Definition mcost (m : mmove) : nat :=
  match m with MCHECK | MCOMMIT | MCERTIFY => 1 | _ => 0 end.

Definition kindcode (i : E.instr) : nat :=
  match i with
  | E.INC _ | E.DEC _ _ => 1 | E.HALT => 0 | E.CHECK _ _ => 2 | E.COMMIT _ _ => 3 | E.CERTIFY => 4
  end.

Definition gnexti (h : cst) : option E.instr := E.next_instr (cP h) (E.core_of (cg h)).

Definition mtrap (h : cst) : cst := mkc (cpc h) (cr h) (cP h) (cg h) (cmir h) true.
Definition madv (h : cst) (i : E.instr) (mir : bool) : cst :=
  mkc (S (cpc h)) (cr h) (cP h) (E.exec (cg h) i) mir false.

Definition mexec (h : cst) (m : mmove) : cst :=
  if cerr h then h else
  match m with
  | MPEEK => mkc (S (cpc h)) (match gnexti h with None => 0 | Some i => kindcode i end)
                 (cP h) (cg h) (cmir h) false
  | MBR j0 j1 j2 j3 j4 =>
      mkc (match cr h with 0 => j0 | 1 => j1 | 2 => j2 | 3 => j3 | _ => j4 end)
          (cr h) (cP h) (cg h) (cmir h) false
  | MGSTEP0 => match gnexti h with
               | Some (E.INC c) => madv h (E.INC c) (cmir h)
               | Some (E.DEC c j) => madv h (E.DEC c j) (cmir h)
               | _ => mtrap h end
  | MCHECK => match gnexti h with
              | Some (E.CHECK p c) => madv h (E.CHECK p c) (cmir h)
              | _ => mtrap h end
  | MCOMMIT => match gnexti h with
               | Some (E.COMMIT p c) => madv h (E.COMMIT p c) (cmir h)
               | _ => mtrap h end
  | MCERTIFY => match gnexti h with
                | Some E.CERTIFY => madv h E.CERTIFY (cmir h || E.cert (E.exec (cg h) E.CERTIFY))
                | _ => mtrap h end
  | MSTOP => h
  end.

Theorem mirror_toll : forall h m, cmir h = false -> cmir (mexec h m) = true -> mcost m >= 1.
Proof.
  intros [pc r P g mir er] m H0 H1. simpl in H0. subst mir.
  unfold mexec in H1. simpl in H1. destruct er; [discriminate |].
  destruct m; simpl; try lia; exfalso; simpl in H1;
  repeat match goal with
         | H : context [match ?x with _ => _ end] |- _ => destruct x; simpl in H
         end; discriminate.
Qed.

Definition mnext (Q : list mmove) (h : cst) : option mmove :=
  if cerr h then None else
  match E.fetch Q (cpc h) with Some MSTOP => None | o => o end.

Definition mirror_host : host :=
  mk_host cst mmove mexec mcost cmir mirror_toll (list mmove) mnext.

Definition JMP : mmove := MBR 1 1 1 1 1.

(* The one fixed program. *)
Definition MIRROR : list mmove :=
  [MPEEK; MBR 11 3 5 7 9; MGSTEP0; JMP; MCHECK; JMP; MCOMMIT; JMP; MCERTIFY; JMP; MSTOP].

Definition op (i : E.instr) : mmove :=
  match i with
  | E.INC _ | E.DEC _ _ => MGSTEP0 | E.HALT => MSTOP
  | E.CHECK _ _ => MCHECK | E.COMMIT _ _ => MCOMMIT | E.CERTIFY => MCERTIFY
  end.

Definition img (i : E.instr) : list mmove :=
  [MPEEK; MBR 11 3 5 7 9; op i; JMP].

(* The host's own trace. *)
Fixpoint htr (Q : list mmove) (h : cst) (n : nat) : list mmove :=
  match n with
  | 0 => []
  | S n' => match mnext Q h with None => [] | Some m => m :: htr Q (mexec h m) n' end
  end.

Lemma htr_add : forall a b Q h, htr Q h (a + b) = htr Q h a ++ htr Q (hr (H:=mirror_host) Q h a) b.
Proof.
  induction a; intros b Q h; simpl; [reflexivity |].
  change (hnext mirror_host Q h) with (mnext Q h).
  destruct (mnext Q h) eqn:E; simpl.
  - rewrite IHa. reflexivity.
  - destruct b; simpl; [reflexivity |]. rewrite E. reflexivity.
Qed.

Lemma hr_cons : forall Q h m n, mnext Q h = Some m ->
  hr (H:=mirror_host) Q h (S n) = hr (H:=mirror_host) Q (mexec h m) n.
Proof. intros Q h m n E. simpl. change (hnext mirror_host) with mnext. rewrite E. reflexivity. Qed.

Lemma hl_cons : forall Q h m n, mnext Q h = Some m ->
  hl (H:=mirror_host) Q h (S n) = mcost m + hl (H:=mirror_host) Q (mexec h m) n.
Proof. intros Q h m n E. simpl. change (hnext mirror_host) with mnext. rewrite E. reflexivity. Qed.

Lemma htr_cons : forall Q h m n, mnext Q h = Some m -> htr Q h (S n) = m :: htr Q (mexec h m) n.
Proof. intros Q h m n E. simpl. rewrite E. reflexivity. Qed.

Lemma next_not_halt : forall P k i, E.next_instr P k = Some i -> i <> E.HALT.
Proof.
  intros P k i H ->. unfold E.next_instr in H. destruct (E.err k); [discriminate |].
  destruct (E.fetch P (E.pc k)) as [[] |]; discriminate.
Qed.

Lemma cert_noncertify : forall g i, i <> E.CERTIFY -> E.cert (E.exec g i) = E.cert g.
Proof. intros g i H. rewrite E.cert_latch. destruct i; try (simpl; apply orb_false_r). congruence. Qed.

(* One round: four host moves per guest step. *)
Lemma round : forall r P g i,
  E.next_instr P (E.core_of g) = Some i ->
  hr (H:=mirror_host) MIRROR (mkc 1 r P g (E.cert g) false) 4 =
    mkc 1 (kindcode i) P (E.exec g i) (E.cert (E.exec g i)) false /\
  hl (H:=mirror_host) MIRROR (mkc 1 r P g (E.cert g) false) 4 = E.cost i /\
  htr MIRROR (mkc 1 r P g (E.cert g) false) 4 = img i.
Proof.
  intros r P g i Hn. pose proof (next_not_halt P _ i Hn) as Hh.
  set (h0 := mkc 1 r P g (E.cert g) false).
  assert (S1 : mnext MIRROR h0 = Some MPEEK) by reflexivity.
  set (h1 := mexec h0 MPEEK).
  assert (E1 : h1 = mkc 2 (kindcode i) P g (E.cert g) false)
    by (unfold h1, mexec, gnexti; simpl; rewrite Hn; reflexivity).
  assert (S2 : mnext MIRROR h1 = Some (MBR 11 3 5 7 9)) by (rewrite E1; reflexivity).
  set (h2 := mexec h1 (MBR 11 3 5 7 9)).
  assert (E2 : h2 = mkc (match kindcode i with 0 => 11 | 1 => 3 | 2 => 5 | 3 => 7 | _ => 9 end)
                        (kindcode i) P g (E.cert g) false) by (unfold h2; rewrite E1; reflexivity).
  assert (S3 : mnext MIRROR h2 = Some (op i))
    by (rewrite E2; destruct i; try reflexivity; contradiction).
  set (h3 := mexec h2 (op i)).
  assert (E3 : h3 = mkc (S (match kindcode i with 0 => 11 | 1 => 3 | 2 => 5 | 3 => 7 | _ => 9 end))
                        (kindcode i) P (E.exec g i) (E.cert (E.exec g i)) false).
  { unfold h3. rewrite E2. destruct i; try contradiction; cbn -[E.exec E.next_instr];
      match goal with |- _ => idtac end. all: try (unfold gnexti; simpl cP; simpl cg).
      all: rewrite Hn; cbn -[E.exec].
      all: unfold madv; cbn [cpc cr cP cg cmir cerr].
      all: first [ f_equal; symmetry; apply cert_noncertify; discriminate
            | f_equal; rewrite (E.cert_latch g E.CERTIFY); destruct (E.cert g); reflexivity ]. }
  assert (S4 : mnext MIRROR h3 = Some JMP) by (rewrite E3; destruct i; try reflexivity; contradiction).
  assert (E4 : mexec h3 JMP = mkc 1 (kindcode i) P (E.exec g i) (E.cert (E.exec g i)) false)
    by (rewrite E3; unfold mexec, JMP; cbn [cerr cr cP cg cmir];
        destruct (kindcode i) as [| [| [| [| ]]]]; reflexivity).
  split; [| split].
  - rewrite (hr_cons _ _ _ _ S1). fold h1. rewrite (hr_cons _ _ _ _ S2). fold h2.
    rewrite (hr_cons _ _ _ _ S3). fold h3. rewrite (hr_cons _ _ _ _ S4). rewrite E4. reflexivity.
  - rewrite (hl_cons _ _ _ _ S1). fold h1. rewrite (hl_cons _ _ _ _ S2). fold h2.
    rewrite (hl_cons _ _ _ _ S3). fold h3. rewrite (hl_cons _ _ _ _ S4). simpl.
    destruct i; try contradiction; reflexivity.
  - rewrite (htr_cons _ _ _ _ S1). fold h1. rewrite (htr_cons _ _ _ _ S2). fold h2.
    rewrite (htr_cons _ _ _ _ S3). fold h3. rewrite (htr_cons _ _ _ _ S4). reflexivity.
Qed.

Definition mload (i : sinst) : cst :=
  mkc 1 0 (fst (fst i)) (E.start (snd (fst i)) (snd i)) false false.

Lemma grun_small : forall (i : sinst) m,
  grun (C:=small_class) i m = E.run_prog m (fst (fst i)) (E.start (snd (fst i)) (snd i)).
Proof.
  intros [[P x] y] m. unfold grun. simpl. generalize (E.start x y).
  induction m as [| m IH]; intros s; [reflexivity |].
  simpl. unfold E.step. destruct (E.next_instr P (E.core_of s)) eqn:E.
  - apply IH.
  - symmetry. clear IH. apply E.run_prog_halted. exact E.
Qed.

Lemma trace_succ : forall m P s,
  E.trace_of (S m) P s = E.trace_of m P s ++
  match E.next_instr P (E.core_of (E.run_prog m P s)) with Some i => [i] | None => [] end.
Proof.
  induction m as [| m IH]; intros P s.
  - simpl. destruct (E.next_instr P (E.core_of s)); reflexivity.
  - replace (E.trace_of (S (S m)) P s) with
      (match E.next_instr P (E.core_of s) with
       | None => [] | Some i => i :: E.trace_of (S m) P (E.exec s i) end) by reflexivity.
    replace (E.trace_of (S m) P s) with
      (match E.next_instr P (E.core_of s) with
       | None => [] | Some i => i :: E.trace_of m P (E.exec s i) end) by reflexivity.
    replace (E.run_prog (S m) P s) with (E.run_prog m P (E.step P s)) by reflexivity.
    unfold E.step. destruct (E.next_instr P (E.core_of s)) as [i |] eqn:Hn.
    + rewrite IH. reflexivity.
    + rewrite E.run_prog_halted by exact Hn. rewrite Hn. reflexivity.
Qed.

Lemma mpoints : forall (i : sinst) m, live_before (C:=small_class) i m ->
  exists r,
    hr (H:=mirror_host) MIRROR (mload i) (4 * m) =
      mkc 1 r (fst (fst i)) (grun (C:=small_class) i m) (E.cert (grun (C:=small_class) i m)) false /\
    hl (H:=mirror_host) MIRROR (mload i) (4 * m) = gledger (C:=small_class) i m /\
    htr MIRROR (mload i) (4 * m) =
      flat_map img (E.trace_of m (fst (fst i)) (E.start (snd (fst i)) (snd i))).
Proof.
  intros i m. induction m as [| m IH]; intros Hl.
  - exists 0. split; [reflexivity |]. split; reflexivity.
  - destruct IH as (r & Hh & Hle & Ht). { intros k Hk. apply Hl. lia. }
    assert (Hn : gnext small_class i (grun (C:=small_class) i m) <> None) by (apply Hl; lia).
    destruct (gnext small_class i (grun (C:=small_class) i m)) as [j |] eqn:Ej; [| congruence].
    simpl in Ej.
    destruct (round r (fst (fst i)) (grun (C:=small_class) i m) j Ej) as (R1 & R2 & R3).
    exists (kindcode j).
    replace (4 * S m) with (4 * m + 4) by lia.
    rewrite (hr_add mirror_host MIRROR), (hl_add mirror_host MIRROR), htr_add, Hh, R1, R2, R3, Hle, Ht.
    rewrite trace_succ. rewrite <- grun_small. rewrite Ej. rewrite flat_map_app. simpl flat_map.
    rewrite ?app_nil_r.
    unfold grun, gledger. rewrite (gr_succ small_class i m), (gl_succ small_class i m).
    fold (grun (C:=small_class) i m). simpl gnext. rewrite Ej. simpl.
    split; [reflexivity |]. split; reflexivity.
Qed.

(* ================================================================= *)
(* (1)-(3), in order, surcharge 0.                                    *)
(* ================================================================= *)

Theorem mirror_is_universal :
  forall (Obs : gi small_class -> Type) (obs : forall i, gS small_class i -> Obs i),
  universal_thiele small_class mirror_host Obs obs 0.
Proof.
  intros Obs obs.
  exists MIRROR, mload, (fun i h => obs i (cg h)). intros i. split; [| split].
  - unfold clause1. split.
    + intros [n Hn].
      destruct (live_or_stop i (S n)) as [Hl | (m0 & _ & Hs & _)]; [| exists m0; exact Hs].
      exfalso. destruct (mpoints i n (fun k Hk => Hl k ltac:(lia))) as (r & Hh & _).
      rewrite <- (hr_stopped_stays mirror_host MIRROR (mload i) n (4 * n)) in Hn by (lia || exact Hn).
      rewrite Hh in Hn. discriminate.
    + intros [m Hm].
      destruct (live_or_stop i (S m)) as [Hl | (m0 & _ & Hs & Hl0)].
      { exfalso. exact (Hl m ltac:(lia) Hm). }
      destruct (mpoints i m0 Hl0) as (r & Hh & _).
      exists (4 * m0 + 2). rewrite (hr_add mirror_host MIRROR), Hh.
      simpl in Hs. simpl. unfold mexec at 2. unfold gnexti. simpl. rewrite Hs. reflexivity.
  - exists (fun m => 4 * m). split; [intros; lia |].
    intros m Hl. destruct (mpoints i m Hl) as (r & Hh & Hle & _).
    unfold match_at. simpl hP in *. rewrite Hle, Hh. split; [reflexivity |].
    split; [simpl; symmetry; apply glat_cert |].
    exists 0. split; lia.
  - intros n. apply clause3_free.
Qed.

(* ================================================================= *)
(* The host's own chain.                                              *)
(* ================================================================= *)

Theorem mirror_earned : forall (i : sinst) m,
  live_before (C:=small_class) i m ->
  cmir (hr (H:=mirror_host) MIRROR (mload i) (4 * m)) = true ->
  let P := fst (fst i) in let s0 := E.start (snd (fst i)) (snd i) in
  exists pre1 p c mid1 mid2 post,
    htr MIRROR (mload i) (4 * m) =
      flat_map img pre1 ++ [MPEEK; MBR 11 3 5 7 9; MCHECK; JMP] ++
      flat_map img mid1 ++ [MPEEK; MBR 11 3 5 7 9; MCOMMIT; JMP] ++
      flat_map img mid2 ++ [MPEEK; MBR 11 3 5 7 9; MCERTIFY; JMP] ++ flat_map img post /\
    E.trace_of m P s0 = pre1 ++ E.CHECK p c :: mid1 ++ E.COMMIT p c :: mid2 ++ E.CERTIFY :: post /\
    E.check_ok (E.core_of (E.run pre1 s0)) p c = true /\
    E.holds p (E.val (E.core_of (E.run pre1 s0)) c) /\
    E.commit_ok (E.core_of (E.run (pre1 ++ E.CHECK p c :: mid1) s0)) p c = true /\
    E.certify_ok (E.core_of (E.run (pre1 ++ E.CHECK p c :: mid1 ++ E.COMMIT p c :: mid2) s0)) = true /\
    E.ver (E.core_of (E.run pre1 s0)) c = E.ver (E.core_of (E.run (pre1 ++ E.CHECK p c :: mid1) s0)) c /\
    E.untouched (E.run (pre1 ++ [E.CHECK p c]) s0) mid1 c.
Proof.
  intros i m Hl Hc P s0.
  destruct (mpoints i m Hl) as (r & Hh & _ & Ht). rewrite Hh in Hc. simpl in Hc.
  rewrite grun_small in Hc. fold P s0 in Hc. rewrite E.run_prog_trace in Hc.
  destruct (E.earned_certification_provenance s0 (E.trace_of m P s0) (E.start_clean _ _) Hc)
    as (pre1 & p & c & mid1 & mid2 & post & Htr & Hck & Hcm & Hok & Hv & Hun).
  exists pre1, p, c, mid1, mid2, post.
  split.
  - rewrite Ht. fold P s0. rewrite Htr.
    repeat (rewrite flat_map_app; simpl flat_map). simpl. reflexivity.
  - split; [exact Htr |]. split; [exact Hck |].
    split; [| auto].
    unfold E.check_ok in Hck. apply andb_true_iff in Hck as [Hck _].
    apply andb_true_iff in Hck as [_ Hck]. apply E.eval_iff, Hck.
Qed.

(* ================================================================= *)
(* Not a register host.                                               *)
(* ================================================================= *)

Definition ms (P : list E.instr) (err : bool) : cst := mkc 3 0 P (E.start 0 0) false err.

Theorem mirror_not_reg_host : reg_host mirror_host -> False.
Proof.
  intros R.
  pose proof (b_cost mirror_host R MGSTEP0) as Hc. simpl in Hc.
  assert (Live : forall P, b_err R (ms P false) = false).
  { intros P. destruct (b_err R (ms P false)) eqn:E; [| reflexivity].
    pose proof (b_next_err mirror_host R [MPEEK; MPEEK; MGSTEP0] (ms P false) E) as X.
    discriminate X. }
  set (sp := ms [E.CERTIFY] false).
  assert (Tp : hstep mirror_host sp MGSTEP0 = ms [E.CERTIFY] true) by reflexivity.
  assert (Fix : forall m, hstep mirror_host (ms [E.CERTIFY] true) m = ms [E.CERTIFY] true)
    by (intros m; reflexivity).
  destruct (b_kind R MGSTEP0) as [r | r j | |] eqn:K.
  - destruct (b_inc mirror_host R sp MGSTEP0 r (Live _) K) as (E1 & _ & _). rewrite Tp in E1.
    destruct (b_inc mirror_host R _ MGSTEP0 r E1 K) as (_ & P2 & _). rewrite Fix in P2. lia.
  - destruct (b_dec mirror_host R sp MGSTEP0 r j (Live _) K) as (E1 & _). rewrite Tp in E1.
    destruct (b_dec mirror_host R _ MGSTEP0 r j E1 K) as (_ & D2). rewrite Fix in D2.
    destruct (b_reg R (ms [E.CERTIFY] true) r) as [| n] eqn:V.
    + destruct D2 as [P2 _]. lia.
    + destruct D2 as [_ R2]. specialize (R2 r). unfold upd in R2. rewrite Nat.eqb_refl, V in R2. lia.
  - set (sf := ms [E.INC E.CA] false).
    destruct (b_halt mirror_host R sf MGSTEP0 K) as (E2 & P2 & _).
    pose proof (b_next mirror_host R [MPEEK; MPEEK; MGSTEP0; MSTOP] _ _ E2 P2) as N.
    discriminate N.
  - lia.
Qed.

Print Assumptions mirror_toll.
Print Assumptions mirror_is_universal.
Print Assumptions mirror_earned.
Print Assumptions mirror_not_reg_host.
