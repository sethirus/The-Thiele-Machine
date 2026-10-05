(** CompilerGuestRun.v: the guest of a computably presented machine, run
    on EarnedPriced's own runner, and what it does.

    The guest of M (with presentation pc) is the compiled source program
    of CompilerGuest.v, translated to EarnedPriced instructions:

      cg_guest M pc = map cg_tr (cg_code k r (1, cg_SRC M pc) 1)

    with k = cg_k M pc and the fixed checker's routine code r = cg_r M pc.
    Started from s0, it runs from cg_ystart M pc s0 = G.start 0 (g), where g
    is the Godel code of the register file holding the code of s0 in S.
    Every run below is pr_run_prog of EarnedPriced.v with the fixed property
    language cg_uprop and the fixed checker cg_ueval of CompilerChecker.v.

    Results (all for every presented machine M, presentation pc, start s0):

      cg_guest_matching_points
          while the driver has not halted before step n, some run length
          N >= n reaches the image of HEAD, untrapped, with counter B
          decoding (exponent of the first prime, then pm_sdec) to the state
          after n steps, ledger = mledger n + surcharge n and flag =
          mlatch n;
      cg_guest_halts_at
          when the driver first halts at step n, some run length reaches
          the image of HALTB, a halted state with the same decoding,
          ledger and flag, and stays there for every longer run;
      cg_guest_halting_iff
          some run of the guest halts exactly when the driver halts;
      cg_guest_flag_iff
          some run of the guest raises the flag exactly when the reading
          is yes at some state of the driven run;
      cg_guest_earned
          when a run of N steps has the flag up, its trace has exactly one
          passing CHECK; it is CHECK (URun r) on counter B at some run
          length L < N, and counter B there decodes to the first state of
          the driven run whose reading is yes; every passing check before
          N is that one.

    The halting and flag equivalences are the converse direction of the
    compiler: they follow from the matching points, the determinism of
    pr_run_prog, the stability of halted states, the latch of the flag
    and the fact that the image of HEAD is never a halting instruction.
    Stated for the source program [cg_source_halts_of_guest,
    cg_source_certifies_of_guest]: if some run of the guest halts, the
    source program reaches HALTB, where it has no step; if some run of the
    guest raises the flag, the source program reaches HEAD or HALTB with
    the certified flag of its record up.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, EarnedGeneric.v, EarnedPriced.v, ThieleComplete.v,
    Presented.v, Presentation.v and the Compiler*.v files. No axioms, no
    Admitted. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.Shared.Libs.DLW.Code Require Import compiler compiler_correction.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Minimal.EarnedGeneric Minimal.EarnedPriced Minimal.ThieleComplete.
Module G := Minimal.EarnedGeneric.
Module P := Minimal.EarnedPriced.
Module T := Minimal.ThieleComplete.
Require Import Minimal.Presented Minimal.Presentation.
Require Import Minimal.CompilerCodes Minimal.CompilerChecker Minimal.CompilerLifts
  Minimal.CompilerIcomp Minimal.CompilerGuest.

(* ================================================================= *)
(* Generic facts about compiled runs and EarnedPriced runs.            *)
(* ================================================================= *)

(* compiler_sound with a step count: every source step costs at least one
   target step. *)
Lemma cg_compile_steps : forall k r Px iQ q st1 st2 w1,
  cg_simul k (snd st1) w1 ->
  sss_steps (cg_xstep k r) Px q st1 st2 ->
  exists w2 q', q <= q' /\ cg_simul k (snd st2) w2 /\
    sss_steps cg_ystep (iQ, cg_code k r Px iQ) q'
      (cg_link Px iQ (fst st1), w1) (cg_link Px iQ (fst st2), w2).
Proof.
  intros k r Px iQ q st1 st2 w1 Hs H. revert w1 Hs.
  induction H as [st | q st1 st2 st3 H1 H2 IH]; intros w1 Hs.
  - exists w1, 0. split; [lia |]. split; [exact Hs | constructor].
  - destruct H1 as (k0 & l & I & r0 & d & HP & Hst & Hstep).
    destruct st2 as [i2 v2]. subst st1.
    assert (HI : (k0 + length l, [I]) <sc Px).
    { rewrite HP. exists l, r0. split; reflexivity. }
    destruct (compiler_subcode (cg_icomp k r) cg_ilen (cg_icomp_length k r) Px iQ
                (cg_err Px iQ) (k0 + length l) I HI) as [Hsc Hlen].
    destruct (cg_icomp_sound k r (cg_link Px iQ) I (k0 + length l) d i2 v2 w1 Hstep)
      as (w2 & (p & Hp0 & Hp) & Hs2).
    { unfold cg_link. rewrite Hlen, cg_icomp_length. reflexivity. }
    { exact Hs. }
    destruct (IH w2 Hs2) as (w3 & q' & Hq & Hs3 & H3).
    exists w3, (p + q'). split; [lia |]. split; [exact Hs3 |].
    apply sss_steps_trans with (cg_link Px iQ i2, w2); [| exact H3].
    apply subcode_sss_steps with (1 := Hsc). exact Hp.
Qed.

Lemma cg_run_prog_add : forall (prop : Type) eqb ev a b (Q : list (@P.pr_instr prop)) s,
  P.pr_run_prog eqb ev (a + b) Q s = P.pr_run_prog eqb ev b Q (P.pr_run_prog eqb ev a Q s).
Proof. intros prop eqb ev a. induction a as [| a IH]; intros; simpl; [reflexivity | apply IH]. Qed.

Lemma cg_run_prog_stay : forall (prop : Type) eqb ev (Q : list (@P.pr_instr prop)) s N N',
  P.pr_halted Q (G.core_of (P.pr_run_prog eqb ev N Q s)) -> N <= N' ->
  P.pr_run_prog eqb ev N' Q s = P.pr_run_prog eqb ev N Q s.
Proof.
  intros prop eqb ev Q s N N' H Hle. replace N' with (N + (N' - N)) by lia.
  rewrite cg_run_prog_add. apply P.pr_run_prog_halted. exact H.
Qed.

Lemma cg_cert_mono : forall (prop : Type) eqb ev (Q : list (@P.pr_instr prop)) s N N',
  N <= N' -> G.cert (P.pr_run_prog eqb ev N Q s) = true ->
  G.cert (P.pr_run_prog eqb ev N' Q s) = true.
Proof.
  intros prop eqb ev Q s N N' Hle H. replace N' with (N + (N' - N)) by lia.
  rewrite cg_run_prog_add. generalize (P.pr_run_prog eqb ev N Q s) H. clear.
  induction (N' - N) as [| d IH]; intros t H; simpl; [exact H |].
  apply IH. unfold P.pr_step. destruct (P.pr_next_instr Q (G.core_of t)); [| exact H].
  apply P.pr_cert_permanent. exact H.
Qed.

Lemma cg_trace_succ : forall (prop : Type) eqb ev (Q : list (@P.pr_instr prop)) N s,
  P.pr_trace_of eqb ev (S N) Q s =
  P.pr_trace_of eqb ev N Q s ++
  match P.pr_next_instr Q (G.core_of (P.pr_run_prog eqb ev N Q s)) with
  | Some i => [i] | None => [] end.
Proof.
  intros prop eqb ev Q N. induction N as [| N IH]; intros s.
  - simpl. destruct (P.pr_next_instr Q (G.core_of s)); reflexivity.
  - change (P.pr_trace_of eqb ev (S (S N)) Q s) with
      (match P.pr_next_instr Q (G.core_of s) with
       | None => [] | Some i => i :: P.pr_trace_of eqb ev (S N) Q (P.pr_exec eqb ev s i) end).
    change (P.pr_run_prog eqb ev (S N) Q s) with
      (P.pr_run_prog eqb ev N Q (P.pr_step eqb ev Q s)).
    unfold P.pr_step at 1.
    destruct (P.pr_next_instr Q (G.core_of s)) as [i |] eqn:E.
    + rewrite IH. cbn [P.pr_trace_of]. rewrite E. reflexivity.
    + rewrite P.pr_run_prog_halted by exact E. rewrite E.
      cbn [P.pr_trace_of]. rewrite E. reflexivity.
Qed.

Lemma cg_passing_app : forall (prop : Type) eqb ev l1 l2 (s : @G.state prop),
  P.pr_passing_checks eqb ev (l1 ++ l2) s =
  P.pr_passing_checks eqb ev l1 s + P.pr_passing_checks eqb ev l2 (P.pr_run eqb ev l1 s).
Proof.
  intros prop eqb ev l1. induction l1 as [| i l1 IH]; intros l2 s; simpl; [reflexivity |].
  rewrite IH. lia.
Qed.

(* The passing checks at the step taken from run length L. *)
Definition cg_passes_at {prop : Type} eqb ev (Q : list (@P.pr_instr prop)) s (L : nat) : nat :=
  let t := P.pr_run_prog eqb ev L Q s in
  match P.pr_next_instr Q (G.core_of t) with
  | Some i => P.pr_passes ev (G.core_of t) i
  | None => 0
  end.

Fixpoint cg_psum {prop : Type} eqb ev (Q : list (@P.pr_instr prop)) s (N : nat) : nat :=
  match N with
  | 0 => 0
  | S N' => cg_psum eqb ev Q s N' + cg_passes_at eqb ev Q s N'
  end.

Lemma cg_passing_sum : forall (prop : Type) eqb ev (Q : list (@P.pr_instr prop)) s N,
  P.pr_passing_checks eqb ev (P.pr_trace_of eqb ev N Q s) s = cg_psum eqb ev Q s N.
Proof.
  intros prop eqb ev Q s N. induction N as [| N IH]; [reflexivity |].
  rewrite cg_trace_succ, cg_passing_app, IH. cbn [cg_psum]. f_equal.
  rewrite <- P.pr_run_prog_trace. unfold cg_passes_at. cbv zeta.
  destruct (P.pr_next_instr Q (G.core_of (P.pr_run_prog eqb ev N Q s))); simpl; lia.
Qed.

Lemma cg_psum_mono : forall (prop : Type) eqb ev (Q : list (@P.pr_instr prop)) s N N',
  N <= N' -> cg_psum eqb ev Q s N <= cg_psum eqb ev Q s N'.
Proof.
  intros prop eqb ev Q s N N' H. induction H; [lia | simpl; lia].
Qed.

Lemma cg_psum_ge : forall (prop : Type) eqb ev (Q : list (@P.pr_instr prop)) s N L,
  L < N -> cg_passes_at eqb ev Q s L <= cg_psum eqb ev Q s N.
Proof.
  intros prop eqb ev Q s N L H. induction H; simpl; [lia |]. lia.
Qed.

Lemma cg_psum_two : forall (prop : Type) eqb ev (Q : list (@P.pr_instr prop)) s N L L',
  L < N -> L' < N -> L <> L' ->
  cg_passes_at eqb ev Q s L + cg_passes_at eqb ev Q s L' <= cg_psum eqb ev Q s N.
Proof.
  intros prop eqb ev Q s N. induction N as [| N IH]; intros L L' H1 H2 H3; [lia |].
  simpl. destruct (Nat.eq_dec L N) as [-> | HL].
  - generalize (cg_psum_ge prop eqb ev Q s N L' ltac:(lia)). lia.
  - destruct (Nat.eq_dec L' N) as [-> | HL'].
    + generalize (cg_psum_ge prop eqb ev Q s N L ltac:(lia)). lia.
    + generalize (IH L L' ltac:(lia) ltac:(lia) H3). lia.
Qed.

(* ================================================================= *)
(* The guest.                                                          *)
(* ================================================================= *)

Section Run.

Variable M : presented_machine.
Variable pc : cg_presentation M.

Local Notation st := (T.cs_state (pm_sys M)).
Local Notation cstep := (T.cs_step (pm_sys M)).
Local Notation ccost := (T.cs_cost (pm_sys M)).
Local Notation rd := (T.cs_cert (pm_sys M)).
Local Notation sc := (pm_scode M).
Local Notation K := (cg_k M pc).
Local Notation R := (cg_r M pc).
Local Notation SRC := (cg_SRC M pc).
Local Notation lnk := (cg_link (1, cg_SRC M pc) 1).

Definition cg_guest : list (@P.pr_instr cg_uprop) := map cg_tr (cg_code K R (1, SRC) 1).

Definition cg_ystart (s0 : st) : cg_ystate := G.start 0 (cg_gk K (cg_e0 M s0)).

Local Notation Yrun s0 N := (P.pr_run_prog cg_uprop_eqb cg_ueval N cg_guest (cg_ystart s0)).
Local Notation Ystep := (P.pr_run_prog cg_uprop_eqb cg_ueval).

(* A source phase that makes progress is a target run of at least one step
   on EarnedPriced's own runner. *)
Lemma cg_y_phase : forall i x j x' w,
  sss_progress (cg_xstep K R) (1, SRC) (i, x) (j, x') ->
  cg_simul K x w -> G.pc (G.core_of w) = lnk i ->
  exists q w', 0 < q /\ Ystep q cg_guest w = w' /\ G.pc (G.core_of w') = lnk j /\
    cg_simul K x' w'.
Proof.
  intros i x j x' w (q0 & Hq0 & Hs) Hsim Hpc.
  destruct (cg_compile_steps K R (1, SRC) 1 q0 (i, x) (j, x') w Hsim Hs)
    as (w2 & q & Hq & Hsim2 & Hy).
  destruct (cg_lift_run _ q _ w _ w2 Hpc Hy) as [Hrun Hpc2].
  exists q, w2. split; [lia |]. split; [exact Hrun |]. split; [exact Hpc2 | exact Hsim2].
Qed.

(* The first instruction of the image of a source instruction. *)
Lemma cg_fetch_at : forall i J,
  (i, [J]) <sc (1, SRC) ->
  exists y rest, cg_icomp K R lnk i J = y :: rest /\ G.fetch cg_guest (lnk i) = Some (cg_tr y).
Proof.
  intros i J H.
  destruct (compiler_subcode (cg_icomp K R) cg_ilen (cg_icomp_length K R) (1, SRC) 1
              (cg_err (1, SRC) 1) i J H) as [Hsc _].
  assert (Hl : 1 <= length (cg_icomp K R lnk i J)).
  { rewrite cg_icomp_length. destruct J as [[x | x j] | | |]; simpl; lia. }
  change (compiler (cg_icomp K R) cg_ilen (1, SRC) 1 (cg_err (1, SRC) 1))
    with (cg_code K R (1, SRC) 1) in Hsc.
  change (linker cg_ilen (1, SRC) 1 (cg_err (1, SRC) 1)) with lnk in Hsc.
  destruct (cg_icomp K R lnk i J) as [| y rest] eqn:E; [simpl in Hl; lia |].
  exists y, rest. split; [reflexivity |].
  destruct Hsc as (l & r' & Hc & Hi). unfold cg_guest. rewrite Hc, Hi.
  unfold G.fetch. replace (1 + length l) with (S (length l)) by lia.
  rewrite map_app. rewrite nth_error_app2 by (rewrite map_length; lia).
  rewrite map_length, Nat.sub_diag. reflexivity.
Qed.

Lemma cg_fetch_halt : G.fetch cg_guest (lnk (cg_HALTB M pc)) = Some P.HALT.
Proof.
  destruct (cg_fetch_at _ _ (cg_sc_halt M pc)) as (y & rest & E & F).
  simpl in E. injection E as <- _. exact F.
Qed.

Lemma cg_fetch_new : G.fetch cg_guest (lnk (cg_NEW M pc)) = Some (P.CHECK (URun R) G.CB).
Proof.
  destruct (cg_fetch_at _ _ (cg_sc_earn M pc)) as (y & rest & E & F).
  simpl in E. injection E as <- _. exact F.
Qed.

Lemma cg_head_instr : exists J, (2, [XMM J]) <sc (1, SRC).
Proof.
  pose proof (cg_sc_next M pc) as H1. pose proof (cg_sc_dech M pc) as H2.
  destruct (cg_Pn M pc) as [| J l] eqn:E.
  - exists (mm_dec 2 (cg_HALTB M pc)). exact H2.
  - exists J. eapply subcode_trans; [| exact H1].
    simpl map. apply (cg_sc_here1 cg_xinstr 2 2 (XMM J) (map XMM l)). reflexivity.
Qed.

Lemma cg_fetch_head : exists y, G.fetch cg_guest (lnk 2) = Some (cg_tr (YMMA y)).
Proof.
  destruct cg_head_instr as [J HJ].
  destruct (cg_fetch_at _ _ HJ) as (y & rest & E & F).
  destruct J as [x | x j]; unfold cg_icomp in E;
    match type of E with map YMMA ?L = _ => destruct L as [| a L']; [discriminate |] end;
    simpl in E; injection E as <- _; exists a; exact F.
Qed.

(* ================================================================= *)
(* Matching points.                                                    *)
(* ================================================================= *)

Variable s0 : st.

Definition cg_ypoint (n N : nat) : Prop :=
  exists x, cg_inv_head M pc s0 n x /\ G.pc (G.core_of (Yrun s0 N)) = lnk 2 /\
            cg_simul K x (Yrun s0 N).

Lemma cg_ystart_simul : cg_simul K (cg_xstart (cg_e0 M s0)) (cg_ystart s0).
Proof. apply cg_simul_start. intros y Hy. apply (cg_e0_high M pc). exact Hy. Qed.

Lemma cg_y_head : forall n,
  (forall m, m < n -> pm_next M (presented_run M s0 m) <> None) ->
  exists N, n <= N /\ cg_ypoint n N.
Proof.
  induction n as [| n IH]; intros Hn.
  - destruct (cg_x_prologue M pc s0) as (x & Hinv & Hx).
    destruct (cg_y_phase 1 _ 2 x _ Hx cg_ystart_simul (eq_sym (cg_link_start (1, SRC) 1)))
      as (q & w & _ & Hrun & Hpc & Hsim).
    exists q. split; [lia |]. exists x. rewrite Hrun. auto.
  - destruct (IH (fun m Hm => Hn m ltac:(lia))) as (N & HN & x & Hinv & Hpc & Hsim).
    destruct (pm_next M (presented_run M s0 n)) as [i |] eqn:E;
      [| exfalso; exact (Hn n ltac:(lia) E)].
    destruct (cg_x_step M pc s0 n x i Hinv E) as (x' & Hinv' & Hx).
    destruct (cg_y_phase 2 x 2 x' _ Hx Hsim Hpc) as (q & w & Hq & Hrun & Hpc' & Hsim').
    exists (N + q). split; [lia |]. exists x'.
    rewrite cg_run_prog_add, Hrun. auto.
Qed.

Lemma cg_point_facts : forall n N, cg_ypoint n N ->
  G.err (G.core_of (Yrun s0 N)) = false /\
  G.ca (G.core_of (Yrun s0 N)) = 0 /\
  pm_sdec M (cg_expo (qs 0) (G.cb (G.core_of (Yrun s0 N)))) = Some (presented_run M s0 n) /\
  G.mu (Yrun s0 N) = mledger M s0 n + surcharge M s0 n /\
  G.cert (Yrun s0 N) = mlatch M s0 n /\
  length (G.facts (G.core_of (Yrun s0 N))) = (if mlatch M s0 n then 1 else 0).
Proof.
  intros n N ([e a] & [He Ha] & _ & Hsim). cbn [fst snd] in He, Ha. subst a.
  destruct Hsim as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). cbn [cg_a_mu cg_a_cert cg_a_earned] in H4, H5, H7, H8.
  split; [exact H6 |]. split; [exact H1 |]. split.
  { rewrite H2, cg_expo_gk_zero by exact H3. rewrite He. apply pm_sdec_scode. }
  split; [exact H4 |]. split; [exact H5 |].
  destruct (mlatch M s0 n).
  - apply H8. reflexivity.
  - rewrite (proj1 (H7 eq_refl)). reflexivity.
Qed.

(* The image of HEAD is never a halting instruction. *)
Lemma cg_point_live : forall n N, cg_ypoint n N ->
  ~ P.pr_halted cg_guest (G.core_of (Yrun s0 N)).
Proof.
  intros n N Hp Hh. destruct (cg_point_facts n N Hp) as [Herr _].
  destruct Hp as (x & _ & Hpc & _). destruct cg_fetch_head as [y Hy].
  unfold P.pr_halted, P.pr_next_instr in Hh. rewrite Herr, Hpc, Hy in Hh.
  destruct y; discriminate.
Qed.

Definition cg_yhalt (n N : nat) : Prop :=
  exists x, cg_inv_head M pc s0 n x /\ G.pc (G.core_of (Yrun s0 N)) = lnk (cg_HALTB M pc) /\
            cg_simul K x (Yrun s0 N).

Lemma cg_y_stop : forall n N, cg_ypoint n N ->
  pm_next M (presented_run M s0 n) = None ->
  exists N', N <= N' /\ cg_yhalt n N'.
Proof.
  intros n N (x & Hinv & Hpc & Hsim) E.
  destruct (cg_x_stop M pc s0 n x Hinv E) as (x' & Hinv' & Hx).
  destruct (cg_y_phase 2 x _ x' _ Hx Hsim Hpc) as (q & w & Hq & Hrun & Hpc' & Hsim').
  exists (N + q). split; [lia |]. exists x'. rewrite cg_run_prog_add, Hrun. auto.
Qed.

Lemma cg_yhalt_facts : forall n N, cg_yhalt n N ->
  P.pr_halted cg_guest (G.core_of (Yrun s0 N)) /\
  G.ca (G.core_of (Yrun s0 N)) = 0 /\
  pm_sdec M (cg_expo (qs 0) (G.cb (G.core_of (Yrun s0 N)))) = Some (presented_run M s0 n) /\
  G.mu (Yrun s0 N) = mledger M s0 n + surcharge M s0 n /\
  G.cert (Yrun s0 N) = mlatch M s0 n /\
  length (G.facts (G.core_of (Yrun s0 N))) = (if mlatch M s0 n then 1 else 0).
Proof.
  intros n N ([e a] & [He Ha] & Hpc & Hsim). cbn [fst snd] in He, Ha. subst a.
  destruct Hsim as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). cbn [cg_a_mu cg_a_cert cg_a_earned] in H4, H5, H7, H8.
  split.
  { unfold P.pr_halted, P.pr_next_instr. rewrite H6, Hpc, cg_fetch_halt. reflexivity. }
  split; [exact H1 |]. split.
  { rewrite H2, cg_expo_gk_zero by exact H3. rewrite He. apply pm_sdec_scode. }
  split; [exact H4 |]. split; [exact H5 |].
  destruct (mlatch M s0 n).
  - apply H8. reflexivity.
  - rewrite (proj1 (H7 eq_refl)). reflexivity.
Qed.

(* The first halt of the driver, if any, before step N. *)
Lemma cg_first_halt : forall N,
  (forall m, m < N -> pm_next M (presented_run M s0 m) <> None) \/
  (exists h, h < N /\ pm_next M (presented_run M s0 h) = None /\
     forall m, m < h -> pm_next M (presented_run M s0 m) <> None).
Proof.
  induction N as [| N IH].
  - left. intros m Hm. lia.
  - destruct IH as [H | (h & Hh & E & Hb)].
    + destruct (pm_next M (presented_run M s0 N)) as [i |] eqn:E.
      * left. intros m Hm. destruct (Nat.eq_dec m N) as [-> | Hne]; [rewrite E; discriminate |].
        apply H. lia.
      * right. exists N. split; [lia |]. split; [exact E | exact H].
    + right. exists h. split; [lia |]. split; [exact E | exact Hb].
Qed.

(* Every run length is covered by a later matching point or the halting
   point. *)
Lemma cg_cover : forall N, exists N' n x, N <= N' /\ cg_inv_head M pc s0 n x /\
  cg_simul K x (Yrun s0 N').
Proof.
  intros N. destruct (cg_first_halt N) as [H | (h & Hh & E & Hb)].
  - destruct (cg_y_head N H) as (N' & HN & x & Hinv & _ & Hsim).
    exists N', N, x. auto.
  - destruct (cg_y_head h Hb) as (Nh & _ & Hp).
    destruct (cg_y_stop h Nh Hp E) as (N1 & _ & x & Hinv & Hpc & Hsim).
    destruct (le_lt_dec N N1) as [Hle | Hlt].
    + exists N1, h, x. auto.
    + exists N, h, x. split; [lia |]. split; [exact Hinv |].
      rewrite (cg_run_prog_stay _ _ _ _ _ N1 N); [exact Hsim | | lia].
      apply (cg_yhalt_facts h N1). exists x. auto.
Qed.

(* ================================================================= *)
(* The guest theorems.                                                 *)
(* ================================================================= *)

Theorem cg_guest_matching_points : forall n,
  (forall m, m < n -> pm_next M (presented_run M s0 m) <> None) ->
  exists N, n <= N /\
    G.pc (G.core_of (Yrun s0 N)) = lnk 2 /\
    G.err (G.core_of (Yrun s0 N)) = false /\
    G.ca (G.core_of (Yrun s0 N)) = 0 /\
    pm_sdec M (cg_expo (qs 0) (G.cb (G.core_of (Yrun s0 N)))) = Some (presented_run M s0 n) /\
    G.mu (Yrun s0 N) = mledger M s0 n + surcharge M s0 n /\
    G.cert (Yrun s0 N) = mlatch M s0 n.
Proof.
  intros n Hn. destruct (cg_y_head n Hn) as (N & HN & Hp).
  destruct (cg_point_facts n N Hp) as (A & B & C & D & E & _).
  exists N. split; [exact HN |]. split; [destruct Hp as (? & _ & Hpc & _); exact Hpc |].
  auto.
Qed.

Theorem cg_guest_halts_at : forall n,
  (forall m, m < n -> pm_next M (presented_run M s0 m) <> None) ->
  pm_next M (presented_run M s0 n) = None ->
  exists N,
    P.pr_halted cg_guest (G.core_of (Yrun s0 N)) /\
    pm_sdec M (cg_expo (qs 0) (G.cb (G.core_of (Yrun s0 N)))) = Some (presented_run M s0 n) /\
    G.mu (Yrun s0 N) = mledger M s0 n + surcharge M s0 n /\
    G.cert (Yrun s0 N) = mlatch M s0 n /\
    (forall N', N <= N' -> Yrun s0 N' = Yrun s0 N).
Proof.
  intros n Hn E. destruct (cg_y_head n Hn) as (N0 & _ & Hp).
  destruct (cg_y_stop n N0 Hp E) as (N & _ & Hh).
  destruct (cg_yhalt_facts n N Hh) as (A & _ & C & D & F & _).
  exists N. split; [exact A |]. split; [exact C |]. split; [exact D |]. split; [exact F |].
  intros N' HN'. apply cg_run_prog_stay; [exact A | exact HN'].
Qed.

Theorem cg_guest_halting_iff :
  (exists N, P.pr_halted cg_guest (G.core_of (Yrun s0 N))) <->
  (exists n, mhalted M s0 n).
Proof.
  split.
  - intros [N HN]. destruct (cg_first_halt N) as [H | (h & _ & E & _)].
    + exfalso. destruct (cg_y_head N H) as (N' & HN' & Hp).
      apply (cg_point_live N N' Hp).
      rewrite (cg_run_prog_stay _ _ _ _ _ N N' HN HN'). exact HN.
    + exists h. exact E.
  - intros [n Hn]. destruct (cg_first_halt (S n)) as [H | (h & _ & E & Hb)].
    + exfalso. exact (H n ltac:(lia) Hn).
    + destruct (cg_guest_halts_at h Hb E) as (N & HN & _). exists N. exact HN.
Qed.

Theorem cg_guest_flag_iff :
  (exists N, G.cert (Yrun s0 N) = true) <->
  (exists n, rd (presented_run M s0 n) = true).
Proof.
  split.
  - intros [N HN]. destruct (cg_cover N) as (N' & n & [e a] & HN' & [He Ha] & Hsim).
    cbn [snd] in Ha. subst a.
    assert (Hc : G.cert (Yrun s0 N') = true) by (exact (cg_cert_mono _ _ _ _ _ N N' HN' HN)).
    destruct Hsim as (_ & _ & _ & _ & H5 & _). cbn [cg_a_cert] in H5. rewrite Hc in H5.
    symmetry in H5. apply presented_mlatch_iff in H5. destruct H5 as (m & _ & Hm).
    exists m. exact Hm.
  - intros [n Hn]. destruct (cg_first_halt n) as [H | (h & Hh & E & Hb)].
    + destruct (cg_y_head n H) as (N & _ & Hp).
      destruct (cg_point_facts n N Hp) as (_ & _ & _ & _ & Hc & _).
      exists N. rewrite Hc. apply presented_mlatch_iff. exists n. auto.
    + destruct (cg_guest_halts_at h Hb E) as (N & _ & _ & _ & Hc & _).
      exists N. rewrite Hc. apply presented_mlatch_iff. exists h. split; [lia |].
      destruct (presented_halted_stable M s0 h n E ltac:(lia)) as [Hr _].
      rewrite <- Hr. exact Hn.
Qed.

(* The least index whose reading is yes. *)
Lemma cg_first_true : forall n m, m <= n -> rd (presented_run M s0 m) = true ->
  exists m0, rd (presented_run M s0 m0) = true /\
    forall m', m' < m0 -> rd (presented_run M s0 m') = false.
Proof.
  induction n as [| n IH]; intros m Hm H.
  - exists 0. assert (m = 0) as <- by lia. split; [exact H | intros; lia].
  - destruct (mlatch M s0 n) eqn:L.
    + apply presented_mlatch_iff in L. destruct L as (m1 & Hm1 & H1). exact (IH m1 Hm1 H1).
    + destruct (Nat.eq_dec m (S n)) as [-> | Hne]; [| exact (IH m ltac:(lia) H)].
      exists (S n). split; [exact H |]. intros m' Hm'.
      destruct (rd (presented_run M s0 m')) eqn:R'; [| reflexivity].
      assert (mlatch M s0 n = true)
        by (apply presented_mlatch_iff; exists m'; split; [lia | exact R']).
      congruence.
Qed.

Lemma cg_not_halted_before : forall m,
  rd (presented_run M s0 m) = true ->
  (forall m', m' < m -> rd (presented_run M s0 m') = false) ->
  forall h, h < m -> pm_next M (presented_run M s0 h) <> None.
Proof.
  intros m Hm Hb h Hh E.
  destruct (presented_halted_stable M s0 h m E ltac:(lia)) as [Hr _].
  rewrite Hr, (Hb h Hh) in Hm. discriminate.
Qed.

Lemma cg_latch_before : forall m,
  (forall m', m' < m -> rd (presented_run M s0 m') = false) ->
  forall m', m' < m -> mlatch M s0 m' = false.
Proof.
  intros m Hb m' Hm'. destruct (mlatch M s0 m') eqn:L; [| reflexivity].
  apply presented_mlatch_iff in L. destruct L as (k & Hk & Hr).
  rewrite (Hb k ltac:(lia)) in Hr. discriminate.
Qed.

(* At the first index m whose reading is yes, the guest reaches the image
   of NEW with the record unearned, the flag down, S holding the code of
   the state after m steps, and the fixed checker accepting. *)
Lemma cg_y_new : forall m,
  rd (presented_run M s0 m) = true ->
  (forall m', m' < m -> rd (presented_run M s0 m') = false) ->
  exists L ex a, G.pc (G.core_of (Yrun s0 L)) = lnk (cg_NEW M pc) /\
    cg_simul K (ex, a) (Yrun s0 L) /\ cg_a_earned a = false /\ cg_a_cert a = false /\
    ex 0 = sc (presented_run M s0 m) /\ cg_ueval (URun R) (cg_gk K ex) = true.
Proof.
  intros m Hm Hb. destruct m as [| m'].
  - destruct (cg_x_to_new M pc s0 0 (cg_e0 M s0) (cg_mkaux 0 false false)
                (cg_e0_rf M pc s0) Hm) as (ex & t & Hex & Hp & Hck).
    assert (Hx : sss_progress (cg_xstep K R) (1, SRC)
                   (1, (cg_e0 M s0, cg_mkaux 0 false false))
                   (cg_NEW M pc, (ex, cg_mkaux 0 false false))).
    { eapply sss_progress_trans; [| exact Hp].
      apply cg_x_dec0 with (x := 8); [exact (cg_sc_jmp0 M pc) |].
      rewrite (cg_e0_rf M pc s0). reflexivity. }
    destruct (cg_y_phase 1 _ _ _ _ Hx cg_ystart_simul (eq_sym (cg_link_start (1, SRC) 1)))
      as (q & w & _ & Hrun & Hpc & Hsim).
    exists q, ex, (cg_mkaux 0 false false). rewrite Hrun.
    split; [exact Hpc |]. split; [exact Hsim |]. split; [reflexivity |]. split; [reflexivity |].
    split; [rewrite Hex; reflexivity | exact Hck].
  - assert (Hnh := cg_not_halted_before (S m') Hm Hb).
    destruct (cg_y_head m' (fun h Hh => Hnh h ltac:(lia))) as (N & _ & [e a] & [He Ha] & Hpc & Hsim).
    cbn [fst snd] in He, Ha.
    destruct (pm_next M (presented_run M s0 m')) as [i |] eqn:E;
      [| exfalso; exact (Hnh m' ltac:(lia) E)].
    assert (Hl : mlatch M s0 m' = false) by (apply (cg_latch_before (S m') Hb); lia).
    rewrite Hl in He, Ha.
    destruct (cg_x_move M pc _ i 0 e a He E) as (e1 & He1 & H1).
    assert (Hrd : rd (cstep (presented_run M s0 m') i) = true).
    { rewrite presented_run_succ, E in Hm. exact Hm. }
    destruct (cg_x_to_new M pc _ _ e1 a He1 Hrd) as (ex & t & Hex & Hp & Hck).
    assert (Hx : sss_progress (cg_xstep K R) (1, SRC) (2, (e, a)) (cg_NEW M pc, (ex, a)))
      by (eapply sss_progress_trans; [exact H1 | exact Hp]).
    destruct (cg_y_phase 2 _ _ _ _ Hx Hsim Hpc) as (q & w & _ & Hrun & Hpc' & Hsim').
    exists (N + q), ex, a. rewrite cg_run_prog_add, Hrun.
    split; [exact Hpc' |]. split; [exact Hsim' |]. subst a.
    split; [reflexivity |]. split; [reflexivity |].
    split; [| exact Hck]. rewrite Hex, presented_run_succ, E. reflexivity.
Qed.

Theorem cg_guest_earned : forall N, G.cert (Yrun s0 N) = true ->
  P.pr_passing_checks cg_uprop_eqb cg_ueval
    (P.pr_trace_of cg_uprop_eqb cg_ueval N cg_guest (cg_ystart s0)) (cg_ystart s0) = 1 /\
  exists L m, L < N /\
    rd (presented_run M s0 m) = true /\
    (forall m', m' < m -> rd (presented_run M s0 m') = false) /\
    P.pr_next_instr cg_guest (G.core_of (Yrun s0 L)) = Some (P.CHECK (URun R) G.CB) /\
    G.check_ok cg_ueval (G.core_of (Yrun s0 L)) (URun R) G.CB = true /\
    pm_sdec M (cg_expo (qs 0) (G.cb (G.core_of (Yrun s0 L)))) = Some (presented_run M s0 m) /\
    (forall L', L' < N ->
       cg_passes_at cg_uprop_eqb cg_ueval cg_guest (cg_ystart s0) L' = 1 -> L' = L).
Proof.
  intros N HN.
  destruct (proj1 cg_guest_flag_iff (ex_intro _ N HN)) as [n Hn].
  destruct (cg_first_true n n (le_n n) Hn) as (m & Hm & Hb).
  destruct (cg_y_new m Hm Hb) as (L & ex & a & Hpc & Hsim & Hea & Hca & Hex0 & Hck).
  destruct Hsim as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn [cg_a_mu cg_a_cert cg_a_earned] in H4, H5, H7, H8.
  destruct (H7 Hea) as [Hf _].
  assert (Hnext : P.pr_next_instr cg_guest (G.core_of (Yrun s0 L)) = Some (P.CHECK (URun R) G.CB)).
  { unfold P.pr_next_instr. rewrite H6, Hpc, cg_fetch_new. reflexivity. }
  assert (Hok : G.check_ok cg_ueval (G.core_of (Yrun s0 L)) (URun R) G.CB = true).
  { unfold G.check_ok. rewrite H6, Hf. cbn [G.val]. rewrite H2, Hck. reflexivity. }
  assert (Hpass : cg_passes_at cg_uprop_eqb cg_ueval cg_guest (cg_ystart s0) L = 1).
  { unfold cg_passes_at. cbv zeta. rewrite Hnext. unfold P.pr_passes. rewrite Hok. reflexivity. }
  assert (HLN : L < N).
  { destruct (le_lt_dec N L) as [Hle | Hlt]; [| exact Hlt].
    pose proof (cg_cert_mono _ _ _ _ _ N L Hle HN) as C. rewrite H5, Hca in C. discriminate. }
  assert (Hup : cg_psum cg_uprop_eqb cg_ueval cg_guest (cg_ystart s0) N <= 1).
  { destruct (cg_cover N) as (N' & n' & [e' a'] & HN' & _ & Hsim').
    destruct Hsim' as (_ & _ & _ & _ & _ & _ & K7 & K8).
    pose proof (P.pr_facts_count_program cg_uprop_eqb cg_ueval N' cg_guest (cg_ystart s0)) as Hc.
    rewrite cg_passing_sum in Hc. cbn [cg_ystart G.start G.start_core G.core_of G.facts length] in Hc.
    assert (Hl1 : length (G.facts (G.core_of (Yrun s0 N'))) <= 1).
    { destruct (cg_a_earned a') eqn:Ea.
      - rewrite (proj2 (K8 eq_refl)). lia.
      - rewrite (proj1 (K7 eq_refl)). simpl. lia. }
    generalize (cg_psum_mono _ cg_uprop_eqb cg_ueval cg_guest (cg_ystart s0) N N' HN'). lia. }
  assert (Hlow := cg_psum_ge _ cg_uprop_eqb cg_ueval cg_guest (cg_ystart s0) N L HLN).
  split.
  { rewrite cg_passing_sum. lia. }
  exists L, m. split; [exact HLN |]. split; [exact Hm |]. split; [exact Hb |].
  split; [exact Hnext |]. split; [exact Hok |]. split.
  { rewrite H2, cg_expo_gk_zero by exact H3. rewrite Hex0. apply pm_sdec_scode. }
  intros L' HL' Hp'. destruct (Nat.eq_dec L' L) as [-> | Hne]; [reflexivity |].
  generalize (cg_psum_two _ cg_uprop_eqb cg_ueval cg_guest (cg_ystart s0) N L L' HLN HL'
                ltac:(congruence)). lia.
Qed.

(* ================================================================= *)
(* The converse direction, stated for the source program.              *)
(* ================================================================= *)

(* The source program reaches HEAD with the invariant at n while the
   driver has not halted before step n. *)
Lemma cg_x_reach_head : forall n,
  (forall m, m < n -> pm_next M (presented_run M s0 m) <> None) ->
  exists x, cg_inv_head M pc s0 n x /\
    sss_progress (cg_xstep K R) (1, SRC) (1, cg_xstart (cg_e0 M s0)) (2, x).
Proof.
  induction n as [| n IH]; intros Hn.
  - exact (cg_x_prologue M pc s0).
  - destruct (IH (fun m Hm => Hn m ltac:(lia))) as (x & Hinv & Hx).
    destruct (pm_next M (presented_run M s0 n)) as [i |] eqn:E;
      [| exfalso; exact (Hn n ltac:(lia) E)].
    destruct (cg_x_step M pc s0 n x i Hinv E) as (x' & Hinv' & Hx').
    exists x'. split; [exact Hinv' | eapply sss_progress_trans; [exact Hx | exact Hx']].
Qed.

(* At HALTB the source program has no step. *)
Lemma cg_x_halted : forall x st,
  ~ sss_step (cg_xstep K R) (1, SRC) (cg_HALTB M pc, x) st.
Proof.
  intros x st (k0 & l & I & r0 & d & HP & Hst & Hs).
  assert (HI : (cg_HALTB M pc, [I]) <sc (1, SRC)).
  { rewrite HP. injection Hst as Hi _. rewrite Hi. exists l, r0. split; reflexivity. }
  rewrite (subcode_cons_inj _ _ _ _ HI (cg_sc_halt M pc)) in Hs. inversion Hs.
Qed.

(* If some run of the guest halts, the source program, from its start,
   reaches HALTB (where it has no step) with the invariant at some n. *)
Theorem cg_source_halts_of_guest :
  (exists N, P.pr_halted cg_guest (G.core_of (Yrun s0 N))) ->
  exists n x, cg_inv_head M pc s0 n x /\ pm_next M (presented_run M s0 n) = None /\
    sss_progress (cg_xstep K R) (1, SRC) (1, cg_xstart (cg_e0 M s0)) (cg_HALTB M pc, x) /\
    forall st, ~ sss_step (cg_xstep K R) (1, SRC) (cg_HALTB M pc, x) st.
Proof.
  intros H. apply cg_guest_halting_iff in H. destruct H as [n Hn].
  destruct (cg_first_halt (S n)) as [Hb | (h & _ & E & Hb)];
    [exfalso; exact (Hb n ltac:(lia) Hn) |].
  destruct (cg_x_reach_head h Hb) as (x & Hinv & Hx).
  destruct (cg_x_stop M pc s0 h x Hinv E) as (x' & Hinv' & Hx').
  exists h, x'. split; [exact Hinv' |]. split; [exact E |].
  split; [eapply sss_progress_trans; [exact Hx | exact Hx'] | apply cg_x_halted].
Qed.

(* If some run of the guest raises the flag, the source program, from its
   start, reaches HEAD or HALTB with the certified flag of its record up. *)
Theorem cg_source_certifies_of_guest :
  (exists N, G.cert (Yrun s0 N) = true) ->
  exists n i x, (i = 2 \/ i = cg_HALTB M pc) /\ cg_inv_head M pc s0 n x /\
    cg_a_cert (snd x) = true /\
    sss_progress (cg_xstep K R) (1, SRC) (1, cg_xstart (cg_e0 M s0)) (i, x).
Proof.
  intros H. apply cg_guest_flag_iff in H. destruct H as [n Hn].
  destruct (cg_first_halt n) as [Hb | (h & Hh & E & Hb)].
  - destruct (cg_x_reach_head n Hb) as (x & [He Ha] & Hx).
    exists n, 2, x. split; [left; reflexivity |]. split; [split; assumption |].
    split; [| exact Hx]. rewrite Ha. cbn [cg_a_cert].
    apply presented_mlatch_iff. exists n. auto.
  - destruct (cg_x_reach_head h Hb) as (x & Hinv & Hx).
    destruct (cg_x_stop M pc s0 h x Hinv E) as (x' & [He Ha] & Hx').
    exists h, (cg_HALTB M pc), x'. split; [right; reflexivity |]. split; [split; assumption |].
    split; [| eapply sss_progress_trans; [exact Hx | exact Hx']].
    rewrite Ha. cbn [cg_a_cert]. apply presented_mlatch_iff. exists h. split; [lia |].
    destruct (presented_halted_stable M s0 h n E ltac:(lia)) as [Hr _].
    rewrite <- Hr. exact Hn.
Qed.

End Run.
