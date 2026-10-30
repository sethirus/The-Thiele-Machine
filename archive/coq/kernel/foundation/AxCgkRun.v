(** AxCgkRun: the guest of a chain machine, run on the priced machine's own
    runner, and what it does.

    The guest of a chain machine C with presentation cp is the compiled source
    program of AxCgkGuest.v, translated to the priced machine's instructions
    by the compiler of the repository:

      ax_cgk_guest C cp = map cg_tr (cg_code K R (1, SRC) 1)

    with K = ax_cgk_k C cp, the routine code R = ax_cgk_r C cp and SRC = ax_cgk_SRC C cp.
    It starts from ax_cgk_ystart C cp s0 = G.start 0 g, where g is the Godel code of
    the register file holding the code of s0 in register 0.

    Results (all for every chain machine whose heights are at most 16, every
    presentation and every start):

      ax_cgk_guest_matching_points
          while the driver has not halted before step n, some run length N >= n
          reaches the image of HEAD, untrapped, with counter B decoding to the
          state after n steps, the ledger equal to ax_cm_gledger n, the flag up
          exactly when the latched height after n steps is positive, the number
          of facts equal to the latched height, and the channel committed
          exactly when the latched height is positive;
      ax_cgk_guest_halts_at
          when the driver first halts at step n, some run length reaches a
          halted state with the same decoding, ledger, flag and number of
          facts, and stays there;
      ax_cgk_guest_halting_iff
          some run of the guest halts exactly when the driver halts;
      ax_cgk_guest_facts_le
          at every run length the guest holds at most the latched height of a
          later matching step, in particular never more than 16 facts. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is part of the compiler pipeline for chain machines, built on the
   repository's compiler files (CompilerGuest.v and the files it uses). The
   statements that connect it to the axis and to the host that runs the chain
   are AxCgkAxis.v and AxCgkHost.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.Shared.Libs.DLW.Code Require Import compiler compiler_correction.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Minimal.EarnedGeneric Minimal.EarnedPriced.
Module G := Minimal.EarnedGeneric.
Module P := Minimal.EarnedPriced.
Require Import Kernel.CompilerCodes Kernel.CompilerChecker Kernel.CompilerLifts
  Kernel.CompilerIcomp Kernel.CompilerGuestRun.
From Kernel Require Import AxChain AxCgkLang AxCgkGuest.

Section Run.

Variable C : ax_chain_mach.
Variable cp : ax_chain_pres C.

Local Notation st := (ax_cm_st C).
Local Notation cstep := (ax_cm_step C).
Local Notation ccost := (ax_cm_cost C).
Local Notation hh := (ax_cm_h C).
Local Notation next := (ax_cm_next C).
Local Notation sc := (ax_cm_scode C).
Local Notation K := (ax_cgk_k C cp).
Local Notation R := (ax_cgk_r C cp).
Local Notation SRC := (ax_cgk_SRC C cp).
Local Notation lnk := (cg_link (1, ax_cgk_SRC C cp) 1).

Definition ax_cgk_guest : list (@P.pr_instr cg_uprop) := map cg_tr (cg_code K R (1, SRC) 1).

Definition ax_cgk_ystart (s0 : st) : cg_ystate := G.start 0 (cg_gk K (ax_cgk_e0 C s0)).

Local Notation Yrun s0 N := (P.pr_run_prog cg_uprop_eqb cg_ueval N ax_cgk_guest (ax_cgk_ystart s0)).
Local Notation Ystep := (P.pr_run_prog cg_uprop_eqb cg_ueval).

(* A source phase that makes progress is a target run of at least one step
   on the priced machine's own runner. *)
Lemma ax_cgk_y_phase : forall i x j x' w,
  sss_progress (ax_cgk_xstep K R) (1, SRC) (i, x) (j, x') ->
  ax_cgk_simul K x w -> G.pc (G.core_of w) = lnk i ->
  exists q w', 0 < q /\ Ystep q ax_cgk_guest w = w' /\ G.pc (G.core_of w') = lnk j /\
    ax_cgk_simul K x' w'.
Proof.
  intros i x j x' w (q0 & Hq0 & Hs) Hsim Hpc.
  destruct (ax_cgk_compile_steps K R (1, SRC) 1 q0 (i, x) (j, x') w Hsim Hs)
    as (w2 & q & Hq & Hsim2 & Hy).
  destruct (cg_lift_run _ q _ w _ w2 Hpc Hy) as [Hrun Hpc2].
  exists q, w2. split; [lia |]. split; [exact Hrun |]. split; [exact Hpc2 | exact Hsim2].
Qed.

(* The first instruction of the image of a source instruction. *)
Lemma ax_cgk_fetch_at : forall i J,
  (i, [J]) <sc (1, SRC) ->
  exists y rest, cg_icomp K R lnk i J = y :: rest /\ G.fetch ax_cgk_guest (lnk i) = Some (cg_tr y).
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
  destruct Hsc as (l & r' & Hc & Hi). unfold ax_cgk_guest. rewrite Hc, Hi.
  unfold G.fetch. replace (1 + length l) with (S (length l)) by lia.
  rewrite map_app. rewrite nth_error_app2 by (rewrite map_length; lia).
  rewrite map_length, Nat.sub_diag. reflexivity.
Qed.

Lemma ax_cgk_fetch_halt : G.fetch ax_cgk_guest (lnk (ax_cgk_HALTB C cp)) = Some P.HALT.
Proof.
  destruct (ax_cgk_fetch_at _ _ (ax_cgk_sc_halt C cp)) as (y & rest & E & F).
  simpl in E. injection E as <- _. exact F.
Qed.

Lemma ax_cgk_head_instr : exists J, (2, [XMM J]) <sc (1, SRC).
Proof.
  pose proof (ax_cgk_sc_next C cp) as H1. pose proof (ax_cgk_sc_dech C cp) as H2.
  destruct (ax_cgk_Pn C cp) as [| J l] eqn:E.
  - exists (mm_dec 2 (ax_cgk_HALTB C cp)). exact H2.
  - exists J. eapply subcode_trans; [| exact H1].
    simpl map. apply (ax_cgk_sc_here1 cg_xinstr 2 2 (XMM J) (map XMM l)). reflexivity.
Qed.

Lemma ax_cgk_fetch_head : exists y, G.fetch ax_cgk_guest (lnk 2) = Some (cg_tr (YMMA y)).
Proof.
  destruct ax_cgk_head_instr as [J HJ].
  destruct (ax_cgk_fetch_at _ _ HJ) as (y & rest & E & F).
  destruct J as [x | x j]; unfold cg_icomp in E;
    match type of E with map YMMA ?L = _ => destruct L as [| a L']; [discriminate |] end;
    simpl in E; injection E as <- _; exists a; exact F.
Qed.

(* ================================================================= *)
(* Matching points.                                                    *)
(* ================================================================= *)

Variable s0 : st.

Definition ax_cgk_ypoint (n N : nat) : Prop :=
  exists x, ax_cgk_inv_head C cp s0 n x /\ G.pc (G.core_of (Yrun s0 N)) = lnk 2 /\
            ax_cgk_simul K x (Yrun s0 N).

Lemma ax_cgk_ystart_simul : ax_cgk_simul K (ax_cgk_xstart (ax_cgk_e0 C s0)) (ax_cgk_ystart s0).
Proof. apply ax_cgk_simul_start. intros y Hy. apply (ax_cgk_e0_high C cp). exact Hy. Qed.

Lemma ax_cgk_y_head : ax_cm_bounded_from C s0 -> forall n,
  (forall m, m < n -> next (ax_cm_run C s0 m) <> None) ->
  exists N, n <= N /\ ax_cgk_ypoint n N.
Proof.
  intros Hb. induction n as [| n IH]; intros Hn.
  - destruct (ax_cgk_x_prologue C cp s0 (Hb 0)) as (x & Hinv & Hx).
    destruct (ax_cgk_y_phase 1 _ 2 x _ Hx ax_cgk_ystart_simul (eq_sym (cg_link_start (1, SRC) 1)))
      as (q & w & _ & Hrun & Hpc & Hsim).
    exists q. split; [lia |]. exists x. rewrite Hrun. auto.
  - destruct (IH (fun m Hm => Hn m ltac:(lia))) as (N & HN & x & Hinv & Hpc & Hsim).
    destruct (next (ax_cm_run C s0 n)) as [i |] eqn:E;
      [| exfalso; exact (Hn n ltac:(lia) E)].
    assert (Hb' : hh (cstep (ax_cm_run C s0 n) i) <= 16).
    { pose proof (Hb (S n)) as H. rewrite ax_cm_run_succ, E in H. exact H. }
    destruct (ax_cgk_x_step C cp s0 n x i Hb' Hinv E) as (x' & Hinv' & Hx).
    destruct (ax_cgk_y_phase 2 x 2 x' _ Hx Hsim Hpc) as (q & w & Hq & Hrun & Hpc' & Hsim').
    exists (N + q). split; [lia |]. exists x'.
    rewrite cg_run_prog_add, Hrun. auto.
Qed.

Lemma ax_cgk_point_facts : forall n N, ax_cgk_ypoint n N ->
  G.err (G.core_of (Yrun s0 N)) = false /\
  G.ca (G.core_of (Yrun s0 N)) = 0 /\
  ax_cm_sdec C (cg_expo (qs 0) (G.cb (G.core_of (Yrun s0 N)))) = Some (ax_cm_run C s0 n) /\
  G.mu (Yrun s0 N) = ax_cm_gledger C s0 n /\
  G.cert (Yrun s0 N) = Nat.ltb 0 (ax_cm_lat C s0 n) /\
  length (G.facts (G.core_of (Yrun s0 N))) = ax_cm_lat C s0 n /\
  (G.chan (G.core_of (Yrun s0 N)) = None <-> ax_cm_lat C s0 n = 0).
Proof.
  intros n N ([e a] & [He Ha] & _ & Hsim). cbn [fst snd] in He, Ha. subst a.
  destruct Hsim as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  cbn [ax_cgk_a_mu ax_cgk_a_cert ax_cgk_a_earned] in H4, H5, H7, H8, H9.
  split; [exact H6 |]. split; [exact H1 |]. split.
  { rewrite H2, cg_expo_gk_zero by exact H3. rewrite He. apply ax_cm_sdec_scode. }
  split; [exact H4 |]. split; [exact H5 |]. split; [exact H7 |].
  destruct (ax_cm_lat C s0 n) as [| u] eqn:Hl.
  - split; [intros _; reflexivity | intros _; apply H8; reflexivity].
  - split; [| intros E; discriminate E].
    intros Hc. destruct (H9 ltac:(lia)) as [_ Hne]. exact (False_ind _ (Hne Hc)).
Qed.

(* The image of HEAD is never a halting instruction. *)
Lemma ax_cgk_point_live : forall n N, ax_cgk_ypoint n N ->
  ~ P.pr_halted ax_cgk_guest (G.core_of (Yrun s0 N)).
Proof.
  intros n N Hp Hh. destruct (ax_cgk_point_facts n N Hp) as [Herr _].
  destruct Hp as (x & _ & Hpc & _). destruct ax_cgk_fetch_head as [y Hy].
  unfold P.pr_halted, P.pr_next_instr in Hh. rewrite Herr, Hpc, Hy in Hh.
  destruct y; discriminate.
Qed.

Definition ax_cgk_yhalt (n N : nat) : Prop :=
  exists x, ax_cgk_inv_head C cp s0 n x /\ G.pc (G.core_of (Yrun s0 N)) = lnk (ax_cgk_HALTB C cp) /\
            ax_cgk_simul K x (Yrun s0 N).

Lemma ax_cgk_y_stop : forall n N, ax_cgk_ypoint n N ->
  next (ax_cm_run C s0 n) = None ->
  exists N', N <= N' /\ ax_cgk_yhalt n N'.
Proof.
  intros n N (x & Hinv & Hpc & Hsim) E.
  destruct (ax_cgk_x_stop C cp s0 n x Hinv E) as (x' & Hinv' & Hx).
  destruct (ax_cgk_y_phase 2 x _ x' _ Hx Hsim Hpc) as (q & w & Hq & Hrun & Hpc' & Hsim').
  exists (N + q). split; [lia |]. exists x'. rewrite cg_run_prog_add, Hrun. auto.
Qed.

Lemma ax_cgk_yhalt_facts : forall n N, ax_cgk_yhalt n N ->
  P.pr_halted ax_cgk_guest (G.core_of (Yrun s0 N)) /\
  G.ca (G.core_of (Yrun s0 N)) = 0 /\
  ax_cm_sdec C (cg_expo (qs 0) (G.cb (G.core_of (Yrun s0 N)))) = Some (ax_cm_run C s0 n) /\
  G.mu (Yrun s0 N) = ax_cm_gledger C s0 n /\
  G.cert (Yrun s0 N) = Nat.ltb 0 (ax_cm_lat C s0 n) /\
  length (G.facts (G.core_of (Yrun s0 N))) = ax_cm_lat C s0 n /\
  (G.chan (G.core_of (Yrun s0 N)) = None <-> ax_cm_lat C s0 n = 0).
Proof.
  intros n N ([e a] & [He Ha] & Hpc & Hsim). cbn [fst snd] in He, Ha. subst a.
  destruct Hsim as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  cbn [ax_cgk_a_mu ax_cgk_a_cert ax_cgk_a_earned] in H4, H5, H7, H8, H9.
  split.
  { unfold P.pr_halted, P.pr_next_instr. rewrite H6, Hpc, ax_cgk_fetch_halt. reflexivity. }
  split; [exact H1 |]. split.
  { rewrite H2, cg_expo_gk_zero by exact H3. rewrite He. apply ax_cm_sdec_scode. }
  split; [exact H4 |]. split; [exact H5 |]. split; [exact H7 |].
  destruct (ax_cm_lat C s0 n) as [| u] eqn:Hl.
  - split; [intros _; reflexivity | intros _; apply H8; reflexivity].
  - split; [| intros E; discriminate E].
    intros Hc. destruct (H9 ltac:(lia)) as [_ Hne]. exact (False_ind _ (Hne Hc)).
Qed.

Lemma ax_cgk_yhalt_err : forall n N, ax_cgk_yhalt n N ->
  G.err (G.core_of (Yrun s0 N)) = false.
Proof.
  intros n N ([e a] & _ & _ & Hsim). destruct Hsim as (_ & _ & _ & _ & _ & H6 & _). exact H6.
Qed.

(* The first halt of the driver, if any, before step N. *)
Lemma ax_cgk_first_halt : forall N,
  (forall m, m < N -> next (ax_cm_run C s0 m) <> None) \/
  (exists h, h < N /\ next (ax_cm_run C s0 h) = None /\
     forall m, m < h -> next (ax_cm_run C s0 m) <> None).
Proof.
  induction N as [| N IH].
  - left. intros m Hm. lia.
  - destruct IH as [H | (h & Hh & E & Hb)].
    + destruct (next (ax_cm_run C s0 N)) as [i |] eqn:E.
      * left. intros m Hm. destruct (Nat.eq_dec m N) as [-> | Hne]; [rewrite E; discriminate |].
        apply H. lia.
      * right. exists N. split; [lia |]. split; [exact E | exact H].
    + right. exists h. split; [lia |]. split; [exact E | exact Hb].
Qed.

(* Every run length is covered by a later matching point or the halting
   point. *)
Lemma ax_cgk_cover : ax_cm_bounded_from C s0 -> forall N, exists N' n x, N <= N' /\ ax_cgk_inv_head C cp s0 n x /\
  ax_cgk_simul K x (Yrun s0 N').
Proof.
  intros Hb N. destruct (ax_cgk_first_halt N) as [H | (h & Hh & E & Hb')].
  - destruct (ax_cgk_y_head Hb N H) as (N' & HN & x & Hinv & _ & Hsim).
    exists N', N, x. auto.
  - destruct (ax_cgk_y_head Hb h Hb') as (Nh & _ & Hp).
    destruct (ax_cgk_y_stop h Nh Hp E) as (N1 & _ & x & Hinv & Hpc & Hsim).
    destruct (le_lt_dec N N1) as [Hle | Hlt].
    + exists N1, h, x. auto.
    + exists N, h, x. split; [lia |]. split; [exact Hinv |].
      rewrite (cg_run_prog_stay _ _ _ _ _ N1 N); [exact Hsim | | lia].
      apply (ax_cgk_yhalt_facts h N1). exists x. auto.
Qed.

(* ================================================================= *)
(* The guest theorems.                                                 *)
(* ================================================================= *)

Theorem ax_cgk_guest_matching_points : ax_cm_bounded_from C s0 -> forall n,
  (forall m, m < n -> next (ax_cm_run C s0 m) <> None) ->
  exists N, n <= N /\
    G.pc (G.core_of (Yrun s0 N)) = lnk 2 /\
    G.err (G.core_of (Yrun s0 N)) = false /\
    G.ca (G.core_of (Yrun s0 N)) = 0 /\
    ax_cm_sdec C (cg_expo (qs 0) (G.cb (G.core_of (Yrun s0 N)))) = Some (ax_cm_run C s0 n) /\
    G.mu (Yrun s0 N) = ax_cm_gledger C s0 n /\
    G.cert (Yrun s0 N) = Nat.ltb 0 (ax_cm_lat C s0 n) /\
    length (G.facts (G.core_of (Yrun s0 N))) = ax_cm_lat C s0 n /\
    (G.chan (G.core_of (Yrun s0 N)) = None <-> ax_cm_lat C s0 n = 0).
Proof.
  intros Hb n Hn. destruct (ax_cgk_y_head Hb n Hn) as (N & HN & Hp).
  destruct (ax_cgk_point_facts n N Hp) as (A & B & C0 & D & E & F & G0).
  exists N. split; [exact HN |]. split; [destruct Hp as (? & _ & Hpc & _); exact Hpc |].
  exact (conj A (conj B (conj C0 (conj D (conj E (conj F G0)))))).
Qed.

Theorem ax_cgk_guest_halts_at : ax_cm_bounded_from C s0 -> forall n,
  (forall m, m < n -> next (ax_cm_run C s0 m) <> None) ->
  next (ax_cm_run C s0 n) = None ->
  exists N,
    P.pr_halted ax_cgk_guest (G.core_of (Yrun s0 N)) /\
    ax_cm_sdec C (cg_expo (qs 0) (G.cb (G.core_of (Yrun s0 N)))) = Some (ax_cm_run C s0 n) /\
    G.mu (Yrun s0 N) = ax_cm_gledger C s0 n /\
    G.cert (Yrun s0 N) = Nat.ltb 0 (ax_cm_lat C s0 n) /\
    length (G.facts (G.core_of (Yrun s0 N))) = ax_cm_lat C s0 n /\
    (G.chan (G.core_of (Yrun s0 N)) = None <-> ax_cm_lat C s0 n = 0) /\
    G.err (G.core_of (Yrun s0 N)) = false /\
    (forall N', N <= N' -> Yrun s0 N' = Yrun s0 N).
Proof.
  intros Hb n Hn E. destruct (ax_cgk_y_head Hb n Hn) as (N0 & _ & Hp).
  destruct (ax_cgk_y_stop n N0 Hp E) as (N & _ & Hh).
  destruct (ax_cgk_yhalt_facts n N Hh) as (A & _ & C0 & D & F & G0 & H0).
  exists N. split; [exact A |]. split; [exact C0 |]. split; [exact D |]. split; [exact F |].
  split; [exact G0 |]. split; [exact H0 |]. split; [exact (ax_cgk_yhalt_err n N Hh) |].
  intros N' HN'. apply cg_run_prog_stay; [exact A | exact HN'].
Qed.

Theorem ax_cgk_guest_halting_iff : ax_cm_bounded_from C s0 ->
  (exists N, P.pr_halted ax_cgk_guest (G.core_of (Yrun s0 N))) <->
  (exists n, next (ax_cm_run C s0 n) = None).
Proof.
  intros Hb. split.
  - intros [N HN]. destruct (ax_cgk_first_halt N) as [H | (h & _ & E & _)].
    + exfalso. destruct (ax_cgk_y_head Hb N H) as (N' & HN' & Hp).
      apply (ax_cgk_point_live N N' Hp).
      rewrite (cg_run_prog_stay _ _ _ _ _ N N' HN HN'). exact HN.
    + exists h. exact E.
  - intros [n Hn]. destruct (ax_cgk_first_halt (S n)) as [H | (h & _ & E & Hb')].
    + exfalso. exact (H n ltac:(lia) Hn).
    + destruct (ax_cgk_guest_halts_at Hb h Hb' E) as (N & HN & _). exists N. exact HN.
Qed.

(* At every run length the fact table holds at most 16 facts, and the
   number of facts is at most the latched height of a later matching step. *)
Theorem ax_cgk_guest_facts_le : ax_cm_bounded_from C s0 -> forall N,
  exists n, length (G.facts (G.core_of (Yrun s0 N))) <= ax_cm_lat C s0 n /\
            ax_cm_lat C s0 n <= 16.
Proof.
  intros Hb N. destruct (ax_cgk_cover Hb N) as (N' & n & [e a] & HN' & [He Ha] & Hsim).
  cbn [snd] in Ha. subst a.
  destruct Hsim as (_ & _ & _ & _ & _ & _ & H7 & _).
  cbn [ax_cgk_a_earned] in H7.
  exists n. split; [| exact (ax_cm_lat_le_from C s0 Hb n)].
  rewrite <- H7.
  pose proof (P.pr_facts_count_program cg_uprop_eqb cg_ueval (N' - N) ax_cgk_guest (Yrun s0 N)) as Hc.
  rewrite <- (cg_run_prog_add _ cg_uprop_eqb cg_ueval N (N' - N)) in Hc.
  replace (N + (N' - N)) with N' in Hc by lia.
  lia.
Qed.

End Run.

Print Assumptions ax_cgk_y_phase.
Print Assumptions ax_cgk_y_head.
Print Assumptions ax_cgk_point_facts.
Print Assumptions ax_cgk_cover.
Print Assumptions ax_cgk_guest_matching_points.
Print Assumptions ax_cgk_guest_halts_at.
Print Assumptions ax_cgk_guest_halting_iff.
Print Assumptions ax_cgk_guest_facts_le.
