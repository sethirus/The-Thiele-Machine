(** AxCgkLang: the source language of the compiler with a record that can be
    earned more than once.

    The compiler of the repository (CompilerLifts.v, CompilerIcomp.v) turns a
    program over many counter registers (language X) into a program of the
    two-counter priced machine (language Y).  Its instruction XEARN adds 3 to
    the ledger and raises the flag, but only while the record has not
    been earned (cg_a_earned = false).  A guest compiled that way therefore makes
    one chain, CHECK, COMMIT, CERTIFY, and no more.

    Here the earned mark is a COUNT.  XEARN steps while fewer than 16 chains
    have been made (the fact table of the machine holds 16), adds 3 to the
    ledger, raises the flag and adds one to the count.  The target language,
    the instruction compiler (cg_icomp), the linker and the whole-program
    simulation are those of the repository; only the source semantics and the
    simulation relation change, and the XEARN case of the soundness proof
    becomes a proof for any earlier facts, any channel and any flag.

    The simulation relation says, besides what cg_simul says: the fact table
    has exactly as many facts as the count; with count 0 the channel is
    empty; with a positive count the flag is up and the channel committed.

    Results (all closed):

      ax_cgk_lift_mm          a counter run on registers below k is an X run
                           that keeps the record;
      ax_cgk_icomp_sound      the instruction compiler is sound for the new
                           source semantics and simulation;
      ax_cgk_compile_sound    whole-program simulation;
      ax_cgk_compile_start    at address 1 the compiled program runs on the
                           priced machine's own runner from the start state;
      ax_cgk_simul_start      the start relation. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is part of the compiler pipeline for chain machines, built on the
   repository's compiler files (CompilerGuest.v and the files it uses). The
   statements that connect it to the axis and to the host that runs the chain
   are AxCgkAxis.v and AxCgkHost.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.Shared.Libs.DLW.Utils Require Import gcd.
From Undecidability.Shared.Libs.DLW.Code Require Import compiler compiler_correction.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs mma_utils.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Minimal.EarnedGeneric Minimal.EarnedPriced.
Module G := Minimal.EarnedGeneric.
Module P := Minimal.EarnedPriced.
Require Import Kernel.CompilerCodes Kernel.CompilerChecker Kernel.CompilerLifts Kernel.CompilerIcomp.

#[local] Opaque qs.

(** * 1. The source semantics *)

Record ax_cgk_aux : Type := ax_cgk_mkaux {
  ax_cgk_a_mu : nat;
  ax_cgk_a_cert : bool;
  ax_cgk_a_earned : nat }.

Definition ax_cgk_xstate : Type := (env nat nat * ax_cgk_aux)%type.

Definition ax_cgk_pay (a : ax_cgk_aux) : ax_cgk_aux :=
  ax_cgk_mkaux (S (ax_cgk_a_mu a)) (ax_cgk_a_cert a) (ax_cgk_a_earned a).

Definition ax_cgk_earn (a : ax_cgk_aux) : ax_cgk_aux :=
  ax_cgk_mkaux (ax_cgk_a_mu a + 3) true (S (ax_cgk_a_earned a)).

Inductive ax_cgk_xstep (k r : nat) : cg_xinstr -> nat * ax_cgk_xstate -> nat * ax_cgk_xstate -> Prop :=
| ax_cgk_xstep_mm : forall J i e j e' a,
    cg_xreg J < k ->
    mm_sss_env eq_nat_dec J (i, e) (j, e') ->
    ax_cgk_xstep k r (XMM J) (i, (e, a)) (j, (e', a))
| ax_cgk_xstep_pay : forall i e a,
    ax_cgk_xstep k r XPAY (i, (e, a)) (S i, (e, ax_cgk_pay a))
| ax_cgk_xstep_earn : forall i e a,
    cg_ueval (URun r) (cg_gk k e) = true ->
    ax_cgk_a_earned a < 16 ->
    ax_cgk_xstep k r XEARN (i, (e, a)) (S i, (e, ax_cgk_earn a)).

Lemma ax_cgk_xstep_fun : forall k r J st st1 st2,
  ax_cgk_xstep k r J st st1 -> ax_cgk_xstep k r J st st2 -> st1 = st2.
Proof.
  intros k r J st st1 st2 H1 H2. destruct H1; inversion H2; subst; try reflexivity.
  match goal with
  | H : mm_sss_env _ _ _ _, H' : mm_sss_env _ _ _ _ |- _ =>
      generalize (mm_sss_env_fun H H'); intros E; injection E as -> ->; reflexivity
  end.
Qed.

Theorem ax_cgk_lift_mm : forall k r i0 (Q : list (mm_instr nat)) n i e j e' a,
  (forall J, In J Q -> cg_xreg J < k) ->
  sss_steps (mm_sss_env eq_nat_dec) (i0, Q) n (i, e) (j, e') ->
  sss_steps (ax_cgk_xstep k r) (i0, map XMM Q) n (i, (e, a)) (j, (e', a)).
Proof.
  intros k r i0 Q n i e j e' a HQ Hs.
  assert (Hstep : forall J i1 d j1 d' (w : ax_cgk_xstate), In J Q ->
            mm_sss_env eq_nat_dec J (i1, d) (j1, d') -> w = (d, a) ->
            exists w', ax_cgk_xstep k r (XMM J) (i1, w) (j1, w') /\ w' = (d', a)).
  { intros J i1 d j1 d' w HJ H1 ->. exists (d', a). split; [| reflexivity].
    constructor; [apply HQ; exact HJ | exact H1]. }
  destruct (cg_sss_lift _ _ _ _ (mm_sss_env eq_nat_dec) (ax_cgk_xstep k r) XMM
              (fun d w => w = (d, a)) i0 Q Hstep n i e j e' (e, a) Hs eq_refl)
    as (w' & Hs' & ->).
  exact Hs'.
Qed.

(** * 2. The simulation relation *)

Definition ax_cgk_simul (k : nat) (st : ax_cgk_xstate) (s : cg_ystate) : Prop :=
  match st with
  | (e, a) =>
      G.ca (G.core_of s) = 0 /\
      G.cb (G.core_of s) = cg_gk k e /\
      (forall x, k <= x -> e x = 0) /\
      G.mu s = ax_cgk_a_mu a /\
      G.cert s = ax_cgk_a_cert a /\
      G.err (G.core_of s) = false /\
      length (G.facts (G.core_of s)) = ax_cgk_a_earned a /\
      (ax_cgk_a_earned a = 0 -> G.chan (G.core_of s) = None) /\
      (0 < ax_cgk_a_earned a -> G.cert s = true /\ G.chan (G.core_of s) <> None)
  end.

#[local] Opaque cg_ueval.

Lemma ax_cgk_simul_counter : forall k e a s s' e' v',
  ax_cgk_simul k (e, a) s -> cg_yrel v' s' -> cg_keep s s' ->
  vec_pos v' pos0 = 0 -> vec_pos v' pos1 = cg_gk k e' ->
  (forall x, k <= x -> e' x = 0) ->
  ax_cgk_simul k (e', a) s'.
Proof.
  intros k e a s s' e' v' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) (R1 & R2 & R3)
    (K1 & K2 & K3 & K4) V0 V1 Z.
  unfold ax_cgk_simul.
  split; [congruence |]. split; [congruence |]. split; [exact Z |].
  split; [congruence |]. split; [congruence |]. split; [exact R3 |].
  split; [congruence |]. split.
  - intros Ha. rewrite K2. apply H8, Ha.
  - intros Ha. destruct (H9 Ha) as [A B]. split; [congruence | rewrite K2; exact B].
Qed.

(** * 3. The record instructions on any earlier facts *)

Ltac ax_cgk_yexec_unfold :=
  unfold cg_yexec, cg_at, P.pr_exec, P.pr_cexec, P.pr_fires, P.pr_cost,
    G.check_ok, G.commit_ok, G.certify_ok, G.goto, G.record_fact, G.commit_to,
    G.claim, G.val, G.ver, G.fact_eqb, G.trap, G.fact_cap;
  cbn - [ cg_ueval ].

Lemma ax_cgk_yexec_chk : forall r i ca cb va vb pc fs ch mu ct,
  cg_ueval (URun r) cb = true -> length fs < 16 ->
  cg_yexec (YCHK r) i (G.mkst (G.mkcore ca cb va vb pc fs ch false) mu ct)
  = G.mkst (G.mkcore ca cb va vb (S i) (G.mkfact (URun r) G.CB vb :: fs) ch false) (mu + 1) ct.
Proof.
  intros r i ca cb va vb pc fs ch mu ct H Hlt. ax_cgk_yexec_unfold. rewrite H. cbn.
  rewrite (proj2 (Nat.leb_le (length fs) 15)) by lia.
  cbn. destruct ct; reflexivity.
Qed.

Lemma ax_cgk_yexec_cmt : forall r i ca cb va vb pc fs ch mu ct,
  cg_yexec (YCMT r) i
    (G.mkst (G.mkcore ca cb va vb pc (G.mkfact (URun r) G.CB vb :: fs) ch false) mu ct)
  = G.mkst (G.mkcore ca cb va vb (S i) (G.mkfact (URun r) G.CB vb :: fs)
                     (Some (G.mkfact (URun r) G.CB vb)) false) (mu + 1) ct.
Proof.
  intros. ax_cgk_yexec_unfold. rewrite !Nat.eqb_refl. cbn. destruct ct; reflexivity.
Qed.

(** * 4. Soundness of the instruction compiler *)

Theorem ax_cgk_icomp_sound : forall k r,
  instruction_compiler_sound (cg_icomp k r) (ax_cgk_xstep k r) cg_ystep (ax_cgk_simul k).
Proof.
  intros k r lnk J i1 v1 i2 v2 w1 Hs Hl Hsim.
  rewrite cg_icomp_length in Hl.
  inversion Hs as [J0 i e j e' a Hk Hm | i e a | i e a Hev Hea]; subst.
  - (* a counter instruction *)
    assert (Hy : cg_yrel (0 ## cg_gk k e ## vec_nil) w1).
    { destruct Hsim as (H1 & H2 & _ & _ & _ & H6 & _). repeat split; assumption. }
    assert (Hz : forall x, k <= x -> e x = 0) by (apply Hsim).
    destruct J0 as [x | x jj]; simpl in Hk;
      [| destruct (get_env e x) as [| u] eqn:Ex].
    + (* INC x *)
      apply mm_sss_env_INC_inv in Hm as [-> ->].
      destruct (cg_lift_mma2_progress (lnk i1)
                  (mma_mult_cst_with_zero pos1 pos0 (qs x) (lnk i1)) (lnk i1)
                  (0 ## cg_gk k e ## vec_nil) (8 + qs x + lnk i1)
                  (0 ## qs x * cg_gk k e ## vec_nil) w1)
        as (s' & Hp & Hr & Hkp).
      { apply mma_mult_cst_with_zero_progress; [exact cg_pos10 | reflexivity | reflexivity]. }
      { exact Hy. }
      exists s'. split.
      * assert (E : lnk (1 + i1) = 8 + qs x + lnk i1) by exact Hl.
        rewrite E. unfold cg_icomp.
        match type of Hp with
        | sss_progress _ _ _ (?t, _) => replace (8 + qs x + lnk i1) with t by lia
        end.
        exact Hp.
      * apply (ax_cgk_simul_counter k e a w1 s' _ _ Hsim Hr Hkp); [reflexivity | |].
        -- simpl. rewrite cg_get_env, cg_gk_inc by exact Hk. reflexivity.
        -- intros y Hy'. rewrite cg_set_env_neq by lia. apply Hz. exact Hy'.
    + (* DEC x jj, register zero: jump to jj *)
      apply mm_sss_env_DEC0_inv in Hm as [-> ->]; [| exact Ex].
      rename Ex into Hz0.
      assert (Hp0 : sss_progress (@mma_sss 2)
                (lnk i1, mma_div_branch pos1 pos0 (qs x) (lnk i1) (lnk (S i1))
                         ++ mma_jump (lnk jj) pos0)
                (lnk i1, 0 ## cg_gk k e ## vec_nil) (lnk jj, 0 ## cg_gk k e ## vec_nil)).
      { apply sss_progress_trans with
          (16 + 7 * qs x + lnk i1, 0 ## cg_gk k e ## vec_nil).
        - apply subcode_sss_progress with
            (P := (lnk i1, mma_div_branch pos1 pos0 (qs x) (lnk i1) (lnk (S i1)))).
          + apply subcode_left. reflexivity.
          + apply mma_div_branch_1_progress; [exact cg_pos10 | reflexivity | apply cg_qs_pos | |
                                              reflexivity].
            simpl. apply cg_gk_zero_not_div. rewrite cg_get_env in Hz0. exact Hz0.
        - apply subcode_sss_progress with (P := (16 + 7 * qs x + lnk i1, mma_jump (lnk jj) pos0)).
          + apply subcode_right. rewrite mma_div_branch_length. lia.
          + apply mma_jump_progress. reflexivity. }
      destruct (cg_lift_mma2_progress _ _ _ _ _ _ w1 Hp0 Hy) as (s' & Hp & Hr & Hkp).
      exists s'. split.
      * unfold cg_icomp. exact Hp.
      * apply (ax_cgk_simul_counter k e a w1 s' _ _ Hsim Hr Hkp); [reflexivity | reflexivity | exact Hz].
    + (* DEC x jj, register S u: divide and go on *)
      apply mm_sss_env_DEC1_inv with (u := u) in Hm as [-> ->]; [| exact Ex].
      rename Ex into Hu.
      assert (Hdiv : cg_gk k e = qs x * cg_gk k (set_env eq_nat_dec e x u)).
      { apply cg_gk_dec; [exact Hk | rewrite cg_get_env in Hu; exact Hu]. }
      assert (Hp0 : sss_progress (@mma_sss 2)
                (lnk i1, mma_div_branch pos1 pos0 (qs x) (lnk i1) (lnk (S i1))
                         ++ mma_jump (lnk jj) pos0)
                (lnk i1, 0 ## cg_gk k e ## vec_nil)
                (lnk (S i1), 0 ## cg_gk k (set_env eq_nat_dec e x u) ## vec_nil)).
      { apply subcode_sss_progress with
          (P := (lnk i1, mma_div_branch pos1 pos0 (qs x) (lnk i1) (lnk (S i1)))).
        - apply subcode_left. reflexivity.
        - apply mma_div_branch_0_progress with (a := cg_gk k (set_env eq_nat_dec e x u));
            [exact cg_pos10 | reflexivity | apply cg_qs_pos | | reflexivity].
          simpl. rewrite Hdiv. ring. }
      destruct (cg_lift_mma2_progress _ _ _ _ _ _ w1 Hp0 Hy) as (s' & Hp & Hr & Hkp).
      exists s'. split.
      * unfold cg_icomp. exact Hp.
      * apply (ax_cgk_simul_counter k e a w1 s' _ _ Hsim Hr Hkp); [reflexivity | reflexivity |].
        intros y Hy'. rewrite cg_set_env_neq by lia. apply Hz. exact Hy'.
  - (* XPAY *)
    destruct w1 as [[ca cb va vb pc fs ch er] mu ct].
    destruct Hsim as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). simpl in *. subst er.
    exists (G.mkst (G.mkcore ca cb va vb (S (lnk i1)) fs ch false) (mu + 1) ct). split.
    + exists 1. split; [lia |]. apply sss_steps_1. simpl in Hl. rewrite Hl.
      unfold cg_icomp. change (lnk i1, [YPAY]) with (lnk i1, [] ++ YPAY :: []).
      replace (lnk i1) with (lnk i1 + length (@nil cg_yinstr)) at 2 by (simpl; lia).
      apply cg_ystep_code. simpl. rewrite Nat.add_0_r.
      unfold cg_ystep. simpl. split; [discriminate |]. split; [reflexivity |].
      split; [rewrite cg_yexec_pay; reflexivity |]. split; reflexivity.
    + unfold ax_cgk_simul, ax_cgk_pay. simpl.
      split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |]. split; [lia |].
      split; [exact H5 |]. split; [reflexivity |]. split; [exact H7 |]. split; [exact H8 | exact H9].
  - (* XEARN *)
    destruct w1 as [[ca cb va vb pc fs ch er] mu ct].
    destruct Hsim as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). simpl in *. subst er.
    subst ca cb.
    assert (Hlen : length fs < 16) by lia.
    set (f := G.mkfact (URun r) G.CB vb).
    set (s1 := G.mkst (G.mkcore 0 (cg_gk k e) va vb (S (lnk i1)) (f :: fs) ch false) (mu + 1) ct).
    set (s2 := G.mkst (G.mkcore 0 (cg_gk k e) va vb (S (S (lnk i1))) (f :: fs) (Some f) false)
                 (mu + 1 + 1) ct).
    set (s3 := G.mkst (G.mkcore 0 (cg_gk k e) va vb (S (S (S (lnk i1)))) (f :: fs) (Some f) false)
                 (mu + 1 + 1 + 1) true).
    exists s3. split.
    + exists 3. split; [lia |]. simpl in Hl. rewrite Hl. unfold cg_icomp.
      apply in_sss_steps_S with (S (lnk i1), s1).
      { change (lnk i1, [YCHK r; YCMT r; YCRT]) with (lnk i1, [] ++ YCHK r :: [YCMT r; YCRT]).
        replace (lnk i1) with (lnk i1 + length (@nil cg_yinstr)) at 2 by (simpl; lia).
        apply cg_ystep_code. simpl. rewrite Nat.add_0_r.
        unfold cg_ystep. simpl. split; [discriminate |]. split; [reflexivity |].
        split; [rewrite ax_cgk_yexec_chk by assumption; reflexivity |]. split; reflexivity. }
      apply in_sss_steps_S with (S (S (lnk i1)), s2).
      { change (lnk i1, [YCHK r; YCMT r; YCRT]) with (lnk i1, [YCHK r] ++ YCMT r :: [YCRT]).
        replace (S (lnk i1)) with (lnk i1 + length [YCHK r]) at 1 by (simpl; lia).
        apply cg_ystep_code. simpl. replace (lnk i1 + 1) with (S (lnk i1)) by lia.
        unfold cg_ystep. simpl. split; [discriminate |]. split; [reflexivity |].
        split; [unfold s1, f; rewrite ax_cgk_yexec_cmt; reflexivity |]. split; reflexivity. }
      apply sss_steps_1.
      change (lnk i1, [YCHK r; YCMT r; YCRT]) with (lnk i1, [YCHK r; YCMT r] ++ YCRT :: []).
      replace (S (S (lnk i1))) with (lnk i1 + length [YCHK r; YCMT r]) at 1 by (simpl; lia).
      replace (3 + lnk i1) with (S (S (S (lnk i1)))) by lia.
      apply cg_ystep_code. simpl. replace (lnk i1 + 2) with (S (S (lnk i1))) by lia.
      unfold cg_ystep. simpl. split; [discriminate |]. split; [reflexivity |].
      split; [unfold s2; rewrite cg_yexec_crt; reflexivity |]. split; reflexivity.
    + unfold ax_cgk_simul, ax_cgk_earn, s3. simpl.
      split; [reflexivity |]. split; [reflexivity |]. split; [exact H3 |]. split; [lia |].
      split; [reflexivity |]. split; [reflexivity |]. split; [lia |].
      split; [intros E; lia |]. intros _. split; [reflexivity | discriminate].
Qed.

(** * 5. Whole programs *)

Theorem ax_cgk_compile_sound : forall k r Px iQ i1 v1 i2 v2 w1,
  ax_cgk_simul k v1 w1 ->
  sss_compute (ax_cgk_xstep k r) Px (i1, v1) (i2, v2) ->
  exists w2, ax_cgk_simul k v2 w2 /\
    sss_compute cg_ystep (iQ, cg_code k r Px iQ) (cg_link Px iQ i1, w1) (cg_link Px iQ i2, w2).
Proof.
  intros k r Px iQ i1 v1 i2 v2 w1 Hs Hc.
  exact (compiler_sound cg_ilen (cg_icomp_length k r) (ax_cgk_icomp_sound k r)
           (cg_link Px iQ) (iQ, cg_code k r Px iQ)
           (fun i rho H => compiler_subcode (cg_icomp k r) cg_ilen (cg_icomp_length k r)
                             Px iQ (cg_err Px iQ) i rho H)
           w1 (conj Hs Hc)).
Qed.

Definition ax_cgk_xstart (e : env nat nat) : ax_cgk_xstate := (e, ax_cgk_mkaux 0 false 0).

Lemma ax_cgk_simul_start : forall k e,
  (forall y, k <= y -> e y = 0) ->
  ax_cgk_simul k (ax_cgk_xstart e) (G.start 0 (cg_gk k e)).
Proof.
  intros k e H. unfold ax_cgk_xstart, G.start, G.start_core. simpl.
  repeat split; auto; intros; lia.
Qed.

(** A source run of q steps is a target run of at least q steps, with the
    simulation relation kept. *)
Lemma ax_cgk_compile_steps : forall k r Px iQ q st1 st2 w1,
  ax_cgk_simul k (snd st1) w1 ->
  sss_steps (ax_cgk_xstep k r) Px q st1 st2 ->
  exists w2 q', q <= q' /\ ax_cgk_simul k (snd st2) w2 /\
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
    destruct (ax_cgk_icomp_sound k r (cg_link Px iQ) I (k0 + length l) d i2 v2 w1 Hstep)
      as (w2 & (p & Hp0 & Hp) & Hs2).
    { unfold cg_link. rewrite Hlen, cg_icomp_length. reflexivity. }
    { exact Hs. }
    destruct (IH w2 Hs2) as (w3 & q' & Hq & Hs3 & H3).
    exists w3, (p + q'). split; [lia |]. split; [exact Hs3 |].
    apply sss_steps_trans with (cg_link Px iQ i2, w2); [| exact H3].
    apply subcode_sss_steps with (1 := Hsc). exact Hp.
Qed.

(** At address 1, the compiled program runs on the priced machine's own
    runner from the start state. *)
Theorem ax_cgk_compile_start : forall k r (Q : list cg_xinstr) e i2 v2,
  (forall y, k <= y -> e y = 0) ->
  sss_compute (ax_cgk_xstep k r) (1, Q) (1, ax_cgk_xstart e) (i2, v2) ->
  exists n w2,
    P.pr_run_prog cg_uprop_eqb cg_ueval n (map cg_tr (cg_code k r (1, Q) 1))
      (G.start 0 (cg_gk k e)) = w2 /\
    ax_cgk_simul k v2 w2 /\
    G.pc (G.core_of w2) = cg_link (1, Q) 1 i2.
Proof.
  intros k r Q e i2 v2 He Hc.
  destruct (ax_cgk_compile_sound k r (1, Q) 1 1 (ax_cgk_xstart e) i2 v2 _ (ax_cgk_simul_start k e He) Hc)
    as (w2 & Hs2 & n & Hn).
  assert (E : cg_link (1, Q) 1 1 = 1) by apply (cg_link_start (1, Q) 1).
  rewrite E in Hn.
  destruct (cg_lift_run _ n 1 (G.start 0 (cg_gk k e)) _ _ eq_refl Hn) as [Hrun Hpc].
  exists n, w2. split; [exact Hrun | split; [exact Hs2 | exact Hpc]].
Qed.

Print Assumptions ax_cgk_xstep_fun.
Print Assumptions ax_cgk_lift_mm.
Print Assumptions ax_cgk_simul_counter.
Print Assumptions ax_cgk_yexec_chk.
Print Assumptions ax_cgk_yexec_cmt.
Print Assumptions ax_cgk_icomp_sound.
Print Assumptions ax_cgk_compile_sound.
Print Assumptions ax_cgk_simul_start.
Print Assumptions ax_cgk_compile_steps.
Print Assumptions ax_cgk_compile_start.
