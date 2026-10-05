(** CompilerIcomp.v: the instruction compiler from the many-register
    source language X to the two-counter target language Y, its soundness,
    and whole-program simulation.

    Counter A of the target is the spare counter, always 0 between source
    instructions; counter B holds the Godel code cg_gk k e of the source
    registers. Following the pattern of the vendored
    mma_k_mma_2_compiler.v:

      XMM (INC x)    multiply B by qs x       (mma_mult_cst_with_zero)
      XMM (DEC x j)  if qs x divides B, divide and go on to the next
                     instruction; otherwise jump to the image of j
                     (mma_div_branch, then mma_jump)
      XPAY           YPAY
      XEARN          YCHK r; YCMT r; YCRT
      XHALT          YHALT

    The simulation relation cg_simul k (e, a) s says: A is 0, B is the code
    of e, the registers from k on are 0, the ledger and flag of s are those
    of a, s is not trapped, an unearned record has no facts and no
    commitment, and an earned record has the flag up and exactly one fact.

    cg_icomp_sound is the vendored instruction_compiler_sound for this
    compiler. With the vendored linker and compiler of compiler.v,
    compiler_sound then gives whole-program simulation [cg_compile_sound],
    and at address 1 the target run is EarnedPriced's own runner from the
    start state G.start 0 (cg_gk k e) [cg_compile_start].

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, EarnedGeneric.v, EarnedPriced.v and the Compiler*.v files
    before this one. No axioms, no Admitted. *)

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
Require Import Minimal.CompilerCodes Minimal.CompilerChecker Minimal.CompilerLifts.

#[local] Opaque qs.

(* ================================================================= *)
(* The instruction compiler.                                          *)
(* ================================================================= *)

Definition cg_ilen (J : cg_xinstr) : nat :=
  match J with
  | XMM (mm_inc x) => 8 + qs x
  | XMM (mm_dec x _) => 18 + 7 * qs x
  | XPAY => 1
  | XEARN => 3
  | XHALT => 1
  end.

Definition cg_icomp (k r : nat) (lnk : nat -> nat) (i : nat) (J : cg_xinstr)
  : list cg_yinstr :=
  match J with
  | XMM (mm_inc x) => map YMMA (mma_mult_cst_with_zero pos1 pos0 (qs x) (lnk i))
  | XMM (mm_dec x j) =>
      map YMMA (mma_div_branch pos1 pos0 (qs x) (lnk i) (lnk (S i))
                ++ mma_jump (lnk j) pos0)
  | XPAY => [YPAY]
  | XEARN => [YCHK r; YCMT r; YCRT]
  | XHALT => [YHALT]
  end.

Lemma cg_icomp_length : forall k r lnk n J, length (cg_icomp k r lnk n J) = cg_ilen J.
Proof.
  intros k r lnk n [[x | x j] | | |]; unfold cg_icomp, cg_ilen; try reflexivity.
  - rewrite map_length, mma_mult_cst_with_zero_length. reflexivity.
  - rewrite map_length, app_length, mma_div_branch_length, mma_jump_length. lia.
Qed.

Definition cg_simul (k : nat) (st : cg_xstate) (s : cg_ystate) : Prop :=
  match st with
  | (e, a) =>
      G.ca (G.core_of s) = 0 /\
      G.cb (G.core_of s) = cg_gk k e /\
      (forall x, k <= x -> e x = 0) /\
      G.mu s = cg_a_mu a /\
      G.cert s = cg_a_cert a /\
      G.err (G.core_of s) = false /\
      (cg_a_earned a = false -> G.facts (G.core_of s) = [] /\ G.chan (G.core_of s) = None) /\
      (cg_a_earned a = true -> G.cert s = true /\ length (G.facts (G.core_of s)) = 1)
  end.

(* ================================================================= *)
(* The record instructions on concrete states.                         *)
(* ================================================================= *)

#[local] Opaque cg_ueval.

Ltac cg_yexec_unfold :=
  unfold cg_yexec, cg_at, P.pr_exec, P.pr_cexec, P.pr_fires, P.pr_cost,
    G.check_ok, G.commit_ok, G.certify_ok, G.goto, G.record_fact, G.commit_to,
    G.claim, G.val, G.ver, G.fact_eqb, G.trap, G.fact_cap;
  cbn - [ cg_ueval ].

Lemma cg_yexec_pay : forall i ca cb va vb pc fs ch mu ct,
  cg_yexec YPAY i (G.mkst (G.mkcore ca cb va vb pc fs ch false) mu ct)
  = G.mkst (G.mkcore ca cb va vb (S i) fs ch false) (mu + 1) ct.
Proof. intros. cg_yexec_unfold. destruct ct; reflexivity. Qed.

Lemma cg_yexec_chk : forall r i ca cb va vb pc ch mu ct,
  cg_ueval (URun r) cb = true ->
  cg_yexec (YCHK r) i (G.mkst (G.mkcore ca cb va vb pc [] ch false) mu ct)
  = G.mkst (G.mkcore ca cb va vb (S i) [G.mkfact (URun r) G.CB vb] ch false) (mu + 1) ct.
Proof.
  intros r i ca cb va vb pc ch mu ct H. cg_yexec_unfold. rewrite H. cbn.
  destruct ct; reflexivity.
Qed.

Lemma cg_yexec_cmt : forall r i ca cb va vb pc ch mu ct,
  cg_yexec (YCMT r) i
    (G.mkst (G.mkcore ca cb va vb pc [G.mkfact (URun r) G.CB vb] ch false) mu ct)
  = G.mkst (G.mkcore ca cb va vb (S i) [G.mkfact (URun r) G.CB vb]
                     (Some (G.mkfact (URun r) G.CB vb)) false) (mu + 1) ct.
Proof.
  intros. cg_yexec_unfold. rewrite !Nat.eqb_refl. cbn. destruct ct; reflexivity.
Qed.

Lemma cg_yexec_crt : forall i ca cb va vb pc fs f mu ct,
  cg_yexec YCRT i (G.mkst (G.mkcore ca cb va vb pc fs (Some f) false) mu ct)
  = G.mkst (G.mkcore ca cb va vb (S i) fs (Some f) false) (mu + 1) true.
Proof. intros. cg_yexec_unfold. destruct ct; reflexivity. Qed.

(* One target step at the start of a code fragment. *)
Lemma cg_ystep_code : forall i0 l y r s s',
  cg_ystep y (i0 + length l, s) s' ->
  sss_step cg_ystep (i0, l ++ y :: r) (i0 + length l, s) s'.
Proof. intros. apply in_sss_step; [reflexivity | assumption]. Qed.

(* ================================================================= *)
(* Soundness of the instruction compiler.                              *)
(* ================================================================= *)

Lemma cg_pos10 : (pos1 : pos 2) <> pos0.
Proof. discriminate. Qed.

Lemma cg_qs_pos : forall x, 0 < qs x.
Proof. intros x. generalize (cg_qs_gt1 x). lia. Qed.

Lemma cg_simul_counter : forall k e a s s' e' v',
  cg_simul k (e, a) s -> cg_yrel v' s' -> cg_keep s s' ->
  vec_pos v' pos0 = 0 -> vec_pos v' pos1 = cg_gk k e' ->
  (forall x, k <= x -> e' x = 0) ->
  cg_simul k (e', a) s'.
Proof.
  intros k e a s s' e' v' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (R1 & R2 & R3)
    (K1 & K2 & K3 & K4) V0 V1 Z.
  unfold cg_simul.
  split; [congruence |]. split; [congruence |]. split; [exact Z |].
  split; [congruence |]. split; [congruence |]. split; [exact R3 |]. split.
  - intros Ha. destruct (H7 Ha) as [A B]. split; congruence.
  - intros Ha. destruct (H8 Ha) as [A B]. split; congruence.
Qed.

Theorem cg_icomp_sound : forall k r,
  instruction_compiler_sound (cg_icomp k r) (cg_xstep k r) cg_ystep (cg_simul k).
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
      * apply (cg_simul_counter k e a w1 s' _ _ Hsim Hr Hkp); [reflexivity | |].
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
      * apply (cg_simul_counter k e a w1 s' _ _ Hsim Hr Hkp); [reflexivity | reflexivity | exact Hz].
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
      * apply (cg_simul_counter k e a w1 s' _ _ Hsim Hr Hkp); [reflexivity | reflexivity |].
        intros y Hy'. rewrite cg_set_env_neq by lia. apply Hz. exact Hy'.
  - (* XPAY *)
    destruct w1 as [[ca cb va vb pc fs ch er] mu ct].
    destruct Hsim as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). simpl in *. subst er.
    exists (G.mkst (G.mkcore ca cb va vb (S (lnk i1)) fs ch false) (mu + 1) ct). split.
    + exists 1. split; [lia |]. apply sss_steps_1. simpl in Hl. rewrite Hl.
      unfold cg_icomp. change (lnk i1, [YPAY]) with (lnk i1, [] ++ YPAY :: []).
      replace (lnk i1) with (lnk i1 + length (@nil cg_yinstr)) at 2 by (simpl; lia).
      apply cg_ystep_code. simpl. rewrite Nat.add_0_r.
      unfold cg_ystep. simpl. split; [discriminate |]. split; [reflexivity |].
      split; [rewrite cg_yexec_pay; reflexivity |]. split; reflexivity.
    + unfold cg_simul, cg_pay. simpl.
      split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |]. split; [lia |].
      split; [exact H5 |]. split; [reflexivity |]. split; [exact H7 | exact H8].
  - (* XEARN *)
    destruct w1 as [[ca cb va vb pc fs ch er] mu ct].
    destruct Hsim as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). simpl in *. subst er.
    destruct (H7 Hea) as [-> ->]. subst ca cb.
    set (f := G.mkfact (URun r) G.CB vb).
    set (s1 := G.mkst (G.mkcore 0 (cg_gk k e) va vb (S (lnk i1)) [f] None false) (mu + 1) ct).
    set (s2 := G.mkst (G.mkcore 0 (cg_gk k e) va vb (S (S (lnk i1))) [f] (Some f) false)
                 (mu + 1 + 1) ct).
    set (s3 := G.mkst (G.mkcore 0 (cg_gk k e) va vb (S (S (S (lnk i1)))) [f] (Some f) false)
                 (mu + 1 + 1 + 1) true).
    exists s3. split.
    + exists 3. split; [lia |]. simpl in Hl. rewrite Hl. unfold cg_icomp.
      apply in_sss_steps_S with (S (lnk i1), s1).
      { change (lnk i1, [YCHK r; YCMT r; YCRT]) with (lnk i1, [] ++ YCHK r :: [YCMT r; YCRT]).
        replace (lnk i1) with (lnk i1 + length (@nil cg_yinstr)) at 2 by (simpl; lia).
        apply cg_ystep_code. simpl. rewrite Nat.add_0_r.
        unfold cg_ystep. simpl. split; [discriminate |]. split; [reflexivity |].
        split; [rewrite cg_yexec_chk by exact Hev; reflexivity |]. split; reflexivity. }
      apply in_sss_steps_S with (S (S (lnk i1)), s2).
      { change (lnk i1, [YCHK r; YCMT r; YCRT]) with (lnk i1, [YCHK r] ++ YCMT r :: [YCRT]).
        replace (S (lnk i1)) with (lnk i1 + length [YCHK r]) at 1 by (simpl; lia).
        apply cg_ystep_code. simpl. replace (lnk i1 + 1) with (S (lnk i1)) by lia.
        unfold cg_ystep. simpl. split; [discriminate |]. split; [reflexivity |].
        split; [unfold s1, f; rewrite cg_yexec_cmt; reflexivity |]. split; reflexivity. }
      apply sss_steps_1.
      change (lnk i1, [YCHK r; YCMT r; YCRT]) with (lnk i1, [YCHK r; YCMT r] ++ YCRT :: []).
      replace (S (S (lnk i1))) with (lnk i1 + length [YCHK r; YCMT r]) at 1 by (simpl; lia).
      replace (3 + lnk i1) with (S (S (S (lnk i1)))) by lia.
      apply cg_ystep_code. simpl. replace (lnk i1 + 2) with (S (S (lnk i1))) by lia.
      unfold cg_ystep. simpl. split; [discriminate |]. split; [reflexivity |].
      split; [unfold s2; rewrite cg_yexec_crt; reflexivity |]. split; reflexivity.
    + unfold cg_simul, cg_earn, s3. simpl.
      split; [reflexivity |]. split; [reflexivity |]. split; [exact H3 |]. split; [lia |].
      split; [reflexivity |]. split; [reflexivity |].
      split; [intros Hf; discriminate Hf | intros _; split; reflexivity].
Qed.

(* ================================================================= *)
(* Whole programs.                                                     *)
(* ================================================================= *)

Definition cg_err (Px : nat * list cg_xinstr) (iQ : nat) : nat :=
  iQ + length_compiler cg_ilen (snd Px).

Definition cg_link (Px : nat * list cg_xinstr) (iQ : nat) : nat -> nat :=
  linker cg_ilen Px iQ (cg_err Px iQ).

Definition cg_code (k r : nat) (Px : nat * list cg_xinstr) (iQ : nat) : list cg_yinstr :=
  compiler (cg_icomp k r) cg_ilen Px iQ (cg_err Px iQ).

Theorem cg_compile_sound : forall k r Px iQ i1 v1 i2 v2 w1,
  cg_simul k v1 w1 ->
  sss_compute (cg_xstep k r) Px (i1, v1) (i2, v2) ->
  exists w2, cg_simul k v2 w2 /\
    sss_compute cg_ystep (iQ, cg_code k r Px iQ) (cg_link Px iQ i1, w1) (cg_link Px iQ i2, w2).
Proof.
  intros k r Px iQ i1 v1 i2 v2 w1 Hs Hc.
  exact (compiler_sound cg_ilen (cg_icomp_length k r) (cg_icomp_sound k r)
           (cg_link Px iQ) (iQ, cg_code k r Px iQ)
           (fun i rho H => compiler_subcode (cg_icomp k r) cg_ilen (cg_icomp_length k r)
                             Px iQ (cg_err Px iQ) i rho H)
           w1 (conj Hs Hc)).
Qed.

Lemma cg_link_start : forall Px iQ, cg_link Px iQ (fst Px) = iQ.
Proof. intros. unfold cg_link. apply (linker_code_start cg_ilen Px). Qed.

Lemma cg_code_length : forall k r Px iQ,
  length (cg_code k r Px iQ) = length_compiler cg_ilen (snd Px).
Proof. intros. unfold cg_code. apply compiler_length, cg_icomp_length. Qed.

Lemma cg_link_out : forall Px iQ j,
  out_code j Px -> cg_link Px iQ j = iQ + length_compiler cg_ilen (snd Px).
Proof.
  intros Px iQ j H. unfold cg_link.
  rewrite (@linker_out_err _ cg_ilen Px iQ (cg_err Px iQ) j); [reflexivity | | exact H].
  unfold cg_err. lia.
Qed.

(* A source run that leaves its code is matched by a target run that
   leaves the compiled code, from the start of the code to its end. *)
Theorem cg_compile_output : forall k r Px iQ v1 i2 v2 w1,
  cg_simul k v1 w1 ->
  sss_output (cg_xstep k r) Px (fst Px, v1) (i2, v2) ->
  exists w2, cg_simul k v2 w2 /\
    sss_output cg_ystep (iQ, cg_code k r Px iQ) (iQ, w1)
      (iQ + length_compiler cg_ilen (snd Px), w2).
Proof.
  intros k r Px iQ v1 i2 v2 w1 Hs [Hc Hout].
  destruct (cg_compile_sound k r Px iQ _ _ _ _ w1 Hs Hc) as (w2 & Hs2 & Hc2).
  rewrite cg_link_start, (cg_link_out Px iQ i2 Hout) in Hc2.
  exists w2. split; [exact Hs2 | split; [exact Hc2 |]].
  unfold out_code, code_end. simpl. rewrite cg_code_length. lia.
Qed.

(* The clean start of a guest with registers e (0 from k on). *)
Definition cg_xstart (e : env nat nat) : cg_xstate := (e, cg_mkaux 0 false false).

Lemma cg_simul_start : forall k e,
  (forall y, k <= y -> e y = 0) ->
  cg_simul k (cg_xstart e) (G.start 0 (cg_gk k e)).
Proof.
  intros k e H. unfold cg_xstart, G.start, G.start_core. simpl.
  repeat split; auto; discriminate.
Qed.

(* At address 1, the compiled program runs on EarnedPriced's own runner
   from the start state G.start 0 (cg_gk k e). *)
Theorem cg_compile_start : forall k r (Q : list cg_xinstr) e i2 v2,
  (forall y, k <= y -> e y = 0) ->
  sss_compute (cg_xstep k r) (1, Q) (1, cg_xstart e) (i2, v2) ->
  exists n w2,
    P.pr_run_prog cg_uprop_eqb cg_ueval n (map cg_tr (cg_code k r (1, Q) 1))
      (G.start 0 (cg_gk k e)) = w2 /\
    cg_simul k v2 w2 /\
    G.pc (G.core_of w2) = cg_link (1, Q) 1 i2.
Proof.
  intros k r Q e i2 v2 He Hc.
  destruct (cg_compile_sound k r (1, Q) 1 1 (cg_xstart e) i2 v2 _ (cg_simul_start k e He) Hc)
    as (w2 & Hs2 & n & Hn).
  assert (E : cg_link (1, Q) 1 1 = 1) by apply (cg_link_start (1, Q) 1).
  rewrite E in Hn.
  destruct (cg_lift_run _ n 1 (G.start 0 (cg_gk k e)) _ _ eq_refl Hn) as [Hrun Hpc].
  exists n, w2. split; [exact Hrun | split; [exact Hs2 | exact Hpc]].
Qed.
