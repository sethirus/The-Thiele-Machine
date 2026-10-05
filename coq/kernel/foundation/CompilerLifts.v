(** CompilerLifts.v: the source and target languages of the compiler, and
    the lifts between counter-machine runs and runs of the two languages.

    Source X: many registers. XMM J is a counter instruction J with the
    vendored mm_sss_env semantics (DEC jumps when the register is zero),
    allowed on registers below k only. XPAY adds 1 to the ledger. XEARN,
    when the fixed checker accepts URun r on the Godel code of the
    registers and the record is not yet earned, adds 3 to the ledger and
    raises both the certified flag and the earned mark. XHALT has no step.

    Target Y: two counters. YMMA J is a vendored alternate counter
    instruction on pos 2 (DEC jumps when the decrement succeeds); YPAY,
    YCHK r, YCMT r, YCRT and YHALT are PAY, CHECK (URun r) on counter B,
    COMMIT (URun r) on counter B, CERTIFY and HALT of EarnedPriced.v
    [cg_tr]. One target step is EarnedPriced's own execution, with the
    program counter set to the position of the instruction and both the
    state before and after untrapped [cg_ystep]; HALT has no step.

    Lifts:
      cg_lift_mm    a counter run on registers below k is an X run with the
                    ledger and record unchanged;
      cg_lift_mma2  a two-counter run of the vendored alternate machine is
                    a Y run with the same counters, the same facts,
                    channel, ledger and flag, and no trap;
      cg_lift_run   a Y run of a program placed at address 1 is exactly
                    EarnedPriced's own runner on the translated program,
                    pr_run_prog, ending at the same program counter.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, EarnedGeneric.v, EarnedPriced.v, CompilerCodes.v and
    CompilerChecker.v. No axioms, no Admitted. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the presented universal machine of
   PresentedUniversal.v and imports only the Coq standard library, the
   vendored coq-undecidability library and the standard-library files under
   minimal/. Its link to the abstract record (the priced host as a
   CertificationSystem, the cost floor of its runs, and the undecidability
   of U_P's halting problem) lives in PricedHostLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Minimal.EarnedGeneric Minimal.EarnedPriced.
Module G := Minimal.EarnedGeneric.
Module P := Minimal.EarnedPriced.
Require Import Kernel.CompilerCodes Kernel.CompilerChecker.

(* ================================================================= *)
(* A generic lift of runs.                                             *)
(* ================================================================= *)

Lemma cg_sss_lift : forall (XA XB : Set) (DA DB : Type)
  (stepA : XA -> nat * DA -> nat * DA -> Prop)
  (stepB : XB -> nat * DB -> nat * DB -> Prop)
  (f : XA -> XB) (R : DA -> DB -> Prop) (i0 : nat) (Q : list XA),
  (forall J i d j d' w, In J Q -> stepA J (i, d) (j, d') -> R d w ->
     exists w', stepB (f J) (i, w) (j, w') /\ R d' w') ->
  forall n i d j d' w,
    sss_steps stepA (i0, Q) n (i, d) (j, d') -> R d w ->
    exists w', sss_steps stepB (i0, map f Q) n (i, w) (j, w') /\ R d' w'.
Proof.
  intros XA XB DA DB stepA stepB f R i0 Q Hstep n i d j d' w Hs.
  remember (i0, Q) as PQ eqn:EPQ.
  remember (i, d) as st eqn:Est. remember (j, d') as st' eqn:Est'.
  revert i d Est j d' Est' w.
  induction Hs as [st | n st1 st2 st3 H1 H2 IH];
    intros i d Est j d' Est' w HR; subst.
  - injection Est' as -> ->. exists w. split; [constructor | exact HR].
  - destruct st2 as [i2 d2].
    destruct H1 as (k & l & J & r & dd & HP & Hst & Hs1).
    injection HP as Hk HQ. injection Hst as Hi Hd. subst.
    assert (HJ : In J (l ++ J :: r)) by (apply in_or_app; right; left; reflexivity).
    destruct (Hstep J _ _ _ _ w HJ Hs1 HR) as (w2 & Hs2 & HR2).
    destruct (IH i2 d2 eq_refl j d' eq_refl w2 HR2) as (w3 & Hs3 & HR3).
    exists w3. split; [| exact HR3].
    apply in_sss_steps_S with (i2, w2); [| exact Hs3].
    rewrite map_app. simpl. apply in_sss_step; [simpl; rewrite map_length; reflexivity |].
    exact Hs2.
Qed.

(* ================================================================= *)
(* The source language X.                                              *)
(* ================================================================= *)

Inductive cg_xinstr : Set :=
| XMM (J : mm_instr nat)
| XPAY
| XEARN
| XHALT.

(* The guest's record: ledger, certified flag, earned mark. *)
Record cg_aux : Type := cg_mkaux {
  cg_a_mu : nat;
  cg_a_cert : bool;
  cg_a_earned : bool }.

Definition cg_xstate : Type := (env nat nat * cg_aux)%type.

Definition cg_pay (a : cg_aux) : cg_aux :=
  cg_mkaux (S (cg_a_mu a)) (cg_a_cert a) (cg_a_earned a).

Definition cg_earn (a : cg_aux) : cg_aux := cg_mkaux (cg_a_mu a + 3) true true.

Definition cg_xreg (J : mm_instr nat) : nat :=
  match J with mm_inc x => x | mm_dec x _ => x end.

Inductive cg_xstep (k r : nat) : cg_xinstr -> nat * cg_xstate -> nat * cg_xstate -> Prop :=
| cg_xstep_mm : forall J i e j e' a,
    cg_xreg J < k ->
    mm_sss_env eq_nat_dec J (i, e) (j, e') ->
    cg_xstep k r (XMM J) (i, (e, a)) (j, (e', a))
| cg_xstep_pay : forall i e a,
    cg_xstep k r XPAY (i, (e, a)) (S i, (e, cg_pay a))
| cg_xstep_earn : forall i e a,
    cg_ueval (URun r) (cg_gk k e) = true ->
    cg_a_earned a = false ->
    cg_xstep k r XEARN (i, (e, a)) (S i, (e, cg_earn a)).

Lemma cg_xstep_fun : forall k r J st st1 st2,
  cg_xstep k r J st st1 -> cg_xstep k r J st st2 -> st1 = st2.
Proof.
  intros k r J st st1 st2 H1 H2. destruct H1; inversion H2; subst; try reflexivity.
  match goal with
  | H : mm_sss_env _ _ _ _, H' : mm_sss_env _ _ _ _ |- _ =>
      generalize (mm_sss_env_fun H H'); intros E; injection E as -> ->; reflexivity
  end.
Qed.

(* lift_mm: a counter run on registers below k is an X run. *)
Theorem cg_lift_mm : forall k r i0 (Q : list (mm_instr nat)) n i e j e' a,
  (forall J, In J Q -> cg_xreg J < k) ->
  sss_steps (mm_sss_env eq_nat_dec) (i0, Q) n (i, e) (j, e') ->
  sss_steps (cg_xstep k r) (i0, map XMM Q) n (i, (e, a)) (j, (e', a)).
Proof.
  intros k r i0 Q n i e j e' a HQ Hs.
  assert (Hstep : forall J i1 d j1 d' (w : cg_xstate), In J Q ->
            mm_sss_env eq_nat_dec J (i1, d) (j1, d') -> w = (d, a) ->
            exists w', cg_xstep k r (XMM J) (i1, w) (j1, w') /\ w' = (d', a)).
  { intros J i1 d j1 d' w HJ H1 ->. exists (d', a). split; [| reflexivity].
    constructor; [apply HQ; exact HJ | exact H1]. }
  destruct (cg_sss_lift _ _ _ _ (mm_sss_env eq_nat_dec) (cg_xstep k r) XMM
              (fun d w => w = (d, a)) i0 Q Hstep n i e j e' (e, a) Hs eq_refl)
    as (w' & Hs' & ->).
  exact Hs'.
Qed.

(* ================================================================= *)
(* The target language Y.                                              *)
(* ================================================================= *)

Inductive cg_yinstr : Set :=
| YMMA (J : mm_instr (pos 2))
| YPAY
| YCHK (r : nat)
| YCMT (r : nat)
| YCRT
| YHALT.

Definition cg_ctr (p : pos 2) : G.ctr :=
  match p with pos_fst => G.CA | pos_nxt _ => G.CB end.

Definition cg_tr (y : cg_yinstr) : @P.pr_instr cg_uprop :=
  match y with
  | YMMA (mm_inc p) => P.INC (cg_ctr p)
  | YMMA (mm_dec p j) => P.DEC (cg_ctr p) j
  | YPAY => P.PAY
  | YCHK r => P.CHECK (URun r) G.CB
  | YCMT r => P.COMMIT (URun r) G.CB
  | YCRT => P.CERTIFY
  | YHALT => P.HALT
  end.

Definition cg_ystate : Type := @G.state cg_uprop.

(* The state with its program counter set to i. *)
Definition cg_at (i : nat) (s : cg_ystate) : cg_ystate :=
  G.mkst (G.goto (G.core_of s) i) (G.mu s) (G.cert s).

Definition cg_yexec (y : cg_yinstr) (i : nat) (s : cg_ystate) : cg_ystate :=
  P.pr_exec cg_uprop_eqb cg_ueval (cg_at i s) (cg_tr y).

Definition cg_ystep (y : cg_yinstr) (st1 st2 : nat * cg_ystate) : Prop :=
  y <> YHALT /\
  G.err (G.core_of (snd st1)) = false /\
  snd st2 = cg_yexec y (fst st1) (snd st1) /\
  fst st2 = G.pc (G.core_of (snd st2)) /\
  G.err (G.core_of (snd st2)) = false.

Lemma cg_ystep_fun : forall y st st1 st2,
  cg_ystep y st st1 -> cg_ystep y st st2 -> st1 = st2.
Proof.
  intros y st [j1 s1] [j2 s2] (_ & _ & E1 & P1 & _) (_ & _ & E2 & P2 & _).
  simpl in *. subst. reflexivity.
Qed.

Lemma cg_ystep_intro : forall y i s,
  y <> YHALT -> G.err (G.core_of s) = false ->
  G.err (G.core_of (cg_yexec y i s)) = false ->
  cg_ystep y (i, s) (G.pc (G.core_of (cg_yexec y i s)), cg_yexec y i s).
Proof. intros y i s H1 H2 H3. repeat split; assumption. Qed.

(* ================================================================= *)
(* lift_mma2: two-counter runs are Y runs.                             *)
(* ================================================================= *)

Definition cg_yrel (v : vec nat 2) (s : cg_ystate) : Prop :=
  G.ca (G.core_of s) = vec_pos v pos0 /\ G.cb (G.core_of s) = vec_pos v pos1 /\
  G.err (G.core_of s) = false.

(* Same facts, channel, ledger and flag. *)
Definition cg_keep (s s' : cg_ystate) : Prop :=
  G.facts (G.core_of s') = G.facts (G.core_of s) /\
  G.chan (G.core_of s') = G.chan (G.core_of s) /\
  G.mu s' = G.mu s /\ G.cert s' = G.cert s.

Lemma cg_keep_refl : forall s, cg_keep s s.
Proof. intros s. repeat split. Qed.

Lemma cg_keep_trans : forall s1 s2 s3, cg_keep s1 s2 -> cg_keep s2 s3 -> cg_keep s1 s3.
Proof.
  intros s1 s2 s3 (A1 & B1 & C1 & D1) (A2 & B2 & C2 & D2).
  repeat split; congruence.
Qed.

Lemma cg_pos2_cases : forall p : pos 2, p = pos0 \/ p = pos1.
Proof. intros p. repeat invert pos p; auto. Qed.

Lemma cg_vec2_ex : forall v : vec nat 2, exists a b, v = a ## b ## vec_nil.
Proof. intros v. vec split v with a; vec split v with b; vec nil v. exists a, b. reflexivity. Qed.

Lemma cg_lift_mma2_step : forall J i v j v' s,
  mma_sss J (i, v) (j, v') -> cg_yrel v s ->
  exists s', cg_ystep (YMMA J) (i, s) (j, s') /\ cg_yrel v' s' /\ cg_keep s s'.
Proof.
  intros J i v j v' s Hs (Ha & Hb & He).
  destruct (cg_vec2_ex v) as (a & b & ->).
  destruct s as [[ca cb va vb pc fs ch err] mu ct]; simpl in Ha, Hb, He; subst.
  exists (cg_yexec (YMMA J) i (G.mkst (G.mkcore a b va vb pc fs ch false) mu ct)).
  inversion Hs as [i1 x w | i1 x k w Hz | i1 x k w u Hu]; subst;
    destruct (cg_pos2_cases x) as [-> | ->]; simpl in *; subst;
    unfold cg_ystep, cg_yrel, cg_keep, cg_yexec, cg_at; simpl;
    rewrite ?orb_false_r, ?Nat.add_0_r; repeat split; (discriminate || reflexivity).
Qed.

Theorem cg_lift_mma2 : forall i0 (Q : list (mm_instr (pos 2))) n i v j v' s,
  sss_steps (@mma_sss 2) (i0, Q) n (i, v) (j, v') -> cg_yrel v s ->
  exists s', sss_steps cg_ystep (i0, map YMMA Q) n (i, s) (j, s') /\
             cg_yrel v' s' /\ cg_keep s s'.
Proof.
  intros i0 Q n i v j v' s Hs Hr.
  assert (Hstep : forall J i1 d j1 d' w, In J Q -> mma_sss J (i1, d) (j1, d') ->
            cg_yrel d w /\ cg_keep s w ->
            exists w', cg_ystep (YMMA J) (i1, w) (j1, w') /\ (cg_yrel d' w' /\ cg_keep s w')).
  { intros J i1 d j1 d' w _ H1 [H2 H3].
    destruct (cg_lift_mma2_step J i1 d j1 d' w H1 H2) as (w' & H4 & H5 & H6).
    exists w'. split; [exact H4 | split; [exact H5 | eapply cg_keep_trans; eauto]]. }
  destruct (cg_sss_lift _ _ _ _ (@mma_sss 2) cg_ystep YMMA
              (fun v s' => cg_yrel v s' /\ cg_keep s s') i0 Q Hstep n i v j v' s Hs
              (conj Hr (cg_keep_refl s)))
    as (s' & Hs' & Hr' & Hk').
  exists s'. auto.
Qed.

Corollary cg_lift_mma2_progress : forall i0 (Q : list (mm_instr (pos 2))) i v j v' s,
  sss_progress (@mma_sss 2) (i0, Q) (i, v) (j, v') -> cg_yrel v s ->
  exists s', sss_progress cg_ystep (i0, map YMMA Q) (i, s) (j, s') /\
             cg_yrel v' s' /\ cg_keep s s'.
Proof.
  intros i0 Q i v j v' s (n & Hn & Hs) Hr.
  destruct (cg_lift_mma2 i0 Q n i v j v' s Hs Hr) as (s' & Hs' & Hr' & Hk').
  exists s'. split; [exists n; split; [exact Hn | exact Hs'] | split; assumption].
Qed.

(* ================================================================= *)
(* lift_run: Y runs at address 1 are EarnedPriced runs.                *)
(* ================================================================= *)

Lemma cg_at_pc : forall i s, G.pc (G.core_of s) = i -> cg_at i s = s.
Proof.
  intros i [[ca cb va vb pc fs ch err] mu ct] H. simpl in H. subst. reflexivity.
Qed.

Lemma cg_pr_step_at : forall l y r (s : cg_ystate),
  y <> YHALT -> G.err (G.core_of s) = false ->
  G.pc (G.core_of s) = 1 + length l ->
  P.pr_step cg_uprop_eqb cg_ueval (map cg_tr (l ++ y :: r)) s
    = cg_yexec y (G.pc (G.core_of s)) s.
Proof.
  intros l y r s Hy He Hpc. unfold P.pr_step, P.pr_next_instr, cg_yexec.
  rewrite He, cg_at_pc by reflexivity. rewrite Hpc. simpl G.fetch.
  rewrite map_app. simpl. rewrite nth_error_app2 by (rewrite map_length; lia).
  rewrite map_length, Nat.sub_diag. simpl.
  destruct y as [[p | p j] | | r' | r' | |]; try reflexivity. contradiction.
Qed.

Theorem cg_lift_run : forall (Q : list cg_yinstr) n i s j s',
  G.pc (G.core_of s) = i ->
  sss_steps cg_ystep (1, Q) n (i, s) (j, s') ->
  P.pr_run_prog cg_uprop_eqb cg_ueval n (map cg_tr Q) s = s' /\
  G.pc (G.core_of s') = j.
Proof.
  intros Q n i s j s' Hpc Hs.
  remember (1, Q) as PQ eqn:EPQ.
  remember (i, s) as st eqn:Est. remember (j, s') as st' eqn:Est'.
  revert i s Est Hpc j s' Est'.
  induction Hs as [st | n st1 st2 st3 H1 H2 IH];
    intros i s Est Hpc j s' Est'.
  - rewrite Est in Est'. injection Est' as <- <-. split; [reflexivity | exact Hpc].
  - destruct st2 as [i2 s2].
    destruct H1 as (k & l & y & r & dd & HP & Hst & Hs1).
    rewrite EPQ in HP. injection HP as Hk HQ. rewrite Est in Hst.
    injection Hst as Hi Hd. subst k dd Q st1.
    destruct Hs1 as (Hy & He & E2 & P2 & He2). simpl in E2, P2, He.
    simpl P.pr_run_prog. rewrite (cg_pr_step_at l y r s Hy He (eq_trans Hpc Hi)).
    rewrite Hpc, <- E2.
    apply (IH i2 s2 eq_refl (eq_sym P2) j s' Est').
Qed.

Print Assumptions cg_sss_lift.
Print Assumptions cg_xstep_fun.
Print Assumptions cg_lift_mm.
Print Assumptions cg_ystep_fun.
Print Assumptions cg_ystep_intro.
Print Assumptions cg_keep_refl.
Print Assumptions cg_keep_trans.
Print Assumptions cg_pos2_cases.
Print Assumptions cg_vec2_ex.
Print Assumptions cg_lift_mma2_step.
Print Assumptions cg_lift_mma2.
Print Assumptions cg_lift_mma2_progress.
Print Assumptions cg_at_pc.
Print Assumptions cg_pr_step_at.
Print Assumptions cg_lift_run.
