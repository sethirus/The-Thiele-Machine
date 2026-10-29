(** CmpGuest.v: the fifth compiler stage, from counter-machine programs to
    guest programs of the two-counter machine, and the universal machine.

    The compiler is the one of CompilerIcomp.v: a counter machine program Q
    on registers below k, as the list map XMM Q of source instructions, is
    compiled to a program of the two-counter machine of EarnedPriced.v
    (cg_code k r), whose second counter holds the Godel code
    cg_gk k e = the product of the primes qs x to the power e x of the
    registers e. That file proves that a source run is matched by a target
    run (cg_compile_output, cg_compile_start). This file adds the converse,
    which the file about presented machines does not need: a target run that
    leaves the compiled program has a source run, ending in the registers
    whose code the second counter holds.

    The converse comes from the vendored completeness theorem of compilers
    (compiler_complete'), which asks every source instruction to have a step
    from every state. An instruction of the source language of CompilerLifts.v
    has none in general (a register above k, XHALT, XEARN with an
    unaccepted claim). The programs here use only counter instructions on
    registers below k; for them the source language is the subtype cmp_gx k,
    on which the step relation is total, and the compilers agree
    (cmp_gcode_eq, cmp_glink_eq).

      cmp_g_complete        a target run from the start of cg_code that
                            leaves the code, from counters with the code
                            of e, matches a source run on map XMM Q from e
      cmp_guest_fwd / cmp_guest_bwd
                            for the guest program cmp_gprog k Q, run by
                            EarnedPriced.v from G.start 0 (cg_gk k e):
                            a counter machine run that leaves Q gives a
                            halted guest state whose second counter holds
                            the code of the final registers, and conversely
      cmp_U_fwd / cmp_U_bwd the same for the fixed universal host U_P of
                            UniversalPRun.v, loaded with the guest

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, the Compiler*.v files, UniversalPRun.v and the Cmp files. No
    axioms and no unfinished proofs.                                                    *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is one stage of the verified compiler pipeline of CmpPipeline.v. Its link
   to the abstract record (the priced host as a CertificationSystem, the cost
   floor of its runs, the undecidability of U_P's halting problem) lives in
   PricedHostLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.Shared.Libs.DLW.Code Require Import compiler compiler_correction.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Import Kernel.CompilerCodes Kernel.CompilerChecker Kernel.CompilerLifts Kernel.CompilerIcomp.
Require Import Kernel.CmpLang Kernel.CmpBlocks.

Local Notation mmstep := (@mm_sss_env nat eq_nat_dec).

(* ================================================================= *)
(* The subtype of source instructions with a step everywhere.         *)
(* ================================================================= *)

Definition cmp_gx (k : nat) : Set := { J : mm_instr nat | cg_xreg J < k }.

Definition cmp_gxi (k : nat) (x : cmp_gx k) : cg_xinstr := XMM (proj1_sig x).

Definition cmp_gicomp (k r : nat) (lnk : nat -> nat) (i : nat) (x : cmp_gx k) : list cg_yinstr :=
  cg_icomp k r lnk i (cmp_gxi k x).

Definition cmp_gilen (k : nat) (x : cmp_gx k) : nat := cg_ilen (cmp_gxi k x).

Definition cmp_gstep (k r : nat) (x : cmp_gx k) : nat * cg_xstate -> nat * cg_xstate -> Prop :=
  cg_xstep k r (cmp_gxi k x).

Lemma cmp_gicomp_length : forall k r lnk n x, length (cmp_gicomp k r lnk n x) = cmp_gilen k x.
Proof. intros. unfold cmp_gicomp, cmp_gilen. apply cg_icomp_length. Qed.

Lemma cmp_gstep_total : forall k r x st, exists st2, cmp_gstep k r x st st2.
Proof.
  intros k r [J HJ] [i [e a]]. destruct (mm_sss_env_total eq_nat_dec J (i, e)) as ([j e'] & Hs).
  exists (j, (e', a)). unfold cmp_gstep, cmp_gxi. simpl. apply cg_xstep_mm; assumption.
Qed.

Theorem cmp_gicomp_sound : forall k r,
  instruction_compiler_sound (cmp_gicomp k r) (cmp_gstep k r) cg_ystep (cg_simul k).
Proof.
  intros k r lnk x i1 v1 i2 v2 w1 Hs Hl Hsim.
  exact (cg_icomp_sound k r lnk (cmp_gxi k x) i1 v1 i2 v2 w1 Hs Hl Hsim).
Qed.

Fixpoint cmp_gwrap (k : nat) (Q : list (mm_instr nat)) : (forall J, In J Q -> cg_xreg J < k) -> list (cmp_gx k) :=
  match Q with
  | [] => fun _ => []
  | J :: Q' => fun H => exist _ J (H J (or_introl eq_refl)) :: cmp_gwrap k Q' (fun J' H' => H J' (or_intror H'))
  end.

Lemma cmp_gwrap_map : forall k Q H, map (cmp_gxi k) (cmp_gwrap k Q H) = map XMM Q.
Proof. induction Q as [| J Q IH]; intros H; simpl; [reflexivity | f_equal; apply IH]. Qed.

Lemma cmp_gwrap_length : forall k Q H, length (cmp_gwrap k Q H) = length Q.
Proof. induction Q as [| J Q IH]; intros H; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(* ================================================================= *)
(* The two compilers agree.                                           *)
(* ================================================================= *)

Lemma cmp_length_compiler_map : forall (A B : Type) (f : A -> B) (lc : B -> nat) (L : list A),
  length_compiler (fun x => lc (f x)) L = length_compiler lc (map f L).
Proof. intros A B f lc. induction L as [| x L IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma cmp_link_map : forall (A B : Type) (f : A -> B) (lc : B -> nat) (L : list A) i j,
  link (fun x => lc (f x)) i L j = link lc i (map f L) j.
Proof. intros A B f lc. induction L as [| x L IH]; intros i j; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma cmp_linker_map : forall (A B : Type) (f : A -> B) (lc : B -> nat) i0 (L : list A) i err,
  linker (fun x => lc (f x)) (i0, L) i err = linker lc (i0, map f L) i err.
Proof.
  intros A B f lc i0 L i err. unfold linker. cbn [fst snd].
  rewrite map_length, cmp_length_compiler_map, cmp_link_map. reflexivity.
Qed.

Lemma cmp_comp_map : forall (A B Y : Type) (f : A -> B) (ic : (nat -> nat) -> nat -> B -> list Y) (lc : B -> nat)
  (lnk : nat -> nat) (L : list A) i j,
  comp (fun l n x => ic l n (f x)) (fun x => lc (f x)) lnk i L j = comp ic lc lnk i (map f L) j.
Proof. intros A B Y f ic lc lnk L. induction L as [| x L IH]; intros i j; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Section CmpGuestEq.

Variables (k r : nat) (Q : list (mm_instr nat)) (Hq : forall J, In J Q -> cg_xreg J < k).

Definition cmp_gP : nat * list (cmp_gx k) := (1, cmp_gwrap k Q Hq).

Lemma cmp_gerr_eq : 1 + length_compiler (cmp_gilen k) (snd cmp_gP) = cg_err (1, map XMM Q) 1.
Proof.
  unfold cg_err. cbn [snd]. unfold cmp_gP. cbn [snd].
  rewrite <- (cmp_gwrap_map k Q Hq). rewrite <- (cmp_length_compiler_map _ _ (cmp_gxi k) cg_ilen). reflexivity.
Qed.

Lemma cmp_glink_eq : linker (cmp_gilen k) cmp_gP 1 (1 + length_compiler (cmp_gilen k) (snd cmp_gP)) =
                     cg_link (1, map XMM Q) 1.
Proof.
  unfold cg_link. rewrite <- cmp_gerr_eq. unfold cmp_gP. rewrite <- (cmp_gwrap_map k Q Hq).
  apply (cmp_linker_map _ _ (cmp_gxi k) cg_ilen).
Qed.

Lemma cmp_gcode_eq : compiler (cmp_gicomp k r) (cmp_gilen k) cmp_gP 1 (1 + length_compiler (cmp_gilen k) (snd cmp_gP)) =
                     cg_code k r (1, map XMM Q) 1.
Proof.
  unfold cg_code. rewrite <- cmp_gerr_eq. unfold compiler.
  rewrite <- (cmp_gwrap_map k Q Hq). cbn [fst snd]. unfold cmp_gP. cbn [fst snd].
  rewrite <- (cmp_linker_map _ _ (cmp_gxi k) cg_ilen).
  apply (cmp_comp_map _ _ _ (cmp_gxi k) (cg_icomp k r) cg_ilen).
Qed.

End CmpGuestEq.

(* ================================================================= *)
(* Completeness.                                                      *)
(* ================================================================= *)

Lemma cmp_gstep_lift : forall k r (L : list (cmp_gx k)) n i e j e',
  sss_steps (cmp_gstep k r) (1, L) n (i, e) (j, e') ->
  sss_steps (cg_xstep k r) (1, map (cmp_gxi k) L) n (i, e) (j, e').
Proof.
  intros k r L n i e j e' H.
  destruct (cg_sss_lift _ _ _ _ (cmp_gstep k r) (cg_xstep k r) (cmp_gxi k) (fun d w => w = d) 1 L
              ltac:(intros J i1 d j1 d' w _ Hs Hw; cbv beta in Hw; subst w; exists d'; split; [exact Hs | reflexivity])
              n i e j e' e H eq_refl) as (w' & Hs' & ->).
  exact Hs'.
Qed.

Theorem cmp_g_complete : forall k r Q (Hq : forall J, In J Q -> cg_xreg J < k) v1 w1 j w2,
  cg_simul k v1 w1 ->
  sss_output cg_ystep (1, cg_code k r (1, map XMM Q) 1) (1, w1) (j, w2) ->
  exists i2 v2, cg_simul k v2 w2 /\ sss_output (cg_xstep k r) (1, map XMM Q) (1, v1) (i2, v2) /\
    j = 1 + length (cg_code k r (1, map XMM Q) 1).
Proof.
  intros k r Q Hq v1 w1 j w2 Hs Ho.
  set (P' := cmp_gP k Q Hq).
  set (err' := 1 + length_compiler (cmp_gilen k) (snd P')).
  set (lnk := linker (cmp_gilen k) P' 1 err').
  set (code' := compiler (cmp_gicomp k r) (cmp_gilen k) P' 1 err').
  assert (Hcode : code' = cg_code k r (1, map XMM Q) 1) by (unfold code', err'; apply cmp_gcode_eq).
  assert (Hstart : lnk 1 = 1) by (unfold lnk; apply (linker_code_start (cmp_gilen k) P')).
  assert (Ho' : sss_output cg_ystep (1, code') (lnk (fst P'), w1) (j, w2)).
  { assert (Hfst : lnk (fst P') = 1) by exact Hstart. rewrite Hfst, Hcode. exact Ho. }
  destruct (compiler_complete' (cmp_gilen k) (cmp_gicomp_length k r) (cmp_gstep_total k r) cg_ystep_fun
              (cmp_gicomp_sound k r) lnk P'
              (fun i rho H => compiler_subcode (cmp_gicomp k r) (cmp_gilen k) (cmp_gicomp_length k r) P' 1 err' i rho H)
              (fst P') v1 (conj Hs Ho')) as (i2 & v2 & w2' & Hs2 & Hf & Hq2).
  destruct Hf as [[n Hn] Hfo]. destruct Hq2 as [Hq2 Hqo].
  assert (Hlen : length code' = length_compiler (cmp_gilen k) (snd P'))
    by (unfold code'; apply compiler_length; apply cmp_gicomp_length).
  assert (Hl : lnk i2 = 1 + length code').
  { unfold lnk. rewrite (@linker_out_err _ (cmp_gilen k) P' 1 err' i2) by (first [unfold err'; lia | exact Hfo]).
    rewrite Hlen. reflexivity. }
  assert (Hlo : out_code (fst (lnk i2, w2')) (1, code')).
  { cbn [fst]. rewrite Hl. unfold out_code, code_end. cbn [fst snd]. right. apply Nat.le_refl. }
  pose proof (sss_compute_stop Hlo Hq2) as E. inversion E; subst.
  exists i2, v2. split; [exact Hs2 |]. split.
  - split.
    + exists n. cbn [fst] in Hn. unfold P' in Hn. cbn [snd] in Hn.
      pose proof (cmp_gstep_lift k r _ n _ _ _ _ Hn) as Hn'. rewrite (cmp_gwrap_map k Q Hq) in Hn'. exact Hn'.
    + unfold out_code, code_end. cbn [fst snd]. unfold out_code, code_end, code_start in Hfo. unfold P', cmp_gP in Hfo. cbn [fst snd] in Hfo.
      rewrite cmp_gwrap_length in Hfo. rewrite map_length. exact Hfo.
  - rewrite Hl, Hcode. reflexivity.
Qed.

Print Assumptions cmp_g_complete.

(* ================================================================= *)
(* Source runs: a run of X on map XMM Q is a counter machine run.     *)
(* ================================================================= *)

Lemma cmp_xunlift : forall k r (Q : list (mm_instr nat)) n i e a j e' a',
  sss_steps (cg_xstep k r) (1, map XMM Q) n (i, (e, a)) (j, (e', a')) ->
  a' = a /\ sss_steps mmstep (1, Q) n (i, e) (j, e').
Proof.
  intros k r Q n. induction n as [| n IH]; intros i e a j e' a' H.
  - apply sss_steps_0_inv in H. inversion H; subst. split; [reflexivity | constructor].
  - destruct (sss_steps_S_inv' H) as ((i2 & (e2 & a2)) & H1 & H2).
    destruct H1 as (k0 & l & I & r0 & d & HP & Hst & Hs1). injection HP as Hk0 HQ. subst k0.
    apply map_eq_app in HQ as (l1 & l2 & -> & Hl1 & Hl2).
    destruct l2 as [| J l2]; [discriminate Hl2 |]. simpl in Hl2. injection Hl2 as <- Hr0.
    inversion Hst; subst.
    inversion Hs1; subst. clear Hs1.
    destruct (IH _ _ _ _ _ _ H2) as (Ea & Hrest).
    split; [exact Ea |].
    eapply in_sss_steps_S with (st2 := (i2, e2)); [| exact Hrest].
    apply in_sss_step; [simpl; rewrite map_length; reflexivity | assumption].
Qed.


(* ================================================================= *)
(* The guest machine runs the compiled program.                       *)
(* ================================================================= *)

Module G := Minimal.EarnedGeneric.
Module P := Minimal.EarnedPriced.

(* The guest program of a counter machine program Q on registers below k.
   The record instruction of the compiler is not used, so any routine code
   would do; 0 is fixed. *)
Definition cmp_gprog (k : nat) (Q : list (mm_instr nat)) : list (@P.pr_instr cg_uprop) :=
  map cg_tr (cg_code k 0 (1, map XMM Q) 1).

(* The guest starts with counter A at 0 and counter B at the code of e. *)
Definition cmp_gstart (k : nat) (e : env nat nat) : cg_ystate := G.start 0 (cg_gk k e).

Lemma cmp_icomp_xmm_map : forall k r lnk i J, exists l : list (mm_instr (pos 2)), cg_icomp k r lnk i (XMM J) = map YMMA l.
Proof. intros k r lnk i [x | x t]; unfold cg_icomp; eexists; reflexivity. Qed.

Lemma cmp_comp_ymma : forall k r lnk (L : list (mm_instr nat)) i j y,
  In y (comp (cg_icomp k r) cg_ilen lnk i (map XMM L) j) -> exists J, y = YMMA J.
Proof.
  intros k r lnk L. induction L as [| J L IH]; intros i j y H; cbn [comp map] in H; [destruct H |].
  apply in_app_or in H. destruct H as [H | H]; [| exact (IH _ _ _ H)].
  destruct (cmp_icomp_xmm_map k r lnk i J) as (l & Hl). rewrite Hl in H.
  apply in_map_iff in H as (J0 & <- & _). eexists; reflexivity.
Qed.

Lemma cmp_gcode_ymma : forall k r Q y, In y (cg_code k r (1, map XMM Q) 1) -> exists J, y = YMMA J.
Proof. intros k r Q y H. unfold cg_code, compiler in H. exact (cmp_comp_ymma _ _ _ _ _ _ _ H). Qed.

Lemma cmp_ystep_ex : forall J i s, G.err (G.core_of s) = false ->
  exists j s', cg_ystep (YMMA J) (i, s) (j, s').
Proof.
  intros J i s He.
  destruct (mma_sss_total_ni J (i, (G.ca (G.core_of s) ## G.cb (G.core_of s) ## vec_nil))) as ([j v'] & Hm).
  destruct (cg_lift_mma2_step J i _ j v' s Hm (conj eq_refl (conj eq_refl He))) as (s' & Hs & _).
  exists j, s'. exact Hs.
Qed.

Lemma cmp_pr_halted_out : forall (Qy : list cg_yinstr) (s : cg_ystate),
  (forall y, In y Qy -> exists J, y = YMMA J) -> G.err (G.core_of s) = false ->
  P.pr_halted (map cg_tr Qy) (G.core_of s) -> out_code (G.pc (G.core_of s)) (1, Qy).
Proof.
  intros Qy s Hy He Hh. destruct (in_out_code_dec (G.pc (G.core_of s)) (1, Qy)) as [Hi | Ho]; [| exact Ho].
  exfalso. destruct (in_code_subcode Hi) as (y & (l & r & HQ & Hpc)). simpl in HQ, Hpc.
  assert (Hyin : In y Qy) by (rewrite HQ; apply in_or_app; right; left; reflexivity).
  destruct (Hy y Hyin) as (J & ->).
  unfold P.pr_halted, P.pr_next_instr in Hh. rewrite He in Hh.
  assert (Hf : G.fetch (map cg_tr Qy) (G.pc (G.core_of s)) = Some (cg_tr (YMMA J))).
  { rewrite HQ. unfold G.fetch. assert (G.pc (G.core_of s) = S (length l)) by lia. rewrite H.
    rewrite map_app. simpl. rewrite nth_error_app2 by (rewrite map_length; lia).
    rewrite map_length. replace (length l - length l) with 0 by lia. reflexivity. }
  rewrite Hf in Hh. destruct J as [p | p j]; simpl in Hh; discriminate.
Qed.

Lemma cmp_lift_run_conv : forall (Qy : list cg_yinstr), (forall y, In y Qy -> exists J, y = YMMA J) ->
  forall n s, G.err (G.core_of s) = false ->
  P.pr_halted (map cg_tr Qy) (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval n (map cg_tr Qy) s)) ->
  exists s', P.pr_run_prog cg_uprop_eqb cg_ueval n (map cg_tr Qy) s = s' /\
    G.err (G.core_of s') = false /\
    sss_output cg_ystep (1, Qy) (G.pc (G.core_of s), s) (G.pc (G.core_of s'), s').
Proof.
  intros Qy Hy n. induction n as [| n IH]; intros s He Hh.
  - simpl in Hh. exists s. split; [reflexivity |]. split; [exact He |].
    split; [exists 0; constructor | exact (cmp_pr_halted_out Qy s Hy He Hh)].
  - destruct (in_out_code_dec (G.pc (G.core_of s)) (1, Qy)) as [Hi | Ho].
    + destruct (in_code_subcode Hi) as (y & (l & r & HQ & Hpc)). simpl in HQ, Hpc.
      assert (Hyin : In y Qy) by (rewrite HQ; apply in_or_app; right; left; reflexivity).
      destruct (Hy y Hyin) as (J & Hyj). subst y.
      destruct (cmp_ystep_ex J (G.pc (G.core_of s)) s He) as (j & s2 & Hst).
      assert (Hpc' : G.pc (G.core_of s) = 1 + length l) by lia.
      assert (Hs2 : P.pr_step cg_uprop_eqb cg_ueval (map cg_tr Qy) s = s2).
      { rewrite HQ. rewrite (cg_pr_step_at l (YMMA J) r s ltac:(discriminate) He Hpc').
        destruct Hst as (_ & _ & E & _). exact (eq_sym E). }
      simpl in Hh. rewrite Hs2 in Hh.
      destruct Hst as (Hne & He0 & E2 & P2 & He2).
      destruct (IH s2 He2 Hh) as (s' & Hrun & Her & Hout).
      exists s'. split; [simpl; rewrite Hs2; exact Hrun |]. split; [exact Her |].
      destruct Hout as [Hc Hoc]. split; [| exact Hoc].
      destruct Hc as (m & Hm). exists (S m). simpl in P2.
      eapply in_sss_steps_S; [| rewrite <- P2 in Hm; exact Hm].
      rewrite HQ. apply in_sss_step with (l := l); [simpl; lia |].
      repeat split; assumption.
    + assert (Hh0 : P.pr_halted (map cg_tr Qy) (G.core_of s)).
      { unfold P.pr_halted, P.pr_next_instr. rewrite He.
        assert (Hf : G.fetch (map cg_tr Qy) (G.pc (G.core_of s)) = None).
        { unfold G.fetch. destruct (G.pc (G.core_of s)) as [| p] eqn:Ep; [reflexivity |].
          apply nth_error_None. rewrite map_length. unfold out_code, code_end in Ho. simpl in Ho. lia. }
        rewrite Hf. reflexivity. }
      rewrite (P.pr_run_prog_halted cg_uprop_eqb cg_ueval (S n) _ _ Hh0). exists s. split; [reflexivity |]. split; [exact He |].
      split; [exists 0; constructor | exact Ho].
Qed.

(* ================================================================= *)
(* The theorems about the guest program.                              *)
(* ================================================================= *)

(* The guest has stopped at the end of its program, counter A is 0,
   counter B holds the code of e, and nothing else has changed: no trap,
   no fact, no commitment, ledger 0, flag down. *)
Definition cmp_guest_final (k : nat) (Q : list (mm_instr nat)) (e : env nat nat) (s : cg_ystate) : Prop :=
  P.pr_halted (cmp_gprog k Q) (G.core_of s) /\
  G.pc (G.core_of s) = 1 + length (cmp_gprog k Q) /\
  G.ca (G.core_of s) = 0 /\ G.cb (G.core_of s) = cg_gk k e /\
  G.err (G.core_of s) = false /\ G.facts (G.core_of s) = [] /\ G.chan (G.core_of s) = None /\
  G.mu s = 0 /\ G.cert s = false.

Lemma cmp_pr_out_halted : forall (Qy : list cg_yinstr) (s : cg_ystate),
  G.err (G.core_of s) = false -> out_code (G.pc (G.core_of s)) (1, Qy) ->
  P.pr_halted (map cg_tr Qy) (G.core_of s).
Proof.
  intros Qy s He Ho. unfold P.pr_halted, P.pr_next_instr. rewrite He.
  assert (Hf : G.fetch (map cg_tr Qy) (G.pc (G.core_of s)) = None).
  { unfold G.fetch. destruct (G.pc (G.core_of s)) as [| p] eqn:Ep; [reflexivity |].
    apply nth_error_None. rewrite map_length. unfold out_code, code_end in Ho. simpl in Ho. lia. }
  rewrite Hf. reflexivity.
Qed.

Lemma cmp_guest_final_of : forall k Q e s,
  cg_simul k (e, cg_mkaux 0 false false) s ->
  P.pr_halted (cmp_gprog k Q) (G.core_of s) -> G.pc (G.core_of s) = 1 + length (cmp_gprog k Q) ->
  cmp_guest_final k Q e s.
Proof.
  intros k Q e s (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hh Hpc. simpl in H4, H5, H7, H8.
  destruct (H7 eq_refl) as [Hf Hc]. unfold cmp_guest_final. repeat split; assumption.
Qed.

Theorem cmp_guest_fwd : forall k Q, (forall J, In J Q -> cg_xreg J < k) ->
  forall e0, (forall x, k <= x -> e0 x = 0) -> forall j e1,
  sss_output mmstep (1, Q) (1, e0) (j, e1) ->
  exists n, cmp_guest_final k Q e1 (P.pr_run_prog cg_uprop_eqb cg_ueval n (cmp_gprog k Q) (cmp_gstart k e0)).
Proof.
  intros k Q Hq e0 He0 j e1 [[n Hn] Hout].
  assert (Hx : sss_output (cg_xstep k 0) (1, map XMM Q) (fst (1, map XMM Q), (e0, cg_mkaux 0 false false))
                 (j, (e1, cg_mkaux 0 false false))).
  { split.
    - exists n. cbn [fst]. exact (cg_lift_mm k 0 1 Q n 1 e0 j e1 _ Hq Hn).
    - unfold out_code, code_end in Hout |- *. cbn [fst snd] in Hout |- *. rewrite map_length. exact Hout. }
  destruct (cg_compile_output k 0 (1, map XMM Q) 1 (e0, cg_mkaux 0 false false) j (e1, cg_mkaux 0 false false)
              (cmp_gstart k e0) (cg_simul_start k e0 He0) Hx) as (w2 & Hs2 & [[m Hm] Hyo]).
  destruct (cg_lift_run _ m 1 (cmp_gstart k e0) _ w2 eq_refl Hm) as [Hrun Hpc].
  exists m.
  assert (Hg : P.pr_run_prog cg_uprop_eqb cg_ueval m (cmp_gprog k Q) (cmp_gstart k e0) = w2) by exact Hrun.
  rewrite Hg.
  assert (Hlen : length (cmp_gprog k Q) = length_compiler cg_ilen (map XMM Q))
    by (unfold cmp_gprog; rewrite map_length; apply cg_code_length).
  apply cmp_guest_final_of; [exact Hs2 | | ].
  - apply cmp_pr_out_halted; [apply Hs2 |]. rewrite Hpc. unfold out_code, code_end. cbn [fst snd]. right.
    rewrite cg_code_length. simpl. lia.
  - rewrite Hpc, Hlen. reflexivity.
Qed.

Theorem cmp_guest_bwd : forall k Q, (forall J, In J Q -> cg_xreg J < k) ->
  forall e0, (forall x, k <= x -> e0 x = 0) -> forall n,
  P.pr_halted (cmp_gprog k Q) (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval n (cmp_gprog k Q) (cmp_gstart k e0))) ->
  exists j e1, sss_output mmstep (1, Q) (1, e0) (j, e1) /\
    cmp_guest_final k Q e1 (P.pr_run_prog cg_uprop_eqb cg_ueval n (cmp_gprog k Q) (cmp_gstart k e0)).
Proof.
  intros k Q Hq e0 He0 n Hh.
  assert (Hs0 := cg_simul_start k e0 He0).
  destruct (cmp_lift_run_conv (cg_code k 0 (1, map XMM Q) 1) (cmp_gcode_ymma k 0 Q) n (cmp_gstart k e0)
              ltac:(reflexivity) Hh) as (s' & Hrun & Her & [[m Hm] Hoc]).
  assert (Hpc0 : G.pc (G.core_of (cmp_gstart k e0)) = 1) by reflexivity. rewrite Hpc0 in Hm.
  destruct (cmp_g_complete k 0 Q Hq (e0, cg_mkaux 0 false false) (cmp_gstart k e0) (G.pc (G.core_of s')) s' Hs0
              (conj (ex_intro _ m Hm) Hoc)) as (i2 & v2 & Hs2 & Hxo & Hj).
  destruct v2 as [e1 a1]. destruct Hxo as [[mx Hmx] Hxout].
  destruct (cmp_xunlift k 0 Q mx 1 e0 _ i2 e1 a1 Hmx) as [Ea Hmm]. subst a1.
  exists i2, e1. split.
  - split; [exists mx; exact Hmm |]. unfold out_code, code_end in Hxout |- *. cbn [fst snd] in Hxout |- *.
    rewrite map_length in Hxout. exact Hxout.
  - assert (Hg : P.pr_run_prog cg_uprop_eqb cg_ueval n (cmp_gprog k Q) (cmp_gstart k e0) = s') by exact Hrun.
    rewrite Hg. apply cmp_guest_final_of; [exact Hs2 | | ].
    + rewrite <- Hg. exact Hh.
    + rewrite Hj. unfold cmp_gprog. rewrite map_length. reflexivity.
Qed.

Print Assumptions cmp_guest_fwd.
Print Assumptions cmp_guest_bwd.
