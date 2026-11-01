(** CmpMM.v: the third compiler stage, from flat programs to counter-machine
    programs of the vendored library.

    Variable x of the flat program is register x + 1 of the counter machine,
    register 0 stays 0 (it is the register of every jump), and the working
    space of the expression code starts at register nv + 1 where nv bounds
    the variables. Each flat instruction is compiled by itself, in place:

      FAssign x e    the code of e into register nv + 1, then clear register
                     x + 1, then move register nv + 1 into register x + 1
      FJmpF b j      the condition code of b, true: the next instruction,
                     false: the instruction j
      FJmp j         one DEC 0 j

    The instruction compiler cmp_icomp is given the address function lnk
    (the position in the target of every source address, supplied by the
    vendored linker). The simulation relation cmp_simul nv v w says that
    register 0 of w is 0, that registers 1 .. nv of w are the variables
    0 .. nv - 1 of v, and that every register above nv is 0.

      cmp_icomp_sound   one source step is matched by a run of at least one
                        step of the compiled instruction, which preserves
                        the relation (this is instruction_compiler_sound of
                        the vendored compiler theory)
      cmp_mm_sound      a flat run gives a counter machine run (the vendored
                        compiler_sound)
      cmp_mm_complete   a counter machine run that leaves the compiled
                        program passes through the image of a source run that
                        leaves the source program (the vendored
                        compiler_complete', which needs the flat step to be
                        total and the counter machine step to be functional,
                        both proved)

    Dependencies: Coq standard library, the vendored coq-undecidability
    library and the Cmp files before this one. No axioms and no unfinished proofs.     *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is one stage of the verified compiler pipeline of CmpPipeline.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library and the Cmp files. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.Shared.Libs.DLW.Code Require Import compiler compiler_correction.
From Undecidability.MinskyMachines Require Import MM.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Import Kernel.CmpLang Kernel.CmpInline Kernel.CmpFlat Kernel.CmpBlocks Kernel.CmpExpr.

Local Notation mmstep := (@mm_sss_env nat eq_nat_dec).

Lemma cmp_blen_pos : forall b, 1 <= cmp_blen b.
Proof.
  induction b as [| | x y | x y | c IH | c IHc d IHd | c IHc d IHd]; simpl; lia.
Qed.

Definition cmp_ilen (nv : nat) (I : cmp_fi) : nat :=
  match I with
  | FAssign _ e => if cmp_fi_ok nv I then cmp_alen e + 5 else 1
  | FJmpF b _ => if cmp_fi_ok nv I then cmp_blen b else 1
  | FJmp _ => 1
  end.

Definition cmp_icomp (nv : nat) (lnk : nat -> nat) (i : nat) (I : cmp_fi) : list cmp_mi :=
  match I with
  | FAssign x e =>
      if cmp_fi_ok nv I then
        cmp_cexp (S nv) e (lnk i) ++ cmp_clear (lnk i + cmp_alen e) (S x) ++
        cmp_addmv (lnk i + cmp_alen e + 2) (S nv) (S x)
      else [mm_dec 0 (lnk (S i))]
  | FJmpF b j =>
      if cmp_fi_ok nv I then cmp_cb (S nv) b (lnk i) (lnk (S i)) (lnk j) else [mm_dec 0 (lnk (S i))]
  | FJmp j => [mm_dec 0 (lnk j)]
  end.

Lemma cmp_icomp_length : forall nv lnk i I, length (cmp_icomp nv lnk i I) = cmp_ilen nv I.
Proof.
  intros nv lnk i I. destruct I as [x e | b j | j]; simpl.
  - destruct (cmp_fi_ok nv (FAssign x e)); [| reflexivity].
    rewrite !app_length, cmp_cexp_len. simpl. lia.
  - destruct (cmp_fi_ok nv (FJmpF b j)); [| reflexivity]. apply cmp_cb_len.
  - reflexivity.
Qed.

(* Registers 1 .. nv are the variables, 0 is zero, the rest is empty. *)
Definition cmp_simul (nv : nat) (v : cmp_env) (w : env nat nat) : Prop :=
  w 0 = 0 /\ (forall r, r < nv -> w (S r) = v r) /\ (forall r, S nv <= r -> w r = 0).

Lemma cmp_fi_ok_true : forall nv I, cmp_fi_ok nv I = true -> cmp_fi_max I <= nv.
Proof. intros nv I H. unfold cmp_fi_ok in H. apply Nat.leb_le. exact H. Qed.

Lemma cmp_aeval_simul : forall nv v w a, cmp_simul nv v w -> cmp_avmax a <= nv ->
  cmp_aeval (fun x => w (S x)) a = cmp_aeval v a.
Proof.
  intros nv v w a (H0 & Hv & Hz) Ha. apply cmp_aeval_below. intros r Hr. apply Hv. lia.
Qed.

Lemma cmp_beval_simul : forall nv v w b, cmp_simul nv v w -> cmp_bvmax b <= nv ->
  cmp_beval (fun x => w (S x)) b = cmp_beval v b.
Proof.
  intros nv v w b (H0 & Hv & Hz) Hb. apply cmp_beval_below. intros r Hr. apply Hv. lia.
Qed.


Lemma cmp_icomp_assign_core : forall nv a0 x e v w1,
  cmp_fi_max (FAssign x e) <= nv -> cmp_simul nv v w1 ->
  exists w2,
    cmp_reach (a0, cmp_cexp (S nv) e a0 ++ cmp_clear (a0 + cmp_alen e) (S x) ++
                   cmp_addmv (a0 + cmp_alen e + 2) (S nv) (S x))
      a0 w1 (a0 + (cmp_alen e + 5)) w2 /\
    cmp_simul nv (cmp_upd v x (cmp_aeval v e)) w2.
Proof.
  intros nv a0 x e v w1 Hm Hsim. cbn [cmp_fi_max] in Hm.
  pose proof Hsim as Hsim'. destruct Hsim' as (H0 & Hv & Hz).
  set (la := cmp_alen e). set (t := S nv).
  set (P := (a0, cmp_cexp t e a0 ++ cmp_clear (a0 + la) (S x) ++ cmp_addmv (a0 + la + 2) t (S x))).
  assert (s1 : (a0, cmp_cexp t e a0) <sc P) by (apply cmp_sc_l with (r := cmp_clear (a0 + la) (S x) ++ cmp_addmv (a0 + la + 2) t (S x)); apply subcode_refl).
  assert (s2 : (a0 + la, cmp_clear (a0 + la) (S x)) <sc P).
  { apply cmp_sc_l with (r := cmp_addmv (a0 + la + 2) t (S x)).
    apply cmp_sc_r with (l := cmp_cexp t e a0) (a := a0); [unfold la; rewrite cmp_cexp_len; reflexivity | apply subcode_refl]. }
  assert (s3 : (a0 + la + 2, cmp_addmv (a0 + la + 2) t (S x)) <sc P).
  { apply cmp_sc_r with (l := cmp_cexp t e a0 ++ cmp_clear (a0 + la) (S x)) (a := a0);
      [rewrite app_length, cmp_cexp_len; unfold la; simpl; lia |]. rewrite <- app_assoc. apply subcode_refl. }
  set (val := cmp_aeval (fun z => w1 (S z)) e).
  assert (Hval : val = cmp_aeval v e) by (unfold val; apply (cmp_aeval_simul nv v w1 e Hsim); lia).
  set (w2 := cmp_upd w1 t val).
  assert (E20 : w2 0 = 0) by (unfold w2; rewrite cmp_upd_other by (unfold t; lia); exact H0).
  set (w3 := cmp_upd w2 (S x) 0).
  assert (E30 : w3 0 = 0) by (unfold w3; rewrite cmp_upd_other by lia; exact E20).
  assert (R1 : cmp_reach0 P a0 w1 (a0 + la) w2).
  { apply (cmp_cexp_spec e t a0 P w1 s1 ltac:(unfold t; lia) H0 (fun r Hr => Hz r Hr)). }
  assert (R2 : cmp_reach P (a0 + la) w2 (a0 + la + 2) w3).
  { apply (cmp_blk_clear P (a0 + la) (S x) w2 s2 ltac:(lia) E20). }
  assert (R3 : cmp_reach P (a0 + la + 2) w3 (a0 + la + 2 + 3)
                 (fun y => if Nat.eqb y t then 0 else if Nat.eqb y (S x) then w3 (S x) + w3 t else w3 y)).
  { apply (cmp_blk_addmv P (a0 + la + 2) t (S x) w3 s3 ltac:(unfold t; lia) ltac:(lia) ltac:(unfold t; lia) E30). }
  assert (R23 := cmp_reach_trans _ _ _ _ _ _ _ R2 R3).
  assert (R := cmp_reach0_trans_reach _ _ _ _ _ _ _ R1 R23).
  exists (fun y => if Nat.eqb y t then 0 else if Nat.eqb y (S x) then w3 (S x) + w3 t else w3 y).
  split.
  - eapply cmp_reach_at; [exact R | unfold la; lia].
  - assert (Ex : forall r, r < nv -> w1 (S r) = v r) by exact Hv.
    unfold cmp_simul. repeat split.
    + unfold w3, w2, cmp_upd, t in *. eqb_all.
    + intros r Hr. unfold w3, w2, cmp_upd, t in *.
      assert (Hr1 := Ex r Hr). eqb_all; try (rewrite Hval; reflexivity); try (apply Ex; lia); try lia.
    + intros r Hr. unfold w3, w2, cmp_upd, t in *.
      assert (Hr1 := Hz r Hr). eqb_all.
Qed.

Lemma cmp_icomp_jmpf_core : forall nv a0 b lt lf v w1, cmp_bvmax b <= nv -> cmp_simul nv v w1 ->
  exists w2, cmp_reach (a0, cmp_cb (S nv) b a0 lt lf) a0 w1 (if cmp_beval v b then lt else lf) w2 /\
             cmp_simul nv v w2.
Proof.
  intros nv a0 b lt lf v w1 Hb Hsim. pose proof Hsim as Hsim'. destruct Hsim' as (H0 & Hv & Hz).
  exists w1. split; [| exact Hsim].
  rewrite <- (cmp_beval_simul nv v w1 b Hsim Hb).
  apply (cmp_cb_spec b (S nv) a0 lt lf (a0, cmp_cb (S nv) b a0 lt lf) w1 (subcode_refl _) ltac:(lia) H0 Hz).
Qed.

Lemma cmp_nop_prog : forall a k (w : nat -> nat), w 0 = 0 ->
  sss_progress mmstep (a, [mm_dec 0 k]) (a, w) (k, w).
Proof.
  intros a k w H0. unfold sss_progress.
  eapply mm_env_progress_DEC_0 with (st := (k, w)); [apply subcode_refl | rewrite cmp_get_env; exact H0 | exists 0; constructor].
Qed.

Lemma cmp_icomp_assign_eq : forall nv lnk i x e, cmp_fi_ok nv (FAssign x e) = true ->
  cmp_icomp nv lnk i (FAssign x e) =
  cmp_cexp (S nv) e (lnk i) ++ cmp_clear (lnk i + cmp_alen e) (S x) ++ cmp_addmv (lnk i + cmp_alen e + 2) (S nv) (S x).
Proof. intros nv lnk i x e H. unfold cmp_icomp. rewrite H. reflexivity. Qed.

Lemma cmp_icomp_jmpf_eq : forall nv lnk i b j, cmp_fi_ok nv (FJmpF b j) = true ->
  cmp_icomp nv lnk i (FJmpF b j) = cmp_cb (S nv) b (lnk i) (lnk (S i)) (lnk j).
Proof. intros nv lnk i b j H. unfold cmp_icomp. rewrite H. reflexivity. Qed.

Lemma cmp_icomp_nop_eq : forall nv lnk i I, cmp_fi_ok nv I = false ->
  cmp_icomp nv lnk i I = [mm_dec 0 (lnk (S i))].
Proof.
  intros nv lnk i I H. destruct I as [x e | b j | j].
  - unfold cmp_icomp. rewrite H. reflexivity.
  - unfold cmp_icomp. rewrite H. reflexivity.
  - rewrite cmp_fi_ok_jmp in H. discriminate.
Qed.


Lemma cmp_simul_pw : forall nv v w3 w2, cmp_simul nv v w2 -> (forall y, w3 y = w2 y) -> cmp_simul nv v w3.
Proof.
  intros nv v w3 w2 (A & B & C) Hw. repeat split.
  - rewrite Hw. exact A.
  - intros r Hr. rewrite Hw. apply B. exact Hr.
  - intros r Hr. rewrite Hw. apply C. exact Hr.
Qed.

Lemma cmp_sound_nop : forall nv lnk I i1 v w1, cmp_fi_ok nv I = false -> cmp_simul nv v w1 ->
  exists w2, sss_progress mmstep (lnk i1, cmp_icomp nv lnk i1 I) (lnk i1, w1) (lnk (S i1), w2) /\ cmp_simul nv v w2.
Proof.
  intros nv lnk I i1 v w1 H Hsim. exists w1. split; [| exact Hsim].
  rewrite (cmp_icomp_nop_eq nv lnk i1 I H). apply cmp_nop_prog. exact (proj1 Hsim).
Qed.

Lemma cmp_sound_assign : forall nv lnk x a i1 v w1,
  cmp_fi_ok nv (FAssign x a) = true -> lnk (S i1) = cmp_ilen nv (FAssign x a) + lnk i1 -> cmp_simul nv v w1 ->
  exists w2, sss_progress mmstep (lnk i1, cmp_icomp nv lnk i1 (FAssign x a)) (lnk i1, w1) (lnk (S i1), w2) /\
             cmp_simul nv (cmp_upd v x (cmp_aeval v a)) w2.
Proof.
  intros nv lnk x a i1 v w1 Hok Hl Hsim.
  assert (H : cmp_fi_max (FAssign x a) <= nv) by (apply cmp_fi_ok_true; exact Hok).
  cbn [cmp_ilen] in Hl. rewrite Hok in Hl.
  destruct (cmp_icomp_assign_core nv (lnk i1) x a v w1 H Hsim) as (w2 & (w3 & Hw3 & k & Hk & Hs3) & Hsim2).
  exists w3. split.
  - rewrite (cmp_icomp_assign_eq nv lnk i1 x a Hok). exists k. split; [exact Hk |].
    replace (lnk (S i1)) with (lnk i1 + (cmp_alen a + 5)) by lia. exact Hs3.
  - eapply cmp_simul_pw; [exact Hsim2 | exact Hw3].
Qed.

Lemma cmp_sound_jmpf : forall nv lnk b j i1 v w1 (taken : bool),
  cmp_fi_ok nv (FJmpF b j) = true -> cmp_beval v b = taken -> cmp_simul nv v w1 ->
  exists w2, sss_progress mmstep (lnk i1, cmp_icomp nv lnk i1 (FJmpF b j)) (lnk i1, w1)
               (if taken then lnk (S i1) else lnk j, w2) /\ cmp_simul nv v w2.
Proof.
  intros nv lnk b j i1 v w1 taken Hok Hb Hsim.
  assert (Hm : cmp_bvmax b <= nv) by (apply cmp_fi_ok_true in Hok; exact Hok).
  destruct (cmp_icomp_jmpf_core nv (lnk i1) b (lnk (S i1)) (lnk j) v w1 Hm Hsim) as (w2 & (w3 & Hw3 & k & Hk & Hs3) & Hsim2).
  exists w3. split.
  - rewrite (cmp_icomp_jmpf_eq nv lnk i1 b j Hok). exists k. split; [exact Hk |].
    rewrite Hb in Hs3. exact Hs3.
  - eapply cmp_simul_pw; [exact Hsim2 | exact Hw3].
Qed.

Theorem cmp_icomp_sound : forall nv, instruction_compiler_sound (cmp_icomp nv) (cmp_fstep nv) mmstep (cmp_simul nv).
Proof.
  intros nv lnk I i1 v1 i2 v2 w1 Hstep Hl Hsim.
  rewrite cmp_icomp_length in Hl.
  inversion Hstep; subst.
  - eapply cmp_sound_nop; eassumption.
  - eapply cmp_sound_assign; eassumption.
  - eapply cmp_sound_jmpf with (taken := true); eassumption.
  - eapply cmp_sound_jmpf with (taken := false); eassumption.
  - exists w1. split; [| exact Hsim]. cbn [cmp_icomp]. apply cmp_nop_prog. exact (proj1 Hsim).
Qed.

(* ================================================================= *)
(* Whole programs, with the vendored linker.                          *)
(* ================================================================= *)

Lemma cmp_mm_fun : forall I st st1 st2, mmstep I st st1 -> mmstep I st st2 -> st1 = st2.
Proof. intros I st st1 st2 H1 H2. exact (mm_sss_env_fun H1 H2). Qed.

Definition cmp_err (nv : nat) (Px : nat * list cmp_fi) (iQ : nat) : nat :=
  iQ + length_compiler (cmp_ilen nv) (snd Px).

Definition cmp_link (nv : nat) (Px : nat * list cmp_fi) (iQ : nat) : nat -> nat :=
  linker (cmp_ilen nv) Px iQ (cmp_err nv Px iQ).

Definition cmp_code (nv : nat) (Px : nat * list cmp_fi) (iQ : nat) : list cmp_mi :=
  compiler (cmp_icomp nv) (cmp_ilen nv) Px iQ (cmp_err nv Px iQ).

Lemma cmp_code_length : forall nv Px iQ, length (cmp_code nv Px iQ) = length_compiler (cmp_ilen nv) (snd Px).
Proof. intros. unfold cmp_code. apply compiler_length, cmp_icomp_length. Qed.

Lemma cmp_link_start : forall nv Px iQ, cmp_link nv Px iQ (fst Px) = iQ.
Proof. intros. unfold cmp_link. apply (linker_code_start (cmp_ilen nv) Px). Qed.

Lemma cmp_link_out : forall nv Px iQ j,
  out_code j Px -> cmp_link nv Px iQ j = iQ + length_compiler (cmp_ilen nv) (snd Px).
Proof.
  intros nv Px iQ j H. unfold cmp_link.
  rewrite (@linker_out_err _ (cmp_ilen nv) Px iQ (cmp_err nv Px iQ) j); [reflexivity | | exact H].
  unfold cmp_err. lia.
Qed.

Lemma cmp_mm_subcode : forall nv Px iQ i rho,
  (i, [rho]) <sc Px ->
  (cmp_link nv Px iQ i, cmp_icomp nv (cmp_link nv Px iQ) i rho) <sc (iQ, cmp_code nv Px iQ) /\
  cmp_link nv Px iQ (1 + i) = cmp_ilen nv rho + cmp_link nv Px iQ i.
Proof.
  intros nv Px iQ i rho H.
  exact (compiler_subcode (cmp_icomp nv) (cmp_ilen nv) (cmp_icomp_length nv) Px iQ (cmp_err nv Px iQ) i rho H).
Qed.

Theorem cmp_mm_sound : forall nv Px iQ i1 v1 i2 v2 w1,
  cmp_simul nv v1 w1 -> sss_compute (cmp_fstep nv) Px (i1, v1) (i2, v2) ->
  exists w2, cmp_simul nv v2 w2 /\
    sss_compute mmstep (iQ, cmp_code nv Px iQ) (cmp_link nv Px iQ i1, w1) (cmp_link nv Px iQ i2, w2).
Proof.
  intros nv Px iQ i1 v1 i2 v2 w1 Hs Hc.
  exact (compiler_sound (cmp_ilen nv) (cmp_icomp_length nv) (cmp_icomp_sound nv)
           (cmp_link nv Px iQ) (iQ, cmp_code nv Px iQ) (cmp_mm_subcode nv Px iQ) w1 (conj Hs Hc)).
Qed.

Theorem cmp_mm_complete : forall nv Px iQ i1 v1 w1 st,
  cmp_simul nv v1 w1 -> sss_output mmstep (iQ, cmp_code nv Px iQ) (cmp_link nv Px iQ i1, w1) st ->
  exists i2 v2 w2, cmp_simul nv v2 w2 /\ sss_output (cmp_fstep nv) Px (i1, v1) (i2, v2) /\
    sss_output mmstep (iQ, cmp_code nv Px iQ) (cmp_link nv Px iQ i2, w2) st.
Proof.
  intros nv Px iQ i1 v1 w1 st Hs Ho.
  exact (compiler_complete' (cmp_ilen nv) (cmp_icomp_length nv) (cmp_fstep_total nv) cmp_mm_fun
           (cmp_icomp_sound nv) (cmp_link nv Px iQ) Px (cmp_mm_subcode nv Px iQ) i1 v1 (conj Hs Ho)).
Qed.

(* A whole run from the start of the flat program, leaving it, is matched by
   a run from the start of the compiled program to its end. *)
Theorem cmp_mm_output : forall nv Px iQ v1 i2 v2 w1,
  cmp_simul nv v1 w1 -> sss_output (cmp_fstep nv) Px (fst Px, v1) (i2, v2) ->
  exists w2, cmp_simul nv v2 w2 /\
    sss_output mmstep (iQ, cmp_code nv Px iQ) (iQ, w1) (iQ + length (cmp_code nv Px iQ), w2).
Proof.
  intros nv Px iQ v1 i2 v2 w1 Hs [Hc Hout].
  destruct (cmp_mm_sound nv Px iQ _ _ _ _ w1 Hs Hc) as (w2 & Hs2 & Hc2).
  rewrite cmp_link_start, (cmp_link_out nv Px iQ i2 Hout) in Hc2.
  exists w2. split; [exact Hs2 |]. split.
  - rewrite cmp_code_length. exact Hc2.
  - unfold out_code, code_end. cbn [fst snd]. right. apply Nat.le_refl.
Qed.

(* Conversely, a run of the compiled program from its start that leaves it
   ends at its end, and the flat program has a run from its start that leaves
   it with the same variables. *)
Theorem cmp_mm_output_conv : forall nv Px iQ v1 j w1 w2,
  cmp_simul nv v1 w1 ->
  sss_output mmstep (iQ, cmp_code nv Px iQ) (iQ, w1) (j, w2) ->
  exists i2 v2, cmp_simul nv v2 w2 /\ sss_output (cmp_fstep nv) Px (fst Px, v1) (i2, v2) /\
    j = iQ + length (cmp_code nv Px iQ).
Proof.
  intros nv Px iQ v1 j w1 w2 Hs Ho.
  assert (Ho' : sss_output mmstep (iQ, cmp_code nv Px iQ) (cmp_link nv Px iQ (fst Px), w1) (j, w2))
    by (rewrite cmp_link_start; exact Ho).
  destruct (cmp_mm_complete nv Px iQ (fst Px) v1 w1 (j, w2) Hs Ho') as (i2 & v2 & w2' & Hs2 & Hf & Hq).
  destruct Hf as [Hf Hfo]. destruct Hq as [Hq Hqo].
  assert (Hl : cmp_link nv Px iQ i2 = iQ + length (cmp_code nv Px iQ)).
  { rewrite cmp_code_length. apply cmp_link_out. exact Hfo. }
  assert (Hlo : out_code (fst (cmp_link nv Px iQ i2, w2')) (iQ, cmp_code nv Px iQ)).
  { cbn [fst]. rewrite Hl. unfold out_code, code_end. cbn [fst snd]. right. apply Nat.le_refl. }
  pose proof (sss_compute_stop Hlo Hq) as E. inversion E; subst.
  exists i2, v2. split; [exact Hs2 | split; [split; assumption | exact Hl]].
Qed.

Print Assumptions cmp_icomp_sound.
Print Assumptions cmp_mm_output.
Print Assumptions cmp_mm_output_conv.
