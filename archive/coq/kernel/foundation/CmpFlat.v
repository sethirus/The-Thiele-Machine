(** CmpFlat.v: the second compiler stage, from structured programs without
    calls to flat programs with jumps.

    The flat language has three instructions, each one machine step:
    FAssign x a sets variable x to the value of a, FJmpF b j goes to address
    j when b is false and to the next address when it is true, FJmp j goes to
    address j. A program is a list placed at a start address (the counter
    machine convention of the vendored library: the instruction at address
    start + i is the i-th of the list). A program counter outside the list
    stops the run.

    The step relation cmp_fstep nv is parameterised by a bound nv on the
    variables. An instruction that names a variable of nv or above does
    nothing but advance (this only makes the relation total, which the
    vendored compiler theory asks for; the compiler never produces such an
    instruction when nv is the largest variable plus one).

    cmp_fc s a is the code of s placed at address a; cmp_flen s is its
    length, which does not depend on a. A while loop is
        a:        FJmpF b (a + l + 2)
        a+1 ..:   the body (l instructions)
        a+l+1:    FJmp a
    and a conditional is FJmpF b to the else part, the then part, FJmp past
    the else part, the else part.

      cmp_fc_fwd   a derivation gives a run from the start of the code to
                   its end, with equal variables
      cmp_fc_bwd   a run from the start of the code that ends outside the
                   code passes through the end of the code, and the
                   statement has a derivation from the start variables

    The second theorem has no assumption about termination: a run that stops
    anywhere outside the code is enough. Together they say that the flat
    program halts exactly when the structured one does.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library and CmpLang.v. No axioms and no unfinished proofs.                         *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is one stage of the verified compiler pipeline of CmpPipeline.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library and CmpLang.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
Require Import Kernel.CmpLang Kernel.CmpInline.

Inductive cmp_fi : Set :=
| FAssign (x : nat) (a : cmp_aexp)
| FJmpF (b : cmp_bexp) (j : nat)
| FJmp (j : nat).

(* One more than the largest variable the instruction names. *)
Definition cmp_fi_max (i : cmp_fi) : nat :=
  match i with
  | FAssign x a => Nat.max (S x) (cmp_avmax a)
  | FJmpF b _ => cmp_bvmax b
  | FJmp _ => 0
  end.

Definition cmp_fi_ok (nv : nat) (i : cmp_fi) : bool := Nat.leb (cmp_fi_max i) nv.

Inductive cmp_fstep (nv : nat) : cmp_fi -> (nat * cmp_env) -> (nat * cmp_env) -> Prop :=
| FSNop : forall I i e, cmp_fi_ok nv I = false -> cmp_fstep nv I (i, e) (S i, e)
| FSAssign : forall x a i e, cmp_fi_ok nv (FAssign x a) = true ->
    cmp_fstep nv (FAssign x a) (i, e) (S i, cmp_upd e x (cmp_aeval e a))
| FSJfT : forall b j i e, cmp_fi_ok nv (FJmpF b j) = true -> cmp_beval e b = true ->
    cmp_fstep nv (FJmpF b j) (i, e) (S i, e)
| FSJfF : forall b j i e, cmp_fi_ok nv (FJmpF b j) = true -> cmp_beval e b = false ->
    cmp_fstep nv (FJmpF b j) (i, e) (j, e)
| FSJmp : forall j i e, cmp_fstep nv (FJmp j) (i, e) (j, e).

Lemma cmp_fi_ok_jmp : forall nv j, cmp_fi_ok nv (FJmp j) = true.
Proof. reflexivity. Qed.

Lemma cmp_fstep_fun : forall nv I s t1 t2, cmp_fstep nv I s t1 -> cmp_fstep nv I s t2 -> t1 = t2.
Proof.
  intros nv I s t1 t2 H1 H2. inversion H1; subst; inversion H2; subst;
    try (rewrite cmp_fi_ok_jmp in *; discriminate); try congruence; reflexivity.
Qed.

Lemma cmp_fstep_total : forall nv I st, exists st', cmp_fstep nv I st st'.
Proof.
  intros nv I [i e]. destruct (cmp_fi_ok nv I) eqn:Ho.
  - destruct I.
    + eexists. apply FSAssign. exact Ho.
    + destruct (cmp_beval e b) eqn:Hb; eexists; [apply FSJfT | apply FSJfF]; eassumption.
    + eexists. apply FSJmp.
  - eexists. apply FSNop. exact Ho.
Qed.

(* ================================================================= *)
(* The compiler stage.                                                *)
(* ================================================================= *)

Fixpoint cmp_flen (s : cmp_stmt) : nat :=
  match s with
  | SSkip => 0
  | SAssign _ _ => 1
  | SSeq s t => cmp_flen s + cmp_flen t
  | SIf _ s t => 1 + cmp_flen s + 1 + cmp_flen t
  | SWhile _ s => 1 + cmp_flen s + 1
  | SCall _ _ _ => 0
  end.

Fixpoint cmp_fc (s : cmp_stmt) (a : nat) : list cmp_fi :=
  match s with
  | SSkip => []
  | SAssign x e => [FAssign x e]
  | SSeq s t => cmp_fc s a ++ cmp_fc t (a + cmp_flen s)
  | SIf b s t =>
      FJmpF b (a + 1 + cmp_flen s + 1) :: (cmp_fc s (S a) ++
      FJmp (a + 1 + cmp_flen s + 1 + cmp_flen t) :: cmp_fc t (a + 1 + cmp_flen s + 1))
  | SWhile b s => FJmpF b (a + 1 + cmp_flen s + 1) :: (cmp_fc s (S a) ++ [FJmp a])
  | SCall _ _ _ => []
  end.

Lemma cmp_fc_length : forall s a, length (cmp_fc s a) = cmp_flen s.
Proof.
  induction s as [| x e | s1 IH1 s2 IH2 | b s1 IH1 s2 IH2 | b s IH | ds p args]; intros a; simpl; auto.
  - rewrite app_length, IH1, IH2. reflexivity.
  - rewrite app_length. simpl. rewrite IH1, IH2. lia.
  - rewrite app_length. simpl. rewrite IH. lia.
Qed.

(* ================================================================= *)
(* Helpers on runs.                                                   *)
(* ================================================================= *)

Local Notation fsteps nv := (sss_steps (cmp_fstep nv)).
Local Notation fcomp nv := (sss_compute (cmp_fstep nv)).

Lemma cmp_sub_left : forall (l r : list cmp_fi) a P, (a, l ++ r) <sc P -> (a, l) <sc P.
Proof. intros l r a P H. apply subcode_trans with (Q := (a, l ++ r)); [apply subcode_left; reflexivity | exact H]. Qed.

Lemma cmp_sub_right : forall (l r : list cmp_fi) a b P, b = a + length l -> (a, l ++ r) <sc P -> (b, r) <sc P.
Proof. intros l r a b P Hb H. apply subcode_trans with (Q := (a, l ++ r)); [apply subcode_right; exact Hb | exact H]. Qed.

(* One instruction in place gives the step. *)
Lemma cmp_instr_at : forall (i : cmp_fi) a P, (a, [i]) <sc P ->
  forall nv e st', fsteps nv P 1 (a, e) st' -> cmp_fstep nv i (a, e) st'.
Proof.
  intros i a P Hsc nv e st' H.
  destruct (sss_steps_S_inv' H) as (st2 & H1 & H2).
  apply sss_steps_0_inv in H2. subst st2.
  eapply subcode_sss_step_inv_1 with (st1 := (a, e)); [exact Hsc | exact H1].
Qed.

(* ================================================================= *)
(* Forward.                                                           *)
(* ================================================================= *)

Lemma cmp_instr_sub : forall (i : cmp_fi) (l : list cmp_fi) q P, (q, i :: l) <sc P ->
  (q, [i]) <sc P /\ (S q, l) <sc P.
Proof. intros i l q P H. apply subcode_cons_invert_left in H. exact H. Qed.

(* One step of an instruction in place, then the rest. *)
Lemma cmp_step_then : forall nv (i : cmp_fi) q P st2 st3,
  (q, [i]) <sc P -> forall e, cmp_fstep nv i (q, e) st2 -> fcomp nv P st2 st3 -> fcomp nv P (q, e) st3.
Proof. intros nv i q P st2 st3 Hsc e Hs Hr. eapply subcode_sss_compute_instr; eassumption. Qed.

Theorem cmp_fc_fwd : forall e s e1 c, cmp_ceval [] e s e1 c ->
  forall FP q nv fe, (q, cmp_fc s q) <sc FP -> cmp_svmax s <= nv -> cmp_eqv e fe ->
  exists fe1, cmp_eqv e1 fe1 /\ fcomp nv FP (q, fe) (q + cmp_flen s, fe1).
Proof.
  intros e s e1 c H. induction H; intros FP q nv fe Hsub Hsv Hq.
  - exists fe. split; [exact Hq |]. replace (q + cmp_flen SSkip) with q by (cbn; lia). exists 0. constructor.
  - cbn [cmp_svmax] in Hsv. cbn [cmp_fc] in Hsub.
    exists (cmp_upd fe x (cmp_aeval fe a)). split.
    + intros y. unfold cmp_upd. destruct (Nat.eqb y x); [apply cmp_aeval_eqv; exact Hq | apply Hq].
    + eapply cmp_step_then; [exact Hsub | apply FSAssign; unfold cmp_fi_ok, cmp_fi_max; apply Nat.leb_le; lia |].
      replace (q + cmp_flen (SAssign x a)) with (S q) by (cbn; lia). exists 0. constructor.
  - cbn [cmp_svmax] in Hsv. cbn [cmp_fc] in Hsub.
    destruct (IHcmp_ceval1 FP q nv fe (cmp_sub_left _ _ _ _ Hsub) ltac:(lia) Hq) as (f1 & Q1 & R1).
    destruct (IHcmp_ceval2 FP (q + cmp_flen s) nv f1
                (cmp_sub_right _ _ _ _ _ ltac:(rewrite cmp_fc_length; reflexivity) Hsub) ltac:(lia) Q1)
      as (f2 & Q2 & R2).
    exists f2. split; [exact Q2 |]. cbn [cmp_flen]. replace (q + (cmp_flen s + cmp_flen t)) with (q + cmp_flen s + cmp_flen t) by lia.
    eapply sss_compute_trans; eassumption.
  - cbn [cmp_svmax] in Hsv. cbn [cmp_fc] in Hsub.
    destruct (cmp_instr_sub _ _ _ _ Hsub) as [Hi Hrest].
    destruct (IHcmp_ceval FP (S q) nv fe (cmp_sub_left _ _ _ _ Hrest) ltac:(lia) Hq) as (f1 & Q1 & R1).
    destruct (cmp_instr_sub _ _ _ _ (cmp_sub_right (cmp_fc s (S q)) _ (S q) (q + 1 + cmp_flen s) _ ltac:(rewrite cmp_fc_length; lia) Hrest)) as [Hj _].
    exists f1. split; [exact Q1 |].
    eapply cmp_step_then; [exact Hi | apply FSJfT; [unfold cmp_fi_ok, cmp_fi_max; apply Nat.leb_le; lia | rewrite <- (cmp_beval_eqv b e fe Hq); exact H] |].
    replace (S q + cmp_flen s) with (q + 1 + cmp_flen s) in R1 by lia.
    eapply sss_compute_trans; [exact R1 |].
    eapply cmp_step_then; [exact Hj | apply FSJmp |].
    cbn [cmp_flen]. replace (q + (1 + cmp_flen s + 1 + cmp_flen t)) with (q + 1 + cmp_flen s + 1 + cmp_flen t) by lia.
    exists 0. constructor.
  - cbn [cmp_svmax] in Hsv. cbn [cmp_fc] in Hsub.
    destruct (cmp_instr_sub _ _ _ _ Hsub) as [Hi Hrest].
    assert (Hsub2 : (q + 1 + cmp_flen s + 1, cmp_fc t (q + 1 + cmp_flen s + 1)) <sc FP).
    { apply cmp_sub_right with (l := cmp_fc s (S q) ++ [FJmp (q + 1 + cmp_flen s + 1 + cmp_flen t)]) (a := S q).
      - rewrite app_length, cmp_fc_length. simpl. lia.
      - rewrite <- app_assoc. exact Hrest. }
    destruct (IHcmp_ceval FP (q + 1 + cmp_flen s + 1) nv fe Hsub2 ltac:(lia) Hq) as (f1 & Q1 & R1).
    exists f1. split; [exact Q1 |].
    eapply cmp_step_then; [exact Hi | apply FSJfF; [unfold cmp_fi_ok, cmp_fi_max; apply Nat.leb_le; lia | rewrite <- (cmp_beval_eqv b e fe Hq); exact H] |].
    cbn [cmp_flen]. replace (q + (1 + cmp_flen s + 1 + cmp_flen t)) with (q + 1 + cmp_flen s + 1 + cmp_flen t) by lia.
    exact R1.
  - cbn [cmp_svmax] in Hsv. cbn [cmp_fc] in Hsub.
    destruct (cmp_instr_sub _ _ _ _ Hsub) as [Hi Hrest].
    exists fe. split; [exact Hq |].
    eapply cmp_step_then; [exact Hi | apply FSJfF; [unfold cmp_fi_ok, cmp_fi_max; apply Nat.leb_le; lia | rewrite <- (cmp_beval_eqv b e fe Hq); exact H] |].
    cbn [cmp_flen]. replace (q + (1 + cmp_flen s + 1)) with (q + 1 + cmp_flen s + 1) by lia.
    exists 0. constructor.
  - cbn [cmp_svmax] in Hsv. cbn [cmp_fc] in Hsub.
    destruct (cmp_instr_sub _ _ _ _ Hsub) as [Hi Hrest].
    destruct (IHcmp_ceval1 FP (S q) nv fe (cmp_sub_left _ _ _ _ Hrest) ltac:(lia) Hq) as (f1 & Q1 & R1).
    pose proof (cmp_sub_right (cmp_fc s (S q)) _ (S q) (q + 1 + cmp_flen s) _ ltac:(rewrite cmp_fc_length; lia) Hrest) as Hj.
    destruct (IHcmp_ceval2 FP q nv f1 Hsub ltac:(cbn [cmp_svmax]; lia) Q1) as (f2 & Q2 & R2).
    exists f2. split; [exact Q2 |].
    eapply cmp_step_then; [exact Hi | apply FSJfT; [unfold cmp_fi_ok, cmp_fi_max; apply Nat.leb_le; lia | rewrite <- (cmp_beval_eqv b e fe Hq); exact H] |].
    replace (S q + cmp_flen s) with (q + 1 + cmp_flen s) in R1 by lia.
    eapply sss_compute_trans; [exact R1 |].
    eapply cmp_step_then; [exact Hj | apply FSJmp |].
    exact R2.
  - exfalso. destruct p; discriminate H.
Qed.

(* ================================================================= *)
(* Backward.                                                          *)
(* ================================================================= *)

Lemma cmp_one_step : forall nv (i : cmp_fi) q P e st2,
  (q, [i]) <sc P -> cmp_fstep nv i (q, e) st2 -> fsteps nv P 1 (q, e) st2.
Proof.
  intros nv i q P e st2 Hsc Hs. apply sss_steps_1.
  eapply subcode_sss_step with (P := (q, [i])); [exact Hsc |].
  apply in_sss_step with (l := []); [simpl; lia | exact Hs].
Qed.

Lemma cmp_first_step : forall nv (i : cmp_fi) q P e k st',
  (q, [i]) <sc P -> fsteps nv P (S k) (q, e) st' ->
  exists st2, cmp_fstep nv i (q, e) st2 /\ fsteps nv P k st2 st'.
Proof.
  intros nv i q P e k st' Hsc H.
  destruct (sss_steps_S_inv' H) as (st2 & H1 & H2). exists st2. split; [| exact H2].
  eapply subcode_sss_step_inv_1 with (st1 := (q, e)); [exact Hsc | exact H1].
Qed.

(* The same step, seen from the stepping relation: determinism. *)
Lemma cmp_steps_fun : forall nv P k s t1 t2,
  fsteps nv P k s t1 -> fsteps nv P k s t2 -> t1 = t2.
Proof. intros. eapply sss_steps_fun; [apply cmp_fstep_fun | eassumption | eassumption]. Qed.

Ltac jmp_nop := match goal with H : cmp_fi_ok _ (FJmp _) = false |- _ => rewrite cmp_fi_ok_jmp in H; discriminate end.

Theorem cmp_fc_bwd : forall s, cmp_nocall s ->
  forall FP q nv fe k j fe', (q, cmp_fc s q) <sc FP -> cmp_svmax s <= nv ->
  fsteps nv FP k (q, fe) (j, fe') -> (j < q \/ q + cmp_flen s <= j) ->
  exists e1 c k1 fe1, cmp_ceval [] fe s e1 c /\ cmp_eqv e1 fe1 /\ k1 <= k /\
    fsteps nv FP k1 (q, fe) (q + cmp_flen s, fe1) /\
    fsteps nv FP (k - k1) (q + cmp_flen s, fe1) (j, fe').
Proof.
  induction s as [| x e | s1 IH1 s2 IH2 | b s1 IH1 s2 IH2 | b s IHs | ds p args];
    intros Hnc FP q nv fe k j fe' Hsub Hsv Hrun Hout.
  - (* skip *)
    exists fe, 0, 0, fe. split; [constructor |]. split; [apply cmp_eqv_refl |]. split; [lia |]. split.
    + replace (q + cmp_flen SSkip) with q by (cbn; lia). constructor.
    + replace (q + cmp_flen SSkip) with q by (cbn; lia). rewrite Nat.sub_0_r. exact Hrun.
  - (* assignment *)
    cbn [cmp_svmax cmp_fc cmp_flen] in *.
    destruct k as [| k]; [apply sss_steps_0_inv in Hrun; inversion Hrun; lia |].
    destruct (cmp_first_step _ _ _ _ _ _ _ Hsub Hrun) as (st2 & Hs & Hr2).
    inversion Hs; subst.
    + unfold cmp_fi_ok, cmp_fi_max in H3. apply Nat.leb_nle in H3. lia.
    + exists (cmp_upd fe x (cmp_aeval fe e)), 1, 1, (cmp_upd fe x (cmp_aeval fe e)).
      split; [constructor |]. split; [apply cmp_eqv_refl |]. split; [lia |]. split.
      * replace (q + 1) with (S q) by lia. eapply cmp_one_step; [exact Hsub | exact Hs].
      * replace (q + 1) with (S q) by lia. replace (S k - 1) with k by lia. exact Hr2.
  - (* sequence *)
    destruct Hnc as [Hn1 Hn2]. cbn [cmp_svmax cmp_fc cmp_flen] in *.
    assert (Hout1 : j < q \/ q + cmp_flen s1 <= j) by lia.
    destruct (IH1 Hn1 FP q nv fe k j fe' (cmp_sub_left _ _ _ _ Hsub) ltac:(lia) Hrun Hout1)
      as (e1 & c1 & k1 & f1 & D1 & Q1 & K1 & R1 & R1').
    destruct (IH2 Hn2 FP (q + cmp_flen s1) nv f1 (k - k1) j fe'
                (cmp_sub_right _ _ _ _ _ ltac:(rewrite cmp_fc_length; reflexivity) Hsub) ltac:(lia) R1' ltac:(lia))
      as (e2 & c2 & k2 & f2 & D2 & Q2 & K2 & R2 & R2').
    destruct (cmp_ceval_ext _ _ _ _ _ D2 e1 (cmp_eqv_sym _ _ Q1)) as (e3 & Q3 & D3).
    exists e3, (c1 + c2), (k1 + k2), f2. split; [econstructor; eassumption |].
    split; [apply cmp_eqv_trans with e2; [apply cmp_eqv_sym; exact Q3 | exact Q2] |]. split; [lia |]. split.
    + replace (q + (cmp_flen s1 + cmp_flen s2)) with (q + cmp_flen s1 + cmp_flen s2) by lia.
      eapply sss_steps_trans; eassumption.
    + replace (q + (cmp_flen s1 + cmp_flen s2)) with (q + cmp_flen s1 + cmp_flen s2) by lia.
      replace (k - (k1 + k2)) with (k - k1 - k2) by lia. exact R2'.
  - (* conditional *)
    destruct Hnc as [Hn1 Hn2]. cbn [cmp_svmax cmp_fc cmp_flen] in *.
    destruct (cmp_instr_sub _ _ _ _ Hsub) as [Hi Hrest].
    destruct k as [| k]; [apply sss_steps_0_inv in Hrun; inversion Hrun; lia |].
    destruct (cmp_first_step _ _ _ _ _ _ _ Hi Hrun) as (st2 & Hs & Hr2).
    inversion Hs; subst.
    + unfold cmp_fi_ok, cmp_fi_max in H3. apply Nat.leb_nle in H3. lia.
    + (* then branch *)
      assert (Hj : (q + 1 + cmp_flen s1, [FJmp (q + 1 + cmp_flen s1 + 1 + cmp_flen s2)]) <sc FP).
      { destruct (cmp_instr_sub _ _ _ _ (cmp_sub_right (cmp_fc s1 (S q)) _ (S q) (q + 1 + cmp_flen s1) _
                  ltac:(rewrite cmp_fc_length; lia) Hrest)) as [Hj' _]. exact Hj'. }
      destruct (IH1 Hn1 FP (S q) nv fe k j fe' (cmp_sub_left _ _ _ _ Hrest) ltac:(lia) Hr2 ltac:(lia))
        as (e1 & c1 & k1 & f1 & D1 & Q1 & K1 & R1 & R1').
      replace (S q + cmp_flen s1) with (q + 1 + cmp_flen s1) in R1, R1' by lia.
      destruct (k - k1) as [| m] eqn:Em; [apply sss_steps_0_inv in R1'; inversion R1'; lia |].
      destruct (cmp_first_step _ _ _ _ _ _ _ Hj R1') as (st3 & Hs3 & Hr3).
      inversion Hs3; subst.
      * jmp_nop.
      * assert (Rfull : fsteps nv FP (1 + (k1 + 1)) (q, fe) (q + 1 + cmp_flen s1 + 1 + cmp_flen s2, f1)).
        { eapply sss_steps_trans with (n := 1) (m := k1 + 1); [eapply cmp_one_step; [exact Hi | exact Hs] |].
          eapply sss_steps_trans with (n := k1) (m := 1); [exact R1 |].
          eapply cmp_one_step; [exact Hj | constructor]. }
        exists e1, (S c1), (1 + (k1 + 1)), f1. split; [apply CEIfT; assumption |].
        split; [exact Q1 |]. split; [lia |].
        replace (q + (1 + cmp_flen s1 + 1 + cmp_flen s2)) with (q + 1 + cmp_flen s1 + 1 + cmp_flen s2) by lia.
        split; [exact Rfull |].
        replace (S k - (1 + (k1 + 1))) with m by lia. exact Hr3.
    + (* else branch *)
      assert (Hsub2 : (q + 1 + cmp_flen s1 + 1, cmp_fc s2 (q + 1 + cmp_flen s1 + 1)) <sc FP).
      { apply cmp_sub_right with (l := cmp_fc s1 (S q) ++ [FJmp (q + 1 + cmp_flen s1 + 1 + cmp_flen s2)]) (a := S q).
        - rewrite app_length, cmp_fc_length. simpl. lia.
        - rewrite <- app_assoc. exact Hrest. }
      destruct (IH2 Hn2 FP (q + 1 + cmp_flen s1 + 1) nv fe k j fe' Hsub2 ltac:(lia) Hr2 ltac:(lia))
        as (e1 & c1 & k1 & f1 & D1 & Q1 & K1 & R1 & R1').
      exists e1, (S c1), (1 + k1), f1. split; [apply CEIfF; assumption |].
      split; [exact Q1 |]. split; [lia |].
      replace (q + (1 + cmp_flen s1 + 1 + cmp_flen s2)) with (q + 1 + cmp_flen s1 + 1 + cmp_flen s2) by lia.
      split.
      * eapply sss_steps_trans with (n := 1) (m := k1); [eapply cmp_one_step; [exact Hi | exact Hs] | exact R1].
      * replace (S k - (1 + k1)) with (k - k1) by lia. exact R1'.
  - (* while *)
    cbn [cmp_nocall] in Hnc. cbn [cmp_svmax cmp_fc cmp_flen] in Hsv, Hsub, Hout |- *.
    destruct (cmp_instr_sub _ _ _ _ Hsub) as [Hi Hrest].
    assert (Hj : (q + 1 + cmp_flen s, [FJmp q]) <sc FP).
    { pose proof (cmp_sub_right (cmp_fc s (S q)) _ (S q) (q + 1 + cmp_flen s) _
                    ltac:(rewrite cmp_fc_length; lia) Hrest) as Hj'. exact Hj'. }
    revert fe j fe' Hrun Hout. induction k as [k IHk] using lt_wf_ind. intros fe j fe' Hrun Hout.
    destruct k as [| k]; [apply sss_steps_0_inv in Hrun; inversion Hrun; lia |].
    destruct (cmp_first_step _ _ _ _ _ _ _ Hi Hrun) as (st2 & Hs & Hr2).
    inversion Hs; subst.
    + unfold cmp_fi_ok, cmp_fi_max in H3. apply Nat.leb_nle in H3. lia.
    + (* the test holds: one round *)
      destruct (IHs Hnc FP (S q) nv fe k j fe' (cmp_sub_left _ _ _ _ Hrest) ltac:(lia) Hr2 ltac:(lia))
        as (e1 & c1 & k1 & f1 & D1 & Q1 & K1 & R1 & R1').
      replace (S q + cmp_flen s) with (q + 1 + cmp_flen s) in R1, R1' by lia.
      destruct (k - k1) as [| m] eqn:Em; [apply sss_steps_0_inv in R1'; inversion R1'; lia |].
      destruct (cmp_first_step _ _ _ _ _ _ _ Hj R1') as (st3 & Hs3 & Hr3).
      inversion Hs3; subst; [jmp_nop |].
      destruct (IHk m ltac:(lia) f1 j fe' Hr3 Hout) as (e2 & c2 & k2 & f2 & D2 & Q2 & K2 & R2 & R2').
      destruct (cmp_ceval_ext _ _ _ _ _ D2 e1 (cmp_eqv_sym _ _ Q1)) as (e3 & Q3 & D3).
      exists e3, (S (c1 + c2)), (1 + (k1 + (1 + k2))), f2.
      split; [apply CEWhileT with (e1 := e1); assumption |].
      split; [apply cmp_eqv_trans with e2; [apply cmp_eqv_sym; exact Q3 | exact Q2] |]. split; [lia |]. split.
      * eapply sss_steps_trans with (n := 1) (m := k1 + (1 + k2)); [eapply cmp_one_step; [exact Hi | exact Hs] |].
        eapply sss_steps_trans with (n := k1) (m := 1 + k2); [exact R1 |].
        eapply sss_steps_trans with (n := 1) (m := k2); [eapply cmp_one_step; [exact Hj | constructor] | exact R2].
      * replace (S k - (1 + (k1 + (1 + k2)))) with (m - k2) by lia. exact R2'.
    + (* the test fails: done *)
      exists fe, 1, 1, fe. split; [apply CEWhileF; assumption |]. split; [apply cmp_eqv_refl |]. split; [lia |].
      replace (q + (1 + cmp_flen s + 1)) with (q + 1 + cmp_flen s + 1) by lia. split.
      * eapply cmp_one_step; [exact Hi | exact Hs].
      * replace (S k - 1) with k by lia. exact Hr2.
  - exfalso. exact Hnc.
Qed.

Print Assumptions cmp_fc_fwd.
Print Assumptions cmp_fc_bwd.
