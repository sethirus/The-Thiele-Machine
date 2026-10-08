(** CmpExpr.v: counter-machine code for arithmetic and boolean expressions.

    Variable x of the source is register x + 1; register 0 stays 0 for the
    whole run. cmp_cexp t e a is the code, placed at address a, that leaves
    the value of e in register t and every register above t at 0 again,
    using only registers t and above as working space. Variables must lie
    below t (cmp_avmax e < t, since the register of variable x is x + 1) and
    registers t and above must be 0 when the code starts.

      CNum n      n times INC t
      CVar x      a copy of register x + 1 into t, through register t + 1
      CAdd a b    a into t, b into t + 1, then t := t + (t + 1)
      CSub a b    a into t, b into t + 1, then t := t - (t + 1), truncated

    cmp_cb t b a lt lf is the code at address a that goes to address lt when
    b is true and to address lf when b is false, with every register as it
    was at the start. Comparisons evaluate both sides into t and t + 1 and
    compare destructively, clearing both registers afterwards.

      cmp_cexp_spec  the registers end as before except register t, which
                     holds the value of e under the variable values read
                     from registers 1, 2, ...
      cmp_cb_spec    the run ends at lt or lf according to the value of b,
                     with all registers unchanged
      cmp_alen, cmp_blen   the lengths, which do not depend on a, t, lt, lf

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, CmpLang.v and CmpBlocks.v. No axioms and no unfinished proofs.            *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is one stage of the verified compiler pipeline of CmpPipeline.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library, CmpLang.v and CmpBlocks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Import Kernel.CmpLang Kernel.CmpBlocks Kernel.CmpInline.

(* ================================================================= *)
(* Arithmetic.                                                        *)
(* ================================================================= *)

Fixpoint cmp_alen (e : cmp_aexp) : nat :=
  match e with
  | CNum n => n
  | CVar _ => 7
  | CAdd a b => cmp_alen a + cmp_alen b + 3
  | CSub a b => cmp_alen a + cmp_alen b + 3
  end.

Fixpoint cmp_cexp (t : nat) (e : cmp_aexp) (a : nat) : list cmp_mi :=
  match e with
  | CNum n => repeat (mm_inc t) n
  | CVar x => cmp_copy a (S x) t (S t)
  | CAdd e1 e2 =>
      cmp_cexp t e1 a ++ cmp_cexp (S t) e2 (a + cmp_alen e1) ++
      cmp_addmv (a + cmp_alen e1 + cmp_alen e2) (S t) t
  | CSub e1 e2 =>
      cmp_cexp t e1 a ++ cmp_cexp (S t) e2 (a + cmp_alen e1) ++
      cmp_sub (a + cmp_alen e1 + cmp_alen e2) t (S t)
  end.

Lemma cmp_cexp_len : forall e t a, length (cmp_cexp t e a) = cmp_alen e.
Proof.
  induction e as [n | x | e1 IH1 e2 IH2 | e1 IH1 e2 IH2]; intros t a; simpl.
  - apply repeat_length.
  - reflexivity.
  - rewrite !app_length, IH1, IH2. simpl. lia.
  - rewrite !app_length, IH1, IH2. simpl. lia.
Qed.

Lemma cmp_blk_incs : forall n P a t m, (a, repeat (mm_inc t) n) <sc P ->
  cmp_reach0 P a m (a + n) (cmp_upd m t (m t + n)).
Proof.
  induction n as [| n IH]; intros P a t m Hs.
  - eapply cmp_reach0_at; [eapply cmp_reach0_refl; intros y; unfold cmp_upd; destruct (Nat.eqb_spec y t); [subst; lia | reflexivity] | lia].
  - apply subcode_cons_invert_left in Hs. destruct Hs as [H1 H2].
    eapply cmp_reach0_trans.
    + apply cmp_reach_reach0. apply cmp_stp_inc with (x := t) (w := cmp_upd m t (S (m t))); [exact H1 |]. intros y. reflexivity.
    + eapply cmp_reach0_at.
      * eapply cmp_reach0_eq; [apply (IH P (S a) t (cmp_upd m t (S (m t))) H2) |].
        intros y. unfold cmp_upd. destruct (Nat.eqb y t); [rewrite Nat.eqb_refl; lia | reflexivity].
      * lia.
Qed.

Lemma cmp_cexp_spec : forall e t a P m, (a, cmp_cexp t e a) <sc P -> cmp_avmax e < t ->
  m 0 = 0 -> (forall r, t <= r -> m r = 0) ->
  cmp_reach0 P a m (a + cmp_alen e) (cmp_upd m t (cmp_aeval (fun x => m (S x)) e)).
Proof.
  induction e as [n | x | e1 IH1 e2 IH2 | e1 IH1 e2 IH2]; intros t a P m Hs Hv H0 Hz.
  - simpl in *. eapply cmp_reach0_eq; [apply cmp_blk_incs; exact Hs |].
    intros y. unfold cmp_upd. rewrite (Hz t) by lia. reflexivity.
  - simpl in Hs, Hv. eapply cmp_reach0_eq.
    + apply cmp_reach_reach0. exact (cmp_blk_copy P a (S x) t (S t) m Hs ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               H0 (Hz (S t) ltac:(lia))).
    + intros y. simpl. unfold cmp_upd. rewrite (Hz t) by lia. reflexivity.
  - simpl in Hs, Hv.
    assert (s1 : (a, cmp_cexp t e1 a) <sc P).
    { apply cmp_sc_l with (r := cmp_cexp (S t) e2 (a + cmp_alen e1) ++ cmp_addmv (a + cmp_alen e1 + cmp_alen e2) (S t) t). exact Hs. }
    assert (s2 : (a + cmp_alen e1, cmp_cexp (S t) e2 (a + cmp_alen e1)) <sc P).
    { apply cmp_sc_l with (r := cmp_addmv (a + cmp_alen e1 + cmp_alen e2) (S t) t).
      apply cmp_sc_r with (l := cmp_cexp t e1 a) (a := a); [rewrite cmp_cexp_len; reflexivity | exact Hs]. }
    assert (s3 : (a + cmp_alen e1 + cmp_alen e2, cmp_addmv (a + cmp_alen e1 + cmp_alen e2) (S t) t) <sc P).
    { apply cmp_sc_r with (l := cmp_cexp t e1 a ++ cmp_cexp (S t) e2 (a + cmp_alen e1)) (a := a);
        [rewrite app_length, !cmp_cexp_len; lia |]. rewrite <- app_assoc. exact Hs. }
    set (v1 := cmp_aeval (fun x => m (S x)) e1).
    set (v2 := cmp_aeval (fun x => m (S x)) e2).
    set (m1 := cmp_upd m t v1).
    assert (E10 : m1 0 = 0) by (unfold m1; rewrite cmp_upd_other by lia; exact H0).
    assert (E1z : forall r, S t <= r -> m1 r = 0) by (intros r Hr; unfold m1; rewrite cmp_upd_other by lia; apply Hz; lia).
    assert (Ev2 : cmp_aeval (fun x => m1 (S x)) e2 = v2).
    { unfold v2. apply cmp_aeval_below. intros r Hr. unfold m1. rewrite cmp_upd_other by lia. reflexivity. }
    set (m2 := cmp_upd m1 (S t) v2).
    eapply cmp_reach0_trans; [apply (IH1 t a P m s1 ltac:(lia) H0 Hz) |].
    eapply cmp_reach0_trans.
    + eapply cmp_reach0_eq; [apply (IH2 (S t) (a + cmp_alen e1) P m1 s2 ltac:(lia) E10 E1z) |].
      intros y. fold m1. rewrite Ev2. reflexivity.
    + assert (E20 : m2 0 = 0) by (unfold m2, m1; rewrite !cmp_upd_other by lia; exact H0).
      eapply cmp_reach0_at.
      * eapply cmp_reach0_eq; [apply cmp_reach_reach0; apply (cmp_blk_addmv P (a + cmp_alen e1 + cmp_alen e2) (S t) t m2 s3 ltac:(lia) ltac:(lia) ltac:(lia) E20) |].
        intros y. unfold m2, m1, cmp_upd.
        assert (Hzt : m (S t) = 0) by (apply Hz; lia).
        eqb_all.
      * cbn [cmp_alen]; lia.
  - simpl in Hs, Hv.
    assert (s1 : (a, cmp_cexp t e1 a) <sc P).
    { apply cmp_sc_l with (r := cmp_cexp (S t) e2 (a + cmp_alen e1) ++ cmp_sub (a + cmp_alen e1 + cmp_alen e2) t (S t)). exact Hs. }
    assert (s2 : (a + cmp_alen e1, cmp_cexp (S t) e2 (a + cmp_alen e1)) <sc P).
    { apply cmp_sc_l with (r := cmp_sub (a + cmp_alen e1 + cmp_alen e2) t (S t)).
      apply cmp_sc_r with (l := cmp_cexp t e1 a) (a := a); [rewrite cmp_cexp_len; reflexivity | exact Hs]. }
    assert (s3 : (a + cmp_alen e1 + cmp_alen e2, cmp_sub (a + cmp_alen e1 + cmp_alen e2) t (S t)) <sc P).
    { apply cmp_sc_r with (l := cmp_cexp t e1 a ++ cmp_cexp (S t) e2 (a + cmp_alen e1)) (a := a);
        [rewrite app_length, !cmp_cexp_len; lia |]. rewrite <- app_assoc. exact Hs. }
    set (v1 := cmp_aeval (fun x => m (S x)) e1).
    set (v2 := cmp_aeval (fun x => m (S x)) e2).
    set (m1 := cmp_upd m t v1).
    assert (E10 : m1 0 = 0) by (unfold m1; rewrite cmp_upd_other by lia; exact H0).
    assert (E1z : forall r, S t <= r -> m1 r = 0) by (intros r Hr; unfold m1; rewrite cmp_upd_other by lia; apply Hz; lia).
    assert (Ev2 : cmp_aeval (fun x => m1 (S x)) e2 = v2).
    { unfold v2. apply cmp_aeval_below. intros r Hr. unfold m1. rewrite cmp_upd_other by lia. reflexivity. }
    set (m2 := cmp_upd m1 (S t) v2).
    eapply cmp_reach0_trans; [apply (IH1 t a P m s1 ltac:(lia) H0 Hz) |].
    eapply cmp_reach0_trans.
    + eapply cmp_reach0_eq; [apply (IH2 (S t) (a + cmp_alen e1) P m1 s2 ltac:(lia) E10 E1z) |].
      intros y. fold m1. rewrite Ev2. reflexivity.
    + assert (E20 : m2 0 = 0) by (unfold m2, m1; rewrite !cmp_upd_other by lia; exact H0).
      eapply cmp_reach0_at.
      * eapply cmp_reach0_eq; [apply cmp_reach_reach0; apply (cmp_blk_sub P (a + cmp_alen e1 + cmp_alen e2) t (S t) m2 s3 ltac:(lia) ltac:(lia) ltac:(lia) E20) |].
        intros y. unfold m2, m1, cmp_upd.
        assert (Hzt : m (S t) = 0) by (apply Hz; lia).
        eqb_all.
      * cbn [cmp_alen]; lia.
Qed.

(* ================================================================= *)
(* Conditions.                                                        *)
(* ================================================================= *)

Fixpoint cmp_blen (b : cmp_bexp) : nat :=
  match b with
  | BTrue | BFalse => 1
  | BEq x y | BLt x y => cmp_alen x + cmp_alen y + 14
  | BNot c => cmp_blen c
  | BAnd c d | BOr c d => cmp_blen c + cmp_blen d
  end.

Fixpoint cmp_cb (t : nat) (b : cmp_bexp) (a lt lf : nat) : list cmp_mi :=
  match b with
  | BTrue => [mm_dec 0 lt]
  | BFalse => [mm_dec 0 lf]
  | BEq x y =>
      cmp_cexp t x a ++ cmp_cexp (S t) y (a + cmp_alen x) ++ cmp_eqblk (a + cmp_alen x + cmp_alen y) t (S t) lt lf
  | BLt x y =>
      cmp_cexp t x a ++ cmp_cexp (S t) y (a + cmp_alen x) ++ cmp_ltblk (a + cmp_alen x + cmp_alen y) t (S t) lt lf
  | BNot c => cmp_cb t c a lf lt
  | BAnd c d => cmp_cb t c a (a + cmp_blen c) lf ++ cmp_cb t d (a + cmp_blen c) lt lf
  | BOr c d => cmp_cb t c a lt (a + cmp_blen c) ++ cmp_cb t d (a + cmp_blen c) lt lf
  end.

Lemma cmp_cb_len : forall b t a lt lf, length (cmp_cb t b a lt lf) = cmp_blen b.
Proof.
  induction b as [| | x y | x y | c IH | c IHc d IHd | c IHc d IHd]; intros t a lt lf; simpl; auto.
  - rewrite !app_length, !cmp_cexp_len. simpl. lia.
  - rewrite !app_length, !cmp_cexp_len. simpl. lia.
  - rewrite app_length, IHc, IHd. reflexivity.
  - rewrite app_length, IHc, IHd. reflexivity.
Qed.

(* A comparison: both sides into t and t + 1, then the destructive test. *)
Lemma cmp_cmp_spec : forall (blk : nat -> nat -> nat -> nat -> nat -> list cmp_mi) (test : nat -> nat -> bool)
  (x y : cmp_aexp) t a lt lf P m,
  (forall a t u lt lf P m, (a, blk a t u lt lf) <sc P -> t <> 0 -> u <> 0 -> t <> u -> m 0 = 0 ->
     cmp_reach P a m (if test (m t) (m u) then lt else lf) (cmp_upd (cmp_upd m u 0) t 0)) ->
  (forall a t u lt lf, length (blk a t u lt lf) = 14) ->
  (a, cmp_cexp t x a ++ cmp_cexp (S t) y (a + cmp_alen x) ++ blk (a + cmp_alen x + cmp_alen y) t (S t) lt lf) <sc P ->
  cmp_avmax x < t -> cmp_avmax y < t -> m 0 = 0 -> (forall r, t <= r -> m r = 0) ->
  cmp_reach P a m (if test (cmp_aeval (fun z => m (S z)) x) (cmp_aeval (fun z => m (S z)) y) then lt else lf) m.
Proof.
  intros blk test x y t a lt lf P m Hblk Hlen Hs Hx Hy H0 Hz.
  assert (s1 : (a, cmp_cexp t x a) <sc P).
  { apply cmp_sc_l with (r := cmp_cexp (S t) y (a + cmp_alen x) ++ blk (a + cmp_alen x + cmp_alen y) t (S t) lt lf). exact Hs. }
  assert (s2 : (a + cmp_alen x, cmp_cexp (S t) y (a + cmp_alen x)) <sc P).
  { apply cmp_sc_l with (r := blk (a + cmp_alen x + cmp_alen y) t (S t) lt lf).
    apply cmp_sc_r with (l := cmp_cexp t x a) (a := a); [rewrite cmp_cexp_len; reflexivity | exact Hs]. }
  assert (s3 : (a + cmp_alen x + cmp_alen y, blk (a + cmp_alen x + cmp_alen y) t (S t) lt lf) <sc P).
  { apply cmp_sc_r with (l := cmp_cexp t x a ++ cmp_cexp (S t) y (a + cmp_alen x)) (a := a);
      [rewrite app_length, !cmp_cexp_len; lia |]. rewrite <- app_assoc. exact Hs. }
  set (vx := cmp_aeval (fun z => m (S z)) x).
  set (vy := cmp_aeval (fun z => m (S z)) y).
  set (m1 := cmp_upd m t vx).
  assert (E10 : m1 0 = 0) by (unfold m1; rewrite cmp_upd_other by lia; exact H0).
  assert (E1z : forall r, S t <= r -> m1 r = 0) by (intros r Hr; unfold m1; rewrite cmp_upd_other by lia; apply Hz; lia).
  assert (Ev : cmp_aeval (fun z => m1 (S z)) y = vy).
  { unfold vy. apply cmp_aeval_below. intros r Hr. unfold m1. rewrite cmp_upd_other by lia. reflexivity. }
  set (m2 := cmp_upd m1 (S t) vy).
  assert (E20 : m2 0 = 0) by (unfold m2, m1; rewrite !cmp_upd_other by lia; exact H0).
  assert (Et2 : m2 t = vx) by (unfold m2, m1; rewrite cmp_upd_other by lia; apply cmp_upd_same).
  assert (Eu2 : m2 (S t) = vy) by (unfold m2; apply cmp_upd_same).
  eapply cmp_reach0_trans_reach; [apply (cmp_cexp_spec x t a P m s1 Hx H0 Hz) |].
  eapply cmp_reach0_trans_reach.
  - eapply cmp_reach0_eq; [apply (cmp_cexp_spec y (S t) (a + cmp_alen x) P m1 s2 ltac:(lia) E10 E1z) |].
    intros z. fold m1. rewrite Ev. reflexivity.
  - replace (test vx vy) with (test (m2 t) (m2 (S t))) by (rewrite Et2, Eu2; reflexivity).
    eapply cmp_reach_eq.
    + apply (Hblk _ _ _ _ _ P m2 s3 ltac:(lia) ltac:(lia) ltac:(lia) E20).
    + intros z. unfold m2, m1, cmp_upd.
      assert (Hzt : m t = 0) by (apply Hz; lia).
      assert (Hzs : m (S t) = 0) by (apply Hz; lia).
      eqb_all.
Qed.

Lemma cmp_cb_spec : forall b t a lt lf P m, (a, cmp_cb t b a lt lf) <sc P -> cmp_bvmax b < t ->
  m 0 = 0 -> (forall r, t <= r -> m r = 0) ->
  cmp_reach P a m (if cmp_beval (fun x => m (S x)) b then lt else lf) m.
Proof.
  induction b as [| | x y | x y | c IH | c IHc d IHd | c IHc d IHd]; intros t a lt lf P m Hs Hv H0 Hz.
  - cbn [cmp_cb] in Hs. cbn [cmp_beval]. apply cmp_stp_dec0 with (x := 0); [cmp_ins Hs 0 | exact H0].
  - cbn [cmp_cb] in Hs. cbn [cmp_beval]. apply cmp_stp_dec0 with (x := 0); [cmp_ins Hs 0 | exact H0].
  - simpl in Hs, Hv. eapply cmp_cmp_spec with (blk := cmp_eqblk) (test := Nat.eqb) (t := t); try assumption; try lia.
    + intros. apply cmp_blk_eq; assumption.
    + intros. reflexivity.
  - simpl in Hs, Hv. eapply cmp_cmp_spec with (blk := cmp_ltblk) (test := Nat.ltb) (t := t); try assumption; try lia.
    + intros. apply cmp_blk_lt; assumption.
    + intros. reflexivity.
  - cbn [cmp_cb] in Hs. cbn [cmp_bvmax] in Hv. eapply cmp_reach_at; [apply (IH t a lf lt P m Hs Hv H0 Hz) |].
    cbn [cmp_beval]. destruct (cmp_beval (fun x => m (S x)) c); reflexivity.
  - simpl in Hs, Hv.
    assert (s1 : (a, cmp_cb t c a (a + cmp_blen c) lf) <sc P).
    { apply cmp_sc_l with (r := cmp_cb t d (a + cmp_blen c) lt lf). exact Hs. }
    assert (s2 : (a + cmp_blen c, cmp_cb t d (a + cmp_blen c) lt lf) <sc P).
    { apply cmp_sc_r with (l := cmp_cb t c a (a + cmp_blen c) lf) (a := a); [rewrite cmp_cb_len; reflexivity | exact Hs]. }
    pose proof (IHc t a (a + cmp_blen c) lf P m s1 ltac:(lia) H0 Hz) as R1.
    pose proof (IHd t (a + cmp_blen c) lt lf P m s2 ltac:(lia) H0 Hz) as R2.
    destruct (cmp_beval (fun x => m (S x)) c) eqn:Ec.
    + simpl. rewrite Ec in *. simpl in *. eapply cmp_reach_trans; [exact R1 | exact R2].
    + simpl. rewrite Ec in *. simpl in *. exact R1.
  - simpl in Hs, Hv.
    assert (s1 : (a, cmp_cb t c a lt (a + cmp_blen c)) <sc P).
    { apply cmp_sc_l with (r := cmp_cb t d (a + cmp_blen c) lt lf). exact Hs. }
    assert (s2 : (a + cmp_blen c, cmp_cb t d (a + cmp_blen c) lt lf) <sc P).
    { apply cmp_sc_r with (l := cmp_cb t c a lt (a + cmp_blen c)) (a := a); [rewrite cmp_cb_len; reflexivity | exact Hs]. }
    pose proof (IHc t a lt (a + cmp_blen c) P m s1 ltac:(lia) H0 Hz) as R1.
    pose proof (IHd t (a + cmp_blen c) lt lf P m s2 ltac:(lia) H0 Hz) as R2.
    destruct (cmp_beval (fun x => m (S x)) c) eqn:Ec.
    + simpl. rewrite Ec in *. simpl in *. exact R1.
    + simpl. rewrite Ec in *. simpl in *. eapply cmp_reach_trans; [exact R1 | exact R2].
Qed.
