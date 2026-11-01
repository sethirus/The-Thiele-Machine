(** CmpLang.v: a small readable source language, its formal semantics and a
    fuel-based interpreter proved to agree with the semantics.

    The language has natural-number variables (numbered), assignment,
    addition, truncated subtraction, comparison, conditionals, while loops
    and procedures. A procedure has a number of parameters, a body and a list
    of result expressions; a call passes argument expressions, runs the body
    in a fresh frame (parameters first, every other local 0) and assigns the
    results to variables of the caller. Procedures may call procedures with
    other numbers; the compiler of CmpFlat.v accepts exactly the programs in
    which a procedure only calls procedures of smaller number (no recursion).
    The semantics itself does not need that restriction.

    The semantics is a big-step relation cmp_ceval ps e s e1 c: statement s,
    run from the variable assignment e, ends in e1 after c primitive
    operations. Every assignment, every test of a condition (a loop test
    counts each time it is made) and every call counts one. A statement that
    does not terminate has no derivation.

    The interpreter cmp_interp keeps the variables in a list (a lookup is
    nth, an update replaces one cell) so that long runs are cheap when it is
    extracted. It takes a fuel that bounds the nesting of calls and the
    number of loop rounds, and accumulates the operation count in its last
    argument.

      cmp_interp_sound      a result of the interpreter has a derivation
                            with the same final variables and the same count
      cmp_interp_complete   a derivation is found by the interpreter once
                            the fuel is large enough, and stays found
      cmp_ceval_det         the semantics is deterministic (up to the value
                            of every variable)

    Dependencies: Coq standard library only. No axioms and no unfinished proofs.        *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is the source language of the verified compiler pipeline of
   CmpPipeline.v and imports only the Coq standard library. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.

(* ================================================================= *)
(* Syntax.                                                            *)
(* ================================================================= *)

Inductive cmp_aexp : Set :=
| CNum (n : nat)
| CVar (x : nat)
| CAdd (a b : cmp_aexp)
| CSub (a b : cmp_aexp).          (* truncated: a - b = 0 when b >= a *)

Inductive cmp_bexp : Set :=
| BTrue
| BFalse
| BEq (a b : cmp_aexp)
| BLt (a b : cmp_aexp)
| BNot (b : cmp_bexp)
| BAnd (b c : cmp_bexp)
| BOr (b c : cmp_bexp).

Inductive cmp_stmt : Set :=
| SSkip
| SAssign (x : nat) (a : cmp_aexp)
| SSeq (s t : cmp_stmt)
| SIf (b : cmp_bexp) (s t : cmp_stmt)
| SWhile (b : cmp_bexp) (s : cmp_stmt)
| SCall (dsts : list nat) (p : nat) (args : list cmp_aexp).

Record cmp_proc : Set := mk_cmp_proc {
  pr_np : nat;                       (* number of parameters (locals 0 .. np-1) *)
  pr_body : cmp_stmt;
  pr_rets : list cmp_aexp            (* result expressions, read in the callee frame *)
}.

Record cmp_prog : Set := mk_cmp_prog {
  cp_procs : list cmp_proc;
  cp_main : cmp_stmt
}.

(* Sugar. *)
Definition BLe (a b : cmp_aexp) : cmp_bexp := BNot (BLt b a).
Definition BNe (a b : cmp_aexp) : cmp_bexp := BNot (BEq a b).

(* ================================================================= *)
(* Values.                                                            *)
(* ================================================================= *)

Definition cmp_env : Type := nat -> nat.

Definition cmp_eqv (e f : cmp_env) : Prop := forall x, e x = f x.

Definition cmp_upd (e : cmp_env) (x v : nat) : cmp_env :=
  fun y => if Nat.eqb y x then v else e y.

Fixpoint cmp_aeval (e : cmp_env) (a : cmp_aexp) : nat :=
  match a with
  | CNum n => n
  | CVar x => e x
  | CAdd a b => cmp_aeval e a + cmp_aeval e b
  | CSub a b => cmp_aeval e a - cmp_aeval e b
  end.

Fixpoint cmp_beval (e : cmp_env) (b : cmp_bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a c => Nat.eqb (cmp_aeval e a) (cmp_aeval e c)
  | BLt a c => Nat.ltb (cmp_aeval e a) (cmp_aeval e c)
  | BNot b => negb (cmp_beval e b)
  | BAnd b c => cmp_beval e b && cmp_beval e c
  | BOr b c => cmp_beval e b || cmp_beval e c
  end.

Lemma cmp_upd_same : forall e x v, cmp_upd e x v x = v.
Proof. intros. unfold cmp_upd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma cmp_upd_other : forall e x y v, y <> x -> cmp_upd e x v y = e y.
Proof.
  intros. unfold cmp_upd. destruct (Nat.eqb_spec y x); [contradiction | reflexivity].
Qed.

Lemma cmp_eqv_refl : forall e, cmp_eqv e e. Proof. intros e x. reflexivity. Qed.
Lemma cmp_eqv_sym : forall e f, cmp_eqv e f -> cmp_eqv f e.
Proof. intros e f H x. symmetry. apply H. Qed.
Lemma cmp_eqv_trans : forall e f g, cmp_eqv e f -> cmp_eqv f g -> cmp_eqv e g.
Proof. intros e f g H1 H2 x. rewrite H1. apply H2. Qed.

Lemma cmp_upd_eqv : forall e f x v, cmp_eqv e f -> cmp_eqv (cmp_upd e x v) (cmp_upd f x v).
Proof. intros e f x v H y. unfold cmp_upd. destruct (Nat.eqb y x); [reflexivity | apply H]. Qed.

Lemma cmp_aeval_eqv : forall a e f, cmp_eqv e f -> cmp_aeval e a = cmp_aeval f a.
Proof. induction a; intros e f H; simpl; auto. Qed.

Lemma cmp_beval_eqv : forall b e f, cmp_eqv e f -> cmp_beval e b = cmp_beval f b.
Proof.
  induction b; intros e f H; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (cmp_aeval_eqv a e f H), (cmp_aeval_eqv b e f H). reflexivity.
  - rewrite (cmp_aeval_eqv a e f H), (cmp_aeval_eqv b e f H). reflexivity.
  - rewrite (IHb e f H). reflexivity.
  - rewrite (IHb1 e f H), (IHb2 e f H). reflexivity.
  - rewrite (IHb1 e f H), (IHb2 e f H). reflexivity.
Qed.

(* Sequential assignment of a list of values to a list of variables; a
   longer list is cut to the shorter. *)
Fixpoint cmp_assigns (e : cmp_env) (ds vs : list nat) : cmp_env :=
  match ds, vs with
  | d :: ds', v :: vs' => cmp_assigns (cmp_upd e d v) ds' vs'
  | _, _ => e
  end.

Lemma cmp_assigns_eqv : forall ds vs e f, cmp_eqv e f -> cmp_eqv (cmp_assigns e ds vs) (cmp_assigns f ds vs).
Proof.
  induction ds as [| d ds IH]; intros [| v vs] e f H; simpl; auto.
  apply IH. apply cmp_upd_eqv. exact H.
Qed.

(* The frame of a call: parameter i gets argument i (0 if absent), the
   other locals 0. *)
Definition cmp_args (pr : cmp_proc) (args : list cmp_aexp) (e : cmp_env) : cmp_env :=
  fun i => if Nat.ltb i (pr_np pr) then cmp_aeval e (nth i args (CNum 0)) else 0.

Lemma cmp_args_eqv : forall pr args e f, cmp_eqv e f -> cmp_eqv (cmp_args pr args e) (cmp_args pr args f).
Proof.
  intros pr args e f H i. unfold cmp_args. destruct (Nat.ltb i (pr_np pr)); [apply cmp_aeval_eqv, H | reflexivity].
Qed.

(* ================================================================= *)
(* Big-step semantics.                                                *)
(* ================================================================= *)

Inductive cmp_ceval (ps : list cmp_proc) : cmp_env -> cmp_stmt -> cmp_env -> nat -> Prop :=
| CESkip : forall e, cmp_ceval ps e SSkip e 0
| CEAssign : forall e x a, cmp_ceval ps e (SAssign x a) (cmp_upd e x (cmp_aeval e a)) 1
| CESeq : forall e s t e1 e2 c1 c2,
    cmp_ceval ps e s e1 c1 -> cmp_ceval ps e1 t e2 c2 -> cmp_ceval ps e (SSeq s t) e2 (c1 + c2)
| CEIfT : forall e b s t e1 c,
    cmp_beval e b = true -> cmp_ceval ps e s e1 c -> cmp_ceval ps e (SIf b s t) e1 (S c)
| CEIfF : forall e b s t e1 c,
    cmp_beval e b = false -> cmp_ceval ps e t e1 c -> cmp_ceval ps e (SIf b s t) e1 (S c)
| CEWhileF : forall e b s,
    cmp_beval e b = false -> cmp_ceval ps e (SWhile b s) e 1
| CEWhileT : forall e b s e1 e2 c1 c2,
    cmp_beval e b = true -> cmp_ceval ps e s e1 c1 -> cmp_ceval ps e1 (SWhile b s) e2 c2 ->
    cmp_ceval ps e (SWhile b s) e2 (S (c1 + c2))
| CECall : forall e ds p args pr e1 c,
    nth_error ps p = Some pr ->
    cmp_ceval ps (cmp_args pr args e) (pr_body pr) e1 c ->
    cmp_ceval ps e (SCall ds p args) (cmp_assigns e ds (map (cmp_aeval e1) (pr_rets pr))) (S c).

(* The semantics does not see how an environment is stored. *)
Lemma cmp_ceval_ext : forall ps e s e1 c, cmp_ceval ps e s e1 c ->
  forall e', cmp_eqv e e' -> exists e1', cmp_eqv e1 e1' /\ cmp_ceval ps e' s e1' c.
Proof.
  intros ps e s e1 c H. induction H; intros e' Hq.
  - exists e'. split; [exact Hq | constructor].
  - exists (cmp_upd e' x (cmp_aeval e' a)). split.
    + intros y. unfold cmp_upd. destruct (Nat.eqb y x); [apply cmp_aeval_eqv, Hq | apply Hq].
    + constructor.
  - destruct (IHcmp_ceval1 e' Hq) as (e1' & Hs1 & D1). destruct (IHcmp_ceval2 e1' Hs1) as (e2' & Hs2 & D2).
    exists e2'. split; [exact Hs2 | econstructor; eauto].
  - destruct (IHcmp_ceval e' Hq) as (e1' & Hs1 & D1). exists e1'. split; [exact Hs1 |].
    apply CEIfT; [rewrite <- (cmp_beval_eqv b e e' Hq); exact H | exact D1].
  - destruct (IHcmp_ceval e' Hq) as (e1' & Hs1 & D1). exists e1'. split; [exact Hs1 |].
    apply CEIfF; [rewrite <- (cmp_beval_eqv b e e' Hq); exact H | exact D1].
  - exists e'. split; [exact Hq |]. apply CEWhileF. rewrite <- (cmp_beval_eqv b e e' Hq). exact H.
  - destruct (IHcmp_ceval1 e' Hq) as (e1' & Hs1 & D1). destruct (IHcmp_ceval2 e1' Hs1) as (e2' & Hs2 & D2).
    exists e2'. split; [exact Hs2 |]. apply CEWhileT with (e1 := e1'); auto.
    rewrite <- (cmp_beval_eqv b e e' Hq). exact H.
  - destruct (IHcmp_ceval (cmp_args pr args e') (cmp_args_eqv pr args e e' Hq)) as (e1' & Hs1 & D1).
    exists (cmp_assigns e' ds (map (cmp_aeval e1') (pr_rets pr))). split.
    + assert (Hm : map (cmp_aeval e1) (pr_rets pr) = map (cmp_aeval e1') (pr_rets pr)).
      { apply map_ext. intros a. apply cmp_aeval_eqv. exact Hs1. }
      rewrite Hm. apply cmp_assigns_eqv. exact Hq.
    + eapply CECall; eauto.
Qed.

Theorem cmp_ceval_det : forall ps e s e1 c, cmp_ceval ps e s e1 c ->
  forall e2 c2, cmp_ceval ps e s e2 c2 -> cmp_eqv e1 e2 /\ c = c2.
Proof.
  intros ps e s e1 c H. induction H; intros ee cc Hd; inversion Hd; subst; try congruence.
  - split; [apply cmp_eqv_refl | reflexivity].
  - split; [apply cmp_eqv_refl | reflexivity].
  - match goal with
    | [ Ha : cmp_ceval _ e s ?x ?y, Hb : cmp_ceval _ ?x t ee ?z |- _ ] =>
        destruct (IHcmp_ceval1 x y Ha) as [Q1 R1]; subst y;
        destruct (cmp_ceval_ext _ _ _ _ _ Hb e1 (cmp_eqv_sym _ _ Q1)) as (e3' & Q2 & D3);
        destruct (IHcmp_ceval2 e3' z D3) as [Q3 R3]; subst z;
        split; [eapply cmp_eqv_trans; [exact Q3 | apply cmp_eqv_sym; exact Q2] | reflexivity]
    end.
  - match goal with [ Hx : cmp_ceval _ e s ?x ?y |- _ ] =>
      destruct (IHcmp_ceval x y Hx) as [Q R]; subst y; split; [exact Q | reflexivity] end.
  - match goal with [ Hx : cmp_ceval _ e t ?x ?y |- _ ] =>
      destruct (IHcmp_ceval x y Hx) as [Q R]; subst y; split; [exact Q | reflexivity] end.
  - split; [apply cmp_eqv_refl | reflexivity].
  - match goal with
    | [ Ha : cmp_ceval _ e s ?x ?y, Hb : cmp_ceval _ ?x (SWhile b s) ee ?z |- _ ] =>
        destruct (IHcmp_ceval1 x y Ha) as [Q1 R1]; subst y;
        destruct (cmp_ceval_ext _ _ _ _ _ Hb e1 (cmp_eqv_sym _ _ Q1)) as (e3' & Q2 & D3);
        destruct (IHcmp_ceval2 e3' z D3) as [Q3 R3]; subst z;
        split; [eapply cmp_eqv_trans; [exact Q3 | apply cmp_eqv_sym; exact Q2] | reflexivity]
    end.
  - match goal with
    | [ Hp : nth_error ps p = Some ?pr2, Hx : cmp_ceval _ _ _ ?x ?y |- _ ] =>
        rewrite H in Hp; injection Hp as <-;
        destruct (IHcmp_ceval x y Hx) as [Q R]; subst y;
        split; [| reflexivity];
        assert (Hm : map (cmp_aeval e1) (pr_rets pr) = map (cmp_aeval x) (pr_rets pr))
          by (apply map_ext; intros a; apply cmp_aeval_eqv; exact Q);
        rewrite Hm; apply cmp_eqv_refl
    end.
Qed.

Lemma cmp_ceval_skip_inv : forall ps e e1 c, cmp_ceval ps e SSkip e1 c -> e1 = e /\ c = 0.
Proof. intros ps e e1 c H. inversion H; subst. split; reflexivity. Qed.

Lemma cmp_ceval_assign_inv : forall ps e x a e1 c,
  cmp_ceval ps e (SAssign x a) e1 c -> e1 = cmp_upd e x (cmp_aeval e a) /\ c = 1.
Proof. intros ps e x a e1 c H. inversion H; subst. split; reflexivity. Qed.

Lemma cmp_ceval_seq_inv : forall ps e s t e2 c,
  cmp_ceval ps e (SSeq s t) e2 c ->
  exists e1 c1 c2, cmp_ceval ps e s e1 c1 /\ cmp_ceval ps e1 t e2 c2 /\ c = c1 + c2.
Proof.
  intros ps e s t e2 c H. inversion H; subst.
  eexists _, _, _. split; [eassumption | split; [eassumption | reflexivity]].
Qed.

Lemma cmp_ceval_if_inv : forall ps e b s t e1 c,
  cmp_ceval ps e (SIf b s t) e1 c ->
  (cmp_beval e b = true /\ exists c0, cmp_ceval ps e s e1 c0 /\ c = S c0) \/
  (cmp_beval e b = false /\ exists c0, cmp_ceval ps e t e1 c0 /\ c = S c0).
Proof.
  intros ps e b s t e1 c H. inversion H; subst.
  - left. split; [assumption |]. eexists. split; [eassumption | reflexivity].
  - right. split; [assumption |]. eexists. split; [eassumption | reflexivity].
Qed.

Lemma cmp_ceval_while_inv : forall ps e b s e2 c,
  cmp_ceval ps e (SWhile b s) e2 c ->
  (cmp_beval e b = false /\ e2 = e /\ c = 1) \/
  (cmp_beval e b = true /\ exists e1 c1 c2,
     cmp_ceval ps e s e1 c1 /\ cmp_ceval ps e1 (SWhile b s) e2 c2 /\ c = S (c1 + c2)).
Proof.
  intros ps e b s e2 c H. inversion H; subst.
  - left. repeat split; auto.
  - right. split; [assumption |]. eexists _, _, _. split; [eassumption | split; [eassumption | reflexivity]].
Qed.

Lemma cmp_ceval_call_inv : forall ps e ds p args e2 c,
  cmp_ceval ps e (SCall ds p args) e2 c ->
  exists pr e1 c0, nth_error ps p = Some pr /\ cmp_ceval ps (cmp_args pr args e) (pr_body pr) e1 c0 /\
    e2 = cmp_assigns e ds (map (cmp_aeval e1) (pr_rets pr)) /\ c = S c0.
Proof.
  intros ps e ds p args e2 c H. inversion H; subst.
  eexists _, _, _. split; [eassumption | split; [eassumption | split; reflexivity]].
Qed.

(* ================================================================= *)
(* The interpreter: variables in a list.                              *)
(* ================================================================= *)

Definition cmp_lget (l : list nat) (x : nat) : nat := nth x l 0.

Fixpoint cmp_lset (l : list nat) (x v : nat) : list nat :=
  match l, x with
  | [], 0 => [v]
  | [], S x' => 0 :: cmp_lset [] x' v
  | _ :: t, 0 => v :: t
  | h :: t, S x' => h :: cmp_lset t x' v
  end.

Lemma cmp_lget_lset : forall l x v y,
  cmp_lget (cmp_lset l x v) y = if Nat.eqb y x then v else cmp_lget l y.
Proof.
  unfold cmp_lget. induction l as [| h t IH]; intros x v y.
  - revert y. induction x as [| x IHx]; intros y; simpl.
    + destruct y as [| y]; [reflexivity |]. simpl. destruct y; reflexivity.
    + destruct y as [| y]; [reflexivity |]. simpl. rewrite IHx. destruct (Nat.eqb y x); [reflexivity | destruct y; reflexivity].
  - destruct x as [| x]; simpl.
    + destruct y as [| y]; reflexivity.
    + destruct y as [| y]; [reflexivity |]. simpl. apply IH.
Qed.

Lemma cmp_lget_lset_eqv : forall l x v, cmp_eqv (cmp_lget (cmp_lset l x v)) (cmp_upd (cmp_lget l) x v).
Proof. intros l x v y. rewrite cmp_lget_lset. reflexivity. Qed.

Fixpoint cmp_lassigns (l : list nat) (ds vs : list nat) : list nat :=
  match ds, vs with
  | d :: ds', v :: vs' => cmp_lassigns (cmp_lset l d v) ds' vs'
  | _, _ => l
  end.

Lemma cmp_lassigns_eqv : forall ds vs l e, cmp_eqv (cmp_lget l) e ->
  cmp_eqv (cmp_lget (cmp_lassigns l ds vs)) (cmp_assigns e ds vs).
Proof.
  induction ds as [| d ds IH]; intros [| v vs] l e H; simpl; auto.
  apply IH. intros y. rewrite cmp_lget_lset. unfold cmp_upd. destruct (Nat.eqb y d); [reflexivity | apply H].
Qed.

Definition cmp_largs (pr : cmp_proc) (args : list cmp_aexp) (l : list nat) : list nat :=
  map (fun i => cmp_aeval (cmp_lget l) (nth i args (CNum 0))) (seq 0 (pr_np pr)).

Lemma cmp_largs_eqv : forall pr args l e, cmp_eqv (cmp_lget l) e ->
  cmp_eqv (cmp_lget (cmp_largs pr args l)) (cmp_args pr args e).
Proof.
  intros pr args l e H i. unfold cmp_lget, cmp_largs, cmp_args.
  destruct (Nat.ltb_spec i (pr_np pr)) as [Hi | Hi].
  - rewrite (nth_indep _ 0 (cmp_aeval (cmp_lget l) (nth i args (CNum 0)))) by (rewrite map_length, seq_length; exact Hi).
    rewrite map_nth with (d := i). rewrite seq_nth by exact Hi. simpl.
    apply cmp_aeval_eqv. exact H.
  - apply nth_overflow. rewrite map_length, seq_length. exact Hi.
Qed.

(* The fuel bounds the nesting of calls and the number of loop rounds; k is
   the operation count so far. *)
Fixpoint cmp_interp (ps : list cmp_proc) (f : nat) (l : list nat) (s : cmp_stmt) (k : nat)
  : option (list nat * nat) :=
  match f with
  | 0 => None
  | S f' =>
    match s with
    | SSkip => Some (l, k)
    | SAssign x a => Some (cmp_lset l x (cmp_aeval (cmp_lget l) a), S k)
    | SSeq s1 s2 =>
        match cmp_interp ps f' l s1 k with
        | Some (l1, k1) => cmp_interp ps f' l1 s2 k1
        | None => None
        end
    | SIf b s1 s2 =>
        if cmp_beval (cmp_lget l) b then cmp_interp ps f' l s1 (S k) else cmp_interp ps f' l s2 (S k)
    | SWhile b s1 =>
        if cmp_beval (cmp_lget l) b then
          match cmp_interp ps f' l s1 (S k) with
          | Some (l1, k1) => cmp_interp ps f' l1 (SWhile b s1) k1
          | None => None
          end
        else Some (l, S k)
    | SCall ds p args =>
        match nth_error ps p with
        | None => None
        | Some pr =>
            match cmp_interp ps f' (cmp_largs pr args l) (pr_body pr) (S k) with
            | Some (l1, k1) =>
                Some (cmp_lassigns l ds (map (cmp_aeval (cmp_lget l1)) (pr_rets pr)), k1)
            | None => None
            end
        end
    end
  end.

Theorem cmp_interp_sound : forall ps f l s k l1 k1,
  cmp_interp ps f l s k = Some (l1, k1) ->
  exists e1 c, cmp_ceval ps (cmp_lget l) s e1 c /\ cmp_eqv e1 (cmp_lget l1) /\ k1 = k + c.
Proof.
  intros ps f. induction f as [| f IH]; intros l s k l1 k1 H; [discriminate |].
  destruct s; simpl in H.
  - injection H as <- <-. exists (cmp_lget l), 0. split; [constructor |]. split; [apply cmp_eqv_refl | lia].
  - injection H as <- <-. exists (cmp_upd (cmp_lget l) x (cmp_aeval (cmp_lget l) a)), 1.
    split; [constructor |]. split; [apply cmp_eqv_sym; apply cmp_lget_lset_eqv | lia].
  - destruct (cmp_interp ps f l s1 k) as [[m1 j1] |] eqn:E1; [| discriminate].
    destruct (IH _ _ _ _ _ E1) as (e1 & c1 & D1 & Q1 & R1).
    destruct (IH _ _ _ _ _ H) as (e2 & c2 & D2 & Q2 & R2).
    destruct (cmp_ceval_ext _ _ _ _ _ D2 e1 (cmp_eqv_sym _ _ Q1)) as (e3 & Q3 & D3).
    exists e3, (c1 + c2). split; [econstructor; eauto |]. split; [apply cmp_eqv_trans with e2; [apply cmp_eqv_sym; exact Q3 | exact Q2] |]. lia.
  - destruct (cmp_beval (cmp_lget l) b) eqn:Eb.
    + destruct (IH _ _ _ _ _ H) as (e1 & c & D & Q & R). exists e1, (S c).
      split; [apply CEIfT; auto |]. split; [exact Q | lia].
    + destruct (IH _ _ _ _ _ H) as (e1 & c & D & Q & R). exists e1, (S c).
      split; [apply CEIfF; auto |]. split; [exact Q | lia].
  - destruct (cmp_beval (cmp_lget l) b) eqn:Eb.
    + destruct (cmp_interp ps f l s (S k)) as [[m1 j1] |] eqn:E1; [| discriminate].
      destruct (IH _ _ _ _ _ E1) as (e1 & c1 & D1 & Q1 & R1).
      destruct (IH _ _ _ _ _ H) as (e2 & c2 & D2 & Q2 & R2).
      destruct (cmp_ceval_ext _ _ _ _ _ D2 e1 (cmp_eqv_sym _ _ Q1)) as (e3 & Q3 & D3).
      exists e3, (S (c1 + c2)). split; [apply CEWhileT with (e1 := e1); auto |].
      split; [apply cmp_eqv_trans with e2; [apply cmp_eqv_sym; exact Q3 | exact Q2] |]. lia.
    + injection H as <- <-. exists (cmp_lget l), 1. split; [apply CEWhileF; auto |].
      split; [apply cmp_eqv_refl | lia].
  - destruct (nth_error ps p) as [pr |] eqn:Ep; [| discriminate].
    destruct (cmp_interp ps f (cmp_largs pr args l) (pr_body pr) (S k)) as [[m1 j1] |] eqn:E1; [| discriminate].
    injection H as <- <-.
    destruct (IH _ _ _ _ _ E1) as (e1 & c & D1 & Q1 & R1).
    destruct (cmp_ceval_ext _ _ _ _ _ D1 (cmp_args pr args (cmp_lget l))
                (cmp_largs_eqv pr args l _ (cmp_eqv_refl _))) as (e2 & Q2 & D2).
    exists (cmp_assigns (cmp_lget l) dsts (map (cmp_aeval e2) (pr_rets pr))), (S c).
    split; [eapply CECall; eauto |]. split; [| lia].
    assert (Hm : map (cmp_aeval e2) (pr_rets pr) = map (cmp_aeval (cmp_lget m1)) (pr_rets pr)).
    { apply map_ext. intros a. apply cmp_aeval_eqv. apply cmp_eqv_trans with e1; [apply cmp_eqv_sym; exact Q2 | exact Q1]. }
    rewrite Hm. apply cmp_eqv_sym. apply cmp_lassigns_eqv. apply cmp_eqv_refl.
Qed.

Theorem cmp_interp_complete : forall ps e s e1 c, cmp_ceval ps e s e1 c ->
  forall l, cmp_eqv e (cmp_lget l) ->
  exists f l1, cmp_eqv e1 (cmp_lget l1) /\
    forall f', f <= f' -> forall k, cmp_interp ps f' l s k = Some (l1, k + c).
Proof.
  intros ps e s e1 c H. induction H; intros l Hq.
  - exists 1, l. split; [exact Hq |]. intros f' Hf k. destruct f'; [lia |]. simpl. f_equal. f_equal. lia.
  - exists 1, (cmp_lset l x (cmp_aeval (cmp_lget l) a)). split.
    + intros y. rewrite cmp_lget_lset. unfold cmp_upd. destruct (Nat.eqb y x); [apply cmp_aeval_eqv, Hq | apply Hq].
    + intros f' Hf k. destruct f'; [lia |]. simpl. f_equal. f_equal. lia.
  - destruct (IHcmp_ceval1 l Hq) as (f1 & l1 & Q1 & F1).
    destruct (IHcmp_ceval2 l1 Q1) as (f2 & l2 & Q2 & F2).
    exists (S (Nat.max f1 f2)), l2. split; [exact Q2 |].
    intros f' Hf k. destruct f' as [| f']; [lia |]. simpl.
    rewrite (F1 f' ltac:(lia) k). rewrite (F2 f' ltac:(lia) (k + c1)). f_equal. f_equal. lia.
  - destruct (IHcmp_ceval l Hq) as (f1 & l1 & Q1 & F1).
    exists (S f1), l1. split; [exact Q1 |].
    intros f' Hf k. destruct f' as [| f']; [lia |]. simpl.
    rewrite <- (cmp_beval_eqv b e (cmp_lget l) Hq), H. rewrite (F1 f' ltac:(lia) (S k)). f_equal. f_equal. lia.
  - destruct (IHcmp_ceval l Hq) as (f1 & l1 & Q1 & F1).
    exists (S f1), l1. split; [exact Q1 |].
    intros f' Hf k. destruct f' as [| f']; [lia |]. simpl.
    rewrite <- (cmp_beval_eqv b e (cmp_lget l) Hq), H. rewrite (F1 f' ltac:(lia) (S k)). f_equal. f_equal. lia.
  - exists 1, l. split; [exact Hq |].
    intros f' Hf k. destruct f' as [| f']; [lia |]. simpl.
    rewrite <- (cmp_beval_eqv b e (cmp_lget l) Hq), H. f_equal. f_equal. lia.
  - destruct (IHcmp_ceval1 l Hq) as (f1 & l1 & Q1 & F1).
    destruct (IHcmp_ceval2 l1 Q1) as (f2 & l2 & Q2 & F2).
    exists (S (Nat.max f1 f2)), l2. split; [exact Q2 |].
    intros f' Hf k. destruct f' as [| f']; [lia |]. simpl.
    rewrite <- (cmp_beval_eqv b e (cmp_lget l) Hq), H. rewrite (F1 f' ltac:(lia) (S k)).
    simpl. rewrite (F2 f' ltac:(lia) (S (k + c1))). f_equal. f_equal. lia.
  - assert (Hq' := cmp_largs_eqv pr args l e (cmp_eqv_sym _ _ Hq)).
    destruct (IHcmp_ceval _ (cmp_eqv_sym _ _ Hq')) as (f1 & l1 & Q1 & F1).
    exists (S f1), (cmp_lassigns l ds (map (cmp_aeval (cmp_lget l1)) (pr_rets pr))). split.
    + assert (Hm : map (cmp_aeval e1) (pr_rets pr) = map (cmp_aeval (cmp_lget l1)) (pr_rets pr)).
      { apply map_ext. intros a. apply cmp_aeval_eqv. exact Q1. }
      rewrite Hm. apply cmp_eqv_sym. apply cmp_lassigns_eqv. apply cmp_eqv_sym. exact Hq.
    + intros f' Hf k. destruct f' as [| f']; [lia |]. simpl. rewrite H.
      rewrite (F1 f' ltac:(lia) (S k)). f_equal. f_equal. lia.
Qed.

(* ================================================================= *)
(* Variable bounds and the shape the compiler accepts.                *)
(* ================================================================= *)

Fixpoint cmp_lmax (l : list nat) : nat := match l with [] => 0 | x :: r => Nat.max x (cmp_lmax r) end.

(* One more than the largest variable named, or 0. *)
Fixpoint cmp_avmax (a : cmp_aexp) : nat :=
  match a with
  | CNum _ => 0
  | CVar x => S x
  | CAdd a b | CSub a b => Nat.max (cmp_avmax a) (cmp_avmax b)
  end.

Fixpoint cmp_bvmax (b : cmp_bexp) : nat :=
  match b with
  | BTrue | BFalse => 0
  | BEq a c | BLt a c => Nat.max (cmp_avmax a) (cmp_avmax c)
  | BNot b => cmp_bvmax b
  | BAnd b c | BOr b c => Nat.max (cmp_bvmax b) (cmp_bvmax c)
  end.

Fixpoint cmp_svmax (s : cmp_stmt) : nat :=
  match s with
  | SSkip => 0
  | SAssign x a => Nat.max (S x) (cmp_avmax a)
  | SSeq s t => Nat.max (cmp_svmax s) (cmp_svmax t)
  | SIf b s t => Nat.max (cmp_bvmax b) (Nat.max (cmp_svmax s) (cmp_svmax t))
  | SWhile b s => Nat.max (cmp_bvmax b) (cmp_svmax s)
  | SCall ds _ args => Nat.max (cmp_lmax (map S ds)) (cmp_lmax (map cmp_avmax args))
  end.

(* The size of the frame of a procedure: parameters, locals and the
   variables its result expressions read. *)
Definition cmp_procsz (pr : cmp_proc) : nat :=
  Nat.max (pr_np pr) (Nat.max (cmp_svmax (pr_body pr)) (cmp_lmax (map cmp_avmax (pr_rets pr)))).

(* Every call in s names a procedure below n. *)
Fixpoint cmp_wfs (n : nat) (s : cmp_stmt) : Prop :=
  match s with
  | SSkip | SAssign _ _ => True
  | SSeq s t | SIf _ s t => cmp_wfs n s /\ cmp_wfs n t
  | SWhile _ s => cmp_wfs n s
  | SCall _ p _ => p < n
  end.

(* Procedure i calls only procedures below i, and every called procedure exists. *)
Definition cmp_wfp (ps : list cmp_proc) : Prop :=
  forall i pr, nth_error ps i = Some pr -> cmp_wfs i (pr_body pr).

Definition cmp_wf (p : cmp_prog) : Prop :=
  cmp_wfp (cp_procs p) /\ cmp_wfs (length (cp_procs p)) (cp_main p).

(* Starting variables: the inputs in variables 0, 1, ... *)
Definition cmp_init (xs : list nat) : cmp_env := cmp_lget xs.

(* The source program computes y from the inputs xs in its variable out. *)
Definition cmp_src_computes (p : cmp_prog) (xs : list nat) (out y : nat) : Prop :=
  exists e1 c, cmp_ceval (cp_procs p) (cmp_init xs) (cp_main p) e1 c /\ e1 out = y.

Print Assumptions cmp_ceval_det.
Print Assumptions cmp_interp_sound.
Print Assumptions cmp_interp_complete.
