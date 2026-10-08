(** LRecursion: Kleene's second recursion theorem and Rice's theorem for L.

    [StructuralUndecidability] states the diagonal once, over any substrate
    that supplies a recursion theorem for the transformers it can express.
    [NatSubstrateInstance] supplies that premise by construction: its
    fixed-point program is defined to copy whatever the transformer returns.
    This file proves a recursion theorem from the reduction rules of L.

    The model is L, the weak call-by-value lambda calculus (Forster and
    Smolka, "Weak call-by-value lambda calculus as a model of computation
    in Coq", ITP 2017). Forster and Smolka show L is Turing-complete; that
    is cited here, not re-proved. Here it is built from scratch,
    with a deterministic left-to-right step relation, so the file needs no
    library beyond the Coq standard library.

    What is proved.

    - Programs are terms. A term's code is its Scott encoding [enc t], itself
      a closed L value.
    - A quote combinator [Q] maps the code of any term to the code of its
      code ([Q_spec]). It is built with a call-by-value fixed-point
      combinator ([rec_spec]).
    - Kleene's second recursion theorem: for every closed value [s] there is
      a closed term [t] that reduces to [s] applied to the code of [t]
      ([second_recursion]).
    - Transformers that an L term computes on codes have extensional fixed
      points ([L_recursion_theorem]). The equivalence here observes reachable
      values. L is not an instance of the total-run [Substrate] interface.
    - The diagonal: no L term decides a property of programs that depends
      only on what they compute, holds for one closed program, and fails
      for another ([L_rice]). Halting is the example: it fails for a
      diverging program ([L_halting_undecidable]).

    The diagonal here is the same argument as [structural_shortcut_undecidable].
    What changes is where the recursion theorem comes from: here it is proved
    from the reduction rules, not assumed and not built in by definition. *)

(* SCOPE NOTE: standalone proof scope. L is a separate model of computation.
   This file imports no kernel semantics on purpose: its point is a
   recursion theorem proved inside a model of its own. *)

From Coq Require Import Arith.PeanoNat Lia.

(** * Syntax *)

Inductive term : Type :=
| var : nat -> term
| app : term -> term -> term
| lam : term -> term.

(** [bound k s]: every free variable of [s] is below [k]. *)
Fixpoint bound (k : nat) (s : term) : Prop :=
  match s with
  | var n => n < k
  | app s t => bound k s /\ bound k t
  | lam s => bound (S k) s
  end.

Definition closed (s : term) : Prop := bound 0 s.

(** Substitution of a closed term for variable [k]. Only closed terms are
    ever substituted, so no shifting is needed. *)
Fixpoint subst (s : term) (k : nat) (u : term) : term :=
  match s with
  | var n => if Nat.eqb n k then u else var n
  | app s t => app (subst s k u) (subst t k u)
  | lam s => lam (subst s (S k) u)
  end.

Lemma bound_mono : forall s k k', k <= k' -> bound k s -> bound k' s.
Proof.
  induction s as [n | s IHs t IHt | s IHs]; simpl; intros k k' Hle Hb.
  - lia.
  - destruct Hb. split; [eapply IHs | eapply IHt]; eauto.
  - eapply IHs; [| exact Hb]. lia.
Qed.

Lemma subst_bound : forall s k j u, bound k s -> k <= j -> subst s j u = s.
Proof.
  induction s as [n | s IHs t IHt | s IHs]; simpl; intros k j u Hb Hle.
  - destruct (Nat.eqb_spec n j); [lia | reflexivity].
  - destruct Hb. rewrite (IHs k), (IHt k); auto.
  - rewrite (IHs (S k)); auto. lia.
Qed.

Lemma subst_closed : forall s k u, closed s -> subst s k u = s.
Proof. intros s k u H. apply (subst_bound s 0); [exact H | lia]. Qed.

Lemma bound_subst :
  forall s k u, bound (S k) s -> closed u -> bound k (subst s k u).
Proof.
  induction s as [n | s IHs t IHt | s IHs]; simpl; intros k u Hb Hu.
  - destruct (Nat.eqb_spec n k).
    + eapply bound_mono; [| exact Hu]. lia.
    + simpl. lia.
  - destruct Hb. split; auto.
  - apply IHs; auto.
Qed.

(** * Reduction *)

Definition value (s : term) : Prop := exists b, s = lam b.

(** Deterministic weak call-by-value reduction, left to right. *)
Inductive step : term -> term -> Prop :=
| stepBeta : forall b v, value v -> step (app (lam b) v) (subst b 0 v)
| stepL : forall s s' t, step s s' -> step (app s t) (app s' t)
| stepR : forall v t t', value v -> step t t' -> step (app v t) (app v t').

Lemma value_no_step : forall v s, value v -> ~ step v s.
Proof. intros v s [b ->] H. inversion H. Qed.

Lemma step_deterministic : forall s t1 t2, step s t1 -> step s t2 -> t1 = t2.
Proof.
  intros s t1 t2 H1. revert t2.
  induction H1; intros t2 H2; inversion H2; subst; try reflexivity;
    try match goal with H : step (lam _) _ |- _ => inversion H end;
    try match goal with
        | Hv : value ?v, H : step ?v _ |- _ => exfalso; exact (value_no_step _ _ Hv H)
        end;
    f_equal; auto.
Qed.

Inductive star : term -> term -> Prop :=
| star_refl : forall s, star s s
| star_step : forall s t u, step s t -> star t u -> star s u.

Lemma star_one : forall s t, step s t -> star s t.
Proof. intros. econstructor; [eassumption | constructor]. Qed.

Lemma star_trans : forall s t u, star s t -> star t u -> star s u.
Proof.
  intros s t u H. induction H; intros; [assumption |].
  econstructor; eauto.
Qed.

Lemma star_appL : forall s s' t, star s s' -> star (app s t) (app s' t).
Proof.
  intros s s' t H. induction H; [constructor |].
  econstructor; [apply stepL; eassumption | assumption].
Qed.

Lemma star_appR :
  forall v t t', value v -> star t t' -> star (app v t) (app v t').
Proof.
  intros v t t' Hv H. induction H; [constructor |].
  econstructor; [apply stepR; eassumption | assumption].
Qed.

(** Reduce both sides of an application to values, then apply. *)
Lemma star_app :
  forall s t b v,
    star s (lam b) -> star t v -> value v ->
    star (app s t) (subst b 0 v).
Proof.
  intros s t b v Hs Ht Hv.
  eapply star_trans; [apply star_appL; exact Hs |].
  eapply star_trans; [apply star_appR; [exists b; reflexivity | exact Ht] |].
  apply star_one. constructor. exact Hv.
Qed.

(** In a deterministic system, reducing to a value is unaffected by the
    path: if [s] reaches [t] and a value [v], then [t] reaches [v]. *)
Lemma star_value_confluent :
  forall s t v, star s t -> star s v -> value v -> star t v.
Proof.
  intros s t v Ht. induction Ht as [s | s s1 t H1 _ IH]; intros Hv Hval.
  - exact Hv.
  - inversion Hv as [| s' s2 v' H2 Hrest]; subst.
    + exfalso. exact (value_no_step v s1 Hval H1).
    + rewrite (step_deterministic s s1 s2 H1 H2) in *. apply IH; assumption.
Qed.

(** * Behaviour *)

(** [eval s v]: [s] reduces to the value [v]. *)
Definition eval (s v : term) : Prop := star s v /\ value v.

(** Two programs are equivalent when they reach the same values. *)
Definition equiv (p q : term) : Prop := forall v, eval p v <-> eval q v.

Lemma equiv_sym : forall p q, equiv p q -> equiv q p.
Proof. intros p q H v. specialize (H v). tauto. Qed.

Lemma equiv_trans : forall p q r, equiv p q -> equiv q r -> equiv p r.
Proof. intros p q r H1 H2 v. rewrite (H1 v). apply H2. Qed.

Lemma star_equiv : forall p q, star p q -> equiv p q.
Proof.
  intros p q H v. split.
  - intros [Hv Hval]. split; [| exact Hval].
    exact (star_value_confluent p q v H Hv Hval).
  - intros [Hv Hval]. split; [eapply star_trans; eauto | exact Hval].
Qed.

(** * Encodings *)

(** Scott numerals. *)
Fixpoint encn (n : nat) : term :=
  match n with
  | 0 => lam (lam (var 1))
  | S n => lam (lam (app (var 0) (encn n)))
  end.

(** Scott encoding of terms: three cases, variable, application, abstraction. *)
Fixpoint enc (s : term) : term :=
  match s with
  | var n => lam (lam (lam (app (var 2) (encn n))))
  | app s t => lam (lam (lam (app (app (var 1) (enc s)) (enc t))))
  | lam s => lam (lam (lam (app (var 0) (enc s))))
  end.

Lemma encn_closed : forall n, closed (encn n).
Proof.
  induction n; unfold closed in *; simpl; [lia |].
  split; [lia |]. eapply bound_mono; [| exact IHn]. lia.
Qed.

Lemma enc_closed : forall s, closed (enc s).
Proof.
  unfold closed. induction s as [n | s IHs t IHt | s IHs]; simpl.
  - split; [lia |]. eapply bound_mono; [| apply encn_closed]. lia.
  - split; [split; [lia |] |];
      (eapply bound_mono; [| eassumption]; lia).
  - split; [lia |]. eapply bound_mono; [| exact IHs]. lia.
Qed.

Lemma encn_value : forall n, value (encn n).
Proof. destruct n; eexists; reflexivity. Qed.

Lemma enc_value : forall s, value (enc s).
Proof. destruct s; eexists; reflexivity. Qed.

(** * Constructors on codes *)

(** [mk_var], [mk_app], [mk_lam] build the code of a variable, application,
    or abstraction from the codes of its parts. *)
Definition mk_var : term := lam (lam (lam (lam (app (var 2) (var 3))))).
Definition mk_app : term :=
  lam (lam (lam (lam (lam (app (app (var 1) (var 4)) (var 3)))))).
Definition mk_lam : term := lam (lam (lam (lam (app (var 0) (var 3))))).

Lemma mk_lam_spec : forall e,
  closed e -> value e -> star (app mk_lam e) (lam (lam (lam (app (var 0) e)))).
Proof.
  intros e Hc Hv. apply star_one. unfold mk_lam.
  replace (lam (lam (lam (app (var 0) e))))
    with (subst (lam (lam (lam (app (var 0) (var 3))))) 0 e) by reflexivity.
  constructor. exact Hv.
Qed.

Lemma mk_var_spec : forall e,
  closed e -> value e -> star (app mk_var e) (lam (lam (lam (app (var 2) e)))).
Proof.
  intros e Hc Hv. apply star_one. unfold mk_var.
  replace (lam (lam (lam (app (var 2) e))))
    with (subst (lam (lam (lam (app (var 2) (var 3))))) 0 e) by reflexivity.
  constructor. exact Hv.
Qed.

Lemma mk_app_spec : forall e1 e2,
  closed e1 -> value e1 -> closed e2 -> value e2 ->
  star (app (app mk_app e1) e2) (lam (lam (lam (app (app (var 1) e1) e2)))).
Proof.
  intros e1 e2 Hc1 Hv1 Hc2 Hv2. unfold mk_app.
  eapply star_trans.
  - apply star_appL. apply star_one.
    replace (lam (lam (lam (lam (app (app (var 1) e1) (var 3))))))
      with (subst (lam (lam (lam (lam (app (app (var 1) (var 4)) (var 3)))))) 0 e1)
      by reflexivity.
    constructor. exact Hv1.
  - apply star_one.
    replace (lam (lam (lam (app (app (var 1) e1) e2))))
      with (subst (lam (lam (lam (app (app (var 1) e1) (var 3))))) 0 e2)
      by (simpl; rewrite (subst_closed e1 3 e2 Hc1); reflexivity).
    constructor. exact Hv2.
Qed.

(** The code of an application, built from the codes of its parts. *)
Lemma mk_app_enc : forall s t,
  star (app (app mk_app (enc s)) (enc t)) (enc (app s t)).
Proof.
  intros s t. apply mk_app_spec;
    [apply enc_closed | apply enc_value | apply enc_closed | apply enc_value].
Qed.

(** Evaluate the argument of a code constructor, then build the code. *)
Lemma mk_lam_eval : forall X e,
  star X e -> value e -> star (app mk_lam X) (lam (lam (lam (app (var 0) e)))).
Proof.
  intros X e HX Hv.
  eapply star_trans; [apply star_appR; [eexists; reflexivity | exact HX] |].
  apply star_one.
  replace (lam (lam (lam (app (var 0) e))))
    with (subst (lam (lam (lam (app (var 0) (var 3))))) 0 e) by reflexivity.
  constructor. exact Hv.
Qed.

Lemma mk_app_eval : forall X Y e1 e2,
  star X e1 -> value e1 -> closed e1 -> star Y e2 -> value e2 ->
  star (app (app mk_app X) Y) (lam (lam (lam (app (app (var 1) e1) e2)))).
Proof.
  intros X Y e1 e2 HX Hv1 Hc1 HY Hv2.
  eapply star_trans.
  { apply star_appL.
    eapply star_trans; [apply star_appR; [eexists; reflexivity | exact HX] |].
    apply star_one.
    replace (lam (lam (lam (lam (app (app (var 1) e1) (var 3))))))
      with (subst (lam (lam (lam (lam (app (app (var 1) (var 4)) (var 3)))))) 0 e1)
      by reflexivity.
    constructor. exact Hv1. }
  eapply star_trans; [apply star_appR; [eexists; reflexivity | exact HY] |].
  apply star_one.
  replace (lam (lam (lam (app (app (var 1) e1) e2))))
    with (subst (lam (lam (lam (app (app (var 1) e1) (var 3))))) 0 e2)
    by (simpl; rewrite (subst_closed e1 3 e2 Hc1); reflexivity).
  constructor. exact Hv2.
Qed.

(** * A call-by-value fixed-point combinator *)

Definition W : term :=
  lam (lam (lam (app (app (var 1) (lam (app (app (app (var 3) (var 3)) (var 2)) (var 0))))
                     (var 0)))).

(** [rec F] behaves like [F (rec F)] on values. *)
Definition rec (F : term) : term := lam (app (app (app W W) F) (var 0)).

Lemma W_closed : closed W.
Proof. cbv. repeat split; lia. Qed.

Lemma rec_closed : forall F, closed F -> closed (rec F).
Proof.
  intros F HF. unfold closed, rec. simpl.
  repeat split; try lia. eapply bound_mono; [| exact HF]. lia.
Qed.

Lemma rec_spec : forall F v,
  closed F -> value F -> closed v -> value v ->
  star (app (rec F) v) (app (app F (rec F)) v).
Proof.
  intros F v HF HFv Hc Hv.
  eapply star_step; [apply stepBeta; exact Hv |].
  simpl. repeat rewrite (subst_closed F) by exact HF.
  eapply star_step.
  { apply stepL. apply stepL. apply stepBeta. eexists; reflexivity. }
  simpl.
  eapply star_step; [apply stepL; apply stepBeta; exact HFv |].
  simpl. repeat rewrite (subst_closed F) by exact HF.
  eapply star_step; [apply stepBeta; exact Hv |].
  simpl. repeat rewrite (subst_closed F) by exact HF.
  apply star_refl.
Qed.

(** * Quoting numerals *)

Definition ZQ : term := enc (encn 0).
Definition EV0 : term := enc (var 0).
Definition EV1 : term := enc (var 1).
Definition EV2 : term := enc (var 2).

Definition Fn : term :=
  lam (lam (app (app (var 0) ZQ)
                (lam (app mk_lam (app mk_lam (app (app mk_app EV0) (app (var 2) (var 0)))))))).

Definition Qn : term := rec Fn.

Lemma Fn_closed : closed Fn.
Proof. cbv. repeat split; lia. Qed.

Lemma Qn_closed : closed Qn.
Proof. apply rec_closed, Fn_closed. Qed.

Lemma Qn_spec : forall n, star (app Qn (encn n)) (enc (encn n)).
Proof.
  induction n as [| n IH].
  - eapply star_trans.
    { apply rec_spec; [exact Fn_closed | eexists; reflexivity
                      | apply encn_closed | apply encn_value]. }
    eapply star_step; [apply stepL; apply stepBeta; eexists; reflexivity |].
    simpl. eapply star_step; [apply stepBeta; eexists; reflexivity |].
    simpl. eapply star_step; [apply stepL; apply stepBeta; eexists; reflexivity |].
    simpl. eapply star_step; [apply stepBeta; eexists; reflexivity |].
    simpl. apply star_refl.
  - eapply star_trans.
    { apply rec_spec; [exact Fn_closed | eexists; reflexivity
                      | apply encn_closed | apply encn_value]. }
    eapply star_step; [apply stepL; apply stepBeta; eexists; reflexivity |].
    simpl. eapply star_step; [apply stepBeta; eexists; reflexivity |].
    simpl. repeat rewrite (subst_closed (encn n)) by apply encn_closed.
    eapply star_step; [apply stepL; apply stepBeta; eexists; reflexivity |].
    simpl. repeat rewrite (subst_closed (encn n)) by apply encn_closed.
    eapply star_step; [apply stepBeta; eexists; reflexivity |].
    simpl. repeat rewrite (subst_closed (encn n)) by apply encn_closed.
    eapply star_step; [apply stepBeta; apply encn_value |].
    simpl. repeat rewrite (subst_closed (encn n)) by apply encn_closed.
    change (lam (lam (lam (app (var 0) (enc (lam (app (var 0) (encn n))))))))
      with (enc (encn (S n))).
    apply mk_lam_eval; [| eexists; reflexivity].
    apply mk_lam_eval; [| eexists; reflexivity].
    apply mk_app_eval; [apply star_refl | eexists; reflexivity
                       | cbv; repeat split; lia | exact IH | apply enc_value].
Qed.

(** * Quoting terms *)

(** [Q] maps the code of a term to the code of that code. It reads the
    Scott code by cases and rebuilds each constructor one level up. *)
Definition Aq : term :=
  lam (app mk_lam (app mk_lam (app mk_lam (app (app mk_app EV2) (app Qn (var 0)))))).

Definition Bq : term :=
  lam (lam (app mk_lam (app mk_lam (app mk_lam
    (app (app mk_app (app (app mk_app EV1) (app (var 3) (var 1))))
         (app (var 3) (var 0))))))).

Definition Cq : term :=
  lam (app mk_lam (app mk_lam (app mk_lam (app (app mk_app EV0) (app (var 2) (var 0)))))).

Definition Fq : term := lam (lam (app (app (app (var 0) Aq) Bq) Cq)).

Definition Q : term := rec Fq.

Lemma Fq_closed : closed Fq.
Proof. cbv. repeat split; lia. Qed.

Lemma Q_closed : closed Q.
Proof. apply rec_closed, Fq_closed. Qed.

Ltac close_subst :=
  repeat first [ rewrite (subst_closed (encn _)) by apply encn_closed
               | rewrite (subst_closed (enc _)) by apply enc_closed ].

Ltac find_beta :=
  first [ apply stepBeta;
          solve [eexists; reflexivity | apply enc_value | apply encn_value]
        | apply stepL; find_beta ].

Ltac beta := eapply star_step; [find_beta | simpl; close_subst].

Lemma EV_closed : closed EV0 /\ closed EV1 /\ closed EV2.
Proof. cbv. repeat split; lia. Qed.

Lemma Q_spec : forall s, star (app Q (enc s)) (enc (enc s)).
Proof.
  destruct EV_closed as [HE0 [HE1 HE2]].
  induction s as [n | s IHs t IHt | s IHs].
  - eapply star_trans.
    { apply rec_spec; [exact Fq_closed | eexists; reflexivity
                      | apply enc_closed | apply enc_value]. }
    unfold Fq at 1. do 5 beta.
    eapply star_step; [apply stepBeta; apply encn_value | simpl; close_subst].
    apply mk_lam_eval; [| eexists; reflexivity].
    apply mk_lam_eval; [| eexists; reflexivity].
    apply mk_lam_eval; [| eexists; reflexivity].
    apply mk_app_eval; [apply star_refl | eexists; reflexivity | exact HE2
                       | apply Qn_spec | apply enc_value].
  - eapply star_trans.
    { apply rec_spec; [exact Fq_closed | eexists; reflexivity
                      | apply enc_closed | apply enc_value]. }
    unfold Fq at 1. do 5 beta.
    eapply star_step; [apply stepL; apply stepBeta; apply enc_value | simpl; close_subst].
    eapply star_step; [apply stepBeta; apply enc_value | simpl; close_subst].
    apply mk_lam_eval; [| eexists; reflexivity].
    apply mk_lam_eval; [| eexists; reflexivity].
    apply mk_lam_eval; [| eexists; reflexivity].
    apply mk_app_eval; [| eexists; reflexivity | | exact IHt | apply enc_value].
    + apply mk_app_eval; [apply star_refl | eexists; reflexivity | exact HE1
                         | exact IHs | apply enc_value].
    + exact (enc_closed (app (var 1) (enc s))).
  - eapply star_trans.
    { apply rec_spec; [exact Fq_closed | eexists; reflexivity
                      | apply enc_closed | apply enc_value]. }
    unfold Fq at 1. do 5 beta.
    eapply star_step; [apply stepBeta; apply enc_value | simpl; close_subst].
    apply mk_lam_eval; [| eexists; reflexivity].
    apply mk_lam_eval; [| eexists; reflexivity].
    apply mk_lam_eval; [| eexists; reflexivity].
    apply mk_app_eval; [apply star_refl | eexists; reflexivity | exact HE0
                       | exact IHs | apply enc_value].
Qed.

(** * Kleene's second recursion theorem *)

(** For every closed value [s] there is a closed term [t] that reduces to
    [s] applied to the code of [t]. The term is [A (enc A)], where [A] reads
    its argument, builds the code of [A (enc A)] from it, and hands that code
    to [s]. *)
Theorem second_recursion :
  forall s, closed s -> value s -> exists t, closed t /\ star t (app s (enc t)).
Proof.
  intros s Hs Hsv.
  pose (A := lam (app s (app (app mk_app (var 0)) (app Q (var 0))))).
  assert (HA : closed A).
  { unfold A, closed. simpl. repeat split; try lia;
      (eapply bound_mono; [| first [exact Hs | exact Q_closed]]; lia). }
  exists (app A (enc A)). split.
  - split; [exact HA | apply enc_closed].
  - eapply star_step; [apply stepBeta; apply enc_value |].
    change (subst (app s (app (app mk_app (var 0)) (app Q (var 0)))) 0 (enc A))
      with (app (subst s 0 (enc A)) (app (app mk_app (enc A)) (app Q (enc A)))).
    rewrite (subst_closed s) by exact Hs.
    apply star_appR; [exact Hsv |].
    change (enc (app A (enc A)))
      with (lam (lam (lam (app (app (var 1) (enc A)) (enc (enc A)))))).
    apply mk_app_eval; [apply star_refl | apply enc_value | apply enc_closed
                       | apply Q_spec | apply enc_value].
Qed.

(** A transformer on programs is L-computable when some closed value maps
    the code of every program to a term that behaves like its image. *)
Definition L_representable (f : term -> term) : Prop :=
  exists s, closed s /\ value s /\ forall p, equiv (app s (enc p)) (f p).

(** Every L-computable transformer has an extensional fixed point under
    the reachable-value equivalence [equiv]. *)
Theorem L_recursion_theorem :
  forall f, L_representable f -> exists p, equiv p (f p).
Proof.
  intros f [s [Hs [Hsv Hf]]].
  destruct (second_recursion s Hs Hsv) as [t [_ Ht]].
  exists t. eapply equiv_trans; [apply star_equiv; exact Ht | apply Hf].
Qed.

(** * The diagonal *)

Definition ltrue : term := lam (lam (var 1)).
Definition lfalse : term := lam (lam (var 0)).
Definition lid : term := lam (var 0).

(** [D] decides [P]: on the code of every program it reduces to true when
    [P] holds and to false when it does not. *)
Definition L_decides (D : term) (P : term -> Prop) : Prop :=
  forall p, (P p -> star (app D (enc p)) ltrue) /\ (~ P p -> star (app D (enc p)) lfalse).

Definition extensional (P : term -> Prop) : Prop :=
  forall p q, equiv p q -> P p -> P q.

(** The flip of a decider: run [D] on the code, return [no] on true and
    [yes] on false. *)
Definition flip_term (D yes no : term) : term :=
  lam (app (app (app (app D (var 0)) (lam no)) (lam yes)) lid).

Lemma flip_term_closed : forall D yes no,
  closed D -> closed yes -> closed no -> closed (flip_term D yes no).
Proof.
  intros D yes no HD Hy Hn. unfold flip_term, closed. simpl.
  repeat split; try lia; eapply bound_mono; try eassumption; lia.
Qed.

Lemma flip_true : forall D yes no p,
  closed D -> closed yes -> closed no ->
  star (app D (enc p)) ltrue ->
  star (app (flip_term D yes no) (enc p)) no.
Proof.
  intros D yes no p HD Hy Hn HT.
  eapply star_step; [apply stepBeta; apply enc_value |].
  simpl. repeat rewrite (subst_closed D) by exact HD.
  repeat rewrite (subst_closed yes) by exact Hy. repeat rewrite (subst_closed no) by exact Hn.
  eapply star_trans; [do 3 apply star_appL; exact HT |].
  eapply star_step; [apply stepL; apply stepL; apply stepBeta; eexists; reflexivity |].
  simpl. repeat rewrite (subst_closed no) by exact Hn.
  eapply star_step; [apply stepL; apply stepBeta; eexists; reflexivity |].
  simpl. repeat rewrite (subst_closed no) by exact Hn.
  eapply star_step; [apply stepBeta; eexists; reflexivity |].
  simpl. repeat rewrite (subst_closed no) by exact Hn. apply star_refl.
Qed.

Lemma flip_false : forall D yes no p,
  closed D -> closed yes -> closed no ->
  star (app D (enc p)) lfalse ->
  star (app (flip_term D yes no) (enc p)) yes.
Proof.
  intros D yes no p HD Hy Hn HF.
  eapply star_step; [apply stepBeta; apply enc_value |].
  simpl. repeat rewrite (subst_closed D) by exact HD.
  repeat rewrite (subst_closed yes) by exact Hy. repeat rewrite (subst_closed no) by exact Hn.
  eapply star_trans; [do 3 apply star_appL; exact HF |].
  eapply star_step; [apply stepL; apply stepL; apply stepBeta; eexists; reflexivity |].
  simpl.
  eapply star_step; [apply stepL; apply stepBeta; eexists; reflexivity |].
  simpl.
  eapply star_step; [apply stepBeta; eexists; reflexivity |].
  simpl. repeat rewrite (subst_closed yes) by exact Hy. apply star_refl.
Qed.

(** Rice's theorem for L. No L term decides a property of programs that
    depends only on what they compute, holds for one closed program, and
    fails for another. *)
Theorem L_rice :
  forall P yes no,
    extensional P -> P yes -> ~ P no -> closed yes -> closed no ->
    ~ exists D, closed D /\ L_decides D P.
Proof.
  intros P yes no Hext Hyes Hno Hy Hn [D [HD Hdec]].
  set (s := flip_term D yes no).
  assert (Hs : closed s) by (apply flip_term_closed; assumption).
  destruct (second_recursion s Hs (ex_intro _ _ eq_refl)) as [t [_ Ht]].
  assert (Hts : equiv t (app s (enc t))) by (apply star_equiv; exact Ht).
  destruct (Hdec t) as [HT HF].
  assert (Hnot : ~ P t).
  { intro HPt.
    pose proof (flip_true D yes no t HD Hy Hn (HT HPt)) as Hno'.
    apply Hno. apply (Hext t no); [| exact HPt].
    eapply equiv_trans; [exact Hts | apply star_equiv; exact Hno']. }
  apply Hnot.
  pose proof (flip_false D yes no t HD Hy Hn (HF Hnot)) as Hyes'.
  apply (Hext yes t); [| exact Hyes].
  apply equiv_sym. eapply equiv_trans; [exact Hts | apply star_equiv; exact Hyes'].
Qed.

(** The same diagonal in the shape of [structural_shortcut_undecidable]: a
    Boolean decider whose flip is L-computable cannot exist, and the
    recursion premise it needs is [L_recursion_theorem], proved above. *)
Theorem L_structural_shortcut_undecidable :
  forall (P : term -> Prop) yes no,
    extensional P -> P yes -> ~ P no ->
    ~ exists decide : term -> bool,
        L_representable (fun p => if decide p then no else yes) /\
        (forall p, decide p = true <-> P p).
Proof.
  intros P yes no Hext Hyes Hno [decide [Hrep Hdec]].
  destruct (L_recursion_theorem _ Hrep) as [t Ht].
  destruct (decide t) eqn:Hd.
  - apply Hno. apply (Hext t no); [exact Ht | apply Hdec; exact Hd].
  - assert (HPt : P t) by (apply (Hext yes t); [apply equiv_sym; exact Ht | exact Hyes]).
    apply Hdec in HPt. congruence.
Qed.

(** * Halting is undecidable in L *)

Definition omega : term := lam (app (var 0) (var 0)).
Definition Omega : term := app omega omega.

Lemma Omega_step : forall t, step Omega t -> t = Omega.
Proof.
  intros t H. inversion H; subst.
  - reflexivity.
  - inversion H3.
  - inversion H4.
Qed.

Lemma Omega_diverges : forall v, ~ eval Omega v.
Proof.
  intros v [Hs [b Hb]]. subst v.
  remember Omega as o eqn:Ho. remember (lam b) as l eqn:Hl.
  induction Hs as [s | s t u H1 H2 IH].
  - subst. discriminate.
  - subst. apply Omega_step in H1. subst. apply IH; reflexivity.
Qed.

Definition halts (p : term) : Prop := exists v, eval p v.

Lemma halts_extensional : extensional halts.
Proof. intros p q Heq [v Hv]. exists v. apply Heq. exact Hv. Qed.

(** No L term decides whether an L program halts. *)
Theorem L_halting_undecidable : ~ exists D, closed D /\ L_decides D halts.
Proof.
  apply (L_rice halts lid Omega halts_extensional).
  - exists lid. split; [apply star_refl | eexists; reflexivity].
  - intros [v Hv]. exact (Omega_diverges v Hv).
  - cbv. lia.
  - cbv. repeat split; lia.
Qed.
