From Coq Require Import QArith.QArith_base.
From Coq Require Import ZArith.
From Coq Require Import ZArith.Zorder.

Open Scope Q_scope.

(* Utilities to work with [Qeq] (notation "==") without trying to
   convert it into Coq's definitional equality.  Instead we expose the
   underlying cross-multiplied integer equations and use them to
   transport order facts (<= / <) where needed.  These lemmas are the
   minimal, mechanically checkable bridge that lets us push Qeq evidence
   into the Z-level inequalities produced by unfolding Qle/Qlt. *)

(** [Qeq_cross_mul]: formal specification. *)
Lemma Qeq_cross_mul : forall x y : Q, x == y ->
  (Qnum x * QDen y = Qnum y * QDen x)%Z.
Proof. intros; unfold Qeq; assumption. Qed.

(** [Qeq_le_compat]: formal specification. *)
Lemma Qeq_le_compat : forall x y z : Q, x == y -> x <= z -> y <= z.
Proof.
  intros x y z Hxy Hxz.
  (* Use setoid-based replacement: [x == y] lets us replace [x] with [y]
     under the Q-ordering because Qle is Proper w.r.t Qeq. *)
  setoid_replace x with y in Hxz by exact Hxy.
  exact Hxz.
Qed.

(** [Qeq_lt_compat]: formal specification. *)
Lemma Qeq_lt_compat : forall x y z : Q, x == y -> x < z -> y < z.
Proof.
   intros x y z Hxy Hxz.
   setoid_replace x with y in Hxz by exact Hxy.
   exact Hxz.
Qed.

(* Qabs is provided by the standard library and already has a registered
   morphism (Qabs_wd : Proper (Qeq ==> Qeq) Qabs).  We keep this file
   focused on the Z-level transport lemmas/tactics and avoid re-proving
   existing QArith properties here. *)

(* A symmetric form of the cross-multiplication identity is often
    convenient when the Z-level product appears with the factors in the
    opposite order. *)
(** [Qeq_cross_mul_sym]: formal specification. *)
Lemma Qeq_cross_mul_sym : forall x y : Q, x == y ->
   (Qnum y * QDen x = Qnum x * QDen y)%Z.
Proof. intros. symmetry. rewrite (Qeq_cross_mul x y H). reflexivity. Qed.

(* Tactic: given a hypothesis H : a == b, try to rewrite any occurrence
    of the Z-level cross-multiplied products arising from [Qnum]/[QDen]
    in the goal. This automates the repetitive pattern-matching and
    rewriting boilerplate we use throughout the Bell mechanisation. *)
Ltac rewrite_Qeq_in_goal :=
   repeat match goal with
   | [ H: ?x == ?y |- context[ (Qnum ?x * QDen ?y)%Z ] ] =>
         rewrite (Qeq_cross_mul x y H)
   | [ H: ?x == ?y |- context[ (Qnum ?y * QDen ?x)%Z ] ] =>
         rewrite <- (Qeq_cross_mul x y H)
   | [ H: ?x == ?y |- context[ (Qnum ?x * Z.pos (Qden ?y))%Z ] ] =>
         rewrite (Qeq_cross_mul x y H)
   | [ H: ?x == ?y |- context[ (Qnum ?y * Z.pos (Qden ?x))%Z ] ] =>
         rewrite <- (Qeq_cross_mul x y H)
   | [ H: ?x == ?y |- context[ (?t * (Qnum ?x * QDen ?y))%Z ] ] =>
      rewrite (Qeq_cross_mul x y H)
   | [ H: ?x == ?y |- context[ ((Qnum ?x * QDen ?y) * ?t)%Z ] ] =>
      rewrite (Qeq_cross_mul x y H)
   | [ H: ?x == ?y |- context[ (?t * (Qnum ?x * Z.pos (Qden ?y)))%Z ] ] =>
      rewrite (Qeq_cross_mul x y H)
   | [ H: ?x == ?y |- context[ ((Qnum ?x * Z.pos (Qden ?y)) * ?t)%Z ] ] =>
      rewrite (Qeq_cross_mul x y H)
   end.

(* Rewrite all reachable Z-level cross-multiplications coming from Qeq
   hypotheses across the whole context (goal and hypotheses).  This is
   useful when many hypotheses supply Qeq evidence and the goal has
   been unfolded into Z-expressions; the tactic tries both forward and
   backward cross-multiplication orientations for each Qeq witness. *)
(* [rewrite_Qeq_everywhere] was removed: the focused [rewrite_Qeq_in_goal]
   tactic below is robust and sufficient for our mechanisation.  A
   lighter-weight 'everywhere' variant could be reintroduced later if
   strictly needed, but the current design prefers explicit, local
   application to avoid surprising rewrite attempts in hypotheses. *)
(* End of extended QHelpers.v: the [rewrite_Qeq_in_goal] tactic lets us
    push Qeq witnesses down to the Z-level products produced by QArith
    unfoldings without brittle global normalisation. *)

