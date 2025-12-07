(* Core.v — nucleus: computation is composition; cut is composition *)

Set Implicit Arguments.

Section Core.
  Variable Obj : Type.

  (* Minimal category interface. *)
  Record Cat := {
    Hom : Obj -> Obj -> Type;
    id  : forall A, Hom A A;
    comp : forall {A B C}, Hom B C -> Hom A B -> Hom A C;
    comp_id_l : forall A B (f:Hom A B), comp (id B) f = f;
    comp_id_r : forall A B (f:Hom A B), comp f (id A) = f;
    comp_assoc : forall A B C D (h:Hom C D) (g:Hom B C) (f:Hom A B),
                  comp h (comp g f) = comp (comp h g) f
  }.

  (* Programs as free-category terms over a generator graph. *)
  Variable Gen : Obj -> Obj -> Type.

  Inductive Prog : Obj -> Obj -> Type :=
  | GenOp : forall A B, Gen A B -> Prog A B
  | Id    : forall A, Prog A A
  | Seq   : forall A B C, Prog B C -> Prog A B -> Prog A C.

  (* Equational theory for categories on Prog. *)
  Inductive EqProg : forall A B, Prog A B -> Prog A B -> Prop :=
  | Eq_refl  : forall A B (p:Prog A B), EqProg p p
  | Eq_sym   : forall A B (p q:Prog A B), EqProg p q -> EqProg q p
  | Eq_trans : forall A B (p q r:Prog A B), EqProg p q -> EqProg q r -> EqProg p r
  | Eq_id_l  : forall A B (p:Prog A B), EqProg (Seq (Id B) p) p
  | Eq_id_r  : forall A B (p:Prog A B), EqProg (Seq p (Id A)) p
  | Eq_assoc : forall A B C0 D (r:Prog C0 D) (q:Prog B C0) (p:Prog A B),
                 EqProg (Seq r (Seq q p)) (Seq (Seq r q) p).

  Arguments EqProg {_ _} _ _.

  (* Interpretation of generators extends homomorphically into any category C. *)
  Variable CatC : Cat.
  Variable interp0 : forall A B, Gen A B -> Hom CatC A B.

  Fixpoint interp {A B} (p:Prog A B) : Hom CatC A B :=
    match p with
    | @GenOp _ _ g      => interp0 g
    | @Id A'            => id CatC A'
    | @Seq _ _ _ q p'   => comp CatC (interp q) (interp p')
    end.

  Theorem interp_respects :
    forall A B (p q : Prog A B), EqProg p q -> interp p = interp q.
  Proof.
    intros A B p q H; induction H.
    - reflexivity.
    - symmetry; assumption.
    - etransitivity; eauto.
    - cbn. rewrite (comp_id_l CatC); reflexivity.
    - cbn. rewrite (comp_id_r CatC); reflexivity.
    - cbn.
      change (comp CatC (interp r) (comp CatC (interp q) (interp p)) =
              comp CatC (comp CatC (interp r) (interp q)) (interp p)).
      apply (comp_assoc CatC).
  Qed.

  (* Logic layer: "cut" is sequential composition. *)
  Definition cut {A B C} (π1 : Prog B C) (π2 : Prog A B) : Prog A C := Seq π1 π2.

  Theorem cut_is_composition :
    forall A B C (π1:Prog B C) (π2:Prog A B),
      interp (cut π1 π2) = comp CatC (interp π1) (interp π2).
  Proof. reflexivity. Qed.
End Core.
