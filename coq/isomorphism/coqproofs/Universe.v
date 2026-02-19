(* Universe.v - The Categorical Formulation of the Thiele Machine *)
Require Import Coq.Lists.List.
Require Import Arith.
Require Import Lia.
Import ListNotations.



(** [list_sum_app]: formal specification. *)
Lemma list_sum_app : forall l1 l2, list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
Proof.
  intros l1 l2. induction l1 as [|h t IH]; simpl; lia.
Qed.

(* --- Section 2: The Category of Physics (C_phys) --- *)

Definition C_phys_Obj := list nat. (* Objects are universe states *)

(* A local physical interaction: two particles collide and exchange momentum. *)
Inductive Interaction (s1 s2 : C_phys_Obj) : Prop :=
| collision : forall i j l1 l2 l3,
    i > 0 -> (* A particle must have momentum to give it away *)
    s1 = l1 ++ [i] ++ l2 ++ [j] ++ l3 ->
    s2 = l1 ++ [i-1] ++ l2 ++ [j+1] ++ l3 ->
    Interaction s1 s2.

(* A path is a sequence of interactions. This forms the arrows of our category. *)
Inductive Path : C_phys_Obj -> C_phys_Obj -> Prop :=
| Path_refl : forall s, Path s s
| Path_step : forall s1 s2 s3, Path s1 s2 -> Interaction s2 s3 -> Path s1 s3.

Definition C_phys_Hom := Path.
Definition C_phys_id := Path_refl.

(* Composition of paths is appending them. *)
Fixpoint C_phys_comp {a b c : C_phys_Obj} (p1 : Path a b) (p2 : Path b c) : Path a c :=
  match p2 in Path b' c' return Path a b' -> Path a c' with
  | Path_refl _ => fun p1' => p1'
  | Path_step b' d e p_bc inter_ce => fun p1' => Path_step a d e (C_phys_comp p1' p_bc) inter_ce
  end p1.

(* --- Section 3: The Category of Logic (C_logic) --- *)

Definition C_logic_Obj := nat. (* Objects are total momentum values *)

Definition C_logic_Hom (m1 m2 : C_logic_Obj) : Prop := m1 = m2.
Definition C_logic_id (m : C_logic_Obj) : C_logic_Hom m m := eq_refl.
Definition C_logic_comp {a b c} (f : C_logic_Hom a b) (g : C_logic_Hom b c) : C_logic_Hom a c :=
  eq_trans f g.

(* --- Section 4: The Functor F (Observation/Measurement) --- *)

Definition F_obj (s : C_phys_Obj) : C_logic_Obj := list_sum s.

(* The functor's action on arrows: it maps a physical path to a proof of momentum conservation. *)
(** [F_hom_proof]: formal specification. *)
Lemma F_hom_proof : forall s1 s2, Path s1 s2 -> F_obj s1 = F_obj s2.
Proof.
  intros s1 s2 Hpath.
  induction Hpath.
  - (* Path_refl *) reflexivity.
  - (* Path_step *)
    apply eq_trans with (y := list_sum s2).
    + exact IHHpath.
    + destruct H as [i j l1 l2 l3 H_i_pos Hs1 Hs2].
      subst.
      repeat rewrite list_sum_app. simpl. lia.
Qed.

Definition F_hom {s1 s2} (p : Path s1 s2) : C_logic_Hom (F_obj s1) (F_obj s2) :=
  F_hom_proof s1 s2 p.

(* --- Section 5: The Grand Unified Theorem --- *)

(* The final statement: The act of observation (F) is a valid, structure-preserving
   map from the world of physics to the world of logic. *)

(** [Thiele_Functor_Is_Sound]: formal specification. *)
Theorem Thiele_Functor_Is_Sound :
  forall (s1 s2 : C_phys_Obj) (p : C_phys_Hom s1 s2),
    C_logic_Hom (F_obj s1) (F_obj s2).
Proof.
  intros s1 s2 p.
  exact (F_hom p).
Qed.