(* PhysRel.v — Concrete physics: the category of types & relations (Rel) *)

Set Implicit Arguments.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import theory.Core.

Module RelCategory.
  (* Objects are types; morphisms are binary relations as predicates. *)
  Definition Rel (A B : Type) := A -> B -> Prop.

  (* Identity relation and relational composition. *)
  Definition rel_id (A : Type) : Rel A A := fun a b => a = b.

  Definition rel_comp {A B C : Type} (R : Rel B C) (S : Rel A B) : Rel A C :=
    fun a c => exists b : B, S a b /\ R b c.

  (* Helper: convert logical equivalence into equality of propositions. *)
  Lemma iff_to_eq (P Q : Prop) : (P <-> Q) -> P = Q.
  Proof.
    intros [PQ QP]. apply propositional_extensionality; split; assumption.
  Qed.

  (* Pointwise equality of relations uses functional extensionality and propositional extensionality. *)
  Lemma rel_comp_id_l :
    forall (A B:Type) (R : Rel A B), rel_comp (@rel_id B) R = R.
  Proof.
    intros A B R. apply functional_extensionality_dep; intros a.
    apply functional_extensionality_dep; intros b. unfold rel_comp, rel_id.
    apply iff_to_eq. split.
    - intros [b' [Hab Hb'b]]. subst; assumption.
    - intros HR. exists b. split; [assumption|reflexivity].
  Qed.

  Lemma rel_comp_id_r :
    forall (A B:Type) (R : Rel A B), rel_comp R (@rel_id A) = R.
  Proof.
    intros A B R. apply functional_extensionality_dep; intros a.
    apply functional_extensionality_dep; intros b. unfold rel_comp, rel_id.
    apply iff_to_eq. split.
    - intros [a' [Haa' HR]]. subst; assumption.
    - intros HR. exists a. split; [reflexivity|assumption].
  Qed.

  Lemma rel_comp_assoc :
    forall (A B C D:Type)
           (T : Rel C D) (R : Rel B C) (S : Rel A B),
      rel_comp T (rel_comp R S) = rel_comp (rel_comp T R) S.
  Proof.
    intros _ _ _ _ _ _ _.
    apply functional_extensionality_dep; intros a.
    apply functional_extensionality_dep; intros d. unfold rel_comp.
    apply iff_to_eq. split.
    - intros [c [HRS HT]].
      destruct HRS as [b [HS HR]].
      exists b. split; [assumption| exists c; split; assumption].
    - intros [b [HS HTR]].
      destruct HTR as [c [HR HT]].
      exists c. split; [exists b; split; assumption | assumption].
  Qed.

  Definition RelCat : Cat Type :=
    @Build_Cat Type Rel
      rel_id
      (fun A B C => @rel_comp A B C)
      (fun A B (f:Rel A B) => @rel_comp_id_l A B f)
      (fun A B (f:Rel A B) => @rel_comp_id_r A B f)
      (fun A B C D (h:Rel C D) (g:Rel B C) (f:Rel A B) => @rel_comp_assoc A B C D h g f).

End RelCategory.
