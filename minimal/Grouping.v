(* SCOPE NOTE: standalone proof scope. groupings, keys and refinement are
   stated over a pile of items alone and do not import the record system. *)
(** Grouping.v: what standing behind a grouping licenses.

    The pile is a finite list of items. A grouping is a bucket label for
    each item; its partition is "same label". The data is a key for each
    item, and a grouping is sound for a key when two items it puts in one
    bucket have the same key. One grouping refines another when every
    bucket of the first sits inside a bucket of the second.

      grouping_partition           the classes of "same label" form a
                                   partition (NecTPartition.v).
      grouping_sound_structural    soundness sees a grouping only through
                                   its partition: relabelling the buckets
                                   changes nothing.
      sound_transfers_iff_refines  over every key, soundness of g gives
                                   soundness of h exactly when h refines g.
      sound_only_for_refinements   a grouping that does not refine g has a
                                   key for which g is sound and it is not.

    Dependencies: NecTPartition.v. No axioms, no Admitted. *)

From Coq Require Import List.
Import ListNotations.
Require Import Minimal.NecTPartition.

Section Pile.

Variable X : Type.
Variable items : list X.

Definition grouping : Type := X -> nat.
Definition key : Type := X -> nat.

(* Two items g puts in one bucket have the same key. *)
Definition sound (k : key) (g : grouping) : Prop :=
  forall x y, In x items -> In y items -> g x = g y -> k x = k y.

(* Every bucket of h sits inside a bucket of g. *)
Definition refines (h g : grouping) : Prop :=
  forall x y, In x items -> In y items -> h x = h y -> g x = g y.

(* g and g' have the same partition of the pile. *)
Definition same_part (g g' : grouping) : Prop :=
  forall x y, In x items -> In y items -> (g x = g y <-> g' x = g' y).

Theorem grouping_partition : forall g : grouping,
  is_partition X (blocks_of X (fun x y => g x = g y)).
Proof.
  intro g. apply nec_t_blocks_of_equiv_partition.
  split; [| split]; intros; congruence.
Qed.

(* Soundness for a key depends on a grouping only through its partition. *)
Theorem grouping_sound_structural : forall k g g',
  same_part g g' -> (sound k g <-> sound k g').
Proof.
  intros k g g' Hs. split.
  - intros Hg x y Hx Hy E. apply Hg; [assumption | assumption |].
    apply (Hs x y Hx Hy). exact E.
  - intros Hg x y Hx Hy E. apply Hg; [assumption | assumption |].
    apply (Hs x y Hx Hy). exact E.
Qed.

Lemma sound_refines : forall k g h, refines h g -> sound k g -> sound k h.
Proof. intros k g h Hr Hg x y Hx Hy E. apply Hg; auto. Qed.

(* Over every key, soundness of g gives soundness of h exactly when h
   refines g. *)
Theorem sound_transfers_iff_refines : forall g h : grouping,
  (forall k : key, sound k g -> sound k h) <-> refines h g.
Proof.
  intros g h. split.
  - intro H. apply (H g). intros x y _ _ E. exact E.
  - intros Hr k Hg. exact (sound_refines k g h Hr Hg).
Qed.

(* A grouping that does not refine g has a key for which g is sound and it
   is not. *)
Theorem sound_only_for_refinements : forall g h,
  ~ refines h g -> exists k, sound k g /\ ~ sound k h.
Proof.
  intros g h Hn. exists g. split.
  - intros x y _ _ E. exact E.
  - intro H. apply Hn. exact H.
Qed.

End Pile.

Print Assumptions grouping_partition.
Print Assumptions grouping_sound_structural.
Print Assumptions sound_transfers_iff_refines.
Print Assumptions sound_only_for_refinements.
