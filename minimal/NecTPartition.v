(** NecTPartition.v: sameness and sorting are one object (Theorem
    thm:equiv-partition of the book), proved, with each hypothesis of a
    partition shown necessary.

    A partition of a type X is a collection of blocks (sets of X) such that
    every block has a member, every member of X lies in a block, two blocks
    that share a member are the same block, and a block is determined by its
    members. An equivalence relation is reflexive, symmetric and transitive.

      [nec_t_rel_of_partition_equiv]  the relation "x and y lie in a common
        block" of a partition is an equivalence relation.
      [nec_t_blocks_of_equiv_partition]  the classes of an equivalence
        relation form a partition.
      [nec_t_rel_round_trip], [nec_t_blocks_round_trip]  the two
        constructions undo each other.
      [nec_t_nonempty_needed], [nec_t_cover_needed], [nec_t_disjoint_needed]
        drop one hypothesis of a partition and one of the claims fails: with
        an empty block the round trip loses it, with a point in no block the
        relation is not reflexive, with overlapping blocks it is not
        transitive.
    "Determined by its members" is how a set is read in this file (two sets
    with the same members are the same block); it is not shown necessary,
    because a counterexample would need two propositionally equal sets that
    are different terms, which Coq cannot separate. *)

(* SCOPE NOTE: standalone proof scope. Sets, blocks and equivalence relations
   over an arbitrary type; no machine is involved. *)

From Coq Require Import Setoid.

Section Partition.

Variable X : Type.

Definition set := X -> Prop.
Definition set_eq (A B : set) : Prop := forall x, A x <-> B x.

Definition is_equiv (R : X -> X -> Prop) : Prop :=
  (forall x, R x x) /\ (forall x y, R x y -> R y x) /\
  (forall x y z, R x y -> R y z -> R x z).

Definition is_partition (P : set -> Prop) : Prop :=
  (forall B, P B -> exists x, B x) /\
  (forall x, exists B, P B /\ B x) /\
  (forall B C x, P B -> P C -> B x -> C x -> set_eq B C) /\
  (forall B C, set_eq B C -> P B -> P C).

Definition rel_of (P : set -> Prop) (x y : X) : Prop := exists B, P B /\ B x /\ B y.

Definition blocks_of (R : X -> X -> Prop) : set -> Prop :=
  fun B => exists x, set_eq B (R x).

Theorem nec_t_rel_of_partition_equiv : forall P, is_partition P -> is_equiv (rel_of P).
Proof.
  intros P [_ [Hcov [Hdis _]]]. split; [| split].
  - intro x. destruct (Hcov x) as [B [HB Hx]]. exists B. auto.
  - intros x y [B [HB [Hx Hy]]]. exists B. auto.
  - intros x y z [B [HB [Hx Hy]]] [C [HC [Hy' Hz]]].
    exists B. split; [exact HB |]. split; [exact Hx |].
    apply (Hdis B C y HB HC Hy Hy'). exact Hz.
Qed.

Theorem nec_t_blocks_of_equiv_partition : forall R, is_equiv R -> is_partition (blocks_of R).
Proof.
  intros R [Hr [Hs Ht]]. split; [| split; [| split]].
  - intros B [x Hx]. exists x. apply Hx. apply Hr.
  - intro x. exists (R x). split; [exists x; intro y; tauto | apply Hr].
  - intros B C x [u Hu] [v Hv] HBx HCx y.
    assert (Hux : R u x) by (apply Hu; exact HBx).
    assert (Hvx : R v x) by (apply Hv; exact HCx).
    rewrite (Hu y), (Hv y). split; intro H.
    + apply Ht with x; [exact Hvx |]. apply Ht with u; [apply Hs; exact Hux | exact H].
    + apply Ht with x; [exact Hux |]. apply Ht with v; [apply Hs; exact Hvx | exact H].
  - intros B C Heq [x Hx]. exists x. intro y. rewrite <- (Hx y). symmetry. apply Heq.
Qed.

Theorem nec_t_rel_round_trip : forall R, is_equiv R ->
  forall x y, rel_of (blocks_of R) x y <-> R x y.
Proof.
  intros R [Hr [Hs Ht]] x y. split.
  - intros [B [[u Hu] [Hx Hy]]].
    apply Hu in Hx. apply Hu in Hy.
    apply Ht with u; [apply Hs; exact Hx | exact Hy].
  - intro H. exists (R x). split; [exists x; intro z; tauto |]. split; [apply Hr | exact H].
Qed.

Theorem nec_t_blocks_round_trip : forall P, is_partition P ->
  forall B, blocks_of (rel_of P) B <-> P B.
Proof.
  intros P HP B. destruct HP as [Hne [Hcov [Hdis Hext]]]. split.
  - intros [x Hx]. destruct (Hcov x) as [C [HC Hxc]].
    apply (Hext C B); [| exact HC].
    intro y. split.
    + intro Hy. apply Hx. exists C. auto.
    + intro Hy. apply Hx in Hy. destruct Hy as [D [HD [Hxd Hyd]]].
      assert (Hcd := Hdis C D x HC HD Hxc Hxd y). apply Hcd. exact Hyd.
  - intro HB. destruct (Hne B HB) as [x Hx]. exists x. intro y. split.
    + intro Hy. exists B. auto.
    + intros [D [HD [Hxd Hyd]]]. assert (Hbd := Hdis B D x HB HD Hx Hxd y).
      apply Hbd. exact Hyd.
Qed.

End Partition.

(* ----------------------------------------------------------------- *)
(* Each hypothesis of a partition is needed.                          *)
(* ----------------------------------------------------------------- *)

(* An empty block: the round trip loses it. *)
Theorem nec_t_nonempty_needed : exists (X : Type) (P : set X -> Prop),
  (forall x, exists B, P B /\ B x) /\
  (forall B C x, P B -> P C -> B x -> C x -> set_eq X B C) /\
  (forall B C, set_eq X B C -> P B -> P C) /\
  ~ (forall B, blocks_of X (rel_of X P) B <-> P B).
Proof.
  exists unit, (fun B => set_eq unit B (fun _ => False) \/ set_eq unit B (fun _ => True)).
  split; [| split; [| split]].
  - intro x. exists (fun _ => True). split; [right; intro; tauto | exact I].
  - intros B C x [HB | HB] [HC | HC] Hb Hc y.
    + apply HB in Hb. contradiction.
    + apply HB in Hb. contradiction.
    + apply HC in Hc. contradiction.
    + rewrite (HB y), (HC y). tauto.
  - intros B C Heq [HB | HB]; [left | right]; intro y; rewrite <- (HB y); symmetry; apply Heq.
  - intro H.
    destruct (proj2 (H (fun _ => False)) (or_introl (fun y => iff_refl _))) as [x Hx].
    assert (Hrel : rel_of unit
                     (fun B => set_eq unit B (fun _ => False) \/ set_eq unit B (fun _ => True)) x x).
    { exists (fun _ => True). split; [right; intro; tauto |]. split; exact I. }
    exact (proj2 (Hx x) Hrel).
Qed.

(* A point in no block: the relation is not reflexive. *)
Theorem nec_t_cover_needed : exists (X : Type) (P : set X -> Prop),
  (forall B, P B -> exists x, B x) /\
  (forall B C x, P B -> P C -> B x -> C x -> set_eq X B C) /\
  (forall B C, set_eq X B C -> P B -> P C) /\
  ~ is_equiv X (rel_of X P).
Proof.
  exists unit, (fun _ => False). split; [| split; [| split]].
  - intros B H. contradiction.
  - intros B C x H. contradiction.
  - intros B C _ H. exact H.
  - intros [Hr _]. destruct (Hr tt) as [B [HB _]]. exact HB.
Qed.

Inductive three : Type := Za | Zb | Zc.

Definition Pov : set three -> Prop :=
  fun B => set_eq three B (fun x => x = Za \/ x = Zb) \/
           set_eq three B (fun x => x = Zb \/ x = Zc).

(* Two blocks that overlap: the relation is not transitive. *)
Theorem nec_t_disjoint_needed : exists (X : Type) (P : set X -> Prop),
  (forall B, P B -> exists x, B x) /\
  (forall x, exists B, P B /\ B x) /\
  (forall B C, set_eq X B C -> P B -> P C) /\
  ~ is_equiv X (rel_of X P).
Proof.
  exists three, Pov. unfold Pov.
  split; [| split; [| split]].
  - intros B [HB | HB]; [exists Za; apply HB; left; reflexivity | exists Zb; apply HB; left; reflexivity].
  - intro x. destruct x.
    + exists (fun x => x = Za \/ x = Zb). split; [left; intro; tauto | left; reflexivity].
    + exists (fun x => x = Za \/ x = Zb). split; [left; intro; tauto | right; reflexivity].
    + exists (fun x => x = Zb \/ x = Zc). split; [right; intro; tauto | right; reflexivity].
  - intros B C Heq [HB | HB]; [left | right]; intro y; rewrite <- (HB y); symmetry; apply Heq.
  - intros [_ [_ Ht]].
    assert (H1 : rel_of three Pov Za Zb).
    { exists (fun x => x = Za \/ x = Zb). split; [left; intro; tauto |]. split; [left; reflexivity | right; reflexivity]. }
    assert (H2 : rel_of three Pov Zb Zc).
    { exists (fun x => x = Zb \/ x = Zc). split; [right; intro; tauto |]. split; [left; reflexivity | right; reflexivity]. }
    destruct (Ht _ _ _ H1 H2) as [B [[HB | HB] [Ha Hc]]].
    + apply HB in Hc. destruct Hc as [Hc | Hc]; discriminate Hc.
    + apply HB in Ha. destruct Ha as [Ha | Ha]; discriminate Ha.
Qed.

Print Assumptions nec_t_rel_of_partition_equiv.
Print Assumptions nec_t_blocks_of_equiv_partition.
Print Assumptions nec_t_rel_round_trip.
Print Assumptions nec_t_blocks_round_trip.
Print Assumptions nec_t_nonempty_needed.
Print Assumptions nec_t_cover_needed.
Print Assumptions nec_t_disjoint_needed.
