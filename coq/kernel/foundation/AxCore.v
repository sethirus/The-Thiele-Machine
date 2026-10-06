(** AxCore: the record axis, its toll, and the two-point order as the
    one-bit special case.

    The record of a machine is not one bit. It is a position in an ordered
    space, any preorder at all, with as many points as you like. Certification
    is the two-point space false < true. This file states the toll over an
    arbitrary preorder and proves it, then shows that the book's
    certification floor is the two-point instance.

    The order is given by a Boolean test, the way the existing records are
    ([GrowingRecordCore]); a preorder is all that the toll needs.

    Results (every one closed under the global context):

      ax_floor_iff_a2         the floor holds from every start exactly when
                              every step that leaves the down-set of the
                              current record pays at least 1.  No growth, no
                              antisymmetry, no finiteness is used.
      ax_cost_ge_exits        the cost of a run is at least the number of its
                              steps that leave the down-set; the bound is
                              attained for every count.
      ax_exit_is_strict_rise  on a growing record over a partial order, "leaves
                              the down-set" and "rises strictly" are the same
                              step; without growth they differ.
      ax_view_a2              every threshold "a <= record" of an axis that
                              pays its toll is a one-bit certification system
                              that pays its toll.
      two_point_nfi           the book's certification floor, derived from the
                              axis theorem by taking the two-point order. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import UniversalCertificationCost.

(** * Orders given by a Boolean test *)

Record BPre (A : Type) : Type := {
  bp_leb : A -> A -> bool;
  bp_refl : forall x, bp_leb x x = true;
  bp_trans : forall x y z, bp_leb x y = true -> bp_leb y z = true ->
    bp_leb x z = true
}.

Definition bp_le {A} (P : BPre A) (x y : A) : Prop := bp_leb A P x y = true.

Lemma bp_le_refl : forall {A} (P : BPre A) x, bp_le P x x.
Proof. intros A [leb Hrefl Htrans] x. exact (Hrefl x). Qed.

Lemma bp_le_trans : forall {A} (P : BPre A) x y z,
  bp_le P x y -> bp_le P y z -> bp_le P x z.
Proof. intros A [leb Hrefl Htrans] x y z. exact (Htrans x y z). Qed.

(** Antisymmetry turns a preorder into a partial order.  It is a separate
    hypothesis because most of the toll does not use it. *)
Definition bp_antisym {A} (P : BPre A) : Prop :=
  forall x y, bp_le P x y -> bp_le P y x -> x = y.

(** The two-point order false < true. *)
Definition two_pre : BPre bool.
Proof.
  refine {| bp_leb := implb |}.
  - intros []; reflexivity.
  - intros [] [] []; simpl; auto.
Defined.

Lemma two_le : forall x y, bp_le two_pre x y <-> (x = true -> y = true).
Proof.
  intros [] []; unfold bp_le; simpl; split; intro H; auto; try discriminate;
    try (apply H; reflexivity).
Qed.

Lemma two_antisym : bp_antisym two_pre.
Proof.
  intros x y H1 H2. unfold bp_le in *.
  destruct x, y; simpl in *; try reflexivity; discriminate.
Qed.

(** The natural numbers as an infinite chain. *)
Definition nat_pre : BPre nat.
Proof.
  refine {| bp_leb := Nat.leb |}.
  - intro x. apply Nat.leb_refl.
  - intros x y z. rewrite !Nat.leb_le. apply Nat.le_trans.
Defined.

Lemma nat_pre_le : forall x y, bp_le nat_pre x y <-> x <= y.
Proof. intros x y. unfold bp_le. simpl. apply Nat.leb_le. Qed.

(** The discrete order on a type with Boolean equality: every point is
    comparable only with itself. *)
Definition disc_pre {A} (eqb : A -> A -> bool)
    (eqb_refl : forall x, eqb x x = true)
    (eqb_trans : forall x y z, eqb x y = true -> eqb y z = true -> eqb x z = true)
    : BPre A :=
  {| bp_leb := eqb; bp_refl := eqb_refl; bp_trans := eqb_trans |}.

(** * Axis systems *)

(** The same shape as a certification system, with the one-bit reading
    replaced by a position in the order P. *)
Record AxSys (A : Type) (P : BPre A) : Type := mk_axsys {
  ax_state : Type;
  ax_instr : Type;
  ax_step : ax_state -> ax_instr -> ax_state;
  ax_cost : ax_instr -> nat;
  ax_rec : ax_state -> A
}.

Section Axis.

Variable A : Type.
Variable P : BPre A.
Variable X : AxSys A P.

Fixpoint ax_run (tr : list (ax_instr A P X)) (s : ax_state A P X) : ax_state A P X :=
  match tr with
  | [] => s
  | i :: rest => ax_run rest (ax_step A P X s i)
  end.

Fixpoint ax_total (tr : list (ax_instr A P X)) : nat :=
  match tr with
  | [] => 0
  | i :: rest => ax_cost A P X i + ax_total rest
  end.

(** A step leaves the down-set of the current record. *)
Definition ax_exits (s : ax_state A P X) (i : ax_instr A P X) : Prop :=
  ~ bp_le P (ax_rec A P X (ax_step A P X s i)) (ax_rec A P X s).

(** The toll: a step that leaves the down-set costs at least 1. *)
Definition ax_a2 : Prop :=
  forall s i, ax_exits s i -> ax_cost A P X i >= 1.

(** The floor: any run that ends outside the down-set of where it started
    costs at least 1. *)
Definition ax_floor : Prop :=
  forall tr s, ~ bp_le P (ax_rec A P X (ax_run tr s)) (ax_rec A P X s) ->
    ax_total tr >= 1.

Lemma ax_run_app : forall l1 l2 s, ax_run (l1 ++ l2) s = ax_run l2 (ax_run l1 s).
Proof. induction l1; intros; simpl; auto. Qed.

Lemma ax_total_app : forall l1 l2, ax_total (l1 ++ l2) = ax_total l1 + ax_total l2.
Proof. induction l1; intros; simpl; [auto | rewrite IHl1; lia]. Qed.

(** The floor is exactly the toll, over any preorder. *)
Theorem ax_floor_iff_a2 : ax_floor <-> ax_a2.
Proof.
  split.
  - intros Hf s i Hex. specialize (Hf [i] s). simpl in Hf.
    assert (H : ax_total [i] >= 1) by (apply Hf; exact Hex).
    simpl in H. lia.
  - intros Ha tr. induction tr as [| i rest IH]; intros s Hnot.
    + simpl in Hnot. exfalso. apply Hnot. apply bp_le_refl.
    + simpl in *. destruct (bp_leb A P (ax_rec A P X (ax_step A P X s i))
                              (ax_rec A P X s)) eqn:Hle.
      * assert (Hn : ~ bp_le P (ax_rec A P X (ax_run rest (ax_step A P X s i)))
                                (ax_rec A P X (ax_step A P X s i))).
        { intro H. apply Hnot. eapply bp_le_trans; [exact H | exact Hle]. }
        specialize (IH _ Hn). lia.
      * assert (Hex : ax_exits s i) by (unfold ax_exits, bp_le; rewrite Hle; discriminate).
        specialize (Ha s i Hex). lia.
Qed.

(** The number of steps along a run that leave the down-set. *)
Fixpoint ax_exit_count (tr : list (ax_instr A P X)) (s : ax_state A P X) : nat :=
  match tr with
  | [] => 0
  | i :: rest =>
      (if bp_leb A P (ax_rec A P X (ax_step A P X s i)) (ax_rec A P X s)
       then 0 else 1) + ax_exit_count rest (ax_step A P X s i)
  end.

(** The cost of a run is at least the number of its exits. *)
Theorem ax_cost_ge_exits : ax_a2 -> forall tr s, ax_total tr >= ax_exit_count tr s.
Proof.
  intros Ha tr. induction tr as [| i rest IH]; intro s; simpl; [lia |].
  specialize (IH (ax_step A P X s i)).
  destruct (bp_leb A P (ax_rec A P X (ax_step A P X s i)) (ax_rec A P X s)) eqn:Hle.
  - lia.
  - assert (Hex : ax_exits s i) by (unfold ax_exits, bp_le; rewrite Hle; discriminate).
    specialize (Ha s i Hex). lia.
Qed.

(** On a growing record, leaving the down-set is a strict rise. *)
Definition ax_grows : Prop :=
  forall s i, bp_le P (ax_rec A P X s) (ax_rec A P X (ax_step A P X s i)).

Definition ax_rises (s : ax_state A P X) (i : ax_instr A P X) : Prop :=
  bp_le P (ax_rec A P X s) (ax_rec A P X (ax_step A P X s i)) /\
  ~ bp_le P (ax_rec A P X (ax_step A P X s i)) (ax_rec A P X s).

Theorem ax_exit_is_strict_rise : ax_grows ->
  forall s i, ax_exits s i <-> ax_rises s i.
Proof.
  intros Hg s i. unfold ax_rises. split.
  - intro H. split; [apply Hg | exact H].
  - intros [_ H]. exact H.
Qed.

End Axis.

Arguments ax_run {A P X}.
Arguments ax_total {A P X}.
Arguments ax_exits {A P X}.
Arguments ax_a2 {A P X}.
Arguments ax_floor {A P X}.
Arguments ax_exit_count {A P X}.
Arguments ax_grows {A P X}.
Arguments ax_rises {A P X}.
Arguments ax_floor_iff_a2 {A P} X.
Arguments ax_cost_ge_exits {A P X} _ _ _.
Arguments ax_exit_is_strict_rise {A P X} _ _ _.

(** The two-point reading of a threshold: is the point a below the record? *)
Definition ax_view {A : Type} {P : BPre A} (X : AxSys A P) (a : A) : AxSys bool two_pre :=
  mk_axsys bool two_pre (ax_state A P X) (ax_instr A P X) (ax_step A P X)
    (ax_cost A P X) (fun s => bp_leb A P a (ax_rec A P X s)).

(** Every threshold of an axis that pays its toll pays its own toll. *)
Theorem ax_view_a2 : forall {A : Type} {P : BPre A} (X : AxSys A P),
  ax_a2 (X := X) -> forall a, ax_a2 (X := ax_view X a).
Proof.
  intros A P X Ha a s i Hex. apply (Ha s i). intro Hle. apply Hex.
  simpl. apply (proj2 (two_le _ _)). intro Hs. simpl in *.
  apply bp_le_trans with (y := ax_rec A P X (ax_step A P X s i));
    [exact Hs | exact Hle].
Qed.


(** * Certification as the two-point instance *)

Definition cs_axsys (CS : CertificationSystem) : AxSys bool two_pre :=
  mk_axsys bool two_pre (cs_state CS) (cs_instr CS) (cs_step CS) (cs_cost CS)
    (cs_cert CS).

Lemma cs_axsys_run : forall CS tr s,
  ax_run (X := cs_axsys CS) tr s = cs_run CS tr s.
Proof. induction tr; intros; simpl; auto. Qed.

Lemma cs_axsys_total : forall CS tr,
  ax_total (X := cs_axsys CS) tr = cs_total_cost CS tr.
Proof. induction tr; intros; simpl; auto. Qed.

(** A certification system pays the axis toll over the two-point order. *)
Theorem cs_axsys_a2 : forall CS, ax_a2 (X := cs_axsys CS).
Proof.
  intros CS s i Hex. unfold ax_exits in Hex. simpl in Hex.
  apply (cs_cert_costs CS s i).
  - destruct (cs_cert CS s) eqn:E; [| reflexivity]. exfalso. apply Hex.
    apply (proj2 (two_le _ _)). intro. destruct (cs_cert CS (cs_step CS s i)); reflexivity.
  - destruct (cs_cert CS (cs_step CS s i)) eqn:E; [reflexivity |]. exfalso.
    apply Hex. apply (proj2 (two_le _ _)). intro H. discriminate.
Qed.

(** The book's certification floor, as a corollary of the axis floor. *)
Corollary two_point_nfi :
  forall (CS : CertificationSystem) (trace : list (cs_instr CS)) (s0 : cs_state CS),
    cs_cert CS s0 = false ->
    cs_cert CS (cs_run CS trace s0) = true ->
    cs_total_cost CS trace >= 1.
Proof.
  intros CS trace s0 H0 H1.
  rewrite <- cs_axsys_total.
  apply (proj2 (ax_floor_iff_a2 (cs_axsys CS)) (cs_axsys_a2 CS) trace s0).
  simpl. rewrite cs_axsys_run. rewrite H0, H1. intro H.
  unfold bp_le in H. simpl in H. discriminate H.
Qed.

(** Conversely an axis system over the two-point order is a certification
    system, when it pays the toll. *)
Definition axsys_cs (X : AxSys bool two_pre) (H : ax_a2 (X := X)) : CertificationSystem.
Proof.
  refine (mk_cert_system (ax_state bool two_pre X) (ax_instr bool two_pre X)
    (ax_step bool two_pre X) (ax_cost bool two_pre X) (ax_rec bool two_pre X) _).
  intros s i H0 H1. apply (H s i). unfold ax_exits. intro Hle.
  unfold bp_le in Hle. simpl in Hle. rewrite H0, H1 in Hle. discriminate.
Defined.

(** The antisymmetric case: thresholds determine the record. *)
Theorem bp_thresholds_determine : forall A (P : BPre A),
  (forall u v : A, bp_le P u v -> bp_le P v u -> u = v) ->
  forall x y : A, (forall a, bp_leb A P a x = bp_leb A P a y) -> x = y.
Proof.
  intros A P Hanti x y H. apply Hanti.
  - unfold bp_le. rewrite <- (H x). apply bp_le_refl.
  - unfold bp_le. rewrite (H y). apply bp_le_refl.
Qed.

(** Without antisymmetry two distinct points can have the same thresholds. *)
Definition indiscrete_pre : BPre bool.
Proof. refine {| bp_leb := fun _ _ => true |}; reflexivity. Defined.

Theorem thresholds_fail_on_preorder :
  ~ bp_antisym indiscrete_pre /\
  (forall a, bp_leb bool indiscrete_pre a true = bp_leb bool indiscrete_pre a false) /\
  true <> false.
Proof.
  split; [| split].
  - intro H. specialize (H true false eq_refl eq_refl). discriminate.
  - intro a. reflexivity.
  - discriminate.
Qed.

Print Assumptions ax_floor_iff_a2.
Print Assumptions ax_cost_ge_exits.
Print Assumptions ax_exit_is_strict_rise.
Print Assumptions ax_view_a2.
Print Assumptions two_point_nfi.
Print Assumptions bp_thresholds_determine.
Print Assumptions thresholds_fail_on_preorder.
