(** PartitionReading.v: a reading that says a grouping has been checked and
    committed, and what it entitles.

    Part I of the book ends on vouching for a grouping: sorting a pile into
    buckets and standing behind "these belong together". Parts II and III
    price any yes-or-no reading. This file attaches the reading to a
    partition.

    The pile is a finite list of items. A grouping is a bucket label for
    each item; its partition is "same label" (a partition in the sense of
    NecTPartition.v [pr_grouping_partition]). The data is a key for each
    item, and a grouping is sound for a key when two items it puts in one
    bucket have the same key. One grouping refines another when every
    bucket of the first sits inside a bucket of the second.

    The bucket machine. Its base move SET replaces the key (and throws away
    every check and commitment made against the old one) for nothing.
    CHECK g passes when g is sound for the current key and writes g in a
    table; COMMIT g passes when the table holds a grouping with the same
    partition as g, and puts g in the channel; CERTIFY passes when the
    channel holds a grouping, and records it with the key it was checked
    against. Each of the three costs 1; a failing one traps, and a trapped
    machine only pays. The reading for a grouping g is: the record holds a
    grouping with the same partition as g.

      pr_reads_structural      the reading sees a grouping only through its
                               partition: relabelling the buckets changes
                               nothing.
      pr_entitled_iff_refines  over every key, soundness of g gives soundness
                               of h exactly when h refines g.
      pr_reading_entitles      on every run from a clean start, if the reading
                               for g is up then g is sound for the key it was
                               checked against, and so is every grouping that
                               refines g;
      pr_reading_entitles_only and no grouping that fails to refine g is
                               entitled by it: there is a key for which g is
                               sound and that grouping is not.
      pr_toll, pr_reading_costs_three
                               the bucket machine pays the toll, and a raised
                               reading from a clean start has cost at least 3.

    Dependencies: ThieleComplete.v (the machine record and the toll) and
    NecTPartition.v. No axioms, no Admitted. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.
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

(* ================================================================= *)
(* The grouping and its partition.                                    *)
(* ================================================================= *)

Theorem pr_grouping_partition : forall g : grouping,
  is_partition X (blocks_of X (fun x y => g x = g y)).
Proof.
  intro g. apply nec_t_blocks_of_equiv_partition.
  split; [| split]; intros; congruence.
Qed.

Lemma same_part_sym : forall g g', same_part g g' -> same_part g' g.
Proof. intros g g' H x y Hx Hy. symmetry. apply H; assumption. Qed.

Lemma same_part_trans : forall g g' g'', same_part g g' -> same_part g' g'' -> same_part g g''.
Proof.
  intros g g' g'' H1 H2 x y Hx Hy. rewrite (H1 x y Hx Hy). apply H2; assumption.
Qed.

Lemma sound_same_part : forall k g g', same_part g g' -> sound k g -> sound k g'.
Proof.
  intros k g g' Hs Hg x y Hx Hy E. apply Hg; [assumption | assumption |].
  apply (Hs x y Hx Hy). exact E.
Qed.

Lemma sound_refines : forall k g h, refines h g -> sound k g -> sound k h.
Proof. intros k g h Hr Hg x y Hx Hy E. apply Hg; auto. Qed.

(* Over every key, soundness of g gives soundness of h exactly when h
   refines g. *)
Theorem pr_entitled_iff_refines : forall g h : grouping,
  (forall k : key, sound k g -> sound k h) <-> refines h g.
Proof.
  intros g h. split.
  - intro H. apply (H g). intros x y _ _ E. exact E.
  - intros Hr k Hg. exact (sound_refines k g h Hr Hg).
Qed.

(* ================================================================= *)
(* The checks, decided.                                               *)
(* ================================================================= *)

Definition pairs_ok (p : X -> X -> bool) : bool :=
  forallb (fun x => forallb (fun y => p x y) items) items.

Lemma pairs_ok_iff : forall p,
  pairs_ok p = true <-> forall x y, In x items -> In y items -> p x y = true.
Proof.
  intro p. unfold pairs_ok. rewrite forallb_forall. split.
  - intros H x y Hx Hy. specialize (H x Hx). rewrite forallb_forall in H. auto.
  - intros H x Hx. rewrite forallb_forall. intros y Hy. auto.
Qed.

Definition sound_b (k : key) (g : grouping) : bool :=
  pairs_ok (fun x y => negb (Nat.eqb (g x) (g y)) || Nat.eqb (k x) (k y)).

Lemma sound_b_iff : forall k g, sound_b k g = true <-> sound k g.
Proof.
  intros k g. unfold sound_b. rewrite pairs_ok_iff. split.
  - intros H x y Hx Hy E. specialize (H x y Hx Hy). simpl in H.
    apply Nat.eqb_eq in E. rewrite E in H. simpl in H. apply Nat.eqb_eq, H.
  - intros H x y Hx Hy. destruct (Nat.eqb (g x) (g y)) eqn:E; simpl; [| reflexivity].
    apply Nat.eqb_eq. apply H; auto. apply Nat.eqb_eq, E.
Qed.

Definition same_part_b (g g' : grouping) : bool :=
  pairs_ok (fun x y => Bool.eqb (Nat.eqb (g x) (g y)) (Nat.eqb (g' x) (g' y))).

Lemma same_part_b_iff : forall g g', same_part_b g g' = true <-> same_part g g'.
Proof.
  intros g g'. unfold same_part_b. rewrite pairs_ok_iff. split.
  - intros H x y Hx Hy. specialize (H x y Hx Hy). apply Bool.eqb_prop in H.
    rewrite <- !Nat.eqb_eq. rewrite H. reflexivity.
  - intros H x y Hx Hy. specialize (H x y Hx Hy).
    destruct (Nat.eqb (g x) (g y)) eqn:E1, (Nat.eqb (g' x) (g' y)) eqn:E2; try reflexivity.
    + apply Nat.eqb_eq in E1. apply H in E1. apply Nat.eqb_eq in E1. congruence.
    + apply Nat.eqb_eq in E2. apply H in E2. apply Nat.eqb_eq in E2. congruence.
Qed.

(* ================================================================= *)
(* The bucket machine.                                                *)
(* ================================================================= *)

Record pstate : Type := mk_ps {
  p_key : key;
  p_table : list grouping;
  p_chan : option grouping;
  p_cert : option (grouping * key);
  p_err : bool;
  p_led : nat
}.

Inductive pmove : Type :=
| PSET (k : key)
| PCHECK (g : grouping)
| PCOMMIT (g : grouping)
| PCERTIFY.

Definition p_cost (m : pmove) : nat := match m with PSET _ => 0 | _ => 1 end.

Definition p_flag (s : pstate) : bool := match p_cert s with Some _ => true | None => false end.

Definition p_trap (s : pstate) : pstate :=
  mk_ps (p_key s) (p_table s) (p_chan s) (p_cert s) true (S (p_led s)).

Definition p_step (s : pstate) (m : pmove) : pstate :=
  if p_err s then mk_ps (p_key s) (p_table s) (p_chan s) (p_cert s) true (p_led s + p_cost m)
  else match m with
  | PSET k => mk_ps k [] None (p_cert s) false (p_led s)
  | PCHECK g =>
      if sound_b (p_key s) g
      then mk_ps (p_key s) (g :: p_table s) (p_chan s) (p_cert s) false (S (p_led s))
      else p_trap s
  | PCOMMIT g =>
      if existsb (same_part_b g) (p_table s)
      then mk_ps (p_key s) (p_table s) (Some g) (p_cert s) false (S (p_led s))
      else p_trap s
  | PCERTIFY =>
      match p_chan s with
      | Some g =>
          match p_cert s with
          | Some c => mk_ps (p_key s) (p_table s) (p_chan s) (Some c) false (S (p_led s))
          | None => mk_ps (p_key s) (p_table s) (p_chan s) (Some (g, p_key s)) false (S (p_led s))
          end
      | None => p_trap s
      end
  end.

Definition pr_machine : T.machine := T.mk_machine pstate pmove p_step p_cost p_flag.

Definition prun (tr : list pmove) (s : pstate) : pstate := T.run pr_machine tr s.

Definition p_clean (s : pstate) : Prop :=
  p_table s = [] /\ p_chan s = None /\ p_cert s = None /\ p_err s = false.

(* The reading for a grouping g: the record holds a grouping with g's
   partition. *)
Definition pr_reads (g : grouping) (s : pstate) : Prop :=
  exists c k, p_cert s = Some (c, k) /\ same_part c g.

(* ================================================================= *)
(* Results.                                                           *)
(* ================================================================= *)

Theorem pr_reads_structural : forall g g' s,
  same_part g g' -> (pr_reads g s <-> pr_reads g' s).
Proof.
  intros g g' s H. split; intros [c [k [Hc Hs]]]; exists c, k; split; auto.
  - exact (same_part_trans _ _ _ Hs H).
  - exact (same_part_trans _ _ _ Hs (same_part_sym _ _ H)).
Qed.

(* Everything the machine holds was checked against the key it holds it
   with. *)
Definition p_inv (s : pstate) : Prop :=
  (forall g, In g (p_table s) -> sound (p_key s) g) /\
  (forall g, p_chan s = Some g -> sound (p_key s) g) /\
  (forall c k, p_cert s = Some (c, k) -> sound k c).

Lemma p_inv_step : forall s m, p_inv s -> p_inv (p_step s m).
Proof.
  intros s m [Ht [Hc Hr]]. unfold p_step.
  destruct (p_err s); [split; [| split]; simpl; assumption |].
  destruct m as [k | g | g |].
  - split; [| split]; simpl.
    + intros g [].
    + intros g E; discriminate.
    + exact Hr.
  - destruct (sound_b (p_key s) g) eqn:E.
    + split; [| split]; simpl; try assumption.
      intros g' [<- | Hin]; [apply sound_b_iff, E | apply Ht, Hin].
    + split; [| split]; simpl; assumption.
  - destruct (existsb (same_part_b g) (p_table s)) eqn:E.
    + split; [| split]; simpl; try assumption.
      intros g' Eg. injection Eg as <-. apply existsb_exists in E.
      destruct E as [c [Hin Hsp]]. apply same_part_b_iff in Hsp.
      apply (sound_same_part _ c g); [apply same_part_sym, Hsp | apply Ht, Hin].
    + split; [| split]; simpl; assumption.
  - destruct (p_chan s) as [g |] eqn:Ech; [destruct (p_cert s) as [c |] eqn:Ecert |].
    + split; [| split]; simpl; intros; try (apply Hc; congruence);
        try (apply Hr; congruence); try (apply Ht; assumption).
    + split; [| split]; simpl; intros; try (apply Hc; congruence);
        try (apply Ht; assumption).
      match goal with E : Some _ = Some _ |- _ => injection E as <- <- end.
      apply Hc. reflexivity.
    + unfold p_trap. split; [| split]; simpl; intros; try (apply Ht; assumption);
        try congruence; apply Hr; assumption.
Qed.

Lemma p_inv_run : forall tr s, p_inv s -> p_inv (prun tr s).
Proof.
  induction tr as [| m tr IH]; intros s H; [exact H |].
  unfold prun. simpl. apply IH, p_inv_step, H.
Qed.

Lemma p_inv_clean : forall s, p_clean s -> p_inv s.
Proof.
  intros s [Ht [Hc [Hr _]]]. split; [| split].
  - rewrite Ht. intros g [].
  - rewrite Hc. discriminate.
  - rewrite Hr. discriminate.
Qed.

(* A raised reading entitles every grouping that refines it. *)
Theorem pr_reading_entitles : forall s0 tr g,
  p_clean s0 -> pr_reads g (prun tr s0) ->
  exists c k, p_cert (prun tr s0) = Some (c, k) /\ sound k g /\
    forall h, refines h g -> sound k h.
Proof.
  intros s0 tr g H0 [c [k [Hc Hs]]].
  pose proof (p_inv_run tr s0 (p_inv_clean s0 H0)) as [_ [_ Hr]].
  assert (Hg : sound k g) by exact (sound_same_part k c g Hs (Hr c k Hc)).
  exists c, k. split; [exact Hc |]. split; [exact Hg |].
  intros h Hh. exact (sound_refines k g h Hh Hg).
Qed.

(* And it entitles nothing else: a grouping that does not refine g has a
   key for which g is sound and it is not. *)
Theorem pr_reading_entitles_only : forall g h,
  ~ refines h g -> exists k, sound k g /\ ~ sound k h.
Proof.
  intros g h Hn. exists g. split.
  - intros x y _ _ E. exact E.
  - intro H. apply Hn. exact H.
Qed.

(* The toll: a step that raises the record costs at least 1. *)
Theorem pr_toll : T.thiele_machine pr_machine.
Proof.
  intros s m H0 H1. simpl in *. unfold p_step in H1.
  destruct (p_err s); [unfold p_flag in *; simpl in H1; congruence |].
  destruct m; simpl; try lia.
  unfold p_flag in *. simpl in H1. congruence.
Qed.

(* A raised reading from a clean start cost at least three. *)
Definition p_pot (s : pstate) : nat :=
  match p_cert s with
  | Some _ => 3
  | None => (match p_table s with [] => 0 | _ => 1 end) +
            (match p_chan s with None => 0 | Some _ => 1 end)
  end.

Definition p_cinv (s0 s : pstate) : Prop :=
  (p_chan s <> None -> p_table s <> []) /\ p_led s >= p_led s0 + p_pot s.

Lemma p_cinv_step : forall s0 s m, p_cinv s0 s -> p_cinv s0 (p_step s m).
Proof.
  intros s0 s m [Hct Hl]. unfold p_cinv, p_step, p_pot in *.
  destruct (p_err s).
  { simpl. split; [exact Hct |].
    destruct (p_cert s), (p_table s), (p_chan s); simpl in *; lia. }
  destruct m as [k | g | g |]; simpl.
  - split; [congruence |]. destruct (p_cert s), (p_table s), (p_chan s); simpl in *; lia.
  - destruct (sound_b (p_key s) g); unfold p_trap; simpl.
    + split; [discriminate |].
      destruct (p_cert s), (p_table s), (p_chan s); simpl in *; lia.
    + split; [exact Hct |].
      destruct (p_cert s), (p_table s), (p_chan s); simpl in *; lia.
  - destruct (existsb (same_part_b g) (p_table s)) eqn:E; unfold p_trap; simpl.
    + assert (Hne : p_table s <> []) by (intro Z; rewrite Z in E; discriminate).
      split; [intros _; exact Hne |].
      destruct (p_cert s), (p_table s), (p_chan s); simpl in *; try lia; congruence.
    + split; [exact Hct |].
      destruct (p_cert s), (p_table s), (p_chan s); simpl in *; lia.
  - destruct (p_chan s) as [g |] eqn:Ech; [destruct (p_cert s) as [c |] eqn:Ecert |];
      unfold p_trap; simpl.
    + split; [exact Hct | lia].
    + split; [exact Hct |].
      assert (Hne : p_table s <> []) by (apply Hct; discriminate).
      destruct (p_table s); [congruence |]. simpl in Hl. lia.
    + split; [rewrite Ech; exact Hct |].
      rewrite Ech. destruct (p_cert s), (p_table s); simpl in *; lia.
Qed.

Theorem pr_reading_costs_three : forall s0 tr,
  p_clean s0 -> p_flag (prun tr s0) = true -> p_led (prun tr s0) >= p_led s0 + 3.
Proof.
  intros s0 tr H0 Hf.
  assert (Hrun : forall tr s, p_cinv s0 s -> p_cinv s0 (prun tr s)).
  { induction tr0 as [| m tr0 IH]; intros s H; [exact H |].
    unfold prun. simpl. apply IH, p_cinv_step, H. }
  assert (Hc0 : p_cinv s0 s0).
  { destruct H0 as [Ht [Hc [Hr _]]]. split; [rewrite Hc; congruence |].
    unfold p_pot. rewrite Hr, Ht, Hc. lia. }
  destruct (Hrun tr s0 Hc0) as [_ Hl]. unfold p_flag, p_pot in *.
  destruct (p_cert (prun tr s0)); [lia | discriminate].
Qed.

End Pile.

Print Assumptions pr_grouping_partition.
Print Assumptions pr_entitled_iff_refines.
Print Assumptions pr_reads_structural.
Print Assumptions pr_reading_entitles.
Print Assumptions pr_reading_entitles_only.
Print Assumptions pr_toll.
Print Assumptions pr_reading_costs_three.
