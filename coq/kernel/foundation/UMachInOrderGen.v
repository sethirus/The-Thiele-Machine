(** UMachInOrderGen.v: from a chain of related (guest step, host time) pairs
    with strictly increasing host times, a single matching function f that
    is strictly increasing in the guest step.

    The simulation theorems for U and U_P state, for each guest step m,
    "there is a host time n" (a Prop existential, one per m).  A function
    f : nat -> nat with f m < f (S m) cannot be read off those separately.
    It can be built constructively (no axiom: ConstructiveEpsilon's
    epsilon_smallest is a linear search) from:

      - a decidable observation predicate D m t ("the host at time t decodes
        to the guest after m steps", with flag and ledger), implied by
      - a relation Rel m t (the simulation invariant, not necessarily
        decidable) that holds at some time for m = 0, and that, whenever
        the guest is live through step m, steps from (m, t) to (S m, t')
        with t < t'.

    f m is the least time after f (m-1) at which D m holds; the invariant
    "some Rel-time for m is >= f m" makes the next search terminate.     *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is a lemma about natural numbers (a strictly increasing matching function
   from a stepping relation) and imports only the Coq standard library. It
   is applied to U and U_P in UMachInOrderU.v and UMachInOrderUP.v. *)

From Coq Require Import Arith Lia ConstructiveEpsilon.

Section InOrder.

Variable L : nat -> Prop.
Hypothesis Ldec : forall m, {L m} + {~ L m}.
Hypothesis Lprev : forall m, L (S m) -> L m.

Variable D : nat -> nat -> Prop.
Hypothesis Ddec : forall m t, {D m t} + {~ D m t}.

Variable Rel : nat -> nat -> Prop.
Hypothesis RelD : forall m t, L m -> Rel m t -> D m t.
Hypothesis Rel0 : L 0 -> exists t, Rel 0 t.
Hypothesis RelS : forall m t, L (S m) -> Rel m t -> exists t', t < t' /\ Rel (S m) t'.

Definition Q0 (t : nat) : Prop := L 0 -> D 0 t.
Definition QS (m prev t : nat) : Prop := prev < t /\ (L (S m) -> D (S m) t).
Definition Inv (m t : nat) : Prop := L m -> exists u, t <= u /\ Rel m u.

Lemma Q0_dec : forall t, {Q0 t} + {~ Q0 t}.
Proof.
  intros t. unfold Q0. destruct (Ldec 0) as [H | H].
  - destruct (Ddec 0 t) as [E | E]; [left; auto | right; auto].
  - left. intros X. contradiction.
Defined.

Lemma QS_dec : forall m prev t, {QS m prev t} + {~ QS m prev t}.
Proof.
  intros m prev t. unfold QS. destruct (lt_dec prev t) as [Hl | Hl].
  - destruct (Ldec (S m)) as [H | H].
    + destruct (Ddec (S m) t) as [E | E]; [left; auto | right; intros [_ X]; auto].
    + left. split; [exact Hl | intros X; contradiction].
  - right. intros [X _]. contradiction.
Defined.

Lemma Q0_ex : exists t, Q0 t.
Proof.
  destruct (Ldec 0) as [H | H].
  - destruct (Rel0 H) as [t Ht]. exists t. intros _. apply RelD; assumption.
  - exists 0. intros X. contradiction.
Qed.

Lemma QS_ex : forall m prev, Inv m prev -> exists t, QS m prev t /\ Inv (S m) t.
Proof.
  intros m prev HI. destruct (Ldec (S m)) as [H | H].
  - destruct (HI (Lprev m H)) as (u & Hu & R).
    destruct (RelS m u H R) as (t & Ht & R').
    exists t. split; [split; [lia | intros _; apply RelD; assumption] |].
    intros _. exists t. split; [lia | exact R'].
  - exists (S prev). split; [split; [lia | intros X; contradiction] |].
    intros X. contradiction.
Qed.

(* The search for step 0. *)
Definition F0 : { t | Q0 t /\ forall k, Q0 k -> t <= k } :=
  epsilon_smallest Q0 Q0_dec Q0_ex.

Lemma Inv0 : Inv 0 (proj1_sig F0).
Proof.
  destruct F0 as [t [Ht Hmin]]. simpl. intros H.
  destruct (Rel0 H) as [u Hu]. exists u. split; [| exact Hu].
  apply Hmin. intros _. apply RelD; assumption.
Qed.

(* The search for step S m, given the time for step m and its invariant. *)
Definition FS (m prev : nat) (HI : Inv m prev) :
  { t | (QS m prev t /\ forall k, QS m prev k -> t <= k) /\ Inv (S m) t }.
Proof.
  assert (E : exists t, QS m prev t).
  { destruct (QS_ex m prev HI) as (t & H & _). exists t. exact H. }
  destruct (epsilon_smallest (QS m prev) (QS_dec m prev) E) as [t [Ht Hmin]].
  exists t. split; [split; assumption |].
  intros HL. destruct (QS_ex m prev HI) as (t' & Ht' & HI').
  destruct (HI' HL) as (u & Hu & R). exists u. split; [| exact R].
  pose proof (Hmin t' Ht'). lia.
Defined.

Fixpoint F (m : nat) : { t | Inv m t /\ (L m -> D m t) } :=
  match m with
  | 0 => exist _ (proj1_sig F0) (conj Inv0 (proj1 (proj2_sig F0)))
  | S m' =>
      let (prev, Hp) := F m' in
      let (t, Ht) := FS m' prev (proj1 Hp) in
      exist _ t (conj (proj2 Ht) (proj2 (proj1 (proj1 Ht))))
  end.

Definition f (m : nat) : nat := proj1_sig (F m).

Lemma f_S : forall m, f m < f (S m).
Proof.
  intros m. unfold f. simpl. destruct (F m) as [prev Hp]. simpl.
  destruct (FS m prev (proj1 Hp)) as [t Ht]. simpl. exact (proj1 (proj1 (proj1 Ht))).
Qed.

Lemma f_D : forall m, L m -> D m (f m).
Proof.
  intros m Hm. unfold f. destruct (F m) as [t Ht]. simpl. exact (proj2 Ht Hm).
Qed.

Theorem in_order :
  exists f : nat -> nat, (forall m, f m < f (S m)) /\ (forall m, L m -> D m (f m)).
Proof.
  exists f. exact (conj f_S f_D).
Qed.

End InOrder.

Print Assumptions in_order.
