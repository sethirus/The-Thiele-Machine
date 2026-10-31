(** LiftPigeon: the pigeonhole principle for functions on the naturals,
    constructively.  Used for the finite-branching counterexample and for
    the one-counter decision procedure. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file is
   a pigeonhole principle for functions on the natural numbers and imports
   nothing but the standard library. LiftOneCounter.v and LiftConverse.v use
   it, and LiftCore.v carries the link to the abstract record. *)

From Coq Require Import List Arith Lia.
Import ListNotations.

(** Among M points mapped into fewer than M boxes, two share a box. *)
Lemma lift_pigeon_dec : forall M (f : nat -> nat),
  (exists i j, i < j /\ j < M /\ f i = f j) \/
  (forall i j, i < j -> j < M -> f i <> f j).
Proof.
  induction M as [| M IH]; intro f.
  - right. intros i j Hij Hj. lia.
  - assert (Hsearch : forall K v, (exists i, i < K /\ f i = v) \/ (forall i, i < K -> f i <> v)).
    { induction K as [| K IHK]; intro v.
      - right. intros i Hi. lia.
      - destruct (Nat.eq_dec (f K) v) as [Hv | Hv].
        + left. exists K. split; [lia | exact Hv].
        + destruct (IHK v) as [[i [Hi Hfi]] | Hn].
          * left. exists i. split; [lia | exact Hfi].
          * right. intros i Hi. destruct (Nat.eq_dec i K) as [-> | Hne]; [exact Hv |].
            apply Hn. lia. }
    destruct (IH f) as [[i [j [Hij [Hj Hf]]]] | Hinj].
    + left. exists i, j. split; [exact Hij | split; [lia | exact Hf]].
    + destruct (Hsearch M (f M)) as [[i [Hi Hfi]] | Hn].
      * left. exists i, M. split; [exact Hi | split; [lia | exact Hfi]].
      * right. intros i j Hij Hj. destruct (Nat.eq_dec j M) as [-> | Hne].
        -- apply Hn. exact Hij.
        -- apply Hinj; [exact Hij | lia].
Qed.

(** Injective into N boxes forces at most N points. *)
Lemma lift_inj_le : forall N M (f : nat -> nat),
  (forall j, j < M -> f j < N) ->
  (forall i j, i < j -> j < M -> f i <> f j) -> M <= N.
Proof.
  induction N as [| N IH]; intros M f Hb Hinj.
  - destruct M; [lia |]. specialize (Hb 0). lia.
  - destruct M as [| M]; [lia |].
    (* find the box of the last point, move the points above it down *)
    set (v := f M).
    assert (Hv : v < S N) by (apply Hb; lia).
    set (g := fun j => let x := f j in if Nat.ltb v x then x - 1 else x).
    assert (Hg : forall j, j < M -> g j < N).
    { intros j Hj. unfold g. pose proof (Hb j ltac:(lia)) as H1.
      assert (H2 : f j <> v) by (apply Hinj; lia).
      destruct (Nat.ltb_spec0 v (f j)); lia. }
    assert (Hgi : forall i j, i < j -> j < M -> g i <> g j).
    { intros i j Hij Hj. unfold g.
      pose proof (Hinj i j Hij ltac:(lia)) as H1.
      assert (H2 : f i <> v) by (apply Hinj; lia).
      assert (H3 : f j <> v) by (apply Hinj; lia).
      destruct (Nat.ltb_spec0 v (f i)); destruct (Nat.ltb_spec0 v (f j)); lia. }
    pose proof (IH M g Hg Hgi). lia.
Qed.

Theorem lift_pigeon : forall N (f : nat -> nat),
  (forall j, j <= N -> f j < N) ->
  exists i j, i < j /\ j <= N /\ f i = f j.
Proof.
  intros N f Hb. destruct (lift_pigeon_dec (S N) f) as [[i [j [Hij [Hj Hf]]]] | Hinj].
  - exists i, j. split; [exact Hij | split; [lia | exact Hf]].
  - exfalso. pose proof (lift_inj_le N (S N) f (fun j Hj => Hb j ltac:(lia)) Hinj). lia.
Qed.
