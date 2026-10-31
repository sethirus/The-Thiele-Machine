(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file is the nondeterministic form of the permanent-flip theorem (a total, closed step relation that raises a permanent reading has a yes-state with two predecessors) and stands alone from the certification-system kernel. *)
(* Attack: nondeterministic machines. A step relation R on a finite state list `all` (no repeats).
   Y is the list of yes-states (no repeats, all in `all`).
   Closed and total on Y: every yes-state has at least one successor, and all its successors are yes-states.
   Raised: some no-state has a successor that is a yes-state.
   Claim: some yes-state has two different predecessors. The merge survives nondeterminism. *)
Require Import List Arith Lia.
Import ListNotations.

Section Nondet.
Variable X : Type.
Hypothesis eq_dec : forall a b : X, {a = b} + {a <> b}.
Variable R : X -> X -> Prop.
Variable Y : list X.
Hypothesis Y_nodup : NoDup Y.
(* a chosen successor for each yes-state, staying in Y (closed and total, made explicit by choice) *)
Variable succ : X -> X.
Hypothesis succ_R : forall y, In y Y -> R y (succ y).
Hypothesis succ_in : forall y, In y Y -> In (succ y) Y.
(* the raise *)
Variable x0 y0 : X.
Hypothesis x0_no : ~ In x0 Y.
Hypothesis y0_yes : In y0 Y.
Hypothesis raise : R x0 y0.

Definition g (s : X) : X := if eq_dec s x0 then y0 else succ s.

Lemma g_in : forall s, In s (x0 :: Y) -> In (g s) Y.
Proof. intros s Hs. unfold g. destruct (eq_dec s x0). auto. destruct Hs; [congruence|auto]. Qed.

Lemma g_R : forall s, In s (x0 :: Y) -> R s (g s).
Proof. intros s Hs. unfold g. destruct (eq_dec s x0). subst; auto. destruct Hs; [congruence|auto]. Qed.

(* if map f over a duplicate-free list is not duplicate-free, two distinct members collide *)
Lemma map_collision : forall (f : X -> X) l, NoDup l -> ~ NoDup (map f l) ->
  exists a b, In a l /\ In b l /\ a <> b /\ f a = f b.
Proof.
  induction l as [|h t IH]; intros Hnd Hnot.
  - exfalso. apply Hnot. constructor.
  - inversion Hnd as [|? ? Hh Ht]; subst.
    destruct (In_dec eq_dec (f h) (map f t)) as [Hin | Hnin].
    + apply in_map_iff in Hin. destruct Hin as [b [Hfb Hb]].
      exists h, b. split. simpl; auto. split. simpl; auto. split.
      intro E. subst. contradiction. auto.
    + destruct (IH Ht) as [a [b [Ha [Hb [Hab Hf]]]]].
      * intro Hnd'. apply Hnot. simpl. constructor; auto.
      * exists a, b. split. simpl; auto. split. simpl; auto. split; auto.
Qed.

Theorem nondet_merge : exists a b y, a <> b /\ R a y /\ R b y /\ In y Y.
Proof.
  assert (Hnd : NoDup (x0 :: Y)) by (constructor; auto).
  assert (Hlen : length (map g (x0 :: Y)) = S (length Y)) by (rewrite map_length; reflexivity).
  destruct (map_collision g (x0 :: Y) Hnd) as [a [b [Ha [Hb [Hab Hg]]]]].
  - intro Hnd'. 
    assert (Hincl : incl (map g (x0 :: Y)) Y).
    { intros z Hz. apply in_map_iff in Hz. destruct Hz as [s [<- Hs]]. apply g_in; auto. }
    pose proof (NoDup_incl_length Hnd' Hincl). lia.
  - exists a, b, (g a). repeat split; auto.
    + apply g_R; auto.
    + rewrite Hg. apply g_R; auto.
    + apply g_in; auto.
Qed.
End Nondet.
