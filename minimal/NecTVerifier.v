(** NecTVerifier.v: what the verifier corollary needs, and its exact converse.

    VerifierSmall.v proves that a collision (one transcript explained by a
    state that satisfies the claim and by one that does not) blocks every
    sound and complete verifier, and that every Thiele-complete machine has
    the collision on bare transcripts. Two questions a careful reader asks.

      1. Is the collision the only obstacle? Yes, up to decidability: a
         sound and complete verifier exists exactly when there is no
         collision [nec_t_ver_exists_iff_collision_free]. Every richer
         transcript that escapes is a transcript without the collision, and
         every transcript without the collision escapes.
      2. Is Thiele-completeness needed, or would "a Thiele machine with a
         universal base" do? It would not: the clock, which is weakly
         Thiele-complete, has a verifier on bare transcripts, because its
         record is a function of its window
         [nec_t_clock_has_bare_verifier, nec_t_weak_does_not_suffice]. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.ThieleCompleteWindow.
Require Import Minimal.VerifierSmall.

(* ================================================================= *)
(* 1. A verifier exists exactly when there is no collision.           *)
(* ================================================================= *)

Section Exact.

Context {St Tr : Type}.
Variable claim : St -> Prop.
Variable explains : St -> Tr -> Prop.

(* No transcript is explained by a state that satisfies the claim and by
   one that does not. *)
Definition ver_collision_free : Prop :=
  forall t A B, explains A t -> explains B t -> claim A -> claim B.

Theorem nec_t_ver_exists_implies_collision_free :
  (exists V, ver_sound claim explains V /\ ver_complete claim explains V) ->
  ver_collision_free.
Proof.
  intros [V [Hs Hc]] t A B HA HB HcA.
  exact (Hs t (Hc A t HcA HA) B HB).
Qed.

(* The converse needs only that "some state behind this transcript satisfies
   the claim" can be decided, which is what it takes to write the verifier
   down. *)
Theorem nec_t_ver_collision_free_implies_exists :
  (forall t, {exists s, explains s t /\ claim s} + {~ exists s, explains s t /\ claim s}) ->
  ver_collision_free ->
  exists V, ver_sound claim explains V /\ ver_complete claim explains V.
Proof.
  intros Hdec Hfree.
  exists (fun t => if Hdec t then true else false). split.
  - intros t Hv B HB. destruct (Hdec t) as [[A [HA HcA]] | Hn]; [| discriminate Hv].
    exact (Hfree t A B HA HB HcA).
  - intros s t Hc He. destruct (Hdec t) as [_ | Hn]; [reflexivity |].
    exfalso. apply Hn. exists s. split; assumption.
Qed.

Theorem nec_t_ver_exists_iff_collision_free :
  (forall t, {exists s, explains s t /\ claim s} + {~ exists s, explains s t /\ claim s}) ->
  ((exists V, ver_sound claim explains V /\ ver_complete claim explains V) <->
   ver_collision_free).
Proof.
  intro Hdec. split;
    [apply nec_t_ver_exists_implies_collision_free
    | apply nec_t_ver_collision_free_implies_exists, Hdec].
Qed.

End Exact.

(* ================================================================= *)
(* 2. Weakly Thiele-complete is not enough.                           *)
(* ================================================================= *)

(* An interface for the clock that fills in every field trivially. It is
   only used to name the bare transcript, which reads the base. *)
Definition nec_t_clock_interface (rd : cm_conf -> bool) : thiele_interface (clock rd) :=
  mk_ti (clock rd) (clock_base rd) unit (fun _ => KBase)
    (fun _ _ => True) (fun _ _ => true) (fun _ _ _ => True)
    (fun _ => True) (fun _ => 0).

Theorem nec_t_clock_has_bare_verifier : forall rd : cm_conf -> bool,
  exists V : ver_bare -> bool,
    ver_sound ver_record (ver_bare_explains (nec_t_clock_interface rd)) V /\
    ver_complete ver_record (ver_bare_explains (nec_t_clock_interface rd)) V.
Proof.
  intros rd. exists (fun t => let '(a, b, w) := t in rd w). split.
  - intros [[a b] w] Hv s [tr [Hs Hw]]. unfold ver_record. simpl in *.
    unfold base_window in Hw. simpl in Hw. subst w. exact Hv.
  - intros s [[a b] w] Hc [tr [Hs Hw]]. unfold ver_record in Hc. simpl in *.
    unfold base_window in Hw. simpl in Hw. subst w. exact Hc.
Qed.

(* The corollary's hypothesis cannot be weakened from Thiele-complete to
   weakly Thiele-complete. *)
Theorem nec_t_weak_does_not_suffice : exists M : machine,
  weakly_thiele_complete M /\ ~ thiele_complete M /\
  exists (I : thiele_interface M) (V : ver_bare -> bool),
    ver_sound ver_record (ver_bare_explains I) V /\
    ver_complete ver_record (ver_bare_explains I) V.
Proof.
  exists (clock (fun _ => true)). split; [apply clock_weakly_thiele_complete |].
  split; [apply clock_not_thiele_complete |].
  exists (nec_t_clock_interface (fun _ => true)).
  apply nec_t_clock_has_bare_verifier.
Qed.

Print Assumptions nec_t_ver_exists_iff_collision_free.
Print Assumptions nec_t_clock_has_bare_verifier.
Print Assumptions nec_t_weak_does_not_suffice.
