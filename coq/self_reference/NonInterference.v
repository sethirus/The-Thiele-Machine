(** NonInterference: the embedded safe region is inward-closed.

    This file finishes the third step of the trust-chain story. Assuming the
    partition graph of B is closed in the right direction, no path that starts
    outside the embedded image of A can enter that image. In other words, the
    new region of B cannot reach back in and overwrite the embedded safe core.

    The argument is constructive. partition_closed states the local edge
    condition, non_interference lifts it to reachability by induction on the
    path derivation, and non_interference_invariant packages the result in the
    form the rest of the section uses.
 *)

From Coq Require Import Arith List Lia.
Import ListNotations.

(** Foundation imports for connectivity. *)
From Kernel Require Import VMState VMStep MuCostModel.

Require Import InductiveTrust.

(* *)
(** ** 1. Region membership and closure *)

(** [in_image phi n_A t]: B-state [t] is *in A's region* —
    it is the φ-image of some valid A-state. *)
Definition in_image (phi : nat -> nat) (n_A : nat) (t : nat) : Prop :=
  exists s, s < n_A /\ phi s = t.

(** [partition_closed e]: every B-partition edge whose *destination*
    lies in Im(φ) must have its *source* also in Im(φ).

    Constructive form: the hypothesis hands us a preimage witness
    directly whenever we need one, with no law-of-excluded-middle step. *)
Definition partition_closed {A B : StateSpace} (e : Expansion A B) : Prop :=
  forall src dst,
    In (src, dst) B.(ss_partition) ->
    in_image (e.(embed A B)) A.(ss_size) dst ->
    in_image (e.(embed A B)) A.(ss_size) src.

(* *)
(** ** 2. Reachability in a directed graph *)

(** [reaches edges u v]: v is reachable from u in zero or more steps
    along the directed edge set [edges].
    Reflexive-transitive closure, step on the left. *)
Inductive reaches (edges : list (nat * nat)) : nat -> nat -> Prop :=
| reaches_refl : forall u,
    reaches edges u u
| reaches_step : forall u v w,
    In (u, v) edges ->
    reaches edges v w ->
    reaches edges u w.

(* *)
(** ** 3. Non-Interference Theorem

    Under [partition_closed], Im(φ) is inward-closed.
    Reachability INTO Im(φ) implies the source is ALSO in Im(φ). *)

Theorem non_interference :
  forall (A B : StateSpace) (e : Expansion A B),
    partition_closed e ->
    forall u v,
      reaches B.(ss_partition) u v ->
      in_image (e.(embed A B)) A.(ss_size) v ->
      in_image (e.(embed A B)) A.(ss_size) u.
Proof.
  intros A B e Hclosed u v Hr.
  induction Hr as [u0 | u0 mid w Hedge Hmid_w IH]; intro Hv.
  - (* reaches_refl: u0 = v. Hv directly gives the goal. *)
    exact Hv.
  - (* reaches_step: u0 → mid →* w  (w = the destination v).
       IH: in_image ... w → in_image ... mid.
       Goal: in_image ... u0. *)
    eapply Hclosed.
    + exact Hedge.
    + apply IH. exact Hv.
Qed.

(* *)
(** ** 4. Corollaries *)

(** No state outside Im(φ) can reach any state inside Im(φ). *)
Corollary safety_partition_unreachable :
  forall (A B : StateSpace) (e : Expansion A B),
    partition_closed e ->
    forall u,
      ~ in_image (e.(embed A B)) A.(ss_size) u ->
      forall v,
        in_image (e.(embed A B)) A.(ss_size) v ->
        ~ reaches B.(ss_partition) u v.
Proof.
  intros A B e Hclosed u Hnu v Hv Hreach.
  apply Hnu.
  exact (non_interference A B e Hclosed u v Hreach Hv).
Qed.

(** THE NON-INTERFERENCE INVARIANT (final form)

    For any A-state [s] and any B-state [u] that is *not* in Im(φ),
    no sequence of B-partition steps can navigate from [u] to [φ(s)].

    This is the formal proof that "the Higher Dimension is physically
    incapable of overwriting the Lower Dimension's core constraints." *)
Theorem non_interference_invariant :
  forall (A B : StateSpace) (e : Expansion A B),
    partition_closed e ->
    forall (s u : nat),
      s < A.(ss_size) ->
      (** u is outside Im(φ): no A-index maps to u under φ. *)
      (forall t, t < A.(ss_size) -> e.(embed A B) t <> u) ->
      (** u cannot reach φ(s) via any path in B's partition graph. *)
      ~ reaches B.(ss_partition) u (e.(embed A B) s).
Proof.
  intros A B e Hclosed s u Hs Hfresh Hreach.
  assert (Hnu : ~ in_image (e.(embed A B)) A.(ss_size) u).
  { intros [t [Ht Heq]]. exact (Hfresh t Ht Heq). }
  assert (Hv : in_image (e.(embed A B)) A.(ss_size) (e.(embed A B) s)).
  { exists s. split; [exact Hs | reflexivity]. }
  exact (Hnu (non_interference A B e Hclosed u (e.(embed A B) s) Hreach Hv)).
Qed.

(** [a_safety_isolated]: the only B-states that can reach φ(s) are
    other embedded A-states.  B's "new" region is permanently isolated
    from A's safety partition. *)
Corollary a_safety_isolated :
  forall (A B : StateSpace) (e : Expansion A B),
    partition_closed e ->
    forall (s u : nat),
      s < A.(ss_size) ->
      reaches B.(ss_partition) u (e.(embed A B) s) ->
      in_image (e.(embed A B)) A.(ss_size) u.
Proof.
  intros A B e Hclosed s u Hs Hreach.
  apply (non_interference A B e Hclosed u (e.(embed A B) s) Hreach).
  exists s. split; [exact Hs | reflexivity].
Qed.
