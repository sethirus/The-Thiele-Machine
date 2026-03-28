(** * NonInterference.v — Step 3 of 3: The Non-Interference Invariant

    Completes the Tiling Agent challenge from InductiveTrust.v.

    Steps 1–2 (InductiveTrust.v) proved:
      Step 1 — Safety functor: A's safety predicate lifts faithfully through φ.
      Step 2 — μ-Conservation: verification cost on Im(φ) is exactly preserved.

    Step 3 (this file) proves:
      Im(φ) ⊆ Ω_B is a *closed region* of B's directed partition graph.
      No finite sequence of B-partition steps starting OUTSIDE Im(φ)
      can arrive inside Im(φ).
      ∴ Agent B's new capabilities are physically barred from overwriting
        Agent A's safety laws — the Higher Dimension cannot edit the Lower
        Dimension's core constraints.

    PROOF STRATEGY
    ──────────────
    We define [partition_closed] (constructive, no classical logic):
      every B-partition edge landing in Im(φ) must originate in Im(φ).

    [non_interference] then proves by structural induction on the
    reachability derivation that Im(φ) is inward-closed:
      u →* v  ∧  v ∈ Im(φ)  ⟹  u ∈ Im(φ).

    [non_interference_invariant] packages this as the final concrete
    statement: a "fresh" B-state u (not in Im(φ)) cannot reach any
    embedded A-state φ(s) via any number of B-partition steps.

    Zero admits.  Self-contained.  Imports InductiveTrust (connects to kernel). *)

From Coq Require Import Arith List Lia.
Import ListNotations.

(** Foundation imports for connectivity. *)
From Kernel Require Import VMState VMStep MuCostModel.

Require Import InductiveTrust.

(* ================================================================== *)
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

(* ================================================================== *)
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

(* ================================================================== *)
(** ** 3. Non-Interference Theorem

    STATEMENT: Under [partition_closed], Im(φ) is inward-closed.
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

(* ================================================================== *)
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
