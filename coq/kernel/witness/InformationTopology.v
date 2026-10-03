(** InformationTopology.v: the mu-cost of a run read as a path cost.

    [mu_path_cost fuel trace s] is the mu a run spends, and
    [mu_distance_le s1 s2 b] says some run takes [s1] to [s2] for at most
    [b]. This is weighted-graph vocabulary over VM runs; it is not a
    physics claim and it does not identify the mu-tensor with a metric.

    Results:

    MU_PATH_COST: [mu_path_cost] is nonnegative and zero on the empty
    run ([mu_path_cost_nonneg], [mu_path_cost_empty]).

    DISTANCE FACTS: self-distance 0 ([mu_distance_self_zero]),
    nonnegativity ([mu_distance_nonneg]), and a triangle bound for two legs
    of the same trace ([mu_distance_le_single_trace_triangle]). It is not a
    full metric: two different states can have distance 0.

    FACTORED SEARCH: at N = 1 the blind program of StructuralAdvantage.v
    spends 0 mu ([blind_is_mu_zero]; the sighted program's 18 is
    [sighted_halts_in_two_n] there); the remaining theorems restate the arithmetic
    savings bounds of StructuralAdvantage.v. No theorem here proves that
    the sighted program spends the least mu among all programs. *)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import MuInitiality.
From Kernel Require Import StructuralAdvantage.

(** ** mu-Path Cost

    The mu cost accumulated along a sequence of instructions is simply
    the increase in vm_mu from the initial to the final state. *)

Definition mu_path_cost (fuel : nat) (trace : list vm_instruction) (s : VMState) : nat :=
  (run_vm fuel trace s).(vm_mu) - s.(vm_mu).

Lemma mu_path_cost_nonneg :
  forall fuel trace s,
    mu_path_cost fuel trace s >= 0.
Proof.
  intros fuel trace s. lia.
Qed.

Lemma mu_path_cost_empty :
  forall s,
    mu_path_cost 0 [] s = 0.
Proof.
  intro s.
  assert (H: run_vm 0 [] s = s) by reflexivity.
  unfold mu_path_cost. rewrite H. lia.
Qed.

(** mu_path_cost is always non-decreasing from initial mu:
    the final mu is at least the initial mu (monotone mu-ledger). *)
Lemma mu_path_cost_bounded_by_mu :
  forall fuel trace s,
    s.(vm_mu) + mu_path_cost fuel trace s = (run_vm fuel trace s).(vm_mu).
Proof.
  intros fuel trace s.
  unfold mu_path_cost.
  assert (H := run_vm_mu_monotonic fuel trace s).
  lia.
Qed.

(** ** mu-Distance between States

    The mu-distance from state s1 to state s2 is the minimum mu-cost over
    all programs that transform s1 into a state observationally equivalent
    to s2 (same mu and certified flag). *)

Definition mu_reaches (s1 s2 : VMState) (fuel : nat) (trace : list vm_instruction) : Prop :=
  run_vm fuel trace s1 = s2.

Definition mu_distance_le (s1 s2 : VMState) (bound : nat) : Prop :=
  exists fuel trace,
    mu_reaches s1 s2 fuel trace /\
    mu_path_cost fuel trace s1 <= bound.

Definition mu_distance_zero (s : VMState) : Prop :=
  mu_distance_le s s 0.

(** PROVEN: Every state has distance 0 to itself (the empty program). *)
Lemma mu_distance_self_zero :
  forall s, mu_distance_zero s.
Proof.
  intro s.
  unfold mu_distance_zero, mu_distance_le, mu_reaches.
  exists 0, [].
  split.
  - reflexivity.
  - unfold mu_path_cost. simpl. lia.
Qed.

(** PROVEN: mu-distance is non-negative. *)
Lemma mu_distance_nonneg :
  forall s1 s2 bound,
    mu_distance_le s1 s2 bound -> bound >= 0.
Proof.
  intros. lia.
Qed.

(** Triangle inequality for [mu_path_cost] over a single trace.

    Given an intermediate state [s_mid] reachable from [s1] in [f1]
    fuel and [s3] reachable from [s_mid] in [f2] fuel (both along the
    SAME trace), running [(f1 + f2)] fuel along that trace from [s1]
    reaches [s3] and the path cost is bounded by the sum of the per-leg
    bounds.

    The single-trace restriction is intrinsic to [run_vm]: the trace is
    not consumed by execution, only fuel is, and PC indexing is into
    that single trace. A two-trace version would require gluing
    semantics ([run_vm f trace1 s1 = s_mid /\ run_vm g trace2 s_mid =
    s3 -> exists trace, run_vm (f+g) trace s1 = s3]) which the
    kernel's PC-indexed [run_vm] does not natively support. *)
Lemma mu_path_cost_triangle :
  forall (s1 s_mid s3 : VMState) (f1 f2 : nat)
         (trace : list vm_instruction) (b1 b2 : nat),
    run_vm f1 trace s1 = s_mid ->
    run_vm f2 trace s_mid = s3 ->
    mu_path_cost f1 trace s1 <= b1 ->
    mu_path_cost f2 trace s_mid <= b2 ->
    run_vm (f1 + f2) trace s1 = s3 /\
    mu_path_cost (f1 + f2) trace s1 <= b1 + b2.
Proof.
  intros s1 s_mid s3 f1 f2 trace b1 b2 H1 H2 Hb1 Hb2.
  pose proof (StructuralAdvantage.run_vm_compose f1 f2 trace s1) as Hc.
  rewrite H1 in Hc.
  rewrite H2 in Hc.
  pose proof (run_vm_mu_monotonic f1 trace s1) as Hmono1.
  pose proof (run_vm_mu_monotonic f2 trace s_mid) as Hmono2.
  rewrite H1 in Hmono1.
  rewrite H2 in Hmono2.
  unfold mu_path_cost in *.
  rewrite H1 in Hb1.
  rewrite H2 in Hb2.
  split.
  - exact Hc.
  - rewrite Hc. lia.
Qed.

(** Corollary on the existential [mu_distance_le] form: if the
    intermediate witness uses the SAME trace and fuel-composes, the
    triangle holds. The general two-arbitrary-trace existential
    triangle is left unproved because the kernel's [run_vm] semantics
    does not provide a generic two-trace gluing operation; see
    [mu_path_cost_triangle] above. *)
Lemma mu_distance_le_single_trace_triangle :
  forall (s1 s_mid s3 : VMState) (b1 b2 f1 f2 : nat)
         (trace : list vm_instruction),
    run_vm f1 trace s1 = s_mid ->
    run_vm f2 trace s_mid = s3 ->
    mu_path_cost f1 trace s1 <= b1 ->
    mu_path_cost f2 trace s_mid <= b2 ->
    mu_distance_le s1 s3 (b1 + b2).
Proof.
  intros s1 s_mid s3 b1 b2 f1 f2 trace H1 H2 Hb1 Hb2.
  unfold mu_distance_le, mu_reaches.
  exists (f1 + f2), trace.
  destruct (mu_path_cost_triangle s1 s_mid s3 f1 f2 trace b1 b2 H1 H2 Hb1 Hb2)
    as [Hreach Hcost].
  split; assumption.
Qed.

(** ** Factored search

    The sighted program from StructuralAdvantage.v spends 18 mu on the
    2D factored search (two EMIT steps of 9 each); that is
    [sighted_halts_in_two_n] there. No theorem states that no program
    spends less. *)

(** PROVEN: the blind program at N = 1 spends 0 mu. It uses no
    cert-setter instruction. *)
Theorem blind_is_mu_zero :
  let s := run_vm 8 (blind_program 0) init_state in
  s.(vm_mu) = 0.
Proof.
  exact (proj1 (proj2 (blind_halts_in_n_squared))).
Qed.

(** Any run from csr_cert_addr = 0 to has_supra_cert executes a cert-setter
    (NoFreeInsight.v), and each cert-setter costs at least 1 mu, so such a
    run spends at least 1 mu. No theorem in this file states that bound. *)

(** PROVEN: arithmetic: for N ≥ 6, N * N > 2 * N + 18. *)
(* SCOPE NOTE: alias for iteration_savings_dwarfs_mu_cost export. *)
Theorem geodesic_efficiency :
  forall N : nat,
    N >= 6 ->
    N * N > 2 * N + 18.
Proof.
  exact iteration_savings_dwarfs_mu_cost.
Qed.

(** ** Routing reading

    Read as routing: a run is a path, mu-cost is its weight. The
    StructuralAdvantage results give, for the factored search, a mu cost
    that grows as O(k) in the number of dimensions k and iteration
    savings that grow as O(N^k). The theorems below are those arithmetic
    bounds; no theorem here is about networks of machines. *)

(** PROVEN: The k-dimensional generalization: N^k > k*N + k for N≥4, k≥2. *)
(* SCOPE NOTE: alias for k_factor_savings_exceed_mu_cost export. *)
Theorem geodesic_routing_k_dimensions :
  forall N k : nat,
    N >= 4 -> k >= 2 ->
    N ^ k > k * N + k.
Proof.
  exact k_factor_savings_exceed_mu_cost.
Qed.

(** PROVEN: Sighted dominates blind for L ≥ 1. *)
(* SCOPE NOTE: alias for sighted_wins_for_nontrivial_left export. *)
Theorem geodesic_dominates_blind :
  forall N L R : nat,
    N >= 3 -> L >= 1 ->
    L * N + R + 1 > L + R + 2.
Proof.
  exact sighted_wins_for_nontrivial_left.
Qed.

(** ** Summary

    1. [mu_path_cost] is non-negative (mu_path_cost_nonneg).
    2. Self-distance is zero (mu_distance_self_zero).
    3. A triangle bound holds for two legs of one trace
       (mu_distance_le_single_trace_triangle).
    4. At N = 1 the sighted program spends 18 mu and the blind program 0.
    5. The arithmetic savings bounds grow with the problem dimension
       (k_factor theorems). *)
