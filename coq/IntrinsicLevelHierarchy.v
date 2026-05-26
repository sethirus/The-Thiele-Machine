(** * IntrinsicLevelHierarchy.v — state-level strict hierarchy.

    State-level companion to [MuHierarchyTheorem]. The latter defines
    the level-k predicate on a trace ("the executed-instruction log
    contains an [instr_certify δ] with [S δ >= k]") and proves the
    cost floor by walking that trace.

    This file defines the level instead on the *final state*: a state
    is intrinsically level-k iff *every* certifying trace reaching it
    executes at least k cert-setter instructions. The level is a
    property of the state, not of any particular trace. The companion
    strict-separation theorem then says level-(k+1) states require
    strictly more cert-events than level-k states.

    The two presentations are complementary entry points to the same
    hierarchy. The trace-level theorem in [MuHierarchyTheorem] supplies
    the achievability witness ([[instr_certify (k-1)]] from
    [init_state]); the state-level theorem here supplies the lower
    bound on Δμ for any state that intrinsically requires k cert-events,
    by composition with [info_priced_cert_executions_bound]. Both close
    under the global context with zero [Admitted].
*)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import SimulationProof.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import MuInitiality.
From Kernel Require Import MuShannonBridge.
From Kernel Require Import MuNoFreeInsightQuantitative.

(* -------------------------------------------------------------------- *)
(** ** The intrinsic level: minimum cert-setter execution count. *)

(** Count cert-setter executions along a [run_vm] trace.
    This is exactly [MuShannonBridge.cert_setter_executions]; we
    re-export the name for visibility. *)
Definition cert_events_in (fuel : nat) (trace : list vm_instruction)
                         (s_init : VMState) : nat :=
  cert_setter_executions fuel trace s_init.

(** A claim has intrinsic level ≥ k iff every certification of it
    from [init_state] requires at least k cert-setter executions.
    The "certification" here means the final state has
    [vm_certified = true]. *)
Definition level_intrinsic_at_least (k : nat) (s_final : VMState) : Prop :=
  forall fuel trace,
    run_vm fuel trace init_state = s_final ->
    s_final.(vm_certified) = true ->
    cert_events_in fuel trace init_state >= k.

(* -------------------------------------------------------------------- *)
(** ** The strict separation.

    The kernel's [info_priced_cert_executions_bound] gives us the
    canonical cost-vs-events inequality:
      `cert_setter_executions ≤ Δ μ`.

    Combined with [init_state_mu_zero], any trace from `init_state`
    has Δ μ = final.(vm_mu). So if `final.(vm_mu) < k`, the trace
    cannot have executed k cert-setters. This is the lower bound on
    "trace cost" from level k.
*)

Theorem level_intrinsic_forces_mu :
  forall k s_final,
    level_intrinsic_at_least k s_final ->
    s_final.(vm_certified) = true ->
    forall fuel trace,
      run_vm fuel trace init_state = s_final ->
      s_final.(vm_mu) >= k.
Proof.
  intros k s_final Hlevel Hcert fuel trace Hrun.
  pose proof (Hlevel fuel trace Hrun Hcert) as Hevents.
  unfold cert_events_in in Hevents.
  pose proof (info_priced_cert_executions_bound fuel trace init_state)
    as Hbound.
  rewrite Hrun in Hbound.
  rewrite init_state_mu_zero in Hbound.
  simpl in Hbound.
  rewrite Nat.sub_0_r in Hbound.
  lia.
Qed.

(** The strict separation at the *level* layer: level-(k+1) claims
    cannot be certified by traces with cert-events ≤ k.

    The arithmetic step is the contrapositive of "cert_events ≥ k+1
    forces cert_events > k." The substantive content is that
    [level_intrinsic_at_least] is a property of the final state —
    the *minimum* taken over all certifying traces — and the kernel's
    [info_priced_cert_executions_bound] pins that minimum to the
    ledger sum. The hierarchy is a property of claims, not of any one
    trace that happens to certify them.
*)
Theorem level_strict_separation :
  forall k s_final,
    level_intrinsic_at_least (k + 1) s_final ->
    s_final.(vm_certified) = true ->
    forall fuel trace,
      run_vm fuel trace init_state = s_final ->
      cert_events_in fuel trace init_state > k.
Proof.
  intros k s_final Hlevel Hcert fuel trace Hrun.
  pose proof (Hlevel fuel trace Hrun Hcert) as Hge.
  unfold cert_events_in in *. lia.
Qed.

Print Assumptions level_strict_separation.
