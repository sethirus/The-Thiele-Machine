(** Ledger uniqueness for a fixed instruction-cost schedule.

    [init_state] supplies a zero initial ledger. Each transition adds exactly
    [canonical_cost], so every reachable ledger equals its initial value plus
    the executed path sum. Any state measure with the same initial value and
    exact increments agrees on reachable states. Zero-cost transitions can
    change other fields; zero ledger does not identify a unique VM state.
    These conditions determine the accumulated measure, not the choice of
    instruction prices or a conversion from cost units to physical energy. *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
From Coq Require Import Strings.String.
Import ListNotations.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import SimulationProof.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import MuCostDerivation.

Definition init_graph : PartitionGraph := {|
  pg_next_id := 0;
  pg_modules := [];
  pg_next_morph_id := 1;
  pg_morphisms := []
|}.

Definition init_csrs : CSRState := {|
  csr_cert_addr := 0;
  csr_status := 0;
  csr_err := 0; csr_heap_base := 0
|}.

Definition init_state : VMState := {|
  vm_graph := init_graph;
  vm_csrs := init_csrs;
  vm_regs := repeat 0 REG_COUNT;
  vm_mem := repeat 0 MEM_SIZE;
  vm_pc := 0;
  vm_mu := 0;
  vm_mu_tensor := vm_mu_tensor_default;
  vm_err := false;
  vm_logic_acc := 0;
  vm_mstatus := 0;
  vm_witness := witness_counts_zero;
  vm_certified := false
|}.

Lemma init_state_mu_zero : init_state.(vm_mu) = 0.
Proof. reflexivity. Qed.

Inductive reachable : VMState -> Prop :=
| reach_init : reachable init_state
| reach_step : forall s instr,
    reachable s -> reachable (vm_apply s instr).

Inductive trace_reaches : VMState -> list vm_instruction -> VMState -> Prop :=
| trace_nil : forall s, trace_reaches s [] s
| trace_cons : forall s instr rest s',
    trace_reaches (vm_apply s instr) rest s' ->
    trace_reaches s (instr :: rest) s'.

Fixpoint exec_trace_from (s : VMState) (trace : list vm_instruction) : VMState :=
  match trace with
  | [] => s
  | instr :: rest => exec_trace_from (vm_apply s instr) rest
  end.

Lemma exec_trace_correct :
  forall s trace,
    trace_reaches s trace (exec_trace_from s trace).
Proof.
  intros s trace. generalize dependent s.
  induction trace as [|instr rest IH]; intros s; simpl.
  - constructor.
  - constructor. apply IH.
Qed.

Lemma trace_reaches_exec :
  forall s trace s',
    trace_reaches s trace s' -> s' = exec_trace_from s trace.
Proof.
  intros s trace s' H.
  induction H; simpl.
  - reflexivity.
  - apply IHtrace_reaches.
Qed.

Lemma reachable_from_trace_gen :
  forall trace s,
    reachable s ->
    reachable (exec_trace_from s trace).
Proof.
  induction trace as [|instr rest IH]; intros s Hs; simpl.
  - exact Hs.
  - apply IH. apply reach_step. exact Hs.
Qed.

Lemma reachable_from_trace :
  forall trace, reachable (exec_trace_from init_state trace).
Proof.
  intro trace.
  apply reachable_from_trace_gen.
  constructor.
Qed.

Lemma reachable_iff_trace :
  forall s,
    reachable s <-> exists trace, s = exec_trace_from init_state trace.
Proof.
  split.
  -
    intro H. induction H.
    + exists []. reflexivity.
    + destruct IHreachable as [trace Htrace].
      exists (trace ++ [instr]).
      rewrite Htrace.
      clear Htrace H.
      generalize dependent init_state.
      induction trace as [|i rest IH]; intros s0; simpl.
      * reflexivity.
      * apply IH.
  -
    intros [trace Htrace].
    rewrite Htrace. clear Htrace s.

    apply reachable_from_trace_gen.
    constructor.
Qed.

Fixpoint trace_total_cost (trace : list vm_instruction) : nat :=
  match trace with
  | [] => 0
  | instr :: rest => instruction_cost instr + trace_total_cost rest
  end.

Lemma mu_accumulates_trace_cost :
  forall s trace,
    (exec_trace_from s trace).(vm_mu) = s.(vm_mu) + trace_total_cost trace.
Proof.
  intros s trace. generalize dependent s.
  induction trace as [|instr rest IH]; intros s; simpl.
  - lia.
  - rewrite IH.
    rewrite vm_apply_mu.
    lia.
Qed.

Corollary mu_equals_trace_cost :
  forall trace,
    (exec_trace_from init_state trace).(vm_mu) = trace_total_cost trace.
Proof.
  intro trace.
  rewrite mu_accumulates_trace_cost.
  unfold init_state. simpl.
  lia.
Qed.

Definition CostAssignment := vm_instruction -> nat.

Definition canonical_cost : CostAssignment := instruction_cost.

Definition instruction_consistent (M : VMState -> nat) (c : CostAssignment) : Prop :=
  forall s instr, M (vm_apply s instr) = M s + c instr.

Definition is_monotone (M : VMState -> nat) : Prop :=
  forall s instr, M s <= M (vm_apply s instr).

Lemma instruction_consistent_monotone :
  forall M c,
    instruction_consistent M c ->
    (forall instr, c instr >= 0) ->
    is_monotone M.
Proof.
  intros M c Hcons Hpos s instr.
  rewrite Hcons.
  specialize (Hpos instr).
  lia.
Qed.

Lemma consistent_accumulates_trace_cost :
  forall M c,
    instruction_consistent M c ->
    forall s trace,
      M (exec_trace_from s trace) = M s +
        (fix trace_cost (t : list vm_instruction) : nat :=
          match t with
          | [] => 0
          | i :: rest => c i + trace_cost rest
          end) trace.
Proof.
  intros M c Hcons s trace.
  generalize dependent s.
  induction trace as [|instr rest IH]; intros s; simpl.
  - lia.
  - rewrite IH.
    rewrite Hcons.
    lia.
Qed.

Theorem mu_is_initial_monotone :
  forall M : VMState -> nat,
    instruction_consistent M canonical_cost ->
    M init_state = 0 ->
    forall s, reachable s -> M s = s.(vm_mu).
Proof.
  intros M Hcons Hinit s Hreach.
  induction Hreach.
  -
    rewrite Hinit.
    unfold init_state. simpl.
    reflexivity.
  -
    rewrite Hcons.
    rewrite vm_apply_mu.
    rewrite IHHreach.
    unfold canonical_cost.
    reflexivity.
Qed.

Corollary mu_trace_determined :
  forall M : VMState -> nat,
    instruction_consistent M canonical_cost ->
    M init_state = 0 ->
    forall trace,
      M (exec_trace_from init_state trace) = trace_total_cost trace.
Proof.
  intros M Hcons Hinit trace.
  rewrite (mu_is_initial_monotone M Hcons Hinit).
  - apply mu_equals_trace_cost.
  - apply reachable_from_trace.
Qed.

Corollary consistent_monotones_agree :
  forall M1 M2 : VMState -> nat,
    instruction_consistent M1 canonical_cost ->
    instruction_consistent M2 canonical_cost ->
    M1 init_state = 0 ->
    M2 init_state = 0 ->
    forall s, reachable s -> M1 s = M2 s.
Proof.
  intros M1 M2 Hcons1 Hcons2 Hinit1 Hinit2 s Hreach.
  rewrite (mu_is_initial_monotone M1 Hcons1 Hinit1 s Hreach).
  rewrite (mu_is_initial_monotone M2 Hcons2 Hinit2 s Hreach).
  reflexivity.
Qed.

Theorem monotone_factors_through_mu :
  forall M : VMState -> nat,
    instruction_consistent M canonical_cost ->
    exists f : nat -> nat,
      (forall n m, n <= m -> f n <= f m) /\
      (forall s, reachable s -> M s = f (s.(vm_mu))).
Proof.
  intros M Hcons.

  exists (fun n => M init_state + n).
  split.
  -
    intros n m Hle. lia.
  -
    intros s Hreach.
    induction Hreach.
    +
      simpl. lia.
    +
      rewrite Hcons.
      rewrite vm_apply_mu.
      rewrite IHHreach.
      unfold canonical_cost.
      lia.
Qed.

Corollary mu_is_identity_factorization :
  forall M : VMState -> nat,
    instruction_consistent M canonical_cost ->
    M init_state = 0 ->
    forall s, reachable s -> M s = (fun n => n) (s.(vm_mu)).
Proof.
  intros M Hcons Hinit s Hreach.
  simpl.
  apply mu_is_initial_monotone; assumption.
Qed.

Record CostFunctional := {
  cf_measure : VMState -> nat;
  cf_instruction_consistent : instruction_consistent cf_measure canonical_cost;
  cf_init_zero : cf_measure init_state = 0
}.

Definition mu_functional : CostFunctional.
Proof.
  refine {| cf_measure := vm_mu |}.
  -
    unfold instruction_consistent, canonical_cost.
    intros s instr.
    apply vm_apply_mu.
  -
    unfold init_state. simpl. reflexivity.
Defined.

Theorem mu_is_universal :
  forall cf : CostFunctional,
    forall s, reachable s -> cf_measure cf s = vm_mu s.
Proof.
  intros cf s Hreach.
  apply mu_is_initial_monotone.
  - exact (cf_instruction_consistent cf).
  - exact (cf_init_zero cf).
  - exact Hreach.
Qed.

Theorem mu_initiality :
  forall cf1 cf2 : CostFunctional,
    forall s, reachable s -> cf_measure cf1 s = cf_measure cf2 s.
Proof.
  intros cf1 cf2 s Hreach.
  rewrite (mu_is_universal cf1 s Hreach).
  rewrite (mu_is_universal cf2 s Hreach).
  reflexivity.
Qed.

Theorem instruction_consistent_measure_equals_mu :
  forall measure : VMState -> nat,
    instruction_consistent measure canonical_cost ->
    measure init_state = 0 ->
    forall s, reachable s -> measure s = s.(vm_mu).
Proof.
  exact mu_is_initial_monotone.
Qed.

