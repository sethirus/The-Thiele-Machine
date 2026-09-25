(** This file defines natural-number cost bounds and a record for comparing a
    measured value with a declared bound. It proves monotonicity of the VM
    ledger and additivity of the list-cost function. The definitions named
    “prediction” or “experimental” are interfaces for later measurements; this
    file does not perform those measurements or prove asymptotic scaling. *)

Require Import VMState VMStep KernelPhysics.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Import Nat.

(** [mu_cost_of_instr] reuses the VM's declared instruction cost. The list
    fold [trace_mu_cost] sums those declarations; correspondence with a
    particular runner is a separate theorem or test. *)

(** Extract μ-cost from instruction *)
Definition mu_cost_of_instr (i : VMStep.vm_instruction) : nat :=
  VMStep.instruction_cost i.

(** Total μ-cost of a trace *)
Fixpoint trace_mu_cost (trace : list VMStep.vm_instruction) : nat :=
  match trace with
  | [] => 0
  | i :: rest => mu_cost_of_instr i + trace_mu_cost rest
  end.

(** The four bound functions use normalized region length or evidence-list
    length as their declared reference quantity. Their names record intended
    comparison surfaces, not the conclusion that the VM or an implementation
    satisfies an O(n) theorem. *)

(** Region "size" as observed by the kernel: duplicates do not count. *)
Definition region_size (region : list nat) : nat :=
  length (normalize_region region).

Definition evidence_size (evidence : list VMAxiom) : nat :=
  length evidence.

(** PREDICTION 1: PNEW cost is O(|region|) *)
Definition pnew_cost_bound (region : list nat) : nat :=
  region_size region.

(** PREDICTION 2: PSPLIT cost is O(|left| + |right|) *)
Definition psplit_cost_bound (left right : list nat) : nat :=
  region_size left + region_size right.

(** PREDICTION 3: PMERGE cost is O(|m1.region| + |m2.region|) with dedup *)
Definition pmerge_cost_bound (r1 r2 : list nat) : nat :=
  region_size r1 + region_size r2.

(** PREDICTION 4: Discovery cost is O(evidence size) *)
Definition discover_cost_bound (evidence : list VMAxiom) : nat :=
  evidence_size evidence.

(** The next theorem is a VM-local monotonicity result. It concerns the
    [vm_mu] field and the [vm_step] relation; it does not assign the field
    thermodynamic units. *)

(** μ never decreases during a single step *)
Theorem mu_monotonic_step : forall s i s',
  VMStep.vm_step s i s' -> (s'.(vm_mu) >= s.(vm_mu))%nat.
Proof.
  intros s i s' Hstep.
  inversion Hstep; subst;
    unfold VMStep.advance_state, VMStep.advance_state_reveal, VMStep.advance_state_rm,
           VMStep.jump_state, VMStep.jump_state_rm, VMStep.apply_cost;
    simpl; try lia.
Qed.

(** The following theorem is definitional additivity for a two-element list.
    It is not a statement about an arbitrary runner or about physical costs. *)

(** Sequential execution costs add *)
Theorem mu_cost_additive : forall i1 i2 cost1 cost2,
  mu_cost_of_instr i1 = cost1 ->
  mu_cost_of_instr i2 = cost2 ->
  trace_mu_cost [i1; i2] = cost1 + cost2.
Proof.
  intros i1 i2 cost1 cost2 H1 H2.
  unfold trace_mu_cost. simpl.
  rewrite H1, H2. lia.
Qed.

(** [cost_violation] and [check_prediction] compare a supplied measured value
    with a supplied bound. [ExperimentalTrial] stores an instruction and a
    measured natural number. The record does not authenticate where that
    measurement came from. *)

(** A prediction is violated if measured cost exceeds predicted bound *)
Definition cost_violation (measured predicted : nat) : Prop :=
  (measured > predicted)%nat.

(** Experimental trial: instruction + actual μ-cost *)
Record ExperimentalTrial := {
  trial_instr : VMStep.vm_instruction;
  trial_measured_cost : nat
}.

(** Check if trial violates prediction *)
Definition check_prediction (t : ExperimentalTrial) : bool :=
  Nat.ltb (mu_cost_of_instr (trial_instr t)) (trial_measured_cost t).

(** These predicates state finite inequalities with an explicit constant [C].
    They do not include a regression model, a sampling protocol, an error
    tolerance, or a theorem that any implementation satisfies them. *)

(** TESTABLE PREDICTION 1: PNEW with n-element region costs ≤ C·n *)
Definition pnew_linear_bound (C : nat) (region : list nat) (measured : nat) : Prop :=
  (measured <= C * region_size region)%nat.

(** TESTABLE PREDICTION 2: Discovery cost scales with evidence count *)
Definition discover_linear_bound (C : nat) (evidence : list VMAxiom) (measured : nat) : Prop :=
  (measured <= C * evidence_size evidence)%nat.

(** TESTABLE PREDICTION 3: Merge deduplication savings *)
Definition merge_dedup_savings (r1 r2 : list nat) (overlap : nat) (measured : nat) : Prop :=
  (measured <= region_size r1 + region_size r2 - overlap)%nat.

(** The remaining comments describe possible external benchmark work. They are
    not executed by Coq and are not evidence of a completed measurement. *)

(** A benchmark implementation would need to specify its input generation,
    measurement source, constants, tolerance, and statistical criterion before
    its result could support one of these predicates. None of those premises is
    represented by the definitions in this file. *)

(** The proved content is the bookkeeping, monotonicity, additivity, and
    finite inequality definitions above. Empirical scaling and correspondence
    to Python or hardware remain outside this file. *)
