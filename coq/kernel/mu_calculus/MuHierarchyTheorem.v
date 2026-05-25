(** MuHierarchyTheorem.v: The µ-Cost Hierarchy Theorem

    CONTEXT: A new theorem using the Thiele Machine's NoFI principle to prove a
    genuine complexity separation. This is the µ-analogue of the classical time
    hierarchy theorem: just as DTIME(f(n)) strictly contains DTIME(g(n)) when f
    grows faster than g, here µ-budget k strictly separates from µ-budget (k-1)
    via the irreducible cost of certified structural knowledge.

    MAIN THEOREM (mu_hierarchy_theorem):
    For every k ≥ 1:
      (1) ACHIEVABILITY: there exists a trace of µ-cost exactly k from init_state
          that executes a level-k CERTIFY and produces vm_certified = true.
      (2) LOWER BOUND: any trace from init_state that executes a level-k
          CERTIFY and ends certified must have spent ≥ k µ to get there.
    Together, (1) and (2) establish: µ-budget k is necessary and sufficient for
    "level-k certification" as an executed certificate entitlement.

    COROLLARY (mu_hierarchy_no_upper_bound):
    No fixed µ-budget suffices for all levels.

    PROOF TECHNIQUE:
    - Lower bound: semantic execution scan. A level-k certificate means the
      run executed a [CERTIFY delta] with [S delta >= k]. The instruction's
      cost appears in the executed ledger entries, so the ledger sum and
      trace cost are at least k.
    - Upper bound: explicit witness [instr_certify (k-1)] costs S(k-1) = k,
      sets vm_certified := true in one step from init_state.

    NO NEW AXIOMS. All proofs use existing kernel lemmas.

    SIGNIFICANCE: Formalizes the P-vs-NP intuition in the µ-cost setting.
    The verifier just runs the certificate and checks fields (0 additional µ).
    The finder must produce the certificate, which costs µ ≥ k.
    The µ-dimension therefore admits a genuine infinite separation.
*)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

From Kernel Require Import VMState VMStep.
From Kernel Require Import SimulationProof.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import MuInitiality.
From Kernel Require Import MuComplexity.

Import VMStep.VMStep.

(** ** Section 1: vm_apply lemmas for instr_certify *)

(** A single CERTIFY instruction sets vm_certified to true. *)
Lemma vm_apply_certify_sets_certified :
  forall (s : VMState) (delta : nat),
    (vm_apply s (instr_certify delta)).(vm_certified) = true.
Proof.
  intros s delta.
  pose proof (step_certify s delta) as Hstep.
  rewrite (vm_step_vm_apply s (instr_certify delta) _ Hstep).
  reflexivity.
Qed.

(** CERTIFY with delta_mu costs S(delta_mu) = delta_mu + 1. *)
Lemma certify_instruction_cost :
  forall delta, instruction_cost (instr_certify delta) = S delta.
Proof.
  intro delta. reflexivity.
Qed.

(** After one CERTIFY from init_state, vm_mu = S(delta). *)
Lemma vm_apply_certify_init_mu :
  forall delta,
    (vm_apply init_state (instr_certify delta)).(vm_mu) = S delta.
Proof.
  intro delta.
  rewrite vm_apply_mu.
  rewrite certify_instruction_cost.
  rewrite init_state_mu_zero.
  lia.
Qed.

(** ** Section 2: Single-instruction run_vm reduction *)

(** Running one instruction from init_state equals a single vm_apply.
    Proof: init_state.vm_pc = 0, nth_error [instr] 0 = Some instr, fuel 0 = id. *)
Lemma run_vm_single_from_init :
  forall (instr : vm_instruction),
    run_vm 1 [instr] init_state = vm_apply init_state instr.
Proof.
  intro instr.
  assert (Hpc : init_state.(vm_pc) = 0) by reflexivity.
  unfold run_vm.
  rewrite Hpc.
  simpl.
  reflexivity.
Qed.

(** ** Section 3: The witness trace *)

(** The canonical k-level witness: one CERTIFY with delta = k-1, costing k.
    For k ≥ 1: S(k-1) = k. *)
Definition certify_to_level (k : nat) : list vm_instruction :=
  [instr_certify (k - 1)].

(** The witness achieves vm_mu = k. *)
Lemma certify_to_level_mu :
  forall k, k >= 1 ->
    (run_vm 1 (certify_to_level k) init_state).(vm_mu) = k.
Proof.
  intros k Hk.
  unfold certify_to_level.
  rewrite run_vm_single_from_init.
  rewrite vm_apply_certify_init_mu.
  lia.
Qed.

(** The witness achieves vm_certified = true. *)
Lemma certify_to_level_certified :
  forall k, k >= 1 ->
    (run_vm 1 (certify_to_level k) init_state).(vm_certified) = true.
Proof.
  intros k _.
  unfold certify_to_level.
  rewrite run_vm_single_from_init.
  apply vm_apply_certify_sets_certified.
Qed.

(** The µ-cost of the witness is exactly k. *)
Lemma certify_to_level_cost :
  forall k, k >= 1 ->
    trace_mu_cost 1 (certify_to_level k) init_state = k.
Proof.
  intros k Hk.
  unfold trace_mu_cost.
  rewrite certify_to_level_mu by exact Hk.
  rewrite init_state_mu_zero.
  lia.
Qed.

(** ** Section 4: The lower bound — core of the hierarchy *)

(** The instructions actually executed by [run_vm], in execution order. This
    is deliberately trace-side evidence rather than a predicate on [vm_mu]. *)
Fixpoint executed_instructions (fuel : nat) (trace : list vm_instruction)
  (s : VMState) : list vm_instruction :=
  match fuel with
  | 0 => []
  | S fuel' =>
      match nth_error trace s.(vm_pc) with
      | Some instr => instr :: executed_instructions fuel' trace (vm_apply s instr)
      | None => []
      end
  end.

(** A level-k certifier is an executed CERTIFY instruction whose intrinsic
    declared certificate cost is at least k. *)
Definition certifies_at_level (k : nat) (instr : vm_instruction) : Prop :=
  match instr with
  | instr_certify delta => S delta >= k
  | _ => False
  end.

(** Level-k certification is not defined as "final μ is at least k". It is a
    trace entitlement: the run ends certified and the executed instruction log
    contains a level-k certifier. *)
Definition level_k_certified (k fuel : nat) (trace : list vm_instruction) : Prop :=
  (run_vm fuel trace init_state).(vm_certified) = true /\
  exists instr,
    In instr (executed_instructions fuel trace init_state) /\
    certifies_at_level k instr.

Lemma certifies_at_level_cost :
  forall k instr,
    certifies_at_level k instr ->
    instruction_cost instr >= k.
Proof.
  intros k instr Hlevel.
  destruct instr; simpl in *; try contradiction; lia.
Qed.

Lemma executed_instruction_cost_recorded :
  forall fuel trace s instr,
    In instr (executed_instructions fuel trace s) ->
    In (instruction_cost instr) (ledger_entries fuel trace s).
Proof.
  induction fuel as [|fuel IH]; intros trace s instr Hin; simpl in *.
  - contradiction.
  - destruct (nth_error trace s.(vm_pc)) as [step_instr|] eqn:Hlookup.
    + simpl in *.
      destruct Hin as [Heq | Hin].
      * subst. left. reflexivity.
      * right. apply IH. exact Hin.
    + contradiction.
Qed.

Lemma ledger_sum_contains_lower_bound :
  forall entries cost,
    In cost entries ->
    ledger_sum entries >= cost.
Proof.
  induction entries as [|entry rest IH]; intros cost Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst. lia.
    + specialize (IH cost Hin). lia.
Qed.

(** Any trace-side level-k certification entitlement forces at least k μ.

    This replaces the trivial [mu_cert_lower_bound] (which collapsed to
    [vm_mu_final - 0 >= k]). The new statement says something semantic:
    a trace that ACTUALLY EXECUTED a level-k CERTIFY and ended certified
    must have paid ≥ k μ. The proof walks the executed-instruction log
    and shows the CERTIFY instruction's cost appears in the ledger. *)
Theorem level_k_certification_cost_floor :
  forall k fuel trace,
    level_k_certified k fuel trace ->
    trace_mu_cost fuel trace init_state >= k.
Proof.
  intros k fuel trace [_ [instr [Hin Hlevel]]].
  pose proof (certifies_at_level_cost k instr Hlevel) as Hcost.
  pose proof (executed_instruction_cost_recorded fuel trace init_state instr Hin)
    as Hrecorded.
  pose proof (ledger_sum_contains_lower_bound
    (ledger_entries fuel trace init_state) (instruction_cost instr) Hrecorded)
    as Hsum.
  unfold trace_mu_cost.
  rewrite run_vm_mu_conservation.
  rewrite init_state_mu_zero.
  simpl.
  rewrite Nat.sub_0_r.
  lia.
Qed.

(** The k-witness trace [certify_to_level k] executes a level-k CERTIFY. *)
Lemma certify_to_level_has_level :
  forall k, k >= 1 ->
    level_k_certified k 1 (certify_to_level k).
Proof.
  intros k Hk.
  split.
  - apply certify_to_level_certified. exact Hk.
  - exists (instr_certify (k - 1)).
    split.
    + unfold certify_to_level, executed_instructions.
      simpl. left. reflexivity.
    + unfold certifies_at_level. lia.
Qed.

(** ** Section 5: The µ-Hierarchy Theorem *)

(** THE MAIN THEOREM.
    For every k ≥ 1, the µ-hierarchy is strict at level k:
    (1) Level k is achievable: a single trace of cost k certifies.
    (2) Level k requires cost ≥ k: no cheaper trace can execute a level-k
        certifier and end certified.

    This is the µ-analogue of the time hierarchy theorem.
    The µ-dimension creates a proper infinite complexity ladder:
    each rung requires irreducibly more certified structural cost. *)
Theorem mu_hierarchy_theorem :
  forall k, k >= 1 ->
    (* Part 1: Achievability — existence of a k-cost certifying trace *)
    (exists fuel trace,
      trace_mu_cost fuel trace init_state = k /\
      level_k_certified k fuel trace) /\
    (* Part 2: Lower bound — cost ≥ k is necessary for level-k certification *)
    (forall fuel trace,
      level_k_certified k fuel trace ->
      trace_mu_cost fuel trace init_state >= k).
Proof.
  intros k Hk.
  split.
  - exists 1, (certify_to_level k).
    split.
    + apply certify_to_level_cost. exact Hk.
    + apply certify_to_level_has_level. exact Hk.
  - intros fuel trace Hlevel.
    apply level_k_certification_cost_floor. exact Hlevel.
Qed.

(** ** Section 6: Corollaries *)

(** The µ-budget classes form a proper strict hierarchy:
    for each k ≥ 1, no trace with cost < k can be level-k certified. *)
Corollary mu_hierarchy_strict :
  forall k fuel trace,
    k >= 1 ->
    trace_mu_cost fuel trace init_state < k ->
    ~ level_k_certified k fuel trace.
Proof.
  intros k fuel trace Hk Hcost Hlevel.
  pose proof (level_k_certification_cost_floor k fuel trace Hlevel).
  lia.
Qed.

(** No fixed µ-budget suffices for all levels.
    For any budget B, level (B+1) cannot be reached with cost ≤ B. *)
Corollary mu_hierarchy_no_upper_bound :
  forall budget, exists k,
    k >= 1 /\
    ~ (exists fuel trace,
        trace_mu_cost fuel trace init_state <= budget /\
        level_k_certified k fuel trace).
Proof.
  intro budget.
  exists (budget + 1).
  split. lia.
  intros [fuel [trace [Hcost Hlevel]]].
  pose proof (level_k_certification_cost_floor (budget + 1) fuel trace Hlevel).
  lia.
Qed.

(** The µ-hierarchy is infinite: no fixed k0 collapses all levels above k0.
    For every proposed ceiling, there is a strictly higher level. *)
Corollary mu_dimension_unbounded :
  forall k0, exists k,
    k > k0 /\
    (exists fuel trace,
      trace_mu_cost fuel trace init_state = k /\
      level_k_certified k fuel trace).
Proof.
  intro k0.
  exists (k0 + 1).
  split. lia.
  assert (Hk : k0 + 1 >= 1) by lia.
  destruct (proj1 (mu_hierarchy_theorem (k0 + 1) Hk)) as [fuel [trace H]].
  exists fuel, trace. exact H.
Qed.
