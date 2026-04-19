(** MuShannonBridge: connecting mu to Shannon-style reasoning.

    Earlier versions of the repo blurred two different claims: the part I can
    actually prove from the VM cost ledger, and the stronger Shannon-style
    story people want to tell about search-space collapse. This file separates
    them cleanly.

    The proven part is modest. I define what it means to distinguish states,
    keep the ledger identity delta-mu = declared cost sum, and prove bounds
    that go through once the pricing policy is assumed. The unproven part is
    also stated plainly: I do not yet have a first-principles proof that every
    n-way distinction requires cost-bearing operations in the general form a
    Shannon argument would want.

    The naive single-trace entropy slogan was too strong, and this file keeps
    that failure visible instead of pretending it is almost proved. *)

(* INQUISITOR NOTE: proof-connectivity — bridges MuLedgerConservation to
   Shannon information theory. Foundational for NoFI generalization. *)

From Coq Require Import List Lia Arith.PeanoNat Arith.Compare_dec.
Import ListNotations.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import SimulationProof.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import MuNoFreeInsightQuantitative.

(**

  A feasible set is just the list of initial VM states still in play before
  execution. Search-space reduction means the trace leaves fewer of those
  states plausible afterward.
  *)

(** The feasible set type: a list of VMStates *)
Definition FeasibleSet := list VMState.

(** Size of a feasible set *)
Definition feasible_size (omega : FeasibleSet) : nat := length omega.

(** A program DISTINGUISHES two states if it maps them to different final states *)
Definition distinguishes (fuel : nat) (trace : list vm_instruction)
    (s1 s2 : VMState) : Prop :=
  run_vm fuel trace s1 <> run_vm fuel trace s2.

(** A program SEPARATES a feasible set: all pairs produce distinct outputs *)
Definition separates (fuel : nat) (trace : list vm_instruction)
    (omega : FeasibleSet) : Prop :=
  forall s1 s2,
    In s1 omega -> In s2 omega -> s1 <> s2 ->
    distinguishes fuel trace s1 s2.

(**

    Nat.log2 is floor log base 2, so the bound gets written with truncated nat
    subtraction rather than real-valued entropy algebra.
    *)

(** Helper: log₂ is monotone *)
Lemma log2_le_mono : forall m n, m <= n -> Nat.log2 m <= Nat.log2 n.
Proof.
  intros m n H.
  apply Nat.log2_le_mono.
  exact H.
Qed.

(** Helper: 2^(log₂ n) ≤ n for n ≥ 1 *)
Lemma pow2_log2_le : forall n, n >= 1 -> 2 ^ (Nat.log2 n) <= n.
Proof.
  intros n H.
  apply Nat.log2_spec.
  lia.
Qed.

(**

  This next bound is policy-based. If the declared costs are chosen to price
  information-carrying operations hard enough, then mu is forced above the
  corresponding log bound. That is useful, but it is not the same thing as a
  first-principles theorem about all possible distinctions.
    "honestly priced." The purpose is to make the pricing requirement explicit.
    *)

(** An instruction is "info-priced" if its cost ≥ 1 whenever it is a
    cert-setting operation.
    Since EMIT, REVEAL, LASSERT, LJOIN, READ_PORT, CERTIFY all include the
    S-cost floor in instruction_cost, this is now unconditionally true for every
    instruction. Some of them also add explicit payload bits.
    The definition is kept for backwards compatibility; use all_info_priced
    to discharge it without any hypothesis. *)
Definition info_priced (instr : vm_instruction) : Prop :=
  is_cert_setterb instr = true -> instruction_cost instr >= 1.

(** A trace is "info-priced" if all instructions are *)
Definition trace_info_priced (trace : list vm_instruction) : Prop :=
  Forall info_priced trace.

(** Number of cert-setting instructions in a trace *)
Fixpoint count_cert_setters (trace : list vm_instruction) : nat :=
  match trace with
  | [] => 0
  | instr :: rest =>
    (match instr with
     | instr_reveal _ _ _ _  => 1
     | instr_emit _ _ _      => 1
     | instr_lassert _ _ _ _ _ => 1
     | instr_certify _       => 1
     | instr_ljoin _ _ _     => 1
     | _                     => 0
     end) + count_cert_setters rest
  end.

(**

    Under the pricing policy, Δμ ≥ count_cert_setters * 1.
    This is a lower bound on information-bearing operations.
    *)

(** all_info_priced: every instruction is info-priced unconditionally.
    Cert-setters (EMIT, REVEAL, LASSERT, LJOIN, READ_PORT, CERTIFY) all
    include an S-cost floor in instruction_cost, so instruction_cost >= 1 by
    construction. *)
Lemma all_info_priced : forall instr, info_priced instr.
Proof.
  intro instr.
  unfold info_priced.
  intro Hcert.
  apply VMStep.cert_setter_cost_pos.
  exact Hcert.
Qed.

(** all_traces_info_priced: every trace is info-priced unconditionally. *)
Lemma all_traces_info_priced : forall trace, trace_info_priced trace.
Proof.
  intro trace.
  apply Forall_forall.
  intros instr _.
  apply all_info_priced.
Qed.

(** Conservation law: Δμ = sum of all instruction costs *)
Theorem delta_mu_equals_ledger_sum :
  forall fuel trace s,
    (run_vm fuel trace s).(vm_mu) - s.(vm_mu) =
    ledger_sum (ledger_entries fuel trace s).
Proof.
  intros fuel trace s.
  pose proof (bounded_model_mu_ledger_conservation fuel trace s) as [_ Hcons].
  lia.
Qed.

(**
    SECTION 4b: POLICY-BASED BOUND (PROVABLE WITHOUT PROBABILISTIC SEMANTICS)

    We prove: under the info-pricing policy, the number of cert-setting
    instruction EXECUTIONS is bounded above by Δμ.

    This is the strongest result we can prove without probabilistic semantics.
    It says: you can't execute more cert-setting operations than you pay for.


    RELATIONSHIP TO THE HISTORICAL SINGLE-TRACE CLAIM:
    This bound gives: Δμ ≥ cert_setter_executions.
    The rejected single-trace claim would need: cert_setter_executions ≥ log₂|Ω|
    on every realized path, which is not true in general.
    The remaining gap is expectation-level or whole-tree: aggregate over the
    entire branching structure, not one lucky execution path.
    *)

(** Number of cert-setting instruction executions in a bounded run *)
Fixpoint cert_setter_executions (fuel : nat) (trace : list vm_instruction)
    (s : VMState) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      match nth_error trace s.(vm_pc) with
      | Some instr =>
          (if is_cert_setterb instr then 1 else 0) +
          cert_setter_executions fuel' trace (vm_apply s instr)
      | None => 0
      end
  end.

(** info_priced_cert_setter_cost_pos: cert-setters cost ≥ 1 (unconditional).
    No trace or pricing-policy hypothesis needed — follows directly from
    cert_setter_cost_pos in VMStep. *)
Lemma info_priced_cert_setter_cost_pos :
  forall (instr : vm_instruction),
    is_cert_setterb instr = true ->
    instruction_cost instr >= 1.
Proof.
  intros instr Hsetter.
  apply VMStep.cert_setter_cost_pos. exact Hsetter.
Qed.

(** cert_executions_le_ledger: unconditional — no pricing-policy hypothesis needed.
    All cert-setters cost ≥ 1 by construction (S cost in instruction_cost). *)
Lemma cert_executions_le_ledger :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState),
    cert_setter_executions fuel trace s <=
    ledger_sum (ledger_entries fuel trace s).
Proof.
  induction fuel as [|fuel IH]; intros trace s; simpl.
  - lia.
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hnth; simpl.
    + pose proof (IH trace (vm_apply s instr)) as IH'.
      destruct (is_cert_setterb instr) eqn:Hsetter.
      * assert (Hcost : instruction_cost instr >= 1).
        { apply info_priced_cert_setter_cost_pos. exact Hsetter. }
        lia.
      * lia.
    + lia.
Qed.

(** THEOREM (Unconditional Cert-Execution Bound):
    Δμ ≥ number of cert-setting instruction executions — no hypothesis needed.
    All cert-setters charge S cost ≥ 1 by construction.

    This is the maximum bound provable without probabilistic semantics.
    The full Shannon bound (Δμ ≥ log₂|Ω|) requires probabilistic semantics. *)
Theorem info_priced_cert_executions_bound :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState),
    cert_setter_executions fuel trace s <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  intros fuel trace s.
  rewrite delta_mu_equals_ledger_sum.
  apply cert_executions_le_ledger.
Qed.

(**

   This section records the rejected single-trace formulation and makes the
   real remaining gap explicit.

   What is rejected:
   1. Bounding one realized execution path by the entropy reduction of the
     whole feasible-set collapse.

   What remains open:
   1. An expectation-level or whole-decision-tree semantics tying the full
     branching structure to entropy reduction.

    *)

(** [shannon_entropy_reduction]: How much Shannon entropy is eliminated when
    a feasible set Ω reduces to Ω' (assuming uniform prior over Ω).

    H(prior) - H(posterior) = log₂|Ω| - log₂|Ω'|
    (using truncated nat subtraction — Nat.log2 0 = 0 by Coq convention) *)
Definition shannon_entropy_reduction (omega_init omega_final : FeasibleSet) : nat :=
  Nat.log2 (feasible_size omega_init) -
  Nat.log2 (feasible_size omega_final).

(** HISTORICAL SINGLE-TRACE CLAIM:
   Executing a trace that reduces the feasible set from Ω to Ω' requires
   Δμ ≥ log₂|Ω| - log₂|Ω'|.

   Status: FALSE IN GENERAL under the current deterministic VM semantics.
   This definition is retained only as a precise record of the rejected claim.

   Why it fails:
   1. A single trace is one realized path through a larger branching object.
   2. Shannon-style lower bounds apply to expected code length or whole-tree
     structure, not to an arbitrarily short successful path.
   3. Under current VM semantics, one short certification path can isolate a
     leaf of a larger feasible set without paying log₂ of the original set size.

    Key challenge: The Thiele VM is DETERMINISTIC. Shannon entropy reduction
    in the classical sense requires a probabilistic model. The connection
    between deterministic VM execution and probabilistic information theory
    requires either:
    (a) A meta-level argument about programs computing over distributions
    (b) An extension of the VM with explicit probability annotations
    (c) An algorithmic information theory approach (Kolmogorov complexity)
        rather than Shannon entropy

    The closest existing result: MuNoFreeInsightQuantitative.supra_cert_implies_mu_lower_bound_trace_run
    proves that cert-setting requires paying some μ > 0.
  The actual missing piece is an expectation-level or whole-tree bridge from
  certification structure to entropy reduction. *)

(** Consistent feasible-set reduction.
    Requires probabilistic semantics (expectation-level feasible-set bridge). *)
Definition consistent_reduction
    (fuel : nat) (trace : list vm_instruction)
    (omega_init omega_final : FeasibleSet)
    (s_init : VMState) : Prop :=
  (* omega_final = states reachable from omega_init via trace *)
  forall s, In s omega_final ->
    In s omega_init /\
    exists s_out, run_vm fuel trace s = s_out.

(** Rejected single-trace formulation, kept as a named boundary marker. *)
Definition MuShannonSingleTraceClaim : Prop :=
  forall (fuel : nat) (trace : list vm_instruction)
         (s_init : VMState)
         (omega_init omega_final : FeasibleSet),
    In s_init omega_init ->
    feasible_size omega_init > 0 ->
    feasible_size omega_final > 0 ->
    feasible_size omega_final <= feasible_size omega_init ->
    consistent_reduction fuel trace omega_init omega_final s_init ->
    trace_info_priced trace ->
    (run_vm fuel trace s_init).(vm_mu) - s_init.(vm_mu) >=
      shannon_entropy_reduction omega_init omega_final.

(** Deprecated alias retained for repository continuity and cross-file comments. *)
Definition MuShannonConjecture : Prop := MuShannonSingleTraceClaim.

(**
    SECTION 5b: DECISION-TREE LOWER-BOUND FRAMEWORK

    Instead of postulating full probabilistic semantics immediately, we can
    factor the Shannon bridge through an abstract binary decision tree.

    Interpretation:
    - each internal node is one certification-bearing binary distinction
    - each leaf is one distinguishable outcome class
    - a trace that realizes such a tree must pay for at least its depth

    This does NOT yet prove that every feasible-set reduction in the VM induces
    such a tree. That remaining step is now isolated as a concrete proof task:
    compile execution-side separation/certification behavior into this tree model.
    *)

Inductive DecisionTree : Type :=
| dt_leaf
| dt_branch (left_tree right_tree : DecisionTree).

Fixpoint decision_tree_depth (tree : DecisionTree) : nat :=
  match tree with
  | dt_leaf => 0
  | dt_branch left_tree right_tree =>
      S (Nat.max (decision_tree_depth left_tree) (decision_tree_depth right_tree))
  end.

Fixpoint decision_tree_leaf_count (tree : DecisionTree) : nat :=
  match tree with
  | dt_leaf => 1
  | dt_branch left_tree right_tree =>
      decision_tree_leaf_count left_tree + decision_tree_leaf_count right_tree
  end.

Lemma decision_tree_leaves_le_pow2_depth :
  forall tree,
    decision_tree_leaf_count tree <= 2 ^ decision_tree_depth tree.
Proof.
  induction tree as [|left IHleft right IHright]; simpl.
  - reflexivity.
  - set (depth_bound := Nat.max (decision_tree_depth left) (decision_tree_depth right)).
    eapply Nat.le_trans.
    + apply Nat.add_le_mono.
      * eapply Nat.le_trans.
        { exact IHleft. }
        apply Nat.pow_le_mono_r.
        { lia. }
        unfold depth_bound.
        apply Nat.le_max_l.
      * eapply Nat.le_trans.
        { exact IHright. }
        apply Nat.pow_le_mono_r.
        { lia. }
        unfold depth_bound.
        apply Nat.le_max_r.
    + unfold depth_bound.
      replace (2 ^ Nat.max (decision_tree_depth left) (decision_tree_depth right) +
               2 ^ Nat.max (decision_tree_depth left) (decision_tree_depth right))
        with (2 * 2 ^ Nat.max (decision_tree_depth left) (decision_tree_depth right)) by lia.
      rewrite <- Nat.pow_succ_r' by lia.
      reflexivity.
Qed.

Lemma decision_tree_log2_leaf_bound :
  forall tree,
    Nat.log2 (decision_tree_leaf_count tree) <= decision_tree_depth tree.
Proof.
  intro tree.
  eapply Nat.le_trans.
  - apply log2_le_mono.
    apply decision_tree_leaves_le_pow2_depth.
  - rewrite Nat.log2_pow2 by lia.
    reflexivity.
Qed.

Definition decision_tree_realized_by_trace
    (fuel : nat) (trace : list vm_instruction) (s : VMState) (tree : DecisionTree) : Prop :=
  decision_tree_depth tree <= cert_setter_executions fuel trace s.

(** A decision tree covers a feasible-set reduction when its leaves are
    numerous enough to index the posterior classes within the prior space. *)
Definition tree_covers_feasible_reduction
    (tree : DecisionTree) (omega_prior omega_posterior : FeasibleSet) : Prop :=
  feasible_size omega_prior <=
    decision_tree_leaf_count tree * feasible_size omega_posterior.

(** A structured feasible-set reduction witness: each posterior state carries
    a finite fiber of prior states that reduce to it, and every fiber is
    bounded by the tree's leaf budget. This is the first semantics layer that
    derives the leaf-cover inequality instead of assuming it numerically. *)
Definition FiberedFeasibleReduction
    (tree : DecisionTree) (omega_prior omega_posterior : FeasibleSet) : Prop :=
  exists fibers : list (VMState * FeasibleSet),
    map fst fibers = omega_posterior /\
    (feasible_size omega_prior <=
      fold_right Nat.add 0 (map (fun '(_, fiber) => feasible_size fiber) fibers)) /\
    Forall (fun '(_, fiber) => feasible_size fiber <= decision_tree_leaf_count tree) fibers.

Definition ObservationFunction := VMState -> list vm_instruction.

Definition observation_equiv
    (obs_fn : ObservationFunction) (s1 s2 : VMState) : Prop :=
  obs_fn s1 = obs_fn s2.

Definition posterior_representative_fibers
    (omega_posterior : FeasibleSet) (fiber_of : VMState -> FeasibleSet)
    : list (VMState * FeasibleSet) :=
  map (fun s_post => (s_post, fiber_of s_post)) omega_posterior.

(** A posterior-representative reduction chooses, for each posterior state,
    a fiber of prior states observation-equivalent to that representative.
    This is stronger than the raw fiber witness because it ties the grouping to
    an explicit observation function on feasible sets. *)
Definition PosteriorRepresentativeReduction
    (obs_fn : ObservationFunction)
    (tree : DecisionTree) (omega_prior omega_posterior : FeasibleSet) : Prop :=
  exists fiber_of : VMState -> FeasibleSet,
    (forall s_prior, In s_prior omega_prior ->
      exists s_post,
        In s_post omega_posterior /\
        In s_prior (fiber_of s_post) /\
        observation_equiv obs_fn s_prior s_post) /\
    (feasible_size omega_prior <=
      fold_right Nat.add 0 (map (fun s_post => feasible_size (fiber_of s_post)) omega_posterior)) /\
    (forall s_post, In s_post omega_posterior ->
      feasible_size (fiber_of s_post) <= decision_tree_leaf_count tree).

Lemma posterior_representative_fibers_index :
  forall omega_posterior fiber_of,
    map fst (posterior_representative_fibers omega_posterior fiber_of) = omega_posterior.
Proof.
  induction omega_posterior as [| s_post rest IH]; intros fiber_of; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma posterior_representative_fibers_bounded :
  forall (tree : DecisionTree) (omega_posterior : FeasibleSet)
         (fiber_of : VMState -> FeasibleSet),
    (forall s_post, In s_post omega_posterior ->
      feasible_size (fiber_of s_post) <= decision_tree_leaf_count tree) ->
    Forall (fun '(_, fiber) => feasible_size fiber <= decision_tree_leaf_count tree)
      (posterior_representative_fibers omega_posterior fiber_of).
Proof.
  intros tree omega_posterior fiber_of Hbound.
  induction omega_posterior as [| s_post rest IH]; simpl.
  - constructor.
  - constructor.
    + apply Hbound. left. reflexivity.
    + apply IH. intros s_post' Hin.
      apply Hbound. right. exact Hin.
Qed.

Lemma posterior_representative_fibers_cover_sum :
  forall omega_posterior fiber_of,
    fold_right Nat.add 0
      (map (fun '(_, fiber) => feasible_size fiber)
        (posterior_representative_fibers omega_posterior fiber_of)) =
    fold_right Nat.add 0
      (map (fun s_post => feasible_size (fiber_of s_post)) omega_posterior).
Proof.
  induction omega_posterior as [| s_post rest IH]; intros fiber_of; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma posterior_representative_reduction_assigns_observation_equiv :
  forall (obs_fn : ObservationFunction) (tree : DecisionTree)
         (omega_prior omega_posterior : FeasibleSet),
    PosteriorRepresentativeReduction obs_fn tree omega_prior omega_posterior ->
    exists fiber_of,
      forall s_prior, In s_prior omega_prior ->
        exists s_post,
          In (s_post, fiber_of s_post)
            (posterior_representative_fibers omega_posterior fiber_of) /\
          In s_prior (fiber_of s_post) /\
          observation_equiv obs_fn s_prior s_post.
Proof.
  intros obs_fn tree omega_prior omega_posterior Hrepr.
  destruct Hrepr as [fiber_of [Hassign [Hcover Hbound]]].
  exists fiber_of.
  intros s_prior Hin_prior.
  destruct (Hassign s_prior Hin_prior) as [s_post [Hin_post [Hin_fiber Hequiv]]].
  exists s_post.
  split.
  - unfold posterior_representative_fibers.
    apply in_map_iff.
    exists s_post.
    split.
    + exact eq_refl.
    + exact Hin_post.
  - split; assumption.
Qed.

Lemma bounded_fiber_sum_le_mul :
  forall (tree : DecisionTree) (fibers : list (VMState * FeasibleSet)),
    Forall (fun '(_, fiber) => feasible_size fiber <= decision_tree_leaf_count tree) fibers ->
    fold_right Nat.add 0 (map (fun '(_, fiber) => feasible_size fiber) fibers) <=
      decision_tree_leaf_count tree * List.length fibers.
Proof.
  intros tree fibers Hbounded.
  induction Hbounded as [| [s_post fiber] rest Hbound Hrest IH]; simpl.
  - lia.
  - lia.
Qed.

Theorem fibered_reduction_implies_tree_cover :
  forall (tree : DecisionTree) (omega_prior omega_posterior : FeasibleSet),
    FiberedFeasibleReduction tree omega_prior omega_posterior ->
    tree_covers_feasible_reduction tree omega_prior omega_posterior.
Proof.
  intros tree omega_prior omega_posterior Hfibered.
  destruct Hfibered as [fibers [Hindex [Hcover Hbounded]]].
  unfold tree_covers_feasible_reduction.
  rewrite <- Hindex.
  unfold feasible_size.
  apply Nat.le_trans with
    (m := fold_right Nat.add 0 (map (fun '(_, fiber) => feasible_size fiber) fibers)).
  - exact Hcover.
  - rewrite map_length.
    apply bounded_fiber_sum_le_mul.
    exact Hbounded.
Qed.

Theorem posterior_representative_reduction_implies_fibered_reduction :
  forall (obs_fn : ObservationFunction) (tree : DecisionTree)
         (omega_prior omega_posterior : FeasibleSet),
    PosteriorRepresentativeReduction obs_fn tree omega_prior omega_posterior ->
    FiberedFeasibleReduction tree omega_prior omega_posterior.
Proof.
  intros obs_fn tree omega_prior omega_posterior Hrepr.
  destruct Hrepr as [fiber_of [_ [Hcover Hbound]]].
  exists (posterior_representative_fibers omega_posterior fiber_of).
  split.
  - apply posterior_representative_fibers_index.
  - split.
    + rewrite posterior_representative_fibers_cover_sum. exact Hcover.
    + apply posterior_representative_fibers_bounded.
      exact Hbound.
Qed.

Lemma decision_tree_leaf_count_positive :
  forall tree,
    decision_tree_leaf_count tree > 0.
Proof.
  induction tree; simpl; lia.
Qed.

Lemma decision_tree_log2_up_leaf_bound :
  forall tree,
    Nat.log2_up (decision_tree_leaf_count tree) <= decision_tree_depth tree.
Proof.
  intro tree.
  apply (proj1 (Nat.log2_up_le_pow2
    (decision_tree_leaf_count tree)
    (decision_tree_depth tree)
    (decision_tree_leaf_count_positive tree))).
  apply decision_tree_leaves_le_pow2_depth.
Qed.

Theorem info_priced_decision_tree_leaf_bound :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState) (tree : DecisionTree),
    decision_tree_realized_by_trace fuel trace s tree ->
    Nat.log2 (decision_tree_leaf_count tree) <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  intros fuel trace s tree Htree.
  unfold decision_tree_realized_by_trace in Htree.
  eapply Nat.le_trans.
  - apply decision_tree_log2_leaf_bound.
  - eapply Nat.le_trans.
    + exact Htree.
    + apply info_priced_cert_executions_bound.
Qed.

Theorem info_priced_decision_tree_log2_up_leaf_bound :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState) (tree : DecisionTree),
    decision_tree_realized_by_trace fuel trace s tree ->
    Nat.log2_up (decision_tree_leaf_count tree) <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  intros fuel trace s tree Htree.
  unfold decision_tree_realized_by_trace in Htree.
  eapply Nat.le_trans.
  - apply decision_tree_log2_up_leaf_bound.
  - eapply Nat.le_trans.
    + exact Htree.
    + apply info_priced_cert_executions_bound.
Qed.

Lemma tree_cover_implies_log2_up_reduction_bound :
  forall (tree : DecisionTree) (omega_prior omega_posterior : FeasibleSet),
    feasible_size omega_posterior > 0 ->
    tree_covers_feasible_reduction tree omega_prior omega_posterior ->
    Nat.log2_up (feasible_size omega_prior) -
      Nat.log2_up (feasible_size omega_posterior) <=
    Nat.log2_up (decision_tree_leaf_count tree).
Proof.
  intros tree omega_prior omega_posterior Hpost Hcover.
  unfold tree_covers_feasible_reduction in Hcover.
  assert (Hmono :
    Nat.log2_up (feasible_size omega_prior) <=
    Nat.log2_up (decision_tree_leaf_count tree * feasible_size omega_posterior)).
  { apply Nat.log2_up_le_mono. exact Hcover. }
  assert (Hmul :
    Nat.log2_up (decision_tree_leaf_count tree * feasible_size omega_posterior) <=
    Nat.log2_up (decision_tree_leaf_count tree) + Nat.log2_up (feasible_size omega_posterior)).
  { apply Nat.log2_up_mul_above; lia. }
  lia.
Qed.

Theorem info_priced_arbitrary_feasible_reduction_bound :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState)
         (omega_prior omega_posterior : FeasibleSet) (tree : DecisionTree),
    decision_tree_realized_by_trace fuel trace s tree ->
    feasible_size omega_posterior > 0 ->
    tree_covers_feasible_reduction tree omega_prior omega_posterior ->
    Nat.log2_up (feasible_size omega_prior) -
      Nat.log2_up (feasible_size omega_posterior) <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  intros fuel trace s omega_prior omega_posterior tree Htree Hpost Hcover.
  eapply Nat.le_trans.
  - apply tree_cover_implies_log2_up_reduction_bound; eauto.
  - apply info_priced_decision_tree_log2_up_leaf_bound; assumption.
Qed.

Theorem info_priced_fibered_feasible_reduction_bound :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState)
         (omega_prior omega_posterior : FeasibleSet) (tree : DecisionTree),
    decision_tree_realized_by_trace fuel trace s tree ->
    feasible_size omega_posterior > 0 ->
    FiberedFeasibleReduction tree omega_prior omega_posterior ->
    Nat.log2_up (feasible_size omega_prior) -
      Nat.log2_up (feasible_size omega_posterior) <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  intros fuel trace s omega_prior omega_posterior tree Htree Hpost Hfibered.
  eapply info_priced_arbitrary_feasible_reduction_bound; eauto.
  apply fibered_reduction_implies_tree_cover.
  exact Hfibered.
Qed.

Theorem info_priced_posterior_representative_reduction_bound :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState)
         (omega_prior omega_posterior : FeasibleSet) (tree : DecisionTree)
         (obs_fn : ObservationFunction),
    decision_tree_realized_by_trace fuel trace s tree ->
    feasible_size omega_posterior > 0 ->
    PosteriorRepresentativeReduction obs_fn tree omega_prior omega_posterior ->
    Nat.log2_up (feasible_size omega_prior) -
      Nat.log2_up (feasible_size omega_posterior) <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  intros fuel trace s omega_prior omega_posterior tree obs_fn.
  intros Htree Hpost Hrepr.
  eapply info_priced_fibered_feasible_reduction_bound; eauto.
  apply posterior_representative_reduction_implies_fibered_reduction with (obs_fn := obs_fn).
  exact Hrepr.
Qed.

(**

    These are theorems that hold unconditionally, establishing the
    infrastructure for the eventual full proof.
    *)

(** Trivial bound: any certified execution spends some μ (from conservation) *)
Theorem mu_nonnegative_under_execution :
  forall fuel trace s,
    (run_vm fuel trace s).(vm_mu) >= s.(vm_mu).
Proof.
  intros fuel trace s.
  pose proof (bounded_model_mu_ledger_conservation fuel trace s) as [_ Hcons].
  lia.
Qed.

(** The image of a list under run_vm has the same cardinality (as a multiset),
    since run_vm is a function. Distinct inputs may be mapped to the same output,
    so the *set* image can only decrease. *)
Lemma run_vm_map_length :
  forall (fuel : nat) (trace : list vm_instruction) (omega : FeasibleSet),
    length (map (run_vm fuel trace) omega) = length omega.
Proof.
  intros fuel trace omega.
  apply map_length.
Qed.
(* NOTE: The set image |{run_vm fuel trace s | s ∈ Ω}| ≤ |Ω|. Formalizing
   this requires decidable equality on VMState for NoDup on the image, which
   is available but verbose. The above multiset bound is the provable form.
   The interesting direction: if the set image is SMALLER, information is lost,
   which requires cert-setting operations to recover via certification.
  This connects to the historical single-trace claim stated above and shows
  why the tree-depth hypothesis must be made explicit. *)

(**

    Summary of how this file fits with existing proofs:

    EXISTING:
    - MuLedgerConservation: Δμ = Σ costs (proven, sound)
    - MuNoFreeInsightQuantitative: cert-setting requires Δμ > 0 (proven)
    - MuChaitin: cert payload bounded by Δμ under pricing policy (proven)
    - NoFreeInsight.v: strengthening P_weak to P_strong requires structure
      event with cost > 0 (proven for the Thiele VM)

    REMAINING OPEN WORK:
    - Expectation-level connection between Δμ and entropy reduction
    - Probabilistic semantics: what distribution over inputs justifies entropy calc
    - Compilation of VM-side separation behavior into a whole decision-tree model

    The existing results prove NoFI QUALITATIVELY (any cert costs > 0).
    The conditional tree bound strengthens this QUANTITATIVELY when the
    decision-tree hypothesis is explicit. The arbitrary feasible-set reduction
    bound packages that hypothesis as an explicit leaf-cover condition over
    |Ω| and |Ω'|. The naive single-trace strengthening is false in general.
    *)

(** End of MuShannonBridge.
    Open work:
  - Define an expectation-level feasible-set semantics over input distributions
  - Connect consistent_reduction / decision-tree structure to Bayesian belief update
  - Prove the expected certification cost bound against the Shannon target *)
