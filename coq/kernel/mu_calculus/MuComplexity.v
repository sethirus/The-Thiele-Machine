(** MuComplexity: trace-budget predicates and program-cost arithmetic.

    The Thiele Machine adds a third axis to computational complexity: mu-cost,
    the price of certified structural knowledge. Classical complexity theory
    measures time (steps) and space (memory). The Thiele Machine also measures
    mu: how much the machine paid for the certified structural insights it used.

    This file does not classify problems along that axis. It defines two
    budget predicates and proves cost arithmetic.

    [error_free_preservation_budget] supplies an error-free trace for each
    input, with bounded length and mu, preserving a Boolean state predicate
    when mu increases. It has no returned-answer requirement and no uniform
    program shared by all inputs.

    [positive_input_certification_budget] supplies a bounded certifying
    trace for each input satisfying a Boolean predicate. It imposes no
    rejection requirement on negative inputs.

    Neither predicate expresses decision or verification complexity.
    Their numeric bounds may be arbitrary functions. The SAT section
    proves arithmetic for specified cost formulas. *)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.

(** ** Basic Definitions *)

(** A program trace is a list of instructions to execute. *)
Definition Trace := list vm_instruction.

(** The mu-cost of a trace starting from a state is the total mu spent. *)
Definition trace_mu_cost (fuel : nat) (trace : Trace) (s : VMState) : nat :=
  (run_vm fuel trace s).(vm_mu) - s.(vm_mu).

(** A decision problem is a function from input states to bool (accept/reject). *)
Definition DecisionProblem := VMState -> bool.

(** Numeric bounds have no polynomiality requirement. *)
Definition BudgetBound := nat -> nat.

Definition error_free_preservation_budget
    (P : DecisionProblem)
    (size : VMState -> nat)
    (p_fuel : BudgetBound)
    (p_mu : BudgetBound) : Prop :=
  forall (s : VMState),
  exists (trace : Trace),
    (* The trace is short enough *)
    length trace <= p_fuel (size s) /\
    (* The mu-cost is bounded *)
    trace_mu_cost (p_fuel (size s)) trace s <= p_mu (size s) /\
    (* Error freedom and conditional preservation of the state predicate. *)
    (run_vm (p_fuel (size s)) trace s).(vm_err) = false /\
    ((run_vm (p_fuel (size s)) trace s).(vm_mu) > s.(vm_mu) ->
     P (run_vm (p_fuel (size s)) trace s) = P s).

(** Every positive input has some bounded trace ending certified. *)

Definition positive_input_certification_budget
    (P : DecisionProblem)
    (size : VMState -> nat)
    (p_fuel : BudgetBound)
    (p_mu : BudgetBound) : Prop :=
  forall (s : VMState),
    P s = true ->
    exists (cert : Trace),
      length cert <= p_fuel (size s) /\
      trace_mu_cost (p_fuel (size s)) cert s <= p_mu (size s) /\
      (run_vm (p_fuel (size s)) cert s).(vm_certified) = true.

(** A named implication between the predicates; no proof is supplied here. *)

Definition preservation_to_certification_premise
    (P : DecisionProblem) (size : VMState -> nat)
    (p_fuel p_mu : BudgetBound) : Prop :=
  error_free_preservation_budget P size p_fuel p_mu ->
  exists p_fuel' p_mu', positive_input_certification_budget P size p_fuel' p_mu'.

(** Zero mu cost. *)
Definition zero_mu_program (fuel : nat) (trace : Trace) (s : VMState) : Prop :=
  trace_mu_cost fuel trace s = 0.

(** Zero-mu error-free witnesses satisfy the preservation budget for every
    Boolean predicate because the positive-mu antecedent never holds. *)
Theorem zero_mu_traces_satisfy_preservation_budget :
  forall P size p_fuel,
    (forall s, exists trace,
      length trace <= p_fuel (size s) /\
      zero_mu_program (p_fuel (size s)) trace s /\
      (run_vm (p_fuel (size s)) trace s).(vm_err) = false) ->
    error_free_preservation_budget P size p_fuel (fun _ => 0).
Proof.
  intros P size p_fuel H s.
  destruct (H s) as [trace [Hlen [Hmu Herr]]].
  exists trace. split. exact Hlen.
  split. unfold zero_mu_program in Hmu. rewrite Hmu. lia.
  split. exact Herr.
  intros Hmu_pos.
  unfold zero_mu_program in Hmu. unfold trace_mu_cost in Hmu.
  (* mu stayed 0, so the condition is vacuously satisfied *)
  exfalso. lia.
Qed.

(** [mu_time_tradeoff]: a concrete trade between mu-cost and step-cost.

    At the StructuralAdvantage witness size the blind program (0 mu) runs in
    N^2 steps while the sighted program (18 mu) runs in 2*N steps. For every
    N > 18 the two axes move in opposite directions: the sighted program pays
    strictly more mu (18 vs 0) and takes strictly fewer steps (2*N < N^2).
    Paying mu buys steps back — that is the trade, stated as real arithmetic
    rather than as a vacuous conjunction.

    This is the in-file arithmetic witness for the 18-mu structural advantage.
    The unbounded, cost-model version is
    [StructuralAdvantage.advantage_factor_unbounded]; the SAT section below
    proves the analogous gap for factored SAT. *)
Definition mu_time_tradeoff : Prop :=
  exists (N blind_steps blind_mu sighted_steps sighted_mu : nat),
    N > 18 /\
    blind_steps   = N * N /\ blind_mu   = 0  /\
    sighted_steps = 2 * N /\ sighted_mu = 18 /\
    sighted_mu    > blind_mu /\       (* the price paid on the mu axis *)
    sighted_steps < blind_steps.      (* and the steps it buys back *)

Lemma mu_time_tradeoff_witness : mu_time_tradeoff.
Proof.
  exists 100, (100 * 100), 0, (2 * 100), 18.
  repeat split; lia.
Qed.

(** ** SAT decomposition benchmark: a concrete blind-vs-sighted cost gap.

    This section establishes a concrete program-cost gap between a blind
    solver (zero mu) and a sighted solver (mu = 1) on factored SAT.

    Problem: factored SAT. A 2k-variable formula φ = φ₁ ∧ φ₂ where
    vars(φ₁) and vars(φ₂) are disjoint and each has k variables.

    A blind solver (0 mu) must search 4^k = 2^(2k) assignments.
    A sighted solver pays 1 mu to certify independence, then searches
    2^k + 2^k = 2 × 2^k assignments.

    Key arithmetic: 4^k > 2 × 2^k + 1 for all k ≥ 2.
    The ratio 4^k / (2 × 2^k) = 2^(k-1) grows without bound.

    These are purely arithmetic theorems; they establish the separation
    at the witness (program-costs) level. They do NOT constitute a
    class separation: there is no Coq object here corresponding to the
    classical complexity class P, and no proof that no zero-mu program
    can solve factored SAT in subexponential time. The witness is
    concrete, the class-level claim is open. *)

Definition blind_sat_steps  (k : nat) : nat := 4 ^ k.
Definition sighted_sat_steps (k : nat) : nat := 2 * 2 ^ k.
Definition sighted_sat_mu : nat := 1.

(** PROVEN: 4^k = (2^k) * (2^k). Direct by induction. *)
Lemma four_pow_is_sq :
  forall k : nat, 4 ^ k = 2 ^ k * 2 ^ k.
Proof.
  induction k as [|k' IH].
  - reflexivity.
  - simpl. rewrite IH. nia.
Qed.

(** PROVEN: The exact ratio between blind and sighted SAT steps:
    blind steps = 2^(k-1) × sighted steps.
    Parameterized as k = S k' to avoid nat subtraction. *)
Theorem sat_blind_sighted_ratio_exact :
  forall k' : nat,
    blind_sat_steps (S k') = 2 ^ k' * sighted_sat_steps (S k').
Proof.
  intros k'.
  unfold blind_sat_steps, sighted_sat_steps.
  rewrite four_pow_is_sq.
  simpl Nat.pow.
  nia.
Qed.

(** PROVEN: For k ≥ 2, blind strictly exceeds sighted + 1 mu cost.
    4^k > 2 × 2^k + 1 for k ≥ 2. This is the core separation arithmetic. *)
Theorem sat_separation :
  forall k : nat,
    k >= 2 ->
    blind_sat_steps k > sighted_sat_steps k + sighted_sat_mu.
Proof.
  intros k Hk.
  unfold blind_sat_steps, sighted_sat_steps, sighted_sat_mu.
  induction k as [|k' IH].
  - lia.
  - destruct k' as [|k''].
    + lia.
    + destruct k'' as [|k'''].
      * simpl. lia.   (* k = 2: 16 > 8 + 1 = 9 *)
      * assert (IH' : 4 ^ S (S k''') > 2 * 2 ^ S (S k''') + 1)
          by (apply IH; lia).
        unfold blind_sat_steps, sighted_sat_steps, sighted_sat_mu in *.
        assert (H4 : 4 ^ S (S (S k''')) = 4 * 4 ^ S (S k''')).
        { simpl; nia. }
        assert (H2 : 2 ^ S (S (S k''')) = 2 * 2 ^ S (S k''')).
        { simpl; nia. }
        rewrite H4, H2. nia.
Qed.

(** PROVEN: 2^n > n for all n. Used to establish unbounded ratio growth. *)
Lemma two_pow_gt :
  forall n : nat, 2 ^ n > n.
Proof.
  induction n as [|n' IH].
  - simpl. lia.
  - simpl. lia.
Qed.

(** PROVEN: The separation ratio grows without bound.
    For any budget B, there exists k such that blind > B × sighted. *)
Theorem sat_separation_ratio_unbounded :
  forall B : nat,
    exists k : nat,
      k >= 2 /\ blind_sat_steps k > B * sighted_sat_steps k.
Proof.
  intro B.
  (* Witness: k = S(S B). Then ratio = 2^(k-1) = 2^(B+1) > B+1 > B. *)
  exists (S (S B)).
  split. lia.
  rewrite (sat_blind_sighted_ratio_exact (S B)).
  (* Goal: 2^(S B) * sighted > B * sighted, i.e., 2^(S B) > B *)
  (* That's 2^(B+1) > B, which follows from two_pow_gt. *)
  apply Nat.mul_lt_mono_pos_r.
  - unfold sighted_sat_steps.
    assert (H2 := two_pow_gt (S (S B))). lia.
  - assert (H := two_pow_gt (S B)). lia.
Qed.

(** PROVEN: The mu-cost of the sighted solver is constant (1), independent of k. *)
Theorem sat_mu_is_constant : forall k : nat, sighted_sat_mu = 1.
Proof. reflexivity. Qed.

(** ** Summary: a concrete blind-vs-sighted gap on structured SAT.

    The factored SAT problem provides a concrete witness gap between a blind
    solver (mu = 0) and a sighted solver (mu = 1):

    - Blind solver: 4^k steps, 0 mu. Cost grows doubly exponentially in k.
    - Sighted solver: 2 × 2^k steps, 1 mu. Cost grows singly exponentially.
    - Ratio: 2^(k-1), unbounded.
    - The 1 mu certificate is the formal cost of "paying attention to
      structure."

    Classical complexity theory has no axis for the cost of certified
    structural knowledge. The Thiele Machine's mu-ledger is exactly that
    axis. The theorem below is the program-cost gap on this one structured
    problem; it is not a class-level separation. *)
Theorem structured_sat_blind_sighted_separation :
  forall k : nat,
    k >= 2 ->
    let blind  := blind_sat_steps k in
    let sighted := sighted_sat_steps k in
    let mu_cert := sighted_sat_mu in
    blind > sighted + mu_cert /\
    (exists ratio, ratio >= 2 /\ blind >= ratio * sighted).
Proof.
  intros k Hk.
  split.
  - exact (sat_separation k Hk).
  - destruct k as [|k']. lia.
    exists (2 ^ k').
    split.
    + (* 2^k' ≥ 2 for k' ≥ 1, since k ≥ 2 means k' ≥ 1 *)
      simpl.
      assert (H2 := two_pow_gt k'). lia.
    + rewrite <- sat_blind_sighted_ratio_exact. lia.
Qed.

(** Corollary: the mu savings exceed any fixed budget lambda once k is large enough.
    This is the analog of StructuralAdvantage.advantage_factor_unbounded for SAT. *)
Corollary sat_savings_unbounded :
  forall lambda : nat,
    exists k : nat,
      k >= 2 /\
      blind_sat_steps k > sighted_sat_steps k + lambda.
Proof.
  intro lambda.
  destruct (sat_separation_ratio_unbounded (lambda + 1)) as [k [Hk Hbig]].
  exists k. split. exact Hk.
  unfold sighted_sat_steps in *.
  assert (H2k : 2 * 2 ^ k >= 1).
  { assert (Hpow := two_pow_gt k). lia. }
  nia.
Qed.
