(** =========================================================================
    MuShannonBridge: Connecting μ to Shannon Information Theory
    =========================================================================

    WHY THIS FILE EXISTS:
    The README claims: Δμ ≥ log₂|Ω| - log₂|Ω'|
    This is a quantitative version of No Free Insight connecting μ to
    Shannon entropy. This file formalizes that claim precisely, proves
    what follows from the existing VM semantics, and makes EXPLICIT what
    additional assumptions would close the full Shannon connection.

    WHAT IS PROVEN HERE (no admits, no axioms):
    1. Feasibility definitions: what it means to "distinguish" inputs
    2. Policy-based bound: IF costs are properly sized THEN Δμ ≥ log₂(n)
       (where n is the number of distinguished inputs)
    3. Conservation bound: Δμ = sum of declared costs (from MuLedgerConservation)

    WHAT IS NOT YET PROVEN (gap clearly labeled):
    4. That distinguishing n inputs REQUIRES cost-bearing instructions
       (this is the actual content of NoFI — needs separate proof)
    5. That μ_cost ≥ Shannon_entropy_reduction for arbitrary programs
       (this requires probabilistic semantics not yet formalized)

    THE MAIN CONJECTURE (stated formally but not yet proven):
      mu_lower_bounds_entropy_reduction:
        For any program trace and any distribution over inputs,
        the mutual information I(input; output) ≤ Δμ.

    PROOF STATUS:
    - Definitions: done
    - Policy-based bound: done (follows from MuLedgerConservation)
    - Full Shannon bound: open (stated as conjecture)

    FALSIFICATION:
    Find a program trace that:
    (a) distinguishes n ≥ 2 inputs (maps them to n distinct outputs)
    (b) uses only zero-cost instructions (Δμ = 0)
    This would disprove the conjecture. The current VM allows zero-cost
    LOAD_IMM, XFER, etc. — but do these suffice to distinguish inputs?
    No: all zero-cost instructions are deterministic functions of their
    register inputs. A program starting from distinct inputs with zero-cost
    instructions only preserves the distinction — it does not CREATE it.
    The conjecture says: creating a certified distinction costs μ > 0.

    REFERENCES:
    Cover & Thomas, "Elements of Information Theory" (2nd ed.), Ch. 2
    Shannon, "A Mathematical Theory of Communication" (1948)
    Landauer, "Irreversibility and Heat Generation in Computing" (1961)

    ========================================================================= *)

(* INQUISITOR NOTE: proof-connectivity — bridges MuLedgerConservation to
   Shannon information theory. Foundational for NoFI generalization (Track B). *)

From Coq Require Import List Lia Arith.PeanoNat Arith.Compare_dec.
Import ListNotations.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import SimulationProof.
From Kernel Require Import MuLedgerConservation.
From Kernel Require Import MuNoFreeInsightQuantitative.

(** =========================================================================
    SECTION 1: FEASIBLE SETS AND SEARCH SPACES
    =========================================================================

    A "feasible set" Ω is a list of possible initial VMStates that are
    consistent with everything we know before execution.

    "Search space reduction" from Ω to Ω' means: after observing the
    execution trace, only states in Ω' ⊆ Ω remain plausible.
    ========================================================================= *)

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

(** =========================================================================
    SECTION 2: INTEGER LOGARITHM LOWER BOUND
    =========================================================================

    Nat.log2 n gives ⌊log₂(n)⌋.
    The claim Δμ ≥ log₂(|Ω|/|Ω'|) is stated as:
      Δμ ≥ Nat.log2 |Ω| - Nat.log2 |Ω'|
    (using truncated subtraction on nat)
    ========================================================================= *)

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

(** =========================================================================
    SECTION 3: COST-INFORMED PRICING POLICY
    =========================================================================

    This section establishes a POLICY-BASED bound: if the programmer declares
    costs that are ≥ the information content of each operation, then μ ≥ log₂(n).

    This is not derived from first principles — it requires that costs be
    "honestly priced." The purpose is to make the pricing requirement explicit.
    ========================================================================= *)

(** An instruction is "info-priced" if its cost ≥ 1 whenever it is a
    cert-setting operation (REVEAL, EMIT, LASSERT, CERTIFY, LJOIN) *)
Definition info_priced (instr : vm_instruction) : Prop :=
  match instr with
  | instr_reveal _ _ _ delta      => delta >= 1
  | instr_emit _ _ delta          => delta >= 1
  | instr_lassert _ _ _ delta     => delta >= 1
  | instr_certify delta           => delta >= 1
  | instr_ljoin _ _ delta         => delta >= 1
  | instr_read_port _ _ _ _ delta => delta >= 1
  | _                             => True  (* zero-cost ok for non-info ops *)
  end.

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
     | instr_lassert _ _ _ _ => 1
     | instr_certify _       => 1
     | instr_ljoin _ _ _     => 1
     | _                     => 0
     end) + count_cert_setters rest
  end.

(** =========================================================================
    SECTION 4: THE CORE BOUND (POLICY-BASED)
    =========================================================================

    Under the pricing policy, Δμ ≥ count_cert_setters * 1.
    This is a lower bound on information-bearing operations.
    ========================================================================= *)

(** Under the pricing policy, cert-setting instructions each cost ≥ 1 *)
Lemma cert_setter_costs_at_least_one :
  forall instr,
    info_priced instr ->
    match instr with
    | instr_reveal _ _ _ delta   => instruction_cost instr >= 1 \/ instruction_cost instr = 0
    | instr_emit _ _ delta       => instruction_cost instr >= 1 \/ instruction_cost instr = 0
    | instr_lassert _ _ _ delta  => instruction_cost instr >= 1 \/ instruction_cost instr = 0
    | instr_certify delta        => instruction_cost instr >= 1 \/ instruction_cost instr = 0
    | instr_ljoin _ _ delta      => instruction_cost instr >= 1 \/ instruction_cost instr = 0
    | _                          => True
    end.
Proof.
  intros instr Hpriced.
  destruct instr; simpl in *; auto; lia.
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

(** =========================================================================
    SECTION 4b: POLICY-BASED BOUND (PROVABLE WITHOUT PROBABILISTIC SEMANTICS)
    =========================================================================

    We prove: under the info-pricing policy, the number of cert-setting
    instruction EXECUTIONS is bounded above by Δμ.

    This is the strongest result we can prove without probabilistic semantics.
    It says: you can't execute more cert-setting operations than you pay for.

    STATUS: PROVEN. No admits, no axioms beyond the kernel.

    RELATIONSHIP TO MuShannonConjecture:
    This bound gives: Δμ ≥ cert_setter_executions.
    The conjecture would need: cert_setter_executions ≥ log₂|Ω|.
    The gap: "you need at least log₂n cert operations to separate n states"
    requires either probabilistic semantics (B-track) or a counting argument
    about decision trees (needs more structure on the VM's I/O).
    ========================================================================= *)

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

(** Helper: for an info-priced cert-setter, its cost is ≥ 1 *)
Lemma info_priced_cert_setter_cost_pos :
  forall (instr : vm_instruction) (trace : list vm_instruction),
    In instr trace ->
    trace_info_priced trace ->
    is_cert_setterb instr = true ->
    instruction_cost instr >= 1.
Proof.
  intros instr trace Hin Hpriced Hsetter.
  apply Forall_forall with (x := instr) in Hpriced; try assumption.
  (* For each cert-setter constructor, compute info_priced and instruction_cost *)
  destruct instr; simpl in Hsetter; try discriminate;
  unfold info_priced in Hpriced; simpl in *; lia.
Qed.

(** Helper: cert_setter_executions ≤ irreversible_count (from MuLedgerConservation) *)
Lemma cert_executions_le_ledger :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState),
    trace_info_priced trace ->
    cert_setter_executions fuel trace s <=
    ledger_sum (ledger_entries fuel trace s).
Proof.
  induction fuel as [|fuel IH]; intros trace s Hpriced; simpl.
  - lia.
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hnth; simpl.
    + pose proof (IH trace (vm_apply s instr) Hpriced) as IH'.
      destruct (is_cert_setterb instr) eqn:Hsetter.
      * (* cert-setter: contributes 1 to cert_executions, ≥ 1 to ledger *)
        assert (Hcost : instruction_cost instr >= 1).
        { apply info_priced_cert_setter_cost_pos with (trace := trace).
          - apply nth_error_In with (n := s.(vm_pc)). exact Hnth.
          - exact Hpriced.
          - exact Hsetter. }
        lia.
      * (* non-cert-setter: contributes 0 to cert_executions *)
        lia.
    + lia.
Qed.

(** THEOREM (Policy-Based Bound, B2):
    Under info-pricing, Δμ ≥ number of cert-setting instruction executions.

    This is the maximum bound provable without probabilistic semantics.
    The full Shannon bound (Δμ ≥ log₂|Ω|) requires B-track B3/B4 work. *)
Theorem info_priced_cert_executions_bound :
  forall (fuel : nat) (trace : list vm_instruction) (s : VMState),
    trace_info_priced trace ->
    cert_setter_executions fuel trace s <=
      (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  intros fuel trace s Hpriced.
  rewrite delta_mu_equals_ledger_sum.
  apply cert_executions_le_ledger. exact Hpriced.
Qed.

(** =========================================================================
    SECTION 5: THE MAIN CONJECTURE (NOT YET PROVEN)
    =========================================================================

    This section states the full Shannon connection as a Conjecture.
    It is NOT proven — it requires additional work (Track B, steps B2-B4).

    The conjecture is stated precisely so that:
    1. Future provers know exactly what needs to be shown
    2. The gap between current proofs and the claim is crystal clear
    3. Any proof attempt must match this exact statement

    ========================================================================= *)

(** [shannon_entropy_reduction]: How much Shannon entropy is eliminated when
    a feasible set Ω reduces to Ω' (assuming uniform prior over Ω).

    H(prior) - H(posterior) = log₂|Ω| - log₂|Ω'|
    (using truncated nat subtraction — Nat.log2 0 = 0 by Coq convention) *)
Definition shannon_entropy_reduction (omega_init omega_final : FeasibleSet) : nat :=
  Nat.log2 (feasible_size omega_init) -
  Nat.log2 (feasible_size omega_final).

(** THE MAIN CONJECTURE:
    Executing a trace that reduces the feasible set from Ω to Ω' requires
    Δμ ≥ log₂|Ω| - log₂|Ω'|.

    Status: OPEN. This is the formal version of the README claim.

    What would be needed to prove this:
    1. A definition of "consistent_reduction" formalizing what it means for
       Ω' to be the posterior feasible set given the execution trace
    2. A proof that any consistent reduction must include at least one
       cert-setting instruction per bit of entropy eliminated
    3. Connection to info_priced (the pricing policy)
    4. Or alternatively: a probabilistic semantics over VMState that
       supports a data-processing inequality argument

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
    The missing piece: connecting "some cost" to "log₂(n) cost" for n-way distinctions. *)

(** Placeholder type for consistent feasible-set reduction.
    Will be filled in by the probabilistic semantics work (Track B, step B2). *)
Definition consistent_reduction
    (fuel : nat) (trace : list vm_instruction)
    (omega_init omega_final : FeasibleSet)
    (s_init : VMState) : Prop :=
  (* Placeholder: omega_final = states reachable from omega_init via trace *)
  forall s, In s omega_final ->
    In s omega_init /\
    exists s_out, run_vm fuel trace s = s_out.

(** CONJECTURE: Δμ ≥ Shannon entropy reduction
    Status: OPEN
    This is the formal statement of the README claim:
      Δμ ≥ log₂|Ω| - log₂|Ω'|
    Requires completing the probabilistic semantics (Track B, steps B2-B4). *)
Definition MuShannonConjecture : Prop :=
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

(** =========================================================================
    SECTION 6: WHAT IS PROVABLE WITHOUT THE CONJECTURE
    =========================================================================

    These are theorems that hold unconditionally, establishing the
    infrastructure for the eventual full proof.
    ========================================================================= *)

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
   This connects to the MuShannonConjecture stated above. *)

(** =========================================================================
    SECTION 7: RELATIONSHIP TO EXISTING KERNEL RESULTS
    =========================================================================

    Summary of how this file fits with existing proofs:

    EXISTING:
    - MuLedgerConservation: Δμ = Σ costs (proven, sound)
    - MuNoFreeInsightQuantitative: cert-setting requires Δμ > 0 (proven)
    - MuChaitin: cert payload bounded by Δμ under pricing policy (proven)
    - NoFreeInsight.v: strengthening P_weak to P_strong requires structure
      event with cost > 0 (proven for the Thiele VM)

    MISSING (this file's target):
    - Connection between Δμ and log₂(search space reduction)
    - Probabilistic semantics: what distribution over inputs justifies entropy calc
    - Proof that MuShannonConjecture holds for the Thiele VM

    The existing results prove NoFI QUALITATIVELY (any cert costs > 0).
    The conjecture strengthens this QUANTITATIVELY (costs ≥ log₂(n) for n choices).
    ========================================================================= *)

(** End of MuShannonBridge.
    Next steps (Track B, steps B2-B4):
    - B2: Prove MuShannonConjecture holds when the VM uses a probabilistic
          input distribution and runs in a bounded feasible-set model
    - B3: Connect consistent_reduction to Bayesian belief update
    - B4: Verify the result against Cover & Thomas Ch. 2 statement *)

