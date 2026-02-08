(** =========================================================================
    μ-INFORMATION: Quantitative Accounting API
    =========================================================================

    WHY THIS FILE EXISTS:
    I claim μ is an information measure, not just an accounting ledger. This
    file packages the "information injected" quantity Δμ = μ_final - μ_init
    and proves it equals the sum of instruction costs. This connects the
    abstract ledger to concrete computational semantics.

    THE CORE CLAIM:
    μ-information injected by execution = sum of instruction costs. Proven:
    - mu_info_z_vm_apply (line 36): Single step injects instruction_cost
    - run_vm_mu_total_decomposes (line 50): Final μ = initial μ + ledger_sum
    - mu_info_z_run_vm_is_ledger_sum (line 60): Δμ = ledger_sum exactly
    - run_vm_mu_total_monotone (line 80): μ never decreases

    WHAT THIS PROVES:
    The μ-accumulator is a genuine information measure (monotone, additive,
    equals computational cost). This API makes μ-accounting reusable across
    the kernel without duplicating ledger conservation proofs.

    PHYSICAL INTERPRETATION:
    Δμ measures "bits of structural information added" by computation. Every
    instruction injects its declared cost. Total information = sum of costs.
    This is information conservation in executable form.

    FALSIFICATION:
    Show that run_vm_mu_total_decomposes fails for some trace - final μ ≠
    initial μ + ledger_sum. This would break the fundamental accounting.

    Or prove μ can decrease (violate run_vm_mu_total_monotone). This would
    allow "free information" and break thermodynamics.

    NO AXIOMS. NO ADMITS. Pure API over verified ledger conservation.

    ========================================================================= *)

From Coq Require Import ZArith Lia List.
Import ListNotations.

Require Import VMState.
Require Import VMStep.
Require Import SimulationProof.
Require Import MuLedgerConservation.

(** =========================================================================
    BASIC μ-EXTRACTION
    ========================================================================= *)

(** Extract total μ from VM state. This is the fundamental quantity. *)
Definition mu_total (s : VMState) : nat := s.(vm_mu).

(** μ-difference in integers (can represent negative, though actual execution
    always increases μ). Prefer this for arithmetic that might subtract. *)
Definition mu_info_z (s_init s_final : VMState) : Z :=
  (Z.of_nat (mu_total s_final) - Z.of_nat (mu_total s_init))%Z.

(** μ-difference in naturals (truncated subtraction). Only meaningful when
    you know s_final comes after s_init in execution order. Use mu_info_z
    for general arithmetic. *)
Definition mu_info_nat (s_init s_final : VMState) : nat :=
  mu_total s_final - mu_total s_init.

(** =========================================================================
    SINGLE-STEP μ-INFORMATION
    ========================================================================= *)

(** SINGLE-STEP ACCOUNTING: Applying instruction injects its cost

    This is the atomic accounting law. One instruction → one cost injection.
    The vm_apply function (from VMStep.v) updates vm_mu by instruction_cost.
    This lemma exposes that fact in mu_info_z form. *)
Lemma mu_info_z_vm_apply :
  forall s instr,
    mu_info_z s (vm_apply s instr) = Z.of_nat (instruction_cost instr).
Proof.
  intros s instr.
  unfold mu_info_z, mu_total.
  (* vm_apply_mu: vm_apply increases μ by instruction_cost *)
  rewrite vm_apply_mu.
  (* (μ + cost) - μ = cost *)
  lia.
Qed.

(** =========================================================================
    MULTI-STEP μ-INFORMATION (TRACE EXECUTION)
    ========================================================================= *)

(** μ-information injected by bounded execution = sum of ledger entries

    The ledger_sum function (from MuLedgerConservation.v) adds up all
    instruction costs along the trace. This definition makes it explicit
    that μ_info equals that sum. *)
Definition mu_info_run_vm (fuel : nat) (trace : list vm_instruction) (s : VMState)
  : nat := ledger_sum (ledger_entries fuel trace s).

(** DECOMPOSITION THEOREM: Final μ = Initial μ + Information injected

    This is the fundamental equation of μ-accounting. After executing a trace,
    the final μ value equals what you started with plus the sum of all costs.

    Proof uses run_vm_mu_conservation from MuLedgerConservation.v, which
    establishes that the kernel faithfully charges every instruction. *)
Theorem run_vm_mu_total_decomposes :
  forall fuel trace s,
    mu_total (run_vm fuel trace s) = mu_total s + mu_info_run_vm fuel trace s.
Proof.
  intros fuel trace s.
  unfold mu_total, mu_info_run_vm.
  (* The ledger conservation theorem says exactly this *)
  rewrite run_vm_mu_conservation.
  reflexivity.
Qed.

(** INTEGER FORM: Δμ in Z equals ledger sum

    Same as decomposition theorem, but expressed as a difference rather than
    a sum. Useful for arithmetic involving subtraction. *)
Theorem mu_info_z_run_vm_is_ledger_sum :
  forall fuel trace s,
    mu_info_z s (run_vm fuel trace s) = Z.of_nat (mu_info_run_vm fuel trace s).
Proof.
  intros fuel trace s.
  unfold mu_info_z.
  (* Use decomposition: mu_final = mu_init + info *)
  rewrite run_vm_mu_total_decomposes.
  unfold mu_total.
  (* (mu + info) - mu = info *)
  lia.
Qed.

(** COROLLARY: μ-information is always non-negative

    Instruction costs are nat (non-negative), so their sum is non-negative.
    This proves μ never decreases during execution - a fundamental property
    for an information measure. *)
Corollary mu_info_z_run_vm_nonneg :
  forall fuel trace s,
    (0 <= mu_info_z s (run_vm fuel trace s))%Z.
Proof.
  intros fuel trace s.
  rewrite mu_info_z_run_vm_is_ledger_sum.
  (* ledger_sum : nat, so Z.of_nat(ledger_sum) >= 0 *)
  lia.
Qed.

(** COROLLARY: μ is monotone (never decreases)

    Directly follows from decomposition + non-negativity of ledger sum.
    This makes μ a valid information measure: information content only
    grows with computation, never shrinks. *)
Corollary run_vm_mu_total_monotone :
  forall fuel trace s,
    mu_total (run_vm fuel trace s) >= mu_total s.
Proof.
  intros fuel trace s.
  rewrite run_vm_mu_total_decomposes.
  unfold mu_info_run_vm.
  (* ledger_sum >= 0, so μ + ledger_sum >= μ *)
  lia.
Qed.

(** =========================================================================
    API SUMMARY

    This file provides clean abstractions for μ-accounting:

    1. mu_total s: Extract current μ value
    2. mu_info_z s s': Compute Δμ between states (integer form)
    3. mu_info_nat s s': Compute Δμ between states (natural form)
    4. mu_info_run_vm fuel trace s: Compute total cost of trace execution

    Key theorems:
    - run_vm_mu_total_decomposes: μ_final = μ_init + ledger_sum
    - run_vm_mu_total_monotone: μ never decreases

    All backed by MuLedgerConservation.v (ledger faithfully tracks costs).
    No axioms, no admits, purely constructive proofs.

    ========================================================================= *)
