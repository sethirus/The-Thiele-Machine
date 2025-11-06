# No-Free-Information Invariants

## Context
The kernel model formalises the Thiele Machine as a small-step virtual machine.  The record `VMState` stores the partition graph, control registers, program counter, the accumulated μ-cost `vm_mu`, and an error latch.  Execution traces in `MuLedgerConservation.v` pair these states with a μ-ledger that records the cost delta for each realised instruction.  The updated development introduces the prefix conservation lemma (`bounded_prefix_mu_balance`) alongside `ledger_component_sum`, allowing the ledger to be sliced along time (prefixes) and cost components (e.g. blind search work vs. sighted certificate processing).

## Theorems (English statements)
1. **`vm_step_respects_mu_ledger`** – Every kernel step debits the μ-ledger by exactly the declared instruction cost; state transitions cannot generate “free” μ-information.
2. **`bounded_prefix_mu_balance`** – Every prefix of a bounded execution preserves μ-conservation: the state reached after `k` steps equals the initial μ plus the partial ledger sum for those steps.  This prevents “borrowing from the future” even when analysing on-the-fly receipts.
3. **`bounded_run_mu_decomposition`** – For any bounded execution, the final μ-accumulator equals the initial μ plus the sum of two complementary components, such as blind and sighted μ contributions.  This yields corollaries ensuring that each component is individually bounded by the total μ-budget.
4. **`gestalt_matches_isomorphism`** – The abstract model of the Rule-30 instrument shows that the gestalt certificate produced from the ledger tail is definitionally identical to the computed isomorphism; the seal-plus-final digest combination cannot diverge from the ledger-based certificate.
## Coq artefacts
- **Files:** `coq/kernel/MuLedgerConservation.v`
- **Key lemmas and theorems:**
  - `vm_step_respects_mu_ledger`
  - `bounded_prefix_mu_balance`
  - `bounded_run_mu_decomposition`
  - `bounded_run_blind_component_le_total`
  - `bounded_run_sighted_component_le_total`
  - `gestalt_matches_isomorphism`
- **Proof status:** All completed using existing kernel lemmas (`vm_step_mu`, `bounded_model_mu_ledger_conservation`). No new admits or axioms were introduced.

## Relation to the broader narrative
The per-step invariant certifies that every atomic transition consumes μ-budget exactly equal to the advertised instruction cost.  The new prefix lemmas show that this conservation persists for every partial execution, enabling auditable receipts even when the trace is observed mid-flight.  The bounded-execution decomposition upgrades the argument to complete traces: any run can be sliced into blind and sighted cost components (or another principled partition), and each slice is guaranteed to be accounted for in the ledger.  The gestalt bridge provides a structural link between the prophecy seal and the ledger tail, mirroring the Python experiment’s certificate equality.  Together these theorems enforce the “nothing is free” ethos—neither blind exploration nor sighted insight can bypass the μ-ledger—and ensure that empirical metrics align with the kernel’s conservation laws across prefixes and entire executions.
