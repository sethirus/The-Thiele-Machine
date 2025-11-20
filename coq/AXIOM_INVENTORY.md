# Axiom and admit inventory for the Thiele Machine development

_Updated after the halting-oracle refactor captured in `docs/COQ_PROOF_AUDIT.md`._

## Summary
- **Total Admitted**: 2 (debug-only `debug_no_rule.v`, excluded from the core build)
- **Total Axioms**: 0 (all oracle hypotheses are now section parameters behind the optional `make oracle` target)
- **Kernel module admits/axioms**: 0

> **Debug artefact:** `coq/thielemachine/coqproofs/debug_no_rule.v` preserves the historical no-rule reproduction (with local
> admits) for experimentation.  It is not wired into `_CoqProject`, so the official admit count above is unchanged.

## Kernel module status

The kernel proof tree (`coq/kernel/`) continues to build without admits or axioms. It provides the audited VM↔kernel simulation and ledger invariants used by downstream tooling.【2fc38d†L1-L27】

## Outstanding items

### Admitted lemmas
- The only remaining admits live in the debugging artefact
  `coq/thielemachine/coqproofs/debug_no_rule.v`, which is not part of the
  `_CoqProject` core or bridge builds.

### Planning stubs
- _None_.  The roadmap wrapper `thiele_simulates_by_tm` has been proved and the file participates in the standard build.

### Conditional sections / oracles
- `coq/thielemachine/coqproofs/HyperThiele_Halting.v` declares the halting oracle
  as a section hypothesis inside `Section OracleHypothesis`.  The file is excluded
  from the `core` build and can be compiled explicitly with `make -C coq oracle`
  when experimenting with the toy hyper-halting wrapper.  The helper
  `hyper_thiele_decides_halting_trace` now exposes the compiled Thiele instruction
  stream corresponding to the oracle query, so the assumption manifests as a
  concrete program/trace pair rather than the abstract `run_program` list.
- `coq/thielemachine/coqproofs/Oracle.v` is purely definitional: it packages the
  `T1_State` record (program, partition, µ-ledger) and the helper lemmas
  `t1_bootstrap_total_zero`, `t1_charge_mu_total`, and
  `ledger_sum_app_singleton` used to keep the µ-ledger totals synchronized with
  discovery steps.  The additional wrappers `t1_with_partition` /
  `t1_repartition` (with `t1_with_partition_prog_preserved`,
  `t1_with_partition_partition_replaced`,
  `t1_repartition_partition_replaced`, and `t1_repartition_total`) describe how
  partition refactorings update the ledger without introducing new hypotheses,
  and preservation lemmas for `t1_charge_mu` keep the mutation story honest.
  The newly introduced `T1_Receipt` record and the `t1_emit_receipt` helpers tie
  the oracle state to the artefact exported to `T_0`, still without postulating
  axioms.  The follow-on `T1_Action` inductive plus `t1_step`, `t1_run`, and the
  accumulator lemmas `t1_run_mu_total` / `t1_emit_receipt_mu_total_run`
  encapsulate multi-step oracle traces so that no extra hypotheses are required
  when reasoning about µ-ledger totals or partition churn.  The trace-level
  receipt helper (`t1_trace_receipt` together with
  `t1_trace_receipt_prog`/`t1_trace_receipt_partition`/`t1_trace_receipt_mu_total`)
  exposes the preserved program, resulting partition, and cumulative µ-total in
  a single lemma, again without importing axioms.  The newly added
  `T1_ReceiptWitness` record and the lemma `t1_receipt_witness_of_exec` bridge
  those oracle receipts back to the audited `ThieleMachine` execution semantics
  by bundling the `Exec` witness, the `replay_ok` fact, and the µ-bound needed by
  `T_0` replay—still without introducing axioms or section parameters.  The new
  corollary `t1_trace_receipt_witness` instantiates that bridge directly from any
  action trace by threading the ledger accumulator through
  `t1_trace_receipt_mu_total`, keeping the scaffolding hypothesis-free while
  providing an off-the-shelf `T1_ReceiptWitness` for downstream subsumption work.
  The latest lemmas (`t1_prog_closed_trace_exec`,
  `t1_closed_trace_sum_bits_le_sum_mu`, and the
  `t1_trace_receipt_closed_witness_from_bits` / `_from_mu` corollaries) wire
  those receipts directly to the canonical closed-state execution trace and the
  universal µ-accounting theorems from `ThieleMachine`, so every oracle trace
  now comes with a canonical `Exec` witness and µ-dominance statement while the
  file remains hypothesis-free.  The latest additions
  (`sum_instr_certificates`, `prog_closed_trace_mu_requirement`,
  `t1_closed_trace_mu_requirement`, and
  `t1_trace_receipt_closed_witness_from_ledger_nat`) further compress that
  µ-bound into a natural-number inequality so downstream subsumption arguments
  can cite a closed-state witness directly from the oracle ledger without any
  new hypotheses.  The newest canonical action constructors
  (`t1_closed_trace_mu_actions`, `t1_run_mu_delta_all_charge`,
  `ledger_sum_map_instr_cert`, `t1_run_mu_delta_closed_trace_mu_actions`,
  `t1_closed_trace_mu_requirement_covered_by_canonical_actions`, and
  `t1_trace_receipt_closed_witness_canonical`) make that inequality constructive
  by exhibiting a concrete charge-only trace whose ledger delta matches the
  required bound, ensuring the entire scaffold remains definitionally closed and
  axiom-free.【F:coq/thielemachine/coqproofs/Oracle.v†L1-L536】  The optional
  `HyperThiele_Halting.v` study now imports that scaffold via
  `halting_solver_t1_state`, `halting_solver_canonical_actions`, and the lemma
  `halting_solver_canonical_receipt_witness`, so every oracle query also exposes a
  canonical `T1_ReceiptWitness` without introducing new axioms beyond the
  existing `H_correct` hypothesis guarded by the `OracleHypothesis` section.

## Next steps
- Maintain `coq/ADMIT_REPORT.txt` alongside this file whenever admits change until the reporting script is repaired.【27e479†L32-L34】
- Track progress in `docs/COQ_PROOF_AUDIT.md` and update these counts immediately after proofs land so the audit stays trustworthy.【6b8295†L1-L45】
