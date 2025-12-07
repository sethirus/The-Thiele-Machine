# Bounded-Model µ-Ledger Conservation

The file [`coq/kernel/MuLedgerConservation.v`](../coq/kernel/MuLedgerConservation.v)
introduces two key constructions:

1. `ledger_entries`, which replays a bounded VM execution and records the
   µ-delta of every realised instruction.
2. `bounded_run`, which collects the state trace induced by the same bounded
   execution.

Using these definitions we proved the main conservation theorem:

```
Theorem bounded_model_mu_ledger_conservation :
  forall fuel trace s,
    ledger_conserved (bounded_run fuel trace s)
                     (ledger_entries fuel trace s) /\
    (run_vm fuel trace s).(vm_mu) =
      s.(vm_mu) + ledger_sum (ledger_entries fuel trace s).
```

This establishes both the per-step invariant (each adjacent pair of states
matches the ledger delta) and the cumulative invariant (the final µ equals the
initial µ plus the ledger sum) for every bounded execution witness.  The lemma
`vm_apply_mu` bridges the operational semantics with the µ-accounting encoded in
`vm_step`, ensuring that the hardware and software definitions of instruction
cost agree.
