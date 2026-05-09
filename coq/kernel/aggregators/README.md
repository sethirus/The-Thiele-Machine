# kernel/aggregators

Files that don't introduce new mathematics — they collect existing theorems
into named records, public interfaces, or audit summaries. Their role is
narrative continuity and dependency-spine verification, not new claims.

## Files

| File | Purpose |
|---|---|
| `MasterSummary.v` | 168-node aggregator listing the kernel's main results in chain order |
| `ThieleGenesis.v` | Guided aggregation layer; cites main results in narrative order |
| `TOE.v` | "Theory of Everything" closure record — locality + monotonicity + causality + Born + Tsirelson |
| `Closure.v` | Public-interface wrapper delegating to `Physics_Closure` |
| `NonCircularityAudit.v` | Audit layer enumerating primitive structures used in correlation development |
| `FalsifiablePrediction.v` | Falsification predicates and empirical-protocol scope statements |
| `PDISCOVERIntegration.v` | PDISCOVER OCaml-extraction parity layer (canonical PDISCOVER semantics) |

## Role

These files are **kept on the active build** but produce no theorem that
isn't proved elsewhere. They exist to:
- verify the dependency spine still type-checks together
- give downstream consumers a single name to import
- document scope boundaries and audit conclusions

If the chain reorganizes upstream, these files break first — that's the
point.

## Imports

Almost everything. These files sit at the top of the dependency tree.
