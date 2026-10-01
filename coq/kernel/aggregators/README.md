# kernel/aggregators

Files that don't introduce new mathematics: they collect existing theorems
into named records, public interfaces, or audit summaries. Their role is
narrative continuity and dependency-spine verification, not new claims.

## Files

| File | Purpose |
|---|---|
| `MasterSummary.v` | Audit-facing index of selected established kernel claims in chain order, each labeled by kind (definitional restatement, algebraic theorem, conditional bridge, wrapper, verification-transfer) |
| `ThieleGenesis.v` | Guided aggregation layer; cites main results in narrative order |
| `TOE.v` | Kernel closure record: locality + monotonicity + causality, plus the conditional Born + Tsirelson wiring (the `TOE` name is a legacy module identifier, **not** a claim of a theory of everything; the project disclaims that explicitly) |
| `Closure.v` | Public-interface wrapper delegating to `Physics_Closure` |
| `NonCircularityAudit.v` | Audit layer enumerating primitive structures used in correlation development |
| `FalsifiablePrediction.v` | Falsification predicates and empirical-protocol scope statements |
| `PDISCOVERIntegration.v` | PDISCOVER OCaml-extraction parity layer (canonical PDISCOVER semantics) |
| `UnificationProbePattern.v` | The shape shared by the physical-bound probes (Landauer, Holevo, Bekenstein, Tsirelson) as an explicit Coq object, with each probe's bound shown to hold (`meta_pattern_holds`) |
| `UnificationProbeBridges.v` | Four bridges that compose a probe theorem with a framework theorem about VM steps, so the conclusion is stated in VM vocabulary (`cert_flip_releases_landauer_heat`, `vm_trace_classical_holevo`, `vm_mu_bekenstein_bound`); the thermal and substrate premises stay named hypotheses |

## Role

These files are **kept on the active build** but produce no theorem that
isn't proved elsewhere. They exist to:
- verify the dependency spine still type-checks together
- give downstream consumers a single name to import
- document scope boundaries and audit conclusions

If the chain reorganizes upstream, these files break first. That is the
point.

## Imports

Almost everything. These files sit at the top of the dependency tree.
