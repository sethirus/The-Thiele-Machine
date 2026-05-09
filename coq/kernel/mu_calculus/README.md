# kernel/mu_calculus

Where μ stops being a counter and becomes the unique honest cost ledger over
the Thiele ISA.

`mu_initiality` is the universal property: any zero-starting,
instruction-consistent monotone equals `vm_mu` on every reachable state. The
other files derive specific cost values from independent information-theory
bounds.

## Files

| File | Purpose |
|---|---|
| `MuInitiality.v` | **`mu_initiality`** — the initiality theorem. Universal property of `vm_mu` |
| `MuCostDerivation.v` | `cost_uniqueness`, `cost_necessity` — LASSERT cost forced by Shannon entropy + description complexity |
| `MuShannonBridge.v` | Connects feasible-set narrowing to log-cardinality reduction |
| `MuShannonQuantitative.v` | Numerical Shannon-bound instances |
| `MuInformation.v` | Reusable Δμ accounting interface |
| `MuGeometry.v` | μ-distance metric on VMState (small, narrow scope) |
| `MuComplexity.v` | `sat_separation_ratio_unbounded` — μ-complexity grows unbounded vs. classical |
| `MuHierarchyTheorem.v` | **`mu_hierarchy_theorem`**, **`mu_hierarchy_no_upper_bound`** — level-k certification ⇔ ≥k μ |
| `MuChaitin.v` | Certificate payload bounds via μ accounting (Chaitin-style accounting, not Kolmogorov) |
| `MuNoFreeInsightQuantitative.v` | Quantitative variant: μ-monotonicity bounds across cert traces |
| `QuantitativeNoFI.v` | Numerical lower bounds on certification cost |
| `KernelBenchmarks.v` | Linear cost bounds for selected partition cost functions (PNEW, PSPLIT, PMERGE) |

## Load-bearing exports cited from the README

- `mu_initiality` — claim 2 of the five formal claims
- `mu_hierarchy_theorem`, `mu_hierarchy_no_upper_bound` — chain link
- `cost_uniqueness`, `cost_necessity` — substantive lower bounds (Layer 3)
- `sat_separation_ratio_unbounded` — chain link
- `mu_accumulates_trace_cost` — used throughout

## Imports

`foundation/` modules.
