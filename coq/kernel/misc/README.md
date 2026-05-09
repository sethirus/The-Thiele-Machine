# kernel/misc

The leftover bucket: 3 files that don't fit cleanly into any of the topical
subdirectories.

## Files

| File | Purpose |
|---|---|
| `ConeAlgebra.v` | Algebraic laws for `causal_cone`: monoid structure, commutativity in independent case |
| `ConeDerivation.v` | Uniqueness theorem: `causal_cone` is forced by composition + empty-trace properties |
| `SemanticMuCost.v` | Semantic-level μ-cost interpretation (small bridge file) |

## Why misc

The cone files sit at the boundary of foundation (causal-cone semantics) and
curvature (causal structure). They could go in either, but they don't depend
on metric/Riemann content, and `foundation/` should stay narrow. Splitting
them off here keeps the bigger directories focused.

`SemanticMuCost.v` is a small bridge between μ-accounting (`mu_calculus/`) and
the semantic-cost reading used in some downstream files. Could move to
`mu_calculus/` if it grows.

## Imports

`foundation/`, `mu_calculus/`.

## Note

If any file here grows enough to justify its own theme, move it. Misc is a
parking lot, not a permanent home.
