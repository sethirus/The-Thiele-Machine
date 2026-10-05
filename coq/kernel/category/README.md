# kernel/category

One file: the algebraic Tsirelson bound from polynomial minors.

## Files

| File | Purpose |
|---|---|
| `AlgebraicCoherence.v` | **`algebraically_coherent_tsirelson_general`**: the bound `|S| <= 2 sqrt 2` from absolute-value bounds and four selected 3-by-3 polynomial minors, by `psatz`; with the rational witness `tsirelson_rational_lower_witness` |

## Load-bearing exports cited from the README

- `algebraically_coherent_tsirelson_general`: the `|S| <= 2 sqrt 2` bound from NPA-1-style polynomial conditions, no Hilbert space invoked

## Imports

The Coq standard library only. `psatz` needs CSDP at build time.
