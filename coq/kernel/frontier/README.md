# kernel/frontier

F1, F2, F3 frontier closure files. Each addresses a hard requirement from
[FRONTIER_PLAN.md](../../../FRONTIER_PLAN.md) (post-2026-05-07-retraction).
The names are intentionally cryptic so the audit trail stays distinct from
the claim names in the README.

These files exist to either close or formally negate a frontier claim, with
no rhetoric: every header lists the FRONTIER_PLAN section it discharges and
the hard requirement it satisfies.

## F1 — physical-reversibility / A2 derivation

| File | Round | Purpose |
|---|---|---|
| `F1_LogicalErasure.v` | R1 | Single-step A2 from physical reversibility + Landauer |
| `F1_AbstractedBridge.v` | — | Substrate-abstracted version of the F1 bridge |
| `F1_StrongForm.v` | — | Stronger form of the A2 derivation |
| `F1_TraceLevelA2.v` | R3 | Multi-step extension via `universal_nfi_any_substrate` |

## F2 — algebraic coherence vs. cost axioms

Settles whether NPA-1 minor inequalities follow from cost axioms alone.

| File | Round | Purpose |
|---|---|---|
| `F2_MinorIndependence.v` | R1 | **Negative result**: PR-box VMState satisfies cost axioms but violates `algebraically_coherent` |
| `F2_MinorFromWitnessLocality.v` | R2 | **Positive**: cost axioms + witness-locality DO entail `algebraically_coherent` |
| `F2_PerMinorFromCostCoherent.v` | R3 | Per-minor existence form derivable from cost axioms alone |

## F3 — non-separable cross-link inequalities

Single-conclusion Coq inequalities that compose multiple chain constants.

| File | Round | Purpose |
|---|---|---|
| `F3_CrossLink.v` | R1 | LASSERT byte coefficient + Tsirelson constant in one bound |
| `F3_TripleCrossLink.v` | R2 | LASSERT + Tsirelson + μ-hierarchy in one bound |
| `F3_MuLaplacianSum.v` | — | Sum-zero lemma for the discrete μ-Laplacian |
| `F3_PartitionTopologyCrossLink.v` | — | Partition-topology cross-link |
| `F3_PlusOneStructural.v` | — | **README's named open problem `OP-Plus-One`** — investigation of the +1 in `triangle_angle` |

## Load-bearing exports

Each F-file is the closure of a documented frontier item; they don't get
re-imported elsewhere because the published statement is the export.

`F3_PlusOneStructural.v` is the only file with a publicly-acknowledged
inconclusive status (it's the **OP-Plus-One** open problem cited in the
README; the audit conclusion is that the +1 is a Tikhonov regularizer,
not an A2 cost floor).

## Imports

`foundation/`, `mu_calculus/`, `nfi/`, plus quantum/curvature for cross-link
constants.
