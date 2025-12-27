# INQUISITOR REPORT
Generated: 2025-12-27 03:30:00Z (UTC)
Scanned: 210 Coq files across the repo
## Summary
- HIGH: 0
- MEDIUM: 1
- LOW: 0

## Rules
- `ADMITTED`: `Admitted.` (incomplete proof - FORBIDDEN)
- `ADMIT_TACTIC`: `admit.` (proof shortcut - FORBIDDEN)
- `GIVE_UP_TACTIC`: `give_up` (proof shortcut - FORBIDDEN)
- `AXIOM_OR_PARAMETER`: `Axiom` / `Parameter`
- `HYPOTHESIS_ASSUME`: `Hypothesis` (escalates to HIGH for suspicious names)
- `SECTION_BINDER`: `Context` / `Variable` / `Variables` (informational)
- `MODULE_SIGNATURE_DECL`: `Axiom` / `Parameter` inside `Module Type` (informational)
- `COST_IS_LENGTH`: `Definition *cost* := ... length ... .`
- `EMPTY_LIST`: `Definition ... := [].`
- `ZERO_CONST`: `Definition ... := 0.` / `0%Z` / `0%nat`
- `TRUE_CONST`: `Definition ... := True.` or `:= true.`
- `PROP_TAUTOLOGY`: `Theorem ... : True.`
- `IMPLIES_TRUE_STMT`: statement ends with `-> True.`
- `LET_IN_TRUE_STMT`: statement ends with `let ... in True.`
- `EXISTS_TRUE_STMT`: statement ends with `exists ..., True.`
- `CIRCULAR_INTROS_ASSUMPTION`: tautology + `intros; assumption.`
- `TRIVIAL_EQUALITY`: theorem of form `X = X` with reflexivity-ish proof
- `CONST_Q_FUN`: `Definition ... := fun _ => 0%Q` / `1%Q`
- `EXISTS_CONST_Q`: `exists (fun _ => 0%Q)` / `exists (fun _ => 1%Q)`
- `CLAMP_OR_TRUNCATION`: uses `Z.to_nat`, `Z.abs`, `Nat.min`, `Nat.max`
- `ASSUMPTION_AUDIT`: unexpected axioms from `Print Assumptions`
- `SYMMETRY_CONTRACT`: missing equivariance lemma for declared symmetry
- `PAPER_MAP_MISSING`: paper ↔ Coq symbol map entry missing/broken
- `MANIFEST_PARSE_ERROR`: failed to parse Inquisitor manifest JSON
- `COMMENT_SMELL`: TODO/FIXME/WIP markers in Coq comments
- `UNUSED_HYPOTHESIS`: introduced hypothesis not used (heuristic)
- `DEFINITIONAL_INVARIANCE`: invariance lemma appears definitional/vacuous
- `Z_TO_NAT_BOUNDARY`: Z.to_nat without nearby nonnegativity guard
- `PHYSICS_ANALOGY_CONTRACT`: physics-analogy theorem lacks invariance or definitional label

## Vacuity Ranking (file-level)
Higher score = more likely unfinished/vacuous.

| score | tags | file |
|---:|---|---|
| 65 | const-fun | `coq/thielemachine/coqproofs/SpectralApproximation.v` |

## Findings
### MEDIUM

#### `coq/kernel/TsirelsonLowerBound.v`
- L40: **ZERO_CONST** — Definition is a constant zero.
  - `Definition entangled_bit : nat := 0%nat.`

