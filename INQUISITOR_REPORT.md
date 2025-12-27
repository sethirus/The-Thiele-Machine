# INQUISITOR REPORT
Generated: 2025-12-27 05:28:00Z (UTC)
Scanned: 212 Coq files across the repo
## Summary
- HIGH: 0
- MEDIUM: 2
- LOW: 4

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
- `SUSPICIOUS_SHORT_PROOF`: complex theorem has suspiciously short proof (critical files)
- `MU_COST_ZERO`: μ-cost definition is trivially zero
- `CHSH_BOUND_MISSING`: CHSH bound theorem may not reference proper Tsirelson bound
- `PROBLEMATIC_IMPORT`: import may introduce classical axioms

## Vacuity Ranking (file-level)
Higher score = more likely unfinished/vacuous.

| score | tags | file |
|---:|---|---|
| 65 | const-fun | `coq/thielemachine/coqproofs/SpectralApproximation.v` |

## Findings
### MEDIUM

#### `coq/thielemachine/coqproofs/MuAlu.v`
- L189: **MU_COST_ZERO** — μ-cost definition \`mu_zero\` is trivially zero - ensure this is intentional.
  - `Definition mu_zero : MuAccumulator := {| mu_value := 0 |}.`

#### `coq/thielemachine/coqproofs/OracleImpossibility.v`
- L88: **PROBLEMATIC_IMPORT** — Import may introduce classical axioms - verify this is documented and necessary.
  - `Require Import Classical.`

### LOW

#### `coq/thielemachine/coqproofs/BellCheck.v`
- L134: **CHSH_BOUND_MISSING** — CHSH bound theorem \`CHSH_classical_bound\` may not reference proper Tsirelson bound value.
  - `Lemma CHSH_classical_bound :`

#### `coq/thielemachine/coqproofs/BellInequality.v`
- L701: **CHSH_BOUND_MISSING** — CHSH bound theorem \`local_CHSH_bound\` may not reference proper Tsirelson bound value.
  - `Lemma local_CHSH_bound : forall (B : Box), local B -> Qabs (S B) <= 2#1.`
- L839: **CHSH_BOUND_MISSING** — CHSH bound theorem \`tsirelson_gamma_bound\` may not reference proper Tsirelson bound value.
  - `Lemma tsirelson_gamma_bound : -1#1 <= tsirelson_gamma <= 1#1.`

#### `coq/thielemachine/coqproofs/BellReceiptLocalGeneral.v`
- L291: **CHSH_BOUND_MISSING** — CHSH bound theorem \`local_trials_CHSH_bound\` may not reference proper Tsirelson bound value.
  - `Theorem local_trials_CHSH_bound :`

