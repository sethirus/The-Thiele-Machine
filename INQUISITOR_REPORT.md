# INQUISITOR REPORT
Generated: 2025-12-31 07:22:47Z (UTC)
Scanned: 228 Coq files across the repo
## Summary
- HIGH: 6
- MEDIUM: 4
- LOW: 9

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
### HIGH

#### `coq/kernel/BoxCHSH.v`
- L68: **ADMIT_TACTIC** — admit tactic found (proof shortcut - FORBIDDEN).
  - `admit.`
- L75: **ADMIT_TACTIC** — admit tactic found (proof shortcut - FORBIDDEN).
  - `admit.`
- L76: **ADMITTED** — Admitted found (incomplete proof - FORBIDDEN).
  - `Admitted.`
- L122: **AXIOM_OR_PARAMETER** — Found Axiom valid_box_S_le_4.
  - `Axiom valid_box_S_le_4 : forall B,`
- L146: **AXIOM_OR_PARAMETER** — Found Axiom local_box_S_le_2.
  - `Axiom local_box_S_le_2 : forall B,`

#### `coq/kernel/TestTripartite.v`
- L53: **AXIOM_OR_PARAMETER** — Found Axiom pr_box_no_extension.
  - `Axiom pr_box_no_extension : ~ has_valid_extension pr_box.`

### MEDIUM

#### `coq/kernel/TsirelsonUniqueness.v`
- L25: **SUSPICIOUS_SHORT_PROOF** — Complex theorem \`mu_zero_algebraic_bound\` has very short proof (1 lines) - verify this is not a placeholder.
  - `Theorem mu_zero_algebraic_bound :`

#### `coq/kernel/TsirelsonUpperBound.v`
- L347: **SUSPICIOUS_SHORT_PROOF** — Complex theorem \`tsirelson_bound_lt_algebraic_max\` has very short proof (2 lines) - verify this is not a placeholder.
  - `Lemma tsirelson_bound_lt_algebraic_max : tsirelson_bound < 4%Q.`

#### `coq/thielemachine/coqproofs/MuAlu.v`
- L189: **MU_COST_ZERO** — μ-cost definition \`mu_zero\` is trivially zero - ensure this is intentional.
  - `Definition mu_zero : MuAccumulator := {| mu_value := 0 |}.`

#### `coq/thielemachine/coqproofs/OracleImpossibility.v`
- L88: **PROBLEMATIC_IMPORT** — Import may introduce classical axioms - verify this is documented and necessary.
  - `Require Import Classical.`

### LOW

#### `coq/kernel/BoxCHSH.v`
- L59: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H00\` not used in proof body or conclusion (heuristic).
  - `intros p00 p01 p10 p11 H00 H01 H10 H11 Hsum.`
- L59: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H01\` not used in proof body or conclusion (heuristic).
  - `intros p00 p01 p10 p11 H00 H01 H10 H11 Hsum.`
- L59: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H10\` not used in proof body or conclusion (heuristic).
  - `intros p00 p01 p10 p11 H00 H01 H10 H11 Hsum.`
- L59: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H11\` not used in proof body or conclusion (heuristic).
  - `intros p00 p01 p10 p11 H00 H01 H10 H11 Hsum.`
- L59: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hsum\` not used in proof body or conclusion (heuristic).
  - `intros p00 p01 p10 p11 H00 H01 H10 H11 Hsum.`

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

