# INQUISITOR REPORT
Generated: 2026-01-19 04:58:21Z (UTC)
Scanned: 0 Coq files under compilation failed
## Summary
- HIGH: 27
- MEDIUM: 0
- LOW: 0

## Rules
- `ADMITTED`: `Admitted.` (incomplete proof - FORBIDDEN)
- `ADMIT_TACTIC`: `admit.` (proof shortcut - FORBIDDEN)
- `GIVE_UP_TACTIC`: `give_up` (proof shortcut - FORBIDDEN)
- `AXIOM_OR_PARAMETER`: `Axiom` / `Parameter` (HIGH - unproven assumptions FORBIDDEN)
- `HYPOTHESIS_ASSUME`: `Hypothesis` (HIGH - functionally equivalent to Axiom, FORBIDDEN)
- `CONTEXT_ASSUMPTION`: `Context` with forall/arrow (HIGH - undocumented section-local axiom)
- `CONTEXT_ASSUMPTION_DOCUMENTED`: `Context` with INQUISITOR NOTE (LOW - documented dependency)
- `SECTION_BINDER`: `Context` / `Variable` / `Variables` (MEDIUM - verify instantiation)
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

## Findings
### HIGH

#### `coq/kernel/MuInformationTheoreticBounds.v`
- L37: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L57: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L79: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L94: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``

#### `coq/theory/EvolutionaryForge.v`
- L65: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L234: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L234: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L238: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L238: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L322: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L322: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L324: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L324: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L341: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L341: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L345: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L345: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``

#### `coq/theory/GeometricSignature.v`
- L69: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L72: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L75: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L78: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L88: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L90: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L92: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L94: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``
- L112: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``

#### `coq/thielemachine/coqproofs/MuAlu.v`
- L249: **COMPILATION_ERROR** — Coq file failed to compile - see build output.
  - ``

