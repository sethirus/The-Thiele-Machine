# INQUISITOR REPORT
Generated: 2026-02-12 09:17:15Z (UTC)
Scanned: 292 Coq files across the repo
## Summary
- HIGH: 0
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
- `RECORD_FIELD_EXTRACTION`: theorem merely extracts a Record field it assumed as input (circular)
- `SELF_REFERENTIAL_RECORD`: Record embeds proposition as field AND a Theorem in the same file extracts it (circular)
- `PHANTOM_KERNEL_IMPORT`: imports Kernel modules but no proof engages with VM semantics
- `TRIVIAL_EXISTENTIAL`: trivially satisfiable existential (e.g. 'every list has a length')
- `ARITHMETIC_ONLY_PHYSICS`: physics-named theorem proved by pure arithmetic (lia/lra) only
- `PHANTOM_VM_STEP`: theorem takes vm_step as hypothesis but proof never uses it
- `CIRCULAR_DEFINITION`: theorem unfolds definition and proves by simple tactics (potentially restating definition)
- `EMERGENCE_CIRCULARITY`: 'emergence' claim where emergent property is in the definition (circular)
- `CONSTRUCTOR_ROUND_TRIP`: construct object, immediately extract property (not proving anything)
- `DEFINITIONAL_WITNESS`: existential witnessed by definition, then unfolds it (trivially proves definition exists)
- `VACUOUS_CONJUNCTION`: theorem has `True` as a conjunct leaf — likely a weakened/placeholder conclusion
- `TAUTOLOGICAL_IMPLICATION`: theorem conclusion is identical to one of its hypotheses (P -> P tautology)
- `HYPOTHESIS_RESTATEMENT`: proof destructures hypothesis and extracts one piece (restating assumption, not deriving)

## Findings
(none)
