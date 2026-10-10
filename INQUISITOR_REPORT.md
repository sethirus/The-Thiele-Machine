# INQUISITOR REPORT
Generated: 2026-10-10 07:01:59Z (UTC)
Scanned: 343 Coq files across the repo
## Summary
- HIGH: 0
- MEDIUM: 0
- LOW: 0
- SCOPE NOTES: 196 in-source scope markers across 163 files (166 SCOPE NOTE, 30 SAFE markers)
  - Read the severity counts as *unsuppressed* findings. Each scope note silences one check at one site; the justification is the comment text itself. Grep for the markers to audit them.

## Rules
- `ADMITTED`: `Admitted.` (incomplete proof - FORBIDDEN)
- `ADMIT_TACTIC`: `admit.` (proof shortcut - FORBIDDEN)
- `GIVE_UP_TACTIC`: `give_up` (proof shortcut - FORBIDDEN)
- `AXIOM_OR_PARAMETER`: `Axiom` / `Parameter` (HIGH - unproven assumptions FORBIDDEN)
- `HYPOTHESIS_ASSUME`: `Hypothesis` (HIGH - functionally equivalent to Axiom, FORBIDDEN)
- `CONTEXT_ASSUMPTION`: `Context` with forall/arrow (HIGH - undocumented section-local axiom)
- `CONTEXT_ASSUMPTION_DOCUMENTED`: `Context` with SCOPE NOTE (LOW - documented dependency)
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
- `EXACT_ALIAS`: `Theorem A. Proof. exact B. Qed.` (pure alias — proves nothing new, just re-exports an existing proof under a new name)
- `SCOPE_DRIFT_TIER1`: coq/kernel/ (Tier 1) file imports a Tier-2 or Tier-3 namespace — contaminates the proof tree
- `FOUNDATION_UTILIZATION_GAP`: proof file neither uses nor imports anything in the foundation chain (abstract model and small machine) and gives no SCOPE NOTE
- `SCOPE_DRIFT_TIER2`: Core Tier-2 file imports a Tier-3 exploratory namespace
- `TRIVIAL_EQUALITY`: theorem of form `X = X` with reflexivity-ish proof
- `CONST_Q_FUN`: `Definition ... := fun _ => 0%Q` / `1%Q`
- `EXISTS_CONST_Q`: `exists (fun _ => 0%Q)` / `exists (fun _ => 1%Q)`
- `CLAMP_OR_TRUNCATION`: uses `Z.to_nat` (can truncate negative values; Nat.min/max/Z.abs are safe)
- `ASSUMPTION_AUDIT`: unexpected axioms from `Print Assumptions`
- `SYMMETRY_CONTRACT`: missing equivariance lemma for declared symmetry
- `PAPER_MAP_MISSING`: paper ↔ Coq symbol map entry missing/broken
- `MANIFEST_PARSE_ERROR`: failed to parse Inquisitor manifest JSON
- `COMMENT_SMELL`: TODO/FIXME/WIP markers in Coq comments
- `UNUSED_HYPOTHESIS`: disabled source-text heuristic; Coq's checked proof term is authoritative for hypothesis use
- `DEFINITIONAL_INVARIANCE`: invariance lemma appears definitional/vacuous
- `Z_TO_NAT_BOUNDARY`: Z.to_nat without nearby nonnegativity guard
- `PHYSICS_ANALOGY_CONTRACT`: physics-analogy theorem lacks invariance or definitional label
- `SUSPICIOUS_SHORT_PROOF`: complex theorem has suspiciously short proof (critical files)
- `MU_COST_ZERO`: μ-cost definition is trivially zero
- `CHSH_BOUND_MISSING`: CHSH bound theorem may not reference proper Tsirelson bound
- `PROBLEMATIC_IMPORT`: import may introduce classical axioms
- `RECORD_FIELD_EXTRACTION`: theorem merely extracts a Record field it assumed as input (circular)
- `SELF_REFERENTIAL_RECORD`: Record embeds proposition as field AND a Theorem in the same file extracts it (circular)
- `PHANTOM_KERNEL_IMPORT`: imports a foundation module but uses nothing it declares
- `TRIVIAL_EXISTENTIAL`: trivially satisfiable existential (e.g. 'every list has a length')
- `ARITHMETIC_ONLY_PHYSICS`: physics-named theorem proved by pure arithmetic (lia/lra) only
- `CIRCULAR_DEFINITION`: theorem unfolds definition and proves by simple tactics (potentially restating definition)
- `EMERGENCE_CIRCULARITY`: 'emergence' claim where emergent property is in the definition (circular)
- `CONSTRUCTOR_ROUND_TRIP`: construct object, immediately extract property (not proving anything)
- `DEFINITIONAL_WITNESS`: existential witnessed by definition, then unfolds it (trivially proves definition exists)
- `VACUOUS_CONJUNCTION`: theorem has `True` as a conjunct leaf — likely a weakened/placeholder conclusion
- `TAUTOLOGICAL_IMPLICATION`: theorem conclusion is identical to one of its hypotheses (P -> P tautology)
- `HYPOTHESIS_RESTATEMENT`: heuristic style warning (disabled in max-strict mode)
- `PHYSICS_STUB_DEFINITION`: physics/geometry definition returns placeholder constant (0, 1, PI/3)
- `MISSING_CORE_THEOREM`: file defines physics machinery (einstein_tensor, stress_energy) but lacks core theorem (einstein_equation)
- `DEFINITIONAL_CONSTRUCTION`: curvature/physics quantity DEFINED as relationship that should be PROVEN
- `DEFINITION_BUILT_IN_THEOREM`: theorem proves relationship that's built into the definition (circular)
- `INCOMPLETE_PHYSICS_DERIVATION`: gravity/physics file contains explicit unfinished marker text
- `FAKE_COMPLETION_CLAIM`: completion rhetoric appears while core theorem/stub criteria are unmet
- `UNUSED_LOCAL_DEFINITION`: heuristic style warning (disabled in max-strict mode)
- `PROOF_CONNECTIVITY_GAP`: active proof file lacks the semantic foundation (abstract model and small machine), or a cost-using file lacks the cost foundation; a file that stands alone must say so in a SCOPE NOTE
- `PROOF_BODY_FOUNDATION_DISCONNECT`: theorem-body dependency graph shows a Coq proof file does not transitively reach the canonical foundation theorem chain
- `DISJUNCT_TRUE`: theorem statement contains `\/ True` — vacuously provable via `right. exact I.`
- `TRIVIAL_TRUE_PROOF`: proof body terminates with `exact I.` or `right. exact I.` — only proves `True`
- `EXTRACT_CONSTANT`: `Extract Constant` bypasses Coq extraction with hand-written OCaml (trust boundary)
- `KERNEL_CONVERTIBILITY_VACUITY`: theorem conclusion is kernel-convertible (after δ/ι/ζ/β reduction) to `True` or to a hypothesis — verified by `scripts/vacuity_gate.py` running synthesised Coq proofs (HIGH)

## Vacuity Ranking (file-level)
(no files scored above zero — no trivially-true or placeholder patterns detected)

## Findings
(none)
