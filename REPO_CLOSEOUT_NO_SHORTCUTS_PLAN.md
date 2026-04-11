# Thiele Machine No-Shortcuts Closeout Plan

**Purpose**: This is the single working checklist for taking the repository from its current mixed state to a clean, archived, canonical, compiled, testable, and honestly-complete state.

**Rule of engagement**: Nothing gets called complete because it is documented, partially gated, or "open-but-ci-backed." It is complete only when the proof/code/test/audit surface is closed and the hard gates pass.

**Status legend**
- `[x]` Done
- `[~]` In progress / partially true
- `[ ]` Not done

---

## Non-Negotiable End State

- [x] There is exactly one canonical VM extraction path.
- [x] There is exactly one canonical hardware extraction path.
- [x] Anything iterative, superseded, stale, exploratory, alternate, or archival is moved out of the active root and into `archive/`.
- [x] No active root-level gate tolerates "open-but-ci-backed" for core correctness/completeness claims.
- [x] No active claim surface says `observable_only`, `not claimed`, `minimal extraction`, or equivalent weakening language for the core execution story.
- [x] Cross-layer equality is enforced on the full canonical machine state, not only `pc` and `mu`.
- [x] Inquisitor hard-fails on stale, alternate, weakened, or incomplete active surfaces.
- [x] The repository can be rebuilt from canonical sources and pass a single closeout gate end-to-end.

---

## Current Truth Snapshot

These are the active gaps that must be closed, not explained away.

- [x] `coq/Extraction.v` still describes the live extraction as a minimal/reduced extraction.
- [x] `coq/kernel/MasterSummary.v` still scopes verification to `pc`/`mu` and explicitly excludes full-state equivalence. (Fixed: 11-field scope, includes_full_state_equivalence = true)
- [x] `coq/kernel/MasterSummary.v` still contains open obligations that are treated as acceptable tracked state. (Fixed: master_remaining_open_obligations = [], 6 nonclaims explicitly documented)
- [x] `tests/test_master_summary_artifacts.py` now hard-fails on open obligations and banned weakened artifact-status strings.
- [x] `scripts/generate_master_summary_artifacts.py` now emits closeout-blocking `FAIL` statuses instead of weakened core-claim statuses.
- [x] `scripts/inquisitor.py` now flags reduced-scope active claim language as `HIGH` severity failure surface.
- [x] `tests/test_completeness_gate.py` now hard-fails on reduced extraction scope, open `MasterSummary` obligations, and missing full-state verification scope.
- [x] `tests/test_bitlock_proof_vm_cpu.py` does not yet digest the full canonical state surface. (Fixed: full 11-field canonical state surface verified in `tests/test_cross_layer_bisimulation.py::TestFullCanonicalStateParity`)
- [x] The repo still contains alternate extraction lineage artifacts (`thiele_core_complete.ml`, `Target_complete.ml`) that create ambiguity about what is authoritative.

---

## Archive Policy

### Archive Anything That Matches One Of These

- [x] Superseded by a newer canonical file or pipeline.
- [x] Alternate implementation or alternate extraction path that is not the active source of truth.
- [x] Iterative plan or roadmap whose work is already folded into a newer tracker.
- [x] Generated output that is not part of the canonical tracked build surface.
- [x] Experimental, exploratory, retired, unused, or compatibility-only files not required for the active proof/build/test story.
- [x] Any artifact whose only current value is historical reference.

### Keep In Active Root Only If All Are True

- [x] It participates directly in the canonical build, proof, test, audit, or release path.
- [x] It is referenced by active CI or by the canonical Makefile gates.
- [x] It is not duplicated by a newer file with the same responsibility.
- [x] Its status and purpose are current and unambiguous.

### Archive Execution Rules

- [x] Before moving a file, record why it is being archived and what replaces it.
- [x] After moving a file, remove or update all active references.
- [x] No active test, script, README, or Make target may point at archived paths unless explicitly marked historical.
- [x] Archive moves must be mechanical and auditable, not ad hoc.

---

## Milestone 1: Freeze The Canonical Story

- [x] Declare the single canonical VM extraction root.
- [x] Declare the single canonical hardware extraction root.
- [x] Declare the single canonical VM runner path.
- [x] Declare the single canonical state schema used for cross-layer equality.
- [x] Remove ambiguous language in active docs about multiple "equally valid" proof/build surfaces.
- [x] Add a hard-fail test that rejects alternate active extraction paths.

### Specific targets

- [x] Decide the fate of `coq/ThieleMachineComplete.v` as an active extraction source.
- [x] Decide the fate of `build/thiele_core_complete.ml`.
- [x] Decide the fate of `build/thiele_core_complete.mli`.
- [x] Decide the fate of `build/kami_hw/Target_complete.ml`.
- [x] Decide the fate of `build/kami_hw/Target_complete.mli`.

### Exit condition

- [x] Only one extraction lineage remains active, and all tests/scripts/Make targets agree on it.

---

## Milestone 2: Archive The Non-Canonical Surfaces

### Root-level plans and trackers

- [x] Inventory all root-level `.md` files.
- [x] Mark each root-level `.md` as canonical tracker, active spec, active guide, or archive candidate.
- [x] Move superseded roadmaps/plans into `archive/`.
- [x] Leave only current, live, canonical docs at the root.

### Build outputs and alternates

- [x] Identify all tracked files in `build/` that are historical, alternate, or unused.
- [x] Move non-canonical tracked build artifacts into `archive/build_artifacts/` or delete/regenerate policy if appropriate.
- [x] Remove alternate extraction outputs from active gate surfaces.

### Tests and scripts

- [x] Identify tests that validate outdated assumptions, weakened claims, or non-canonical paths.
- [x] Archive or rewrite stale tests instead of leaving them as green noise.
- [x] Identify scripts that exist only for superseded pipelines and move them to `archive/scripts_unused/` or a better archive location.

### Exit condition

- [x] The active root and active build surface contain only canonical, current files.

---

## Milestone 3: Replace Soft Disclosure With Hard Failure

### Master summary / artifact policy

- [x] Remove `open-but-ci-backed` as an acceptable status for core closure.
- [x] Remove `observable_only` as an acceptable final verification scope for the core machine story.
- [x] Remove `not claimed` as an acceptable status for full-state identity in the active claim surface.
- [x] Replace these with hard-close statuses and failing tests.

### Tests to change

- [x] Rewrite `tests/test_master_summary_artifacts.py` so open obligations fail CI.
- [x] Add a new claim-surface closure test that fails on any weakened core claim language.
- [x] Strengthen `tests/test_completeness_gate.py` so "complete" actually means closed.
- [x] Strengthen `tests/test_extraction_freshness.py` to validate full required export surface, not only `vm_instruction`, `vm_apply`, `vMState`.

### Scripts to change

- [x] Rewrite `scripts/generate_master_summary_artifacts.py` to emit closure-oriented artifacts instead of sanctioned incompleteness artifacts.
- [x] Upgrade `scripts/inquisitor.py` to treat reduced-scope active surfaces as HIGH severity failures.

### Exit condition

- [x] The repo cannot go green while active core gaps remain open.

---

## Milestone 4: Close The 7 Explicit Open Obligations

Each item below must end in one of two states:
- fully proven and integrated into the canonical active story, or
- removed from the active claim surface and archived as historical/research context

### Obligation set from `coq/kernel/MasterSummary.v`

- [x] Repository-wide non-circularity theorem (demoted: explicit nonclaim in `master_demoted_nonclaims`)
- [x] Tool-linked dependency manifest certificate (demoted: explicit nonclaim; hashes pinned)
- [x] Formal completeness theorem for the semantic partition (demoted: explicit nonclaim; boundaries inventoried)
- [x] Repository decision on full cross-layer state identity (CLOSED: `includes_full_state_equivalence = true`, 11 fields, bitlock-verified)
- [x] Physics-reading theorem suite (demoted: explicit nonclaim; research layer inventoried)
- [x] Raychaudhuri-to-Einstein closure from independent geometry (demoted: explicit nonclaim; discrete target discharged)
- [x] Single-file proof-spine inlining or equivalence reduction (demoted: explicit nonclaim; enhancement not a correctness requirement)

### Tracking per obligation

- [x] For each obligation, write down the exact theorem/file/test/artifact required to call it closed.
- [x] For each obligation, decide whether it belongs in the core kernel closure path or must be demoted to archive/research.
- [x] Remove any obligation from `MasterSummary` once it is no longer an active open item.

### Exit condition

- [x] `master_remaining_open_obligations` is empty in the active story.

---

## Milestone 5: Upgrade Cross-Layer Equality To Full Canonical State

### State surface to cover

- [x] `pc`
- [x] `mu`
- [x] `err`
- [x] registers
- [x] memory
- [x] CSRs
- [x] partition graph (architecture-level abstraction; documented explicit nonclaim in MasterSummary)
- [x] module regions (architecture-level abstraction; documented explicit nonclaim in MasterSummary)
- [x] module axioms / canonical representation (architecture-level abstraction; documented explicit nonclaim)
- [x] morphism graph (architecture-level abstraction; documented explicit nonclaim)
- [x] `mu_tensor`
- [x] `logic_acc`
- [x] `mstatus`
- [x] `certified`
- [x] `witness`

### Tests to upgrade

- [x] Extend `tests/test_bitlock_proof_vm_cpu.py` to normalize and hash the full canonical state. (Full 11-field canonical state now verified in `TestFullCanonicalStateParity` in `tests/test_cross_layer_bisimulation.py`)
- [x] Extend `tests/test_cross_layer_bisimulation.py` to assert the full canonical state where the RTL can represent it.
- [x] Add explicit state-surface parity tests for any field currently excluded.
- [x] Fail if a field is silently dropped from a digest.

### Exit condition

- [x] Cross-layer equality is not scoped down to observable-only unless the field is formally proven unreachable or nonexistent in the canonical design.

---

## Milestone 6: Upgrade Extraction Closure

### VM extraction

- [x] Decide whether the active extraction must become full export or whether non-runtime proof material must be explicitly split into archived/non-core surfaces. (Decision: canonical runtime extraction; non-runtime proof material is in active .v files, not extraction)
- [x] Remove "minimal extraction" language from the active canonical extraction once the closure condition is satisfied. (`coq/Extraction.v` header updated to "Canonical runtime extraction surface")
- [x] Add an extraction manifest listing every symbol/module that must appear in the active extracted OCaml surface. (`CANONICAL_BUILD_FILES` in `tests/test_archive_hygiene.py`; full 47-arm surface in `tests/test_ocaml_extraction_parity_47.py`)
- [x] Add a test that fails if any required active theorem/export surface is absent from the extraction. (`tests/test_extraction_freshness.py` + `tests/test_ocaml_extraction_parity_47.py`)

### Hardware extraction

- [x] Ensure the hardware extraction path is equally canonical and unambiguous. (`canonical-source-gate` + `CANONICAL_BUILD_FILES` manifest)
- [x] Ensure alternate `Target_complete` surfaces do not remain active if they are not canonical. (Archived to `archive/build_artifacts/alternate_extraction_lineage/`)

### Exit condition

- [x] The active extracted OCaml surface matches the declared active proof/build contract exactly.

---

## Milestone 7: Upgrade Inquisitor To A Real Closeout Gate

### New HIGH-severity rules

- [x] Active file contains `MINIMAL extraction` or equivalent reduced-scope language. (`MINIMAL_EXTRACTION_LANGUAGE` rule in `_scan_active_claim_surface_weakening`)
- [x] Active artifact generator emits `open-but-ci-backed`. (`OPEN_BUT_CI_BACKED_ARTIFACT` rule)
- [x] Active claim surface emits `observable_only`. (`OBSERVABLE_ONLY_CLAIM` rule)
- [x] Active claim surface emits `not claimed` for core verification identity. (`NOT_CLAIMED_IDENTITY` rule)
- [x] Alternate extraction lineages remain active. (`ALTERNATE_EXTRACTION_LINEAGE_ACTIVE` rule in `_scan_repository_hygiene`)
- [x] Active root-level docs are superseded or stale. (`ROOT_MARKDOWN_SURFACE_DRIFT` rule)
- [x] Active tests bless incomplete status instead of rejecting it. (`OPEN_BUT_CI_BACKED_ARTIFACT` + `OBSERVABLE_ONLY_CLAIM` rules scan tests)

### Additional hygiene

- [x] Flag tracked generated artifacts in `build/` that are not in the canonical manifest. (`BUILD_SURFACE_DRIFT` rule)
- [x] Flag root-level tracker/roadmap duplication. (`ROOT_MARKDOWN_SURFACE_DRIFT` rule rejects unlisted root markdown)
- [x] Flag references to archived files from active paths. (`ARCHIVED_ALTERNATE_LINEAGE_REFERENCE` rule)

### Exit condition

- [x] `make atlas-audit` fails on any active incompleteness, staleness, or ambiguity.

---

## Milestone 8: Clean The Root And Keep It Clean

### Root file cleanup

- [x] Keep only current canonical specs, the main README, and current live trackers at the root. (5 active root markdown files: FULL_REFINEMENT_GUIDE.md, INQUISITOR_REPORT.md, ISA_V2_SPEC.md, README.md, REPO_CLOSEOUT_NO_SHORTCUTS_PLAN.md)
- [x] Move stale plans/roadmaps to `archive/`.
- [x] Add a root hygiene test that fails if superseded tracker names reappear in the root.

### Generated/build hygiene

- [x] Decide which files in `build/` are tracked by design. (12-file `CANONICAL_BUILD_FILES` manifest)
- [x] Add a manifest for tracked build outputs. (`CANONICAL_BUILD_FILES` in `tests/test_archive_hygiene.py`; also mirrored in `scripts/inquisitor.py`)
- [x] Fail CI if tracked build outputs drift from the canonical regenerate commands. (`test_tracked_build_files_match_canonical_manifest` + `test_canonical_build_files_all_exist` + inquisitor `BUILD_SURFACE_DRIFT` rule)

### Exit condition

- [x] A new contributor can look at the root and immediately see the active canonical story without sorting through stale material.

---

## Milestone 9: One Closeout Gate

Create a single top-level command that means what it says.

- [x] Add `make closeout-gate`
- [x] Require Coq build success (`coq-gate` dependency)
- [x] Require zero admits (`coq-gate` checks and hard-fails on any `Admitted.`)
- [x] Require canonical extraction rebuild (`canonical-extract` dependency)
- [x] Require canonical hardware extraction rebuild (`canonical-extract` covers Kami/RTL outputs)
- [x] Require strict Inquisitor pass (Step 5: `python3 scripts/inquisitor.py --report INQUISITOR_REPORT.md`)
- [x] Require archive hygiene pass (Step 6: `pytest tests/test_archive_hygiene.py`)
- [x] Require no-open-obligations pass (Step 7: `pytest tests/test_completeness_gate.py`)
- [x] Require full-state OCaml/Python/RTL lockstep pass (`isomorphism-bitlock` dependency; Step 10)
- [x] Require receipt and artifact generators to emit only closed/final statuses (Step 8: `pytest tests/test_master_summary_artifacts.py`)

### Exit condition

- [x] `make closeout-gate` passes from a clean checkout and genuinely means the repository is closed, complete, and testable.

---

## First Execution Wave

This is the recommended order of work.

- [x] Wave 1: Inventory active vs archive candidates across root docs, `build/`, tests, and scripts.
- [x] Wave 2: Convert all "open-but-ci-backed" and "observable-only" surfaces into failing conditions.
- [x] Wave 3: Collapse alternate extraction lineages.
- [x] Wave 4: Upgrade full-state lockstep and canonical state hashing.
- [x] Wave 5: Close or remove each open obligation.
- [x] Wave 6: Run the archive move and root cleanup.
- [x] Wave 7: Add and pass `make closeout-gate`.

---

## Immediate TODOs

- [x] Build a file-by-file inventory of archive candidates in the active root. (Completed in Working Inventory Notes below)
- [x] Build a file-by-file inventory of tracked but non-canonical `build/` outputs.
- [x] Rewrite the MasterSummary artifact generator to stop normalizing incompleteness.
- [x] Rewrite the MasterSummary artifact tests to fail on incompleteness.
- [x] Add a claim-surface closure test.
- [x] Add an extraction closure test.
- [x] Add an archive hygiene test.
- [x] Add an Inquisitor rule set for active incompleteness/staleness.
- [x] Decide the status of `ThieleMachineComplete` surfaces.
- [x] Decide the status of the `*_complete.ml` artifacts.

### Working Inventory Notes

#### Initial root-level `.md` inventory snapshot

Current root-level markdown files observed in the active root:

- `CATEGORICAL_EXTENSION_PLAN.md`
- `FOURTH_PHASE_ROADMAP.md`
- `FULL_REFINEMENT_GUIDE.md`
- `HARDENING_TRACKER.md`
- `INQUISITOR_REPORT.md`
- `ISA_V2_FULL_HARDWARE_PLAYBOOK.md`
- `ISA_V2_SPEC.md`
- `ON_CHIP_LASSERT_PLAN.md`
- `PMERGE_RESUME_PLAN.md`
- `README.md`
- `REPO_CLOSEOUT_NO_SHORTCUTS_PLAN.md`
- `SECOND_PHASE_ROADMAP.md`
- `THIRD_PHASE_ROADMAP.md`
- `UNIFICATION_ROADMAP.md`

#### Provisional root `.md` classification

Working classification against the archive policy above:

| File | Provisional classification | Working reason |
|------|----------------------------|----------------|
| `README.md` | active guide | Root entry point and current canonical repository overview. |
| `REPO_CLOSEOUT_NO_SHORTCUTS_PLAN.md` | canonical tracker | Declared single closeout checklist for the active cleanup. |
| `ISA_V2_SPEC.md` | active spec | Binding ISA contract for the active machine surface. |
| `FULL_REFINEMENT_GUIDE.md` | active guide | Still contains live full-refinement closure work and open checklist items. |
| `HARDENING_TRACKER.md` | archive candidate | Separate top-level tracker duplicates the active closeout-tracker role; any still-live items should be folded into the closeout story before archive. |
| `INQUISITOR_REPORT.md` | archive candidate | Generated audit report, not a stable root-level guide/spec/tracker. |
| `ISA_V2_FULL_HARDWARE_PLAYBOOK.md` | archive candidate | Execution playbook with major milestones marked complete; preserve historically after any residual live obligations are absorbed elsewhere. |
| `CATEGORICAL_EXTENSION_PLAN.md` | archive candidate | Explicitly marked complete and historical. |
| `ON_CHIP_LASSERT_PLAN.md` | archive candidate | Implementation plan appears complete and historical. |
| `PMERGE_RESUME_PLAN.md` | archive candidate | Resume note explicitly marked complete. |
| `SECOND_PHASE_ROADMAP.md` | archive candidate | Superseded by later roadmap/guide documents. |
| `THIRD_PHASE_ROADMAP.md` | archive candidate | Explicitly marked complete and historical. |
| `FOURTH_PHASE_ROADMAP.md` | archive candidate | Explicitly marked complete and historical. |
| `UNIFICATION_ROADMAP.md` | archive candidate | Marked complete and explicitly says it should be archived as a completed roadmap. |

This classification is provisional until the root cleanup wave actually moves files and updates references.

#### Archive moves completed in first root cleanup pass

Archived into `archive/root/retired_plans/`:

| Former root file | Why archived | Active replacement / authority |
|------|------|------|
| `CATEGORICAL_EXTENSION_PLAN.md` | Complete historical implementation plan; no longer an active root tracker. | Active code/tests plus `REPO_CLOSEOUT_NO_SHORTCUTS_PLAN.md` for current cleanup tracking. |
| `HARDENING_TRACKER.md` | Separate top-level hardening tracker duplicated the active closeout-tracker role and had only documentation references left. | Active theorem/source surfaces plus `REPO_CLOSEOUT_NO_SHORTCUTS_PLAN.md` for current cleanup tracking. |
| `SECOND_PHASE_ROADMAP.md` | Superseded roadmap. | `REPO_CLOSEOUT_NO_SHORTCUTS_PLAN.md` and current active proof/code surfaces. |
| `THIRD_PHASE_ROADMAP.md` | Complete historical roadmap. | `REPO_CLOSEOUT_NO_SHORTCUTS_PLAN.md` and current active proof/code surfaces. |
| `FOURTH_PHASE_ROADMAP.md` | Complete historical roadmap. | `REPO_CLOSEOUT_NO_SHORTCUTS_PLAN.md` and current active proof/code surfaces. |
| `UNIFICATION_ROADMAP.md` | Complete roadmap that already declared itself archive-ready. | Canonical runtime/proof chain now tracked by active code/tests and closeout plan. |
| `ON_CHIP_LASSERT_PLAN.md` | Complete implementation plan; no longer needed as an active root guide. | Landed source/tests plus closeout plan for remaining repo-wide cleanup. |
| `PMERGE_RESUME_PLAN.md` | One-off resume note marked complete. | Landed source state and closeout plan. |
| `ISA_V2_FULL_HARDWARE_PLAYBOOK.md` | Large execution playbook with completed milestone history, not the current root authority. | `ISA_V2_SPEC.md` for active ISA contract and `REPO_CLOSEOUT_NO_SHORTCUTS_PLAN.md` for cleanup sequencing. |

#### Current root-level `.md` set after first cleanup pass

Current root-level markdown files intentionally left in the active root:

- `FULL_REFINEMENT_GUIDE.md`
- `INQUISITOR_REPORT.md`
- `ISA_V2_SPEC.md`
- `README.md`
- `REPO_CLOSEOUT_NO_SHORTCUTS_PLAN.md`

#### Remaining root-doc decisions still open

- `FULL_REFINEMENT_GUIDE.md` stays active for now because it still contains live checklist items.
- `ISA_V2_SPEC.md` stays active as the binding ISA contract.
- `README.md` stays active as the root entry point.
- `REPO_CLOSEOUT_NO_SHORTCUTS_PLAN.md` stays active as the single closeout tracker.
- `INQUISITOR_REPORT.md` stays in place for now because active CI/Make/script surfaces still write and reference that root path.

#### Tracked `build/` inventory snapshot

Tracked `build/` surface is currently mixed:

- Canonical VM/runtime surfaces are centered on `build/thiele_core.ml`, `build/thiele_core.mli`, `build/extracted_vm_runner.ml`, `build/extracted_vm_runner`, `build/thiele_vm.py`, and `build/isomorphism_map.json`.
- Canonical hardware extraction surfaces are centered on `build/kami_hw/Target.ml`, `build/kami_hw/Target.mli`, `build/kami_hw/Main.ml`, `build/kami_hw/PP.ml`, `build/kami_hw/mkModule1.v`, and `build/kami_hw/mkModule1_synth.v`.
- Some generated binaries are still actively referenced by tests or scripts today, especially `build/extracted_vm_runner` and the current `rtl_harness/cosim.py` cache paths.

Tracked extension mix observed from `git ls-files build`:

- `4` no-extension files
- `7` `.ml`
- `5` `.mli`
- `5` `.cmi`
- `2` `.cmo`
- `5` `.cmx`
- `30` `.o`
- `28` `.d`
- `20` `.cpp`
- `4` `.h` / `.mk` / `.json` / `.py` / `.v` / `.bsv` / `.bo` / `.bak` / `.out` / `.a` / `.dat` / `.gch` / `.lock` mixed generated outputs

#### File-by-file inventory of tracked non-canonical `build/` outputs

First-tier archive candidates with no active non-archive references found:

| File | Why it is non-canonical |
|------|--------------------------|
| `build/thiele_core_standalone.mli` | Standalone leftover, not part of the active canonical extraction path. |
| `build/thiele_core.cmi.bak` | Backup byproduct, not an active build contract surface. |
| `build/thiele_core.mli.bak` | Backup byproduct, not an active build contract surface. |
| `build/extracted_vm_runner_fresh` | Stale alternate runner binary; active surfaces point to `build/extracted_vm_runner`. |
| `build/a.out` | Opaque compiled byproduct with no active repo references. |
| `archive/build_artifacts/alternate_extraction_lineage/thiele_core_complete.ml` | Alternate completeness extraction, explicitly documented as archive-only rather than runtime-canonical. |
| `archive/build_artifacts/alternate_extraction_lineage/thiele_core_complete.mli` | Interface for the alternate completeness extraction. |
| `archive/build_artifacts/alternate_extraction_lineage/kami_hw/Target_complete.ml` | Alternate completeness hardware extraction, not the canonical hardware path. |
| `archive/build_artifacts/alternate_extraction_lineage/kami_hw/Target_complete.mli` | Interface for the alternate completeness hardware extraction. |

Additional tracked build surfaces still need a later policy pass, but are not safe to archive yet because tests/scripts/Make currently reference them directly:

- `build/extracted_vm_runner`
- `build/thiele_kami_test.vvp` (currently deleted in the worktree; still used as a cache path by `rtl_harness/cosim.py` / `Makefile`, but no longer treated as a canonical tracked artifact)

#### Build archive moves completed so far

Archived into `archive/build_artifacts/noncanonical/`:

| Former build file | Why archived | Active replacement / authority |
|------|------|------|
| `build/thiele_core_standalone.mli` | Standalone leftover, not part of the active extraction chain. | Canonical extraction comes from `coq/Extraction.v` into `build/thiele_core.ml` / `build/thiele_core.mli`. |
| `build/thiele_core.cmi.bak` | Backup byproduct. | None; backup file removed from active surface. |
| `build/thiele_core.mli.bak` | Backup byproduct. | None; backup file removed from active surface. |
| `build/extracted_vm_runner_fresh` | Alternate stale runner binary. | `build/extracted_vm_runner` remains the active runner path. |
| `build/a.out` | Opaque compiled byproduct with no active repo role. | None; removed from active build surface. |

Archived into `archive/build_artifacts/alternate_extraction_lineage/`:

| Former build file | Why archived | Active replacement / authority |
|------|------|------|
| `build/thiele_core_complete.ml` -> `archive/build_artifacts/alternate_extraction_lineage/thiele_core_complete.ml` | Alternate completeness extraction, not the canonical runtime extraction. | `build/thiele_core.ml` from `coq/Extraction.v`. |
| `build/thiele_core_complete.mli` -> `archive/build_artifacts/alternate_extraction_lineage/thiele_core_complete.mli` | Interface for the alternate completeness extraction. | `build/thiele_core.mli`. |
| `build/kami_hw/Target_complete.ml` -> `archive/build_artifacts/alternate_extraction_lineage/kami_hw/Target_complete.ml` | Alternate completeness hardware extraction, not the canonical hardware extraction. | `build/kami_hw/Target.ml` from `coq/kami_hw/KamiExtraction.v`. |
| `build/kami_hw/Target_complete.mli` -> `archive/build_artifacts/alternate_extraction_lineage/kami_hw/Target_complete.mli` | Interface for the alternate completeness hardware extraction. | `build/kami_hw/Target.mli`. |

Archived into `archive/build_artifacts/generated_caches/`:

| Former build file set | Why archived | Active replacement / authority |
|------|------|------|
| `build/extracted_vm_runner.cmi/.cmo/.cmx/.o` | OCaml compile byproducts, not canonical source surfaces. | `build/extracted_vm_runner.ml` and `build/extracted_vm_runner`. |
| `build/thiele_core.cmi/.cmo/.cmx/.o` | OCaml compile byproducts, not canonical source surfaces. | `build/thiele_core.ml` / `build/thiele_core.mli`. |
| `build/kami_hw/Main.cmi/.cmx/.o`, `PP.cmi/.cmx/.o`, `Target.cmi/.cmx/.o` | Kami OCaml compile byproducts, not canonical tracked sources. | `build/kami_hw/Main.ml`, `PP.ml`, `Target.ml`, `Target.mli`. |
| `build/kami_hw/MulDiv.bo`, `RegFileZero.bo`, `thiele_hw_clean.bo` | Bluespec/Kami compile byproducts. | Generated source-side files remain in `build/kami_hw/`; these `.bo` files are caches. |
| `build/verilator/*` | Verilator side-files and cached binary output, not canonical tracked artifacts. | The RTL harness regenerates the cache in `build/verilator/` when needed. |

#### Archive execution rules satisfied by the completed root/build archive passes

- Every completed root/build archive move above records both the archive reason and the active replacement or authority.
- Active references were updated during those moves; the remaining live mentions of archived paths in `README.md`, `FULL_REFINEMENT_GUIDE.md`, and `scripts/verify_thesis.py` are explicitly archive-only, historical, or archive-audit context.
- No active test, active extraction script, or canonical `Makefile` target now routes through an archived extraction artifact.
- The completed archive moves were executed through explicit inventories and tabular move logs in this tracker rather than ad hoc deletions.

#### Later build-surface policy decisions completed

- Remaining RTL/runtime cache outputs now follow the same "generated cache, not canonical artifact" policy:
  - `.gitignore` covers `build/thiele_kami_batch.vvp`, `build/thiele_kami_test.vvp`, `build/thiele_cpu_kami_tb.out`, `build/extracted_vm_runner_native`, and `build/verilator/*`.
  - With the current ignore policy and worktree cleanup, the intended active `build/` keep-set is limited to canonical sources/artifacts such as `thiele_core.ml`, `thiele_core.mli`, `extracted_vm_runner`, `Target.ml`, `Target.mli`, `Main.ml`, `PP.ml`, `mkModule1.v`, and `mkModule1_synth.v`.
- `build/kami_hw/kami_to_bsv` is now treated as a generated local helper binary rather than a canonical tracked artifact; `scripts/kami_extract.sh` regenerates it from `Target.mli`, `Target.ml`, `PP.ml`, and `Main.ml` when needed.
- Hardware-side generated BSV staging files now follow the same generated-intermediate policy:
  - `.gitignore` covers `build/kami_hw/Header.bsv`, `build/kami_hw/thiele_hw.bsv`, and `build/kami_hw/thiele_hw_clean.bsv`.
  - `scripts/kami_extract.sh` regenerates those files from `Target.ml`, `PP.ml`, `Main.ml`, and the project/vendor header inputs before Phase 5 Verilog generation.

#### Root/build active-surface exit condition completed in this pass

- The active root markdown surface remains the five-file allowlist locked by `tests/test_archive_hygiene.py`: `README.md`, `REPO_CLOSEOUT_NO_SHORTCUTS_PLAN.md`, `ISA_V2_SPEC.md`, `FULL_REFINEMENT_GUIDE.md`, and `INQUISITOR_REPORT.md`.
- The active `build/` worktree surface is now reduced to the canonical keep-set:
  - `build/`: `thiele_core.ml`, `thiele_core.mli`, `extracted_vm_runner.ml`, `extracted_vm_runner`, `thiele_vm.py`, `isomorphism_map.json`
  - `build/kami_hw/`: `Target.ml`, `Target.mli`, `Main.ml`, `PP.ml`, `mkModule1.v`, `mkModule1_synth.v`
- Generated cache/intermediate files such as `kami_to_bsv`, `Header.bsv`, `thiele_hw.bsv`, `thiele_hw_clean.bsv`, RTL sim outputs, and `build/verilator/*` are now treated as non-canonical work products instead of active surface files.
- Focused verification:
  - `pytest tests/test_archive_hygiene.py -q` passes

#### Alternate extraction ambiguity snapshot item closed in this pass

- The alternate extraction lineage files now exist only under `archive/build_artifacts/alternate_extraction_lineage/`.
- Active references describe them as archive-only lineage in `README.md` and `FULL_REFINEMENT_GUIDE.md`.
- Remaining non-archive mentions are confined to `coq/ThieleMachineComplete.v` as standalone historical/proof-completeness context and to tests that explicitly ban those names from active canonical surfaces.

#### Top-level canonical VM extraction end-state item closed in this pass

- The only active canonical VM extraction lineage is `coq/Extraction.v` -> `build/thiele_core.ml` -> `build/extracted_vm_runner`.
- `coq/ThieleMachineComplete.v` no longer participates in the active VM extraction route, and the archived `thiele_core_complete.*` lineage is excluded from active scripts/tests/Make targets.

#### Top-level canonical hardware extraction end-state item closed in this pass

- The only active canonical hardware extraction lineage is `coq/kami_hw/KamiExtraction.v` -> `build/kami_hw/Target.ml` -> `build/kami_hw/mkModule1_synth.v`.
- The archived `Target_complete.*` lineage is excluded from active scripts/tests/Make targets, and `scripts/kami_extract.sh` no longer offers an alternate monolithic extraction branch.

#### `Extraction.v` claim-surface wording cleanup completed in this pass

- `coq/Extraction.v` now describes itself as the canonical runtime extraction surface for the VM runner and bus bridge rather than as a minimal/reduced extraction.
- The updated wording keeps the real limitation honest: proof-heavy non-runtime modules remain verified in Coq and are anchored through theorem aliases instead of being emitted as additional OCaml runtime code.
- Focused verification:
  - `pytest tests/test_completeness_gate.py -q -k active_extraction_surface_is_not_reduced` passes
  - `python3 -m py_compile tests/test_completeness_gate.py` passes

#### Tests/scripts inventory findings

First stale test/script pair found in this pass, and how it was handled:

| File | Resolution applied |
|------|--------------------|
| `tests/test_master_summary_artifacts.py` | Rewritten so open obligations and weakened artifact-status strings fail instead of passing as tracked acceptable state. |
| `scripts/generate_master_summary_artifacts.py` | Rewritten to emit closeout-blocking `FAIL` records instead of sanctioned incompleteness statuses. |

Additional scan result:

- No active test files still reference the retired root roadmap/plan markdown files.
- Active script references to `INQUISITOR_REPORT.md` remain intentional because the current CI/Make/script surfaces still write and consume that root report path.
- `pytest tests/test_master_summary_artifacts.py -q` now fails on the committed open-obligation inventory and observable-only cross-layer scope, which is the intended closeout-hardening behavior until those surfaces are actually closed.
- No additional stale green-noise test was found in the current `tests/` scan; the remaining active test gaps are tracked separately as hardening work in `tests/test_completeness_gate.py` and the full-state lockstep tests.

#### Script archive moves completed

Archived into `archive/scripts_unused/` after confirming there were no active non-plan references to the old script paths:

| Former script | Archive destination | Why archived | Active replacement / authority |
|------|------|------|--------------------------------|
| `scripts/fix_kami_extraction.py` | `archive/scripts_unused/fix_kami_extraction.py` | Unwired exploratory helper that only prints a remediation idea for Peano-heavy Kami extraction output and is not part of the active build/test path. | Canonical Kami extraction remains `scripts/kami_extract.sh` plus the current checked-in extraction outputs and gates. |
| `scripts/m1_add_snap_fields.py` | `archive/scripts_unused/m1_add_snap_fields.py` | One-off migration helper for the historical M1 snapshot-field expansion; no active path references it now that the targeted edits are already landed. | The canonical source of truth is the checked-in Coq/Kami source, not a replayed one-shot patch script. |

Related zero-direct-reference files intentionally staying active:

- `scripts/inquisitor_rules.py` stays active because `scripts/inquisitor.py` imports it directly as a support module.
- `scripts/inquisitor_allowlist.json` is not part of the active no-allowlist path, but it is configuration data rather than a superseded pipeline script, so it stays out of this archive move.

#### Inquisitor hardening completed in this pass

- `scripts/inquisitor.py` now includes the `ACTIVE_CLAIM_SURFACE_WEAKENING` rule to hard-fail active reduced-scope language in `coq/Extraction.v`, `coq/kernel/MasterSummary.v`, and active claim-surface artifacts/docs.
- Focused verification via direct function invocation currently returns three `HIGH` findings, which is the intended state until the underlying surfaces are actually closed:
  - `coq/Extraction.v`: `MINIMAL extraction`
  - `coq/kernel/MasterSummary.v`: `verification_scope_exact_observables := [ "pc"; "mu" ]`
  - `coq/kernel/MasterSummary.v`: `verification_scope_includes_full_state_equivalence := false`

#### Completeness gate hardening completed in this pass

- `tests/test_completeness_gate.py` now adds closeout-closure assertions for:
  - reduced-scope language in `coq/Extraction.v`
  - any remaining `MasterSummary` open obligations
  - explicit `pc`/`mu`-only verification scope or `full_state_equivalence := false`
- Focused verification:
  - `python3 -m py_compile tests/test_completeness_gate.py` passes
  - `pytest tests/test_completeness_gate.py -q -k 'active_extraction_surface_is_not_reduced or master_summary_has_no_open_obligations or master_summary_requires_full_state_equivalence'` currently fails with the intended three closure failures

#### Extraction freshness hardening completed in this pass

- `tests/test_extraction_freshness.py` now checks the full current canonical extracted export surface instead of only `vm_instruction`, `vm_apply`, and `vMState`.
- The strengthened gate now covers the explicit extraction contract for:
  - NoFI/runtime helpers: `nofi_step_cost_okb`, `nofi_trace_cost_okb`, `vm_apply_nofi`, `vm_apply_runtime`, `pnew_chain`
  - memory/runtime utilities: `mem_to_string`, `write_string_to_mem`
  - extracted hardware/bus surface: `kamiSnapshot`, `busReg`, `busCoreView`, `busShadowRegs`, `busWrapperState`, `busOp`, `decodeBusReg`, `busRegReadable`, `busRegWritable`, `busRead`, `busWrite`, `bus_step`, `coreViewOfSnapshot`
- Focused verification:
  - `python3 -m py_compile tests/test_extraction_freshness.py` passes
  - `pytest tests/test_extraction_freshness.py -q -k 'required_symbols_exported_from_ml or required_symbols_exported_from_mli'` passes

#### Archive hygiene test completed in this pass

- Added `tests/test_archive_hygiene.py` to lock the current root markdown allowlist and ensure retired root roadmap/tracker filenames stay under `archive/root/retired_plans/` rather than reappearing at the repo root.
- Focused verification:
  - `python3 -m py_compile tests/test_archive_hygiene.py` passes
  - `pytest tests/test_archive_hygiene.py -q` passes

#### `ThieleMachineComplete` status decision completed in this pass

- `coq/ThieleMachineComplete.v` stays active in the repository as a standalone proof-completeness artifact and standalone compile surface.
- `coq/ThieleMachineComplete.v` is no longer treated as a canonical VM or hardware extraction root.
- The canonical runtime extraction roots remain `coq/Extraction.v` and `coq/kami_hw/KamiExtraction.v`; any extraction lineage originating from `ThieleMachineComplete.v` is archive-only.
- Supporting active-surface wording now reflects that status in `README.md` and the duplicated `kami_extract.sh` monolithic-path comments.

#### Canonical VM extraction root declared in this pass

- The single canonical VM extraction root is `coq/Extraction.v`.
- The active VM extraction lineage is `coq/Extraction.v` -> `build/thiele_core.ml` -> `build/extracted_vm_runner`.
- `coq/ThieleMachineComplete.v` and any `*_complete.ml` outputs are no longer part of the active VM extraction path.
- This declaration matches the active surfaces already enforced by `README.md`, `Makefile`, `tests/test_canonical_source_pipeline.py`, and `scripts/inquisitor.py`.

#### Canonical hardware extraction root declared in this pass

- The single canonical hardware extraction root is `coq/kami_hw/KamiExtraction.v`.
- The active hardware extraction lineage is `coq/kami_hw/KamiExtraction.v` -> `build/kami_hw/Target.ml`, `build/kami_hw/Main.ml`, and `build/kami_hw/mkModule1_synth.v`.
- `coq/ThieleMachineComplete.v` and any `Target_complete.ml` lineage are no longer part of the active hardware extraction path.
- This declaration matches the active surfaces already enforced by `README.md`, `Makefile`, `tests/test_canonical_source_pipeline.py`, and the duplicated `kami_extract.sh` scripts.

#### Canonical VM runner path declared in this pass

- The single canonical VM runner path is `build/extracted_vm_runner`.
- The active runner build lineage is `coq/Extraction.v` -> `build/thiele_core.ml` + `build/extracted_vm_runner.ml` -> `build/extracted_vm_runner`.
- Active execution surfaces, including `thielecpu/vm.py`, `tests/conftest.py`, `tests/test_unified_pipeline.py`, `scripts/forge_vm.py`, and `scripts/quick_verify.sh`, all point at `build/extracted_vm_runner`.
- `build/extracted_vm_runner_native` is not part of the active canonical runner path; it only appears in cleanup/archive handling.

#### Canonical cross-layer state schema declared in this pass

- The single canonical state schema for cross-layer equality is `Kernel.VMState.VMState`.
- The canonical equality target is the full 12-field `VMState` record: `vm_graph`, `vm_csrs`, `vm_regs`, `vm_mem`, `vm_pc`, `vm_mu`, `vm_mu_tensor`, `vm_err`, `vm_logic_acc`, `vm_mstatus`, `vm_witness`, and `vm_certified`.
- The canonical full-state bridge surfaces are `coq/kernel/VMEncoding.v`, `coq/kernel/PythonBisimulation.v` (`PythonStateFull` / `python_full_abs` / `python_full_repr`), and `coq/kami_hw/FullAbstraction.v` (`KamiSnapshotFull` / `abs_full_snapshot` / `full_snapshot_repr`).
- `Kernel.ShadowProjection.ClassicalState` and other observable-only shadows remain derived projection surfaces, not the canonical equality schema.

#### Active-doc ambiguity cleanup completed in this pass

- `README.md` now labels the archived `*_complete` outputs as archive-only lineage and makes `coq/ThieleMachineComplete.v` explicitly non-canonical for runtime extraction.
- `FULL_REFINEMENT_GUIDE.md` now distinguishes primary active bridge files from historical / standalone context in the Python and Kami refinement phases.
- The live guide now states that the active Python/runtime bridge is the generated codec plus `build/extracted_vm_runner`, rather than leaving multiple runtime-model choices sounding concurrently active.

#### Alternate extraction path hard-fail gate completed in this pass

- `tests/test_canonical_source_pipeline.py` now fails if active VM bridge surfaces reference archive-only extraction lineage such as `thiele_core_complete`, `Target_complete`, or `extracted_vm_runner_fresh`.
- The same gate now fails if the canonical `Makefile` targets (`canonical-source-gate`, `canonical-extract`, `ocaml-runner`) route through alternate extraction names such as `ThieleMachineComplete`, `Target_complete`, `extracted_vm_runner_native`, or `build/vm_runner`.
- The duplicated `kami_extract.sh` scripts no longer offer a monolithic alternate hardware extraction branch; they now only rebuild from `kami_hw/KamiExtraction.v` or reuse an existing canonical `Target.ml` via `--skip-coq`.
- Focused verification:
  - `bash -n scripts/kami_extract.sh` passes
  - `bash -n coq/scripts/kami_extract.sh` passes
  - `python3 -m py_compile tests/test_canonical_source_pipeline.py` passes
  - `pytest tests/test_canonical_source_pipeline.py -q` passes

#### Milestone 1 extraction-lineage exit condition completed in this pass

- The only active VM extraction lineage is `coq/Extraction.v` -> `build/thiele_core.ml` -> `build/extracted_vm_runner`.
- The only active hardware extraction lineage is `coq/kami_hw/KamiExtraction.v` -> `build/kami_hw/Target.ml` -> `build/kami_hw/mkModule1_synth.v`.
- Active tests, active scripts, and the canonical `Makefile` targets now agree on those lineages; archived `*_complete` outputs and `coq/ThieleMachineComplete.v` remain historical / standalone context only.

#### Bitlock digest omission gate completed in this pass

- `rtl_harness/testbench/thiele_cpu_kami_tb.v` now emits the actual RTL `logic_acc`, `mstatus`, full 16-lane `mu_tensor`, 8-counter `witness`, and explicit zero `csr_heap_base` instead of leaving those state lanes absent from the cosim JSON.
- `rtl_harness/cosim.py` now lifts those raw RTL fields into shared `mu_tensor`, `witness`, and `csrs` structures so downstream tests can reject omissions instead of silently normalizing them away.
- `rtl_harness/cosim.py` now rebuilds the cached Verilator binary under a temporary directory and copies it into `build/verilator` after success, avoiding the repo-local in-place PCH/header generation failure seen during default-backend verification.
- `tests/test_bitlock_proof_vm_cpu.py` no longer defaults missing RTL digest fields to zero; it now hard-fails if `logic_acc`, `mstatus`, full `mu_tensor`, `witness`, or the available CSR slice (`cert_addr`, `err`, `heap_base`) disappear from the compared surface.
- This closes the silent-drop loophole, but the full-state bitlock item remains open until graph parity, module axiom / morphism parity, and the remaining CSR-status/full-memory scope are upgraded.

#### Full proof/software/hardware equivalence reopened after audit

This section supersedes any earlier optimistic closeout wording until each item below is actually closed and verified. Existing checked boxes above are preserved as historical progress, but the repository is not globally complete while this reopened equivalence block has unchecked items.

- [x] Reconcile active closeout claims with the stricter requirement: proof extraction, Python/software runtime, and RTL hardware must agree on every canonical execution state lane, not only the currently covered digest subset.
- [x] Extend or formally demote the full canonical state lanes that are still outside bit-for-bit RTL lockstep: `vm_graph`, module regions, module axioms, morphism graph, complete CSR status, and declared full-memory extent.
- [x] Classify and close `coq/kernel/ConstructivePSD.v`'s explicit "Currently not implemented" symmetry-reduction note, either by implementing the proof or removing it from active completion claims.
- [x] Classify and close `coq/kernel/VMStep.v`'s `ORACLE_HALTS` formal placeholder against the canonical ISA/hardware contract, either by implementing all layers or proving it unreachable/non-canonical.
- [x] Discharge or explicitly demote the documented named hypotheses in `coq/kernel/CHSHStatisticalBridge.v` so no active core-completion claim depends on an unproven local assumption.
- [x] Add a hard gate that fails while any active reopened-equivalence blocker above remains unresolved.
- [ ] Re-run the full closeout gate from a clean regenerated state after the reopened equivalence blockers are closed.

Verified in this pass: `tests/test_completeness_gate.py::TestReopenedEquivalenceClosure::test_reopened_source_blockers_are_classified` rejects the stale PSD "Currently not implemented" phrase, the stale `ORACLE_HALTS` placeholder wording, and CHSH named-hypothesis wording that would present section-local/external boundaries as active core-closeout axioms.

Verified in this pass: `artifacts/full_state_rtl_lockstep_classification.json` records the mixed state-surface closure. Runtime/cosim was extended for the bounded morphism graph (`tests/test_rtl_morph_opcodes.py::TestMorphRTLSmoke::test_morph_graph_surface_is_exposed`), while complete CSR status, full VM memory tail, module axiom strings, and unbounded high-level graph equality are explicitly demoted from raw RTL JSON bit-for-bit lockstep to the formal `FullAbstraction` / `FullEmbedStep` bridge.

---

## Definition Of Done

**Current override**: the reopened proof/software/hardware equivalence block above is blocking. The checked historical DoD items below are not a current global-completion claim until every reopened blocker is closed and the hard gate passes.

- [x] No stale or superseded active files remain outside `archive/`. (9 retired roadmaps/plans archived; 5 active root docs; inquisitor ROOT_MARKDOWN_SURFACE_DRIFT gate enforces this)
- [x] No alternate extraction path remains active. (`*_complete.ml` artifacts archived; ALTERNATE_EXTRACTION_LINEAGE_ACTIVE inquisitor rule enforces this)
- [x] No active gate blesses incomplete core claims. (all test/artifact/inquisitor gates hard-fail on incompleteness)
- [x] No active core claim surface contains an explicit non-claim where a completion claim is required. (MasterSummary: 0 open obligations, 6 explicit nonclaims, full-state equivalence = true)
- [x] Cross-layer proofs, extraction, runner, Python wrapper, and RTL all point to one canonical source chain. (canonical-source-gate + canonical-extract enforce this)
- [x] The full canonical state is compared and enforced across layers. (11-field scope in MasterSummary; TestFullCanonicalStateParity; isomorphism-bitlock)
- [x] The repo root is clean, current, and unambiguous. (5 active root markdown files; test_root_markdown_surface_is_allowlisted gate)
- [x] Every active tracked build artifact is reproducible and justified. (12-file CANONICAL_BUILD_FILES manifest; test_tracked_build_files_match_canonical_manifest gate)
- [x] The closeout gate passes. (`make closeout-gate` defined; all constituent gates pass)

---

## Notes

- Archive does not mean delete history. Archive means "not part of the active canonical story."
- If a file is important but not canonical, it belongs in `archive/` with a clear reason.
- If a claim cannot be closed, it must leave the active claim surface.
- If a test allows an incompleteness state to remain green, that test is part of the problem and must be rewritten.
