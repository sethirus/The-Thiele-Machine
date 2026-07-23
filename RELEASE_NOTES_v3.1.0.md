# The Thiele Machine — v3.1.0 Release Notes (Zenodo publication record)

**Version:** 3.1.0
**Release date:** 2026-07-23
**Author:** Devon Thiele
**Concept DOI (all versions):** [10.5281/zenodo.17316437](https://doi.org/10.5281/zenodo.17316437) — Zenodo mints a new version-specific DOI when this deposit is published; the concept DOI above continues to resolve to the latest version.
**License:** Apache-2.0 (software) · CC-BY-SA-4.0 (monograph and distillation)
**Repository:** https://github.com/sethirus/The-Thiele-Machine

---

## Deposit description (paste-ready for Zenodo / GitHub release)

v3.1.0 — elliptope gate + pointer-observable criterion, honesty pass, integrity fixes.

New formal content (Coq 8.18.0, zero project-local axioms, zero admits):

- **Elliptope completion** (`coq/kernel/quantum/ElliptopeCompletion.v`): the full CHSH
  correlator quantum set characterized as existential completion of the cross moments —
  every LHV correlator inside (deterministic strategies, finite mixtures), the Tsirelson
  bound S² ≤ 8 for the whole set via Cauchy–Schwarz inside the PSD form, the PR box
  excluded, classical ⊂ elliptope strict.
- **Elliptope gate** (`coq/kernel/quantum/ElliptopeGate.v`): a decidable two-branch
  ℤ-arithmetic membership check (fraction-free Sylvester for the strict interior; a
  rational LDLᵀ certificate reaching singular/boundary completions). A passing check
  provably entails elliptope membership (`elliptope_check_full_sound`); the Tsirelson-curve
  Pythagorean point (3/5, 4/5, 4/5, −3/5) is accepted by computation and the PR box is
  never accepted (`elliptope_full_gate_never_accepts_pr_box`).
- **Pointer-observable criterion** (`coq/kernel/frontier/PointerObservable.v`,
  `PointerObservableReductions.v`): redundant record proliferation formalized; all five
  deployed metering disciplines (PoS finality, gas metering, TEE attestation, certificate
  transparency, proof-carrying verification) machine-checked as unique pointers.
  `five_disciplines_are_pointers` closes under the global context — no axioms at all.

Honesty pass across all front doors: the "Thiele-honest" gate framing is renamed
*slice-coherent* (the gate tests slice membership, not truthfulness); the top-of-document
anchor separates what is proved (the lossy-shadow direction) from what is believed ("the
machine is real the way a law is real"); the physics overclaim is cut.

Integrity fixes: the RTL pipeline manifest is regenerated against the committed tree; the
bitstream board reference is corrected to the board actually built (Artix-7 Arty xc7a35t);
two definitionally-trivial positive-witness lemmas are inlined at their use sites per
Inquisitor discipline.

Assumption receipt regenerated for this release: **281 files, 3,980 addressable theorems
probed, zero project-local axioms** (2,934 close under the global context outright; 1,046
lean only on Coq standard-library axiom families).

---

## Assumption receipt — v3.0.1 → v3.1.0

Regenerated end-to-end on Coq 8.18.0 (probe: `coq/AssumptionsProbeAll.v`; receipt:
`artifacts/print_assumptions_all_proofs.json`):

| Metric | v3.0.1 | v3.1.0 |
|---|---|---|
| Files probed | 277 | **281** |
| Addressable theorems probed | 3,937 | **3,980** |
| Closed under the global context | 2,923 | **2,934** |
| Lean only on Coq-stdlib axiom families | 1,014 | **1,046** |
| `functional_extensionality_dep` users | 939 | **968** |
| `sig_forall_dec` users | 976 | **1,008** |
| `sig_not_dec` users | 272 | **276** |
| `classic` (excluded middle) users | 67 | **67** |
| Project-local / third-party axiom findings | 0 | **0** |

The excluded-middle count is unchanged: all 67 uses enter through Coq standard-library
real-analysis lemmas in the physics-bridge families, none through project code. The new
elliptope theorems lean only on the classical-reals construction and functional
extensionality; the pointer-observable theorems close under the global context outright.

## Verification record (release finalization, 2026-07-23)

All gates run on Ubuntu 24.04 with the CI toolchain (Coq 8.18.0, OCaml 4.14.1,
Icarus Verilog 12.0, Verilator 5.020, Yosys 0.33, Z3 4.15.1, Node 24):

| Gate | Result |
|---|---|
| Full Coq proof tree (`coq/_CoqProject`, 281 files) | ✅ 281/281 compile, **0 Admitted** |
| Rebuild determinism | ✅ clean rebuild reproduced every tracked `.vo`/`.glob` and all extraction outputs **byte-identically** |
| Inquisitor proof audit (`scripts/inquisitor.py`) | ✅ **0 HIGH / 0 MEDIUM / 0 LOW** across 284 files |
| Bedrock assumption gate (`scripts/inquisitor_assumption_gate.py`) | ✅ PASS |
| Proof-scope drift gate (`tests/test_coq_proof_scope.py`) | ✅ 5/5 |
| Proof-hygiene numbers (README ↔ receipt, number-by-number) | ✅ PASS |
| Full Python test suite (`pytest tests/ --strict-backends`, no skips permitted) | ✅ **970 passed, 0 failed** |
| 3-layer bisimulation parity (`scripts/parity_extracted_only.sh`) | ✅ PASS (92 tests) |
| RTL pipeline manifest (`tests/test_rtl_pipeline_manifest.py`) | ✅ fresh, matches committed tree |
| Master-summary probe (`coq/AssumptionsProbe.v`, 39 claims) | ✅ 26 closed / 13 stdlib-only; `INQUISITOR_ASSUMPTIONS.json` pin verified |
| Monograph + math spec | ✅ rebuilt from source (pdflatex ×3 + pdftotext), counts and dates current |

Release-finalization corrections applied on top of the v3.1.0 feature commit:

1. **Inquisitor findings fixed** — `toy_cert_proliferates` and
   `mirror_metered_proliferates` (definitionally-trivial positive witnesses flagged
   CIRCULAR_DEFINITION) inlined at their single use sites
   (`toy_cert_unique_pointer`, `mirror_unique_pointer`) and deleted, per the tool's
   prescribed remedy. No remaining theorem's statement or proof content changed.
2. **RTL pipeline manifest regenerated** — the committed manifest predated final source
   edits (44 stale hash/size pins, e.g. `CanonicalCPUProof.v`); regenerated against the
   committed tree.
3. **Assumption receipts regenerated** — main probe (281 files / 3,980 theorems) and
   master-summary probe (the query for `master_non_circular_chsh_formula`, a theorem
   deliberately removed with its vacuous re-export, dropped from the probe: 39 claims).
4. **Version/metadata propagation** — 3.1.0 in `.zenodo.json`, `CITATION.cff`, README
   BibTeX; release date 2026-07-23; July 2026 dates across the disclosure, distillation,
   monograph, and math spec; v3.1.0 changelog row added to `TECHNICAL_DISCLOSURE.md`;
   stale counts and example-file path references corrected repo-wide.
5. **Honesty-pass completion in the math spec** — the biconditional theorem environment,
   Proof-File-Index row, and classification rows renamed from "Thiele honest" to
   *slice-coherent*, matching the corpus-wide rename; the README Formal-Spine row
   likewise; the Turing-point bullet now states plainly that the slice gate rejects it
   while the full-elliptope gate accepts it.
6. **Math spec coverage of the new material** — elliptope-completion/gate rows and a
   frontier block added to the Proof File Index; elliptope and pointer rows added to the
   epistemological classification; a new "The Pointer-Observable Criterion" section
   documents the schema, the five discipline instantiations, and the evidence-not-proof
   scope fence.
7. **Monograph bitstream bookkeeping** — explicit distinction added: the Genesys 2
   K325T bitstream is a CI artifact built on every relevant push and never committed;
   the bitstream committed in the repository is the Artix-7 Arty build
   (`build/thiele_xc7a35t.bit`).
8. **README feature-freeze wording reconciled** — the freeze is stated as what it is:
   machine semantics frozen (no new opcodes, no step-relation or cost-law changes),
   with machine-untouched characterization tiers over the frozen semantics accepted.
9. **MasterSummary roster hygiene** — the name of the removed
   `master_non_circular_chsh_formula` re-export dropped from the exported-names roster,
   metadata ledger, file inventory (52 → 51, count theorem updated), and coverage
   ledger; full tree recompiles, `verify_zero_admits` re-run clean.
10. **Verification receipt now generated, not hand-written** —
    `scripts/generate_verification_receipt.py` derives every field of
    `artifacts/verification_receipt.json` from live checks (Coq build state, a fresh
    Inquisitor run, the blind/sighted structural-advantage programs executed on the VM,
    the full pytest suite) and mechanically re-validates each claim anchor against the
    probe inventory before listing it; the claims list now includes the elliptope-gate
    and pointer-observable anchors.

## How to publish this version on Zenodo

1. Merge `release/v3.1.0` to `main` (done as part of this release process) and create a
   GitHub release tagged `v3.1.0` targeting the merge commit. If the repository's
   GitHub–Zenodo integration is enabled, Zenodo archives the release automatically and
   reads deposit metadata from `.zenodo.json` (already at 3.1.0 with current counts).
2. If publishing manually instead: create a new version of the existing Zenodo record
   (concept DOI 10.5281/zenodo.17316437), upload the release archive, and paste the
   "Deposit description" section above into the description field. Set version `3.1.0`
   and publication date `2026-07-23`.
3. Zenodo mints a new version-specific DOI at publish time. The concept DOI in
   `CITATION.cff` and the README badge/BibTeX is intentionally retained — it always
   resolves to the newest version. No post-publish file edits are required for DOI
   correctness; optionally, cite the new version DOI in contexts that reference v3.1.0
   specifically.

## Post-publish checklist

- [ ] GitHub release `v3.1.0` published (triggers/accompanies the Zenodo deposit)
- [ ] Zenodo deposit shows version 3.1.0, date 2026-07-23, Apache-2.0, open access
- [ ] Concept DOI resolves to the new version
- [ ] CI green on `main` after the merge
