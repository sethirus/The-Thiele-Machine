# GitHub Actions Workflows Documentation

This document provides a comprehensive overview of all GitHub Actions workflows in the Thiele Machine repository, explaining their purpose, triggers, and rationale.

## Overview

The Thiele Machine uses three primary workflows:
1. **CI Workflow** (`ci.yml`) - Continuous Integration and Testing
2. **Release Workflow** (`release.yml`) - Release Packaging with Proofs
3. **Publish Workflow** (`publish.yml`) - PyPI Package Publishing

---

## 1. CI Workflow (ci.yml)

**File:** `.github/workflows/ci.yml`

### Purpose
The CI workflow is the main continuous integration pipeline that validates all code changes, ensures correctness, and maintains the integrity of the Thiele Machine system.

### Triggers
- Push to branches: `new-public-branch-default`, `main`, `master`
- Pull requests to the same branches
- Manual dispatch (`workflow_dispatch`)
- Daily schedule at 3 AM UTC (`cron: '0 3 * * *'`)

### Jobs

#### 1. `build` Job
**Purpose:** Core integration testing and validation

**Rationale:** This job ensures that the Thiele Machine can be built, tested, and verified on a standard Ubuntu environment. It validates the core functionality before more extensive testing.

**Key Steps:**
- Install system dependencies (opam for OCaml/Coq support)
- Set up Python 3.12 environment
- Install project with full dependencies (`pip install -e .[full]`)
- Check Python syntax for critical demo files
- Run pytest test suite
- Run falsifiability analysis (ensures claims are testable)
- Validate README tables and μ-ledger receipts
- Ensure Coq files are admit-free (no unproven assumptions)
- Generate admit report for transparency
- Provision ephemeral kernel keys for CI testing
- Verify Bell inequality artifact (quantum mechanics validation)
- Run fuzzing corpus tests and receipt mutation fuzzer (security testing)

**Why This Matters:** This comprehensive testing ensures that every code change maintains correctness, security, and scientific validity.

#### 2. `self-hosting-kernel` Job
**Purpose:** Cross-platform kernel reconstruction and verification

**Rationale:** The Thiele Machine's self-hosting kernel is a critical component that must work identically across all platforms. This job ensures platform independence and reproducibility.

**Test Matrix:**
- Operating Systems: Ubuntu, macOS, Windows
- Python Versions: 3.11, 3.12

**Key Steps:**
- Test kernel reconstruction from bootstrap receipts
- Verify kernel hash matches expected value (ensures bit-for-bit reproducibility)
- Test kernel self-verification capability
- Test proof pack creation
- Test shell verifier (Unix-only, proves minimal dependencies)
- Verify Lines of Code (LoC) budget compliance (≤220 LoC for verifier)
- Test hello example for end-to-end validation

**Why This Matters:** Self-hosting is fundamental to the Thiele Machine's trustworthiness. If the kernel can reconstruct and verify itself consistently across platforms, it demonstrates the system's mathematical integrity.

#### 3. `experiments` Job
**Purpose:** Run falsification experiments

**Rationale:** The Thiele Machine makes falsifiable claims about computation and physics. This job runs experiments designed to potentially disprove those claims, demonstrating scientific rigor.

**Key Steps:**
- Run falsification experiments via `make experiments-falsify`
- Upload experiment results as artifacts for review

**Why This Matters:** A system that actively tries to falsify its own claims is more trustworthy than one that only seeks confirmation.

#### 4. `as-above-so-below-coq` Job
**Purpose:** Formal verification of theoretical foundations

**Rationale:** The "As Above, So Below" principle connects logical proofs to physical reality. This job verifies the Coq formal proofs that underpin the theoretical framework.

**Proofs Compiled:**
- Genesis.v - Foundation axioms
- Core.v - Core logical framework
- PhysRel.v - Physical relations
- LogicToPhysics.v - Logic-to-physics bridge
- WitnessIsGenesis.v - Witness equivalence proofs
- CostIsComplexity.v - Computational cost theory
- Separation.v - Separation logic
- NoFreeLunch.v - No-free-lunch theorems

**Why This Matters:** Mathematical proofs provide the theoretical foundation. Verifying them in Coq ensures they are logically sound.

#### 5. `as-above-so-below-python` Job
**Purpose:** Execute witness and verifier for theoretical framework

**Rationale:** Complements the Coq proofs by providing executable witnesses that demonstrate the theory in practice.

**Key Steps:**
- Compile Coq proofs
- Install Python dependencies
- Execute Ouroboros witness and verifier

**Why This Matters:** Theory must connect to practice. This job ensures the theoretical proofs have practical implementations.

#### 6. `verify_artifact` Job
**Purpose:** End-to-end artifact verification

**Rationale:** After all individual components pass, this job verifies that the complete proof pack can be packaged and verified as a whole.

**Dependencies:** Requires `build`, `experiments`, `as-above-so-below-coq`, and `as-above-so-below-python` jobs to complete successfully.

**Key Steps:**
- Package complete proof pack
- Run minimal verifier on the proof pack
- Run adversarial checks (attempts to break the system)

**Why This Matters:** Individual tests passing doesn't guarantee the integrated system works. This validates the complete artifact.

#### 7. `proofpack-smoke` Job
**Purpose:** Smoke testing for proof pack generation

**Rationale:** Ensures proof packs can be generated with consistent manifest digests for reproducibility.

**Key Steps:**
- Generate proof pack with timestamped run tag
- Inspect bundle and manifest
- Publish manifest digest
- Update RESULTS.md with digest information
- Upload artifacts for inspection

**Why This Matters:** Proof packs are the deliverable artifacts. This ensures they can be reliably generated and tracked.

#### 8. `turbulence-high` Job
**Purpose:** High-budget turbulence testing

**Rationale:** Tests the system under high-complexity scenarios to ensure robustness under demanding conditions.

**Key Steps:**
- Run high-budget turbulence pipeline
- Inspect turbulence bundle
- Publish turbulence highlights (protocol checks, runtime metrics)
- Upload turbulence artifacts

**Why This Matters:** Systems must work under stress. This validates performance under high-complexity conditions.

#### 9. `test-and-verify` Job
**Purpose:** Comprehensive testing with external proof tools

**Rationale:** Ensures the system works with external proof tools and maintains strict linting/typing standards.

**Key Steps:**
- Install external proof tools
- Provision kernel keys
- Run linters (flake8, mypy)
- Run full test suite
- Run isomorphism demo test
- Canonicalize and verify receipts
- Run packager checks

**Why This Matters:** Integration with external tools proves the system isn't isolated but can work within the broader proof/verification ecosystem.

---

## 2. Release Workflow (release.yml)

**File:** `.github/workflows/release.yml`

### Purpose
Automates the creation of verified releases with cryptographic attestations and SLSA provenance.

### Triggers
- Release creation events (`types: [created]`)
- Manual dispatch (`workflow_dispatch`)

### Rationale
When creating a release, it's critical to:
1. Build receipts for the kernel
2. Generate SLSA (Supply chain Levels for Software Artifacts) provenance
3. Provide transparency logs (via Rekor)
4. Build Go verifier for cross-language verification
5. Package everything with cryptographic verification

### Job: `build-and-prove`

**Key Steps:**
1. **Build receipt for kernel** - Creates cryptographic receipt proving kernel authenticity
2. **Generate SLSA provenance** - Documents the build process for supply chain security
3. **Submit to Rekor** (dry-run) - Prepares transparency log submission
4. **Build Go verifier** - Provides a Go-based verifier for language diversity
5. **Create release bundle** - Packages all artifacts
6. **Upload release assets** - Attaches artifacts to GitHub release
7. **Print verification commands** - Documents how users can verify the release

**Why This Matters:** Releases must be verifiable and traceable. SLSA provenance and transparency logs ensure users can trust the artifacts.

---

## 3. Publish Workflow (publish.yml)

**File:** `.github/workflows/publish.yml`

### Purpose
Publishes the Thiele Machine package to PyPI for easy installation.

### Triggers
- Release publication events (`types: [published]`)
- Manual dispatch (`workflow_dispatch`)

### Rationale
Making the package available via PyPI allows users to install with `pip install thiele-replay`, lowering the barrier to entry.

### Job: `build-and-publish`

**Key Steps:**
1. **Build package** - Creates Python distribution packages
2. **Check package** - Validates package integrity with twine
3. **Publish to PyPI** - Uploads to PyPI using trusted publishing
4. **Test installation** - Verifies the package can be installed from PyPI
5. **Update Homebrew formula** - Prepares Homebrew formula for package managers
6. **Print installation instructions** - Documents user installation process

**Why This Matters:** Distribution is critical for adoption. PyPI integration makes the Thiele Machine accessible to the Python ecosystem.

---

## Workflow Interaction Diagram

```
┌─────────────────┐
│   Code Push/PR  │
└────────┬────────┘
         │
         ▼
┌─────────────────────────────────────────────────────┐
│                  CI Workflow                        │
│  ┌──────────┐  ┌──────────────────┐  ┌───────────┐ │
│  │  build   │  │ self-hosting     │  │experiments│ │
│  └──────────┘  │    kernel        │  └───────────┘ │
│                └──────────────────┘                 │
│  ┌──────────┐  ┌──────────────────┐  ┌───────────┐ │
│  │as-above  │  │ verify_artifact  │  │proofpack  │ │
│  │so-below  │  │                  │  │  -smoke   │ │
│  └──────────┘  └──────────────────┘  └───────────┘ │
└─────────────────────────────────────────────────────┘
         │
         │ (All tests pass)
         ▼
┌─────────────────┐
│  Release Event  │
└────────┬────────┘
         │
         ├──────────────────────┬─────────────────────┐
         ▼                      ▼                     ▼
┌─────────────────┐    ┌─────────────────┐  ┌───────────────┐
│ Release         │    │ Publish         │  │ Artifacts     │
│ Workflow        │    │ Workflow        │  │ Published     │
│ (SLSA+Rekor)    │    │ (PyPI)          │  │ to GitHub     │
└─────────────────┘    └─────────────────┘  └───────────────┘
```

---

## Key Principles

### 1. **Defense in Depth**
Multiple layers of testing (unit tests, integration tests, formal proofs, adversarial testing) ensure robustness.

### 2. **Reproducibility**
All tests verify that outputs are bit-for-bit identical across platforms and runs.

### 3. **Transparency**
Every workflow generates artifacts and logs that can be inspected and verified.

### 4. **Falsifiability**
The system actively tries to disprove its own claims, following the scientific method.

### 5. **Self-Hosting**
The kernel can reconstruct and verify itself, proving the system's mathematical consistency.

### 6. **Supply Chain Security**
SLSA provenance and transparency logs ensure releases can be cryptographically verified.

---

## Maintenance Notes

### When Adding New Features
- Add corresponding tests to the `build` job
- If it affects the kernel, add tests to `self-hosting-kernel`
- If it involves proofs, update `as-above-so-below-coq`
- Update this documentation

### When Relocating Files
- Update all script paths in workflows
- Update paths in scripts themselves (e.g., `verify_bell.sh`, `package_proof.sh`)
- Test locally before committing
- Check symlinks still point to correct locations

### Performance Considerations
- The daily scheduled run helps catch time-dependent bugs
- Matrix testing across OS/Python versions catches platform-specific issues
- Artifact uploads preserve evidence for debugging

---

## Troubleshooting

### Common Issues

1. **"File not found" errors in scripts**
   - Check if files have been reorganized
   - Update paths in both workflows and scripts
   - Verify symlinks are correct

2. **Kernel hash mismatches**
   - Usually indicates non-deterministic behavior
   - Check for timestamps, random values, or filesystem-dependent code
   - Verify Python version consistency

3. **Coq compilation failures**
   - Ensure Coq version compatibility (8.18+)
   - Check for missing dependencies in theory files
   - Verify import paths

4. **Artifact verification failures**
   - Check that all dependencies completed successfully
   - Verify manifest generation logic
   - Inspect uploaded artifacts for corruption

---

## Future Enhancements

- Consider adding workflow status badges to README.md
- Implement automatic rollback on workflow failures
- Add performance regression testing
- Expand turbulence testing scenarios
- Consider adding nightly builds with extended test suites

---

**Last Updated:** 2025-11-03
**Maintainer:** DevOps Team
**Related Documentation:** See README.md, CONTRIBUTING.md, SECURITY.md
