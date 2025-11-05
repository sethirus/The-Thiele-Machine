# Changelog

All notable changes to this repository will be documented in this file.

## [Unreleased] - 2025-10-31

- Merge: Feature branch addressing verifier/receipt pipeline gaps. Key items:
  - Canonical CNF/model mapping and `model_sha256` persistence.
  - LRAT vs RUP handling with conservative analyzer and optional normalization.
  - Receipt specification bump and per-step + top-level signing/verification.
  - Validator μ-spec isolation and production-key generation guard.
  - Operator helpers: `scripts/provision_keys.py`, `scripts/install_proof_tools.sh`.
  - CI updates: proof-tool installation enforcement and targeted linting for new helpers.
  - Tests: medium CNF sanity and expanded test-suite checks; local run: 279 passed, 4 skipped.

### Notes

- The automated merge was performed non-interactively and created an unsigned merge commit to avoid interactive GPG pinentry in the CI environment. If signed history is required, re-apply the merge in an environment with your GPG agent.
