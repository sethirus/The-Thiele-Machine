Helper scripts
===============

This folder contains helper scripts for publishing and verifying release artifacts.

Make scripts executable before running:

  chmod +x scripts/*.sh


Available scripts (core):

- `verify_release.sh` — Verifies tarball SHA-256, optionally verifies GPG detached signature and provides pointers to SWH and DOI checks.

Optional publishing helpers have been archived to `scripts/optional_publish/` to reduce top-level clutter. See that directory for Zenodo/OSF publishing helpers.

If you plan to run the publishing scripts on a machine or CI runner, ensure the required tokens are present in the environment and never hard-code secrets into the repository.
