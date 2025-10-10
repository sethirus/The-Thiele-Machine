Optional publishing helpers (archived)
=====================================

This directory contains optional helper scripts for publishing release
artifacts to archival services (Zenodo and OSF). These helpers are
archived here to reduce top-level clutter while preserving functionality
for future maintainers.

Files:
- `publish_to_zenodo.sh` — creates/updates a Zenodo deposition (requires ZENODO_TOKEN)
- `publish_to_osf.sh` — uploads files to an OSF node (requires OSF_TOKEN and OSF_NODE_ID)
- `publish_archives_helper.sh` — wrapper that calls the two scripts above

To use these scripts:

1. Make them executable: `chmod +x scripts/optional_publish/*.sh`
2. Set environment variables with your tokens (do not commit these):
   - `export ZENODO_TOKEN=...` and/or
   - `export OSF_TOKEN=...; export OSF_NODE_ID=...`
3. Run one of the scripts directly, e.g. `./scripts/optional_publish/publish_to_zenodo.sh`.

Security: These scripts are intentionally inert unless valid tokens are
provided. Keep tokens in environment variables or a secret manager; do not
store them in the repository.
