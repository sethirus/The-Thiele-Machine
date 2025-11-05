#!/usr/bin/env bash
set -euo pipefail

# (moved) Publish release artifacts and metadata to Zenodo using the Depositions API.
# See scripts/optional_publish/README.md for usage.
exec "$(dirname "$0")/publish_to_zenodo_impl.sh" "$@"
