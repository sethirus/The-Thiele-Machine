#!/usr/bin/env bash
set -euo pipefail

# Wrapper stub that runs the real OSF publishing implementation
exec "$(dirname "$0")/publish_to_osf_impl.sh" "$@"
