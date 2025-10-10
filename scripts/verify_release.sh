#!/usr/bin/env bash
set -euo pipefail

# Verify the integrity and provenance of a release tarball and associated artifacts.
# Usage: ./scripts/verify_release.sh The-Thiele-Machine-v1.0.2.tar.gz

TARBALL=${1:-}
if [ -z "$TARBALL" ]; then
  echo "Usage: $0 <release-tarball>" >&2
  exit 2
fi

MANIFEST=artifacts/MANIFEST.sha256
EXPECTED_SHA=$(grep "$(basename "$TARBALL")" "$MANIFEST" | awk '{print $1}')
if [ -z "$EXPECTED_SHA" ]; then
  echo "No SHA entry found for $TARBALL in $MANIFEST" >&2
  exit 3
fi

echo "Expected SHA256: $EXPECTED_SHA"
CALC_SHA=$(sha256sum "$TARBALL" | awk '{print $1}')
if [ "$CALC_SHA" != "$EXPECTED_SHA" ]; then
  echo "SHA mismatch! calculated=$CALC_SHA expected=$EXPECTED_SHA" >&2
  exit 4
fi

echo "SHA256 matches."

# Verify detached GPG signature if present
if [ -f "${TARBALL}.asc" ]; then
  echo "Found detached signature ${TARBALL}.asc — verifying with gpg..."
  if gpg --verify "${TARBALL}.asc" "$TARBALL" 2>/dev/null; then
    echo "GPG signature verification: OK"
  else
    echo "GPG signature verification: FAILED (import required or wrong key)" >&2
  fi
else
  echo "No detached signature (${TARBALL}.asc) found in working directory. Check GitHub release page for uploaded .asc file."
fi

# Print expected SWHID and DOI for manual verification
echo
echo "Expected Software Heritage SWHID: swh:1:dir:d3894a5c31028e8d0b6d3bcdde9d257148d61e59"
echo "Expected DOI (version-specific): 10.5281/zenodo.17316438"

echo
# Optionally verify a signed git tag if present
if git rev-parse v1.0.2 >/dev/null 2>&1; then
  echo "Found git tag v1.0.2 — attempting to verify tag signature..."
  git tag -v v1.0.2 || echo "Tag verification failed or tag is not signed."
else
  echo "No local git tag v1.0.2 found. After you import the maintainer's public key and fetch tags, run: git fetch --tags && git tag -v v1.0.2"
fi

# Receipt verification reminder
echo
echo "To verify the canonical receipts locally run:"
echo "  python3 demonstrate_isomorphism.py"
echo "  python scripts/challenge.py verify receipts"
echo "  ./scripts/verify_truth.sh examples/tsirelson_step_receipts.json"

echo "To re-run the Coq verification inside a container (if available):"
echo "  docker run --rm -v \"$PWD\":/work coqorg/coq:8.18 bash -c \"cd /work && ./coq/verify_subsumption.sh\""

exit 0
