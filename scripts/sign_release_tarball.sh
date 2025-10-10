#!/usr/bin/env bash
set -euo pipefail

# Signs the release tarball and uploads the detached ASCII signature to the
# GitHub release v1.0.2. Requires `gpg` and `gh` on PATH and that the
# signing key is available in the local GPG keyring.

TARBALL="The-Thiele-Machine-v1.0.2.tar.gz"
KEYID="5127D27049B531F1"
RELEASE_TAG="v1.0.2"

if [[ ! -f "$TARBALL" ]]; then
  echo "Tarball $TARBALL not found"
  exit 1
fi

echo "Signing $TARBALL with key $KEYID"
gpg --armor --detach-sign -u "$KEYID" "$TARBALL"

SIGFILE="$TARBALL.asc"
if [[ ! -f "$SIGFILE" ]]; then
  echo "Signature failed to produce $SIGFILE"
  exit 1
fi

echo "Uploading signature to GitHub release $RELEASE_TAG"
gh release upload "$RELEASE_TAG" "$SIGFILE" --clobber

echo "Signature uploaded: $SIGFILE"
