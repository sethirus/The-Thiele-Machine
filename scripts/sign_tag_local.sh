#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<EOF
Usage: $0 -k KEYID -t TAG -c COMMIT

Signs TAG with GPG KEYID at COMMIT and pushes the signed tag to origin.
This script runs locally and will prompt you for your GPG passphrase.

Options:
  -k KEYID    Long or short GPG key id (e.g. 0xABCDEF1234567890 or last 16 digits)
  -t TAG      Tag name to sign (e.g. v1.0.3)
  -c COMMIT   Commit SHA to tag (e.g. 78cfa07...)
  -h          Display this help
EOF
}

KEYID=""
TAG=""
COMMIT=""

while getopts "k:t:c:h" opt; do
  case ${opt} in
    k) KEYID=${OPTARG} ;;
    t) TAG=${OPTARG} ;;
    c) COMMIT=${OPTARG} ;;
    h) usage; exit 0 ;;
    *) usage; exit 1 ;;
  esac
done

if [[ -z "$KEYID" || -z "$TAG" || -z "$COMMIT" ]]; then
  usage
  exit 1
fi

echo "Using GPG key: $KEYID"

echo "Ensure your GPG agent is running and that the key is available. If prompted, enter your passphrase." 
export GPG_TTY=$(tty)

echo "Fetching latest tags from origin..."
git fetch origin --tags

echo "Attempting to create signed tag $TAG at $COMMIT using key $KEYID"
set +e
git tag -s -u "$KEYID" -f "$TAG" -m "Thiele Machine $TAG - signed release" "$COMMIT"
RET=$?
set -e

if [[ $RET -ne 0 ]]; then
  echo "Initial signing failed. Attempting fallback using pinentry loopback..."
  echo "Note: loopback requires 'allow-loopback-pinentry' in your gpg-agent configuration or running 'gpg --pinentry-mode loopback' directly."
  git -c gpg.program="gpg --pinentry-mode loopback" tag -s -u "$KEYID" -f "$TAG" -m "Thiele Machine $TAG - signed release" "$COMMIT"
fi

echo "Pushing signed tag to origin (force update)..."
git push --force origin refs/tags/$TAG

echo "Signed tag pushed. Verify locally with: git tag -v $TAG"
echo "On GitHub, ensure you have uploaded the corresponding public key to your account so the tag displays "Verified"."
