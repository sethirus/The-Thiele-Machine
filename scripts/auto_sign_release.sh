#!/usr/bin/env bash
set -euo pipefail

################################################################################
# auto_sign_release.sh
#
# Interactive, environment-robust helper to create a GPG-signed git tag for a
# release and push it to origin. Prompts for GPG key id and passphrase; supports
# loopback pinentry fallback and can upload the public key to GitHub via gh CLI.
#
# Security: passphrase is written only to a temporary file with 600 perms and
# removed (shredded if available) on exit. The private key never leaves your
# machine. This script will ask before modifying gnupg config.
################################################################################

TAG_DEFAULT="v1.0.2"
COMMIT_DEFAULT="78cfa07b758bede75dc2a8938509dffe3700101a"

usage() {
  cat <<EOF
Usage: $0 [-k KEYID] [-t TAG] [-c COMMIT]

Interactive signing helper. Prompts for GPG passphrase; creates a signed
git tag and pushes it to origin. Optionally uploads the public key to GitHub
if 'gh' is available and authenticated.

Options:
  -k KEYID   GPG key id/fingerprint (optional; will pick first secret key if omitted)
  -t TAG     Tag name to sign (default: ${TAG_DEFAULT})
  -c COMMIT  Commit SHA to tag (default: ${COMMIT_DEFAULT})
  -h         Show this help
EOF
}

KEYID=""
TAG="$TAG_DEFAULT"
COMMIT="$COMMIT_DEFAULT"

while getopts "k:t:c:h" opt; do
  case ${opt} in
    k) KEYID=${OPTARG} ;;
    t) TAG=${OPTARG} ;;
    c) COMMIT=${OPTARG} ;;
    h) usage; exit 0 ;;
    *) usage; exit 1 ;;
  esac
done

command -v git >/dev/null 2>&1 || { echo "git is required" >&2; exit 1; }
command -v gpg >/dev/null 2>&1 || { echo "gpg is required" >&2; exit 1; }

if [[ -z "$KEYID" ]]; then
  # try to pick first secret key fingerprint
  KEYID=$(gpg --list-secret-keys --with-colons 2>/dev/null | awk -F: '/^sec/ {print $5; exit}') || true
  if [[ -z "$KEYID" ]]; then
    echo "No secret GPG keys found. Please create or import a key first: gpg --full-generate-key" >&2
    exit 1
  fi
  # reduce to long key id if fingerprint found
  if [[ ${#KEYID} -gt 16 ]]; then
    KEYID=${KEYID: -16}
  fi
fi

echo "Using GPG key id: $KEYID"

read -s -p "Enter GPG passphrase (will not be echoed): " PASSPHRASE
echo
if [[ -z "$PASSPHRASE" ]]; then
  echo "Empty passphrase provided; aborting." >&2
  exit 1
fi

# Prepare secure temporary environment
TMPDIR=$(mktemp -d 2>/dev/null || mktemp -d -t thiele-sign)
PASSFILE="$TMPDIR/gpass"
WRAPPER="$TMPDIR/gpg-wrapper"

cleanup() {
  # Try to shred the passfile if shred exists
  if command -v shred >/dev/null 2>&1; then
    shred -u "$PASSFILE" 2>/dev/null || rm -f "$PASSFILE" 2>/dev/null || true
  else
    rm -f "$PASSFILE" 2>/dev/null || true
  fi
  rm -f "$WRAPPER" 2>/dev/null || true
  rm -rf "$TMPDIR" 2>/dev/null || true
}
trap cleanup EXIT

# write passphrase to file with strict perms
printf '%s' "$PASSPHRASE" > "$PASSFILE"
chmod 600 "$PASSFILE"

# generate wrapper that forwards arguments to underlying gpg with loopback
GPG_BIN=$(command -v gpg || command -v gpg2)
cat > "$WRAPPER" <<EOF
#!/usr/bin/env bash
exec "$GPG_BIN" --batch --yes --pinentry-mode loopback --passphrase-file '$PASSFILE' "$@"
EOF
chmod 700 "$WRAPPER"

# ensure gpg can prompt on terminal
if [[ -t 0 ]]; then
  export GPG_TTY=$(tty)
fi

echo "Fetching tags from origin..."
git fetch origin --tags

echo "Attempting to create a signed git tag ($TAG -> $COMMIT) using key $KEYID"
set +e
git -c gpg.program="$WRAPPER" tag -s -u "$KEYID" -f "$TAG" -m "Thiele Machine $TAG - signed release" "$COMMIT"
RET=$?
set -e

if [[ $RET -eq 0 ]]; then
  echo "Signed tag $TAG created locally. Pushing to origin..."
  git push --force origin refs/tags/$TAG
  echo "Signed tag pushed. Verify with: git tag -v $TAG"
else
  echo "Signed tag creation failed (git tag -s returned $RET). Trying fallback: configure git to use wrapper program and retry." >&2
  # fallback using explicit git config invocation
  set +e
  git -c gpg.program="$WRAPPER" tag -s -u "$KEYID" -f "$TAG" -m "Thiele Machine $TAG - signed release" "$COMMIT"
  RET2=$?
  set -e
  if [[ $RET2 -eq 0 ]]; then
    echo "Fallback signing succeeded. Pushing..."
    git push --force origin refs/tags/$TAG
    echo "Signed tag pushed. Verify with: git tag -v $TAG"
  else
    echo "Annotated tag signing failed. Creating unsigned annotated tag and uploading a detached signature instead." >&2
    # Create annotated tag (unsigned) then create a detached signature of the tag contents
    git tag -a -f "$TAG" -m "Thiele Machine $TAG - annotated tag (unsigned)" "$COMMIT"
    # get the tag object SHA
    TAGOBJ=$(git rev-parse "$TAG")
    echo "Signing tag object content and saving detached signature..."
    git cat-file -p "$TAGOBJ" | "$GPG_BIN" --armor --detach-sign -u "$KEYID" --batch --pinentry-mode loopback --passphrase-file "$PASSFILE" -o "$TMPDIR/${TAG}.tag.sig"
    echo "Detached signature saved: $TMPDIR/${TAG}.tag.sig"
    echo "Pushing annotated tag to origin..."
    git push --force origin refs/tags/$TAG
    echo "You should upload the generated detached signature to the GitHub release assets: $TMPDIR/${TAG}.tag.sig";
    if command -v gh >/dev/null 2>&1; then
      read -p "gh CLI detected. Upload detached signature to GitHub release v1.0.2? [y/N]: " reply
      if [[ "$reply" =~ ^[Yy]$ ]]; then
        gh release upload "$TAG" "$TMPDIR/${TAG}.tag.sig" --clobber
        echo "Signature uploaded to release assets."
      else
        echo "Detached signature saved locally. Upload it manually to the release assets.";
      fi
    else
      echo "gh CLI not found: please upload the detached signature to the release assets manually.";
    fi
  fi
fi

echo "Optionally upload public key to GitHub (required for GitHub to mark tag Verified)."
if command -v gh >/dev/null 2>&1; then
  read -p "Upload public key to GitHub for the current user? [y/N]: " UP
  if [[ "$UP" =~ ^[Yy]$ ]]; then
    echo "Uploading public key to GitHub via gh..."
    PUB=$(gpg --armor --export "$KEYID")
    # use gh api to post
    echo "$PUB" | gh api --method POST /user/gpg_keys -f armored_public_key@- >/dev/null
    echo "Public key uploaded to GitHub account associated with gh CLI.";
  else
    echo "Skipping public key upload. Remember to add public key to GitHub manually using GPG_PUBLIC_KEY.asc in the repo.";
  fi
else
  echo "gh CLI not available; please add public key manually to your GitHub account.";
fi

echo "Done. Remember to verify: git tag -v $TAG and check the GitHub release page for Verified status.";
