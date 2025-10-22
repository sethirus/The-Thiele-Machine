#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OPAM_ROOT="${REPO_ROOT}/.opam"
SWITCH_NAME="thiele-coq-8.18"
ENV_FILE="${REPO_ROOT}/.coq-env"

if ! command -v opam >/dev/null 2>&1; then
  echo "Error: opam is required to bootstrap the Coq toolchain." >&2
  echo "Install opam (https://opam.ocaml.org) and re-run this script." >&2
  exit 1
fi

export OPAMROOT="${OPAM_ROOT}"

if [ ! -d "${OPAM_ROOT}" ]; then
  opam init --bare --disable-sandboxing --yes
fi

if ! opam switch list --short | grep -Fx "${SWITCH_NAME}" >/dev/null 2>&1; then
  opam switch create "${SWITCH_NAME}" ocaml-base-compiler.4.14.1 --yes
fi

# Ensure environment is ready for installs
opam switch set "${SWITCH_NAME}" --yes >/dev/null

# Update repositories and install Coq
opam update --yes >/dev/null
opam install --yes coq.8.18.0

# Persist an activation script for downstream commands
opam env --root "${OPAM_ROOT}" --switch "${SWITCH_NAME}" > "${ENV_FILE}".tmp
mv "${ENV_FILE}".tmp "${ENV_FILE}"

cat <<MSG
Coq toolchain ready.
To activate the environment in the current shell run:
  source "${ENV_FILE}"
MSG
