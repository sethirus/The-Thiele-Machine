#!/usr/bin/env bash
# Build MetaCoq 1.2.1+8.18 (utils, common, template-coq) from pinned,
# checksum-verified source against the installed Coq 8.18 and install it.
# The vendored L extraction tactics (Undecidability.L.Tactics) need it.
# Usage: scripts/install_metacoq.sh [work-dir]   (default: a temporary dir)
# Build dependencies (Ubuntu 24.04):
#   sudo apt-get install -y libcoq-core-ocaml-dev libcoq-equations libstdlib-shims-ocaml-dev
set -Eeuo pipefail

TAG=v1.2.1-8.18
SHA256=2b5057265344e661371591eaa5d94da9cb45ce4e88867a6cce517f478395a9fe
WORK="${1:-$(mktemp -d)}"
SRC="$WORK/metarocq-1.2.1-8.18"

coqc --version | head -n1 | grep -q "8.18" || { echo "install_metacoq: Coq 8.18 required" >&2; exit 1; }

if [[ ! -f "$SRC/template-coq/theories/All.vo" ]]; then
  mkdir -p "$WORK"
  curl -sSL -o "$WORK/metacoq.tar.gz" \
    "https://github.com/MetaRocq/metarocq/archive/refs/tags/${TAG}.tar.gz"
  echo "${SHA256}  $WORK/metacoq.tar.gz" | sha256sum -c -
  tar -xzf "$WORK/metacoq.tar.gz" -C "$WORK"
  (cd "$SRC" && ./configure.sh)
fi

SUDO=""
[[ $(id -u) -eq 0 ]] || SUDO=sudo
# Each part compiles against the installed previous parts, so build and
# install in order. On a rebuild with outputs present, make only installs.
for part in utils common template-coq; do
  make -C "$SRC/$part" -j"${JOBS:-4}"
  $SUDO make -C "$SRC/$part" install
done
echo "install_metacoq: MetaCoq Template ${TAG} installed"
