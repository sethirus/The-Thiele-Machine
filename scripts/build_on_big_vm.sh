# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env bash
# Usage: run this on a machine with >= 32GB RAM (recommended)
# Example: ssh into the VM and run: bash build_on_big_vm.sh
set -euxo pipefail

# This script installs opam and Coq 8.20.1 (in an opam switch), then
# builds the Coq project (thieleuniversal first, then the rest) and runs
# the flagship auditor. Designed for a large, ephemeral build VM.

# 1. Install system dependencies (Debian/Ubuntu)
sudo apt-get update -y
sudo apt-get install -y build-essential m4 bubblewrap pkg-config git curl ca-certificates

# 2. Install opam if missing
if ! command -v opam >/dev/null 2>&1; then
  sudo apt-get install -y opam
fi

# 3. Initialize opam (non-interactive)
opam init --disable-sandboxing -y

eval "$(opam env)"

# 4. Create a switch for the correct OCaml & Coq versions
opam switch create coq-8.20.1 ocaml-base-compiler.4.14.1 -y || true
eval "$(opam env --switch=coq-8.20.1)"

# 5. Install Coq and essentials
opam install -y coq.8.20.1 dune zarith ocamlfind

# 6. Fetch project sources if not already present; assume you're in repo root.
# (Optional) git clone <repo> .

# 7. Build the heavy universal module first single-threaded to limit peak memory
export COQEXTRAFLAGS='-native-compiler no'
mkdir -p build-logs
echo "Building ThieleUniversal (single-threaded) ..."
make -C coq thieleuniversal/coqproofs/ThieleUniversal.vo COQEXTRAFLAGS="$COQEXTRAFLAGS" 2>&1 | tee build-logs/coq-thieleuniversal.log

# 8. Build remaining Coq files (single-threaded / no native compile)
echo "Building the rest of the Coq project (no native compiler) ..."
make -C coq -j1 COQEXTRAFLAGS="$COQEXTRAFLAGS" 2>&1 | tee build-logs/coq-make.log

# 9. Run the flagship auditor (n=80)
./scripts/verify_flagship_theorem.sh --enforce --force-coq --n 80 --seed 0 | tee build-logs/flagship-audit.log

# 10. Summarize artifacts
echo "Build logs are in build-logs/ and receipts/; compressing into artifacts.tgz"
tar -czf artifacts.tgz build-logs receipts coq/**/*.vo || true

# 11. Done
echo "Build complete. artifacts.tgz created (inspect build-logs for details)."
