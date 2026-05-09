#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COQ_DIR="$ROOT/coq"
ART_DIR="$ROOT/artifacts/proof_gate"
mkdir -p "$ART_DIR"

{
  echo "proof_gate_started=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "repo=$ROOT"
  echo "coq_dir=$COQ_DIR"
} > "$ART_DIR/metadata.txt"

cd "$ROOT"

echo "[proof] clean rebuild"
make -C "$COQ_DIR" clean > "$ART_DIR/make_clean.log" 2>&1
make -C "$COQ_DIR" -j"$(nproc)" > "$ART_DIR/make_build.log" 2>&1

echo "[proof] zero Admitted gate"
# Use ^\s*Admitted\. to match only actual proof-hole tactics, not comments that
# say "Zero Admitted." (e.g., (* ... zero Admitted. *)) which are status notes.
admitted_count=$(grep -Rns --include='*.v' '^\s*Admitted\.' "$COQ_DIR" | grep -v patches | wc -l || true)
echo "admitted_count=$admitted_count" | tee "$ART_DIR/admitted_count.txt"
if [[ "$admitted_count" != "0" ]]; then
  grep -Rns --include='*.v' '^\s*Admitted\.' "$COQ_DIR" | grep -v patches > "$ART_DIR/admitted_hits.txt" || true
  echo "FAIL: found Admitted proofs"
  exit 1
fi

echo "[proof] coqchk reproducibility gate"
# Build the -R/-Q load-path arguments from _CoqProject so the gate stays in
# sync with the project layout (kernel sources live under
# coq/kernel/{foundation,nfi,mu_calculus,...}, all mapped to logical
# namespace Kernel; see _CoqProject for the canonical mapping).
COQCHK_LOADPATH=$(awk '/^-(R|Q)[ \t]/ {print $1, $2, $3}' "$COQ_DIR/_CoqProject" | tr '\n' ' ')
(
  cd "$COQ_DIR"
  coqchk $COQCHK_LOADPATH Kernel.Kernel Kernel.KernelTM Kernel.KernelThiele
) > "$ART_DIR/coqchk_kernel.log" 2>&1
(
  cd "$COQ_DIR"
  coqchk $COQCHK_LOADPATH Kernel.PythonBisimulation Kernel.HardwareBisimulation Kernel.ThreeLayerIsomorphism
) > "$ART_DIR/coqchk_bisim.log" 2>&1
(
  cd "$COQ_DIR"
  coqchk $COQCHK_LOADPATH Kernel.VMState Kernel.VMStep Kernel.PythonBisimulation
) > "$ART_DIR/coqchk_bridge.log" 2>&1

sha256sum "$ART_DIR"/*.log "$ART_DIR"/*.txt > "$ART_DIR/checksums.sha256"

echo "proof_gate_finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$ART_DIR/metadata.txt"
echo "[proof] PASS"
