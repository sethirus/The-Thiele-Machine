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
admitted_count=$(grep -Rns --include='*.v' 'Admitted\.' "$COQ_DIR" | grep -v patches | wc -l || true)
echo "admitted_count=$admitted_count" | tee "$ART_DIR/admitted_count.txt"
if [[ "$admitted_count" != "0" ]]; then
  grep -Rns --include='*.v' 'Admitted\.' "$COQ_DIR" | grep -v patches > "$ART_DIR/admitted_hits.txt" || true
  echo "FAIL: found Admitted proofs"
  exit 1
fi

echo "[proof] coqchk reproducibility gate"
(
  cd "$COQ_DIR"
  coqchk -R kernel Kernel Kernel.Kernel Kernel.KernelTM Kernel.KernelThiele
) > "$ART_DIR/coqchk_kernel.log" 2>&1
(
  cd "$COQ_DIR"
  coqchk -R kernel Kernel Kernel.PythonBisimulation Kernel.HardwareBisimulation Kernel.ThreeLayerIsomorphism
) > "$ART_DIR/coqchk_bisim.log" 2>&1
(
  cd "$COQ_DIR"
  coqchk -R kernel Kernel -R bridge Bridge Kernel.VMState Kernel.VMStep Bridge.PythonMuLedgerBisimulation
) > "$ART_DIR/coqchk_bridge.log" 2>&1

sha256sum "$ART_DIR"/*.log "$ART_DIR"/*.txt > "$ART_DIR/checksums.sha256"

echo "proof_gate_finished=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$ART_DIR/metadata.txt"
echo "[proof] PASS"
