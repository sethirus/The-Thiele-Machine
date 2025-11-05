#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COQ_DIR="${ROOT_DIR}/coq"
MODULAR_DIR="${COQ_DIR}/modular_proofs"
UNIVERSAL_DIR="${COQ_DIR}/thieleuniversal/coqproofs"
LEGACY_DIR="${COQ_DIR}/thielemachine/coqproofs"

MODULAR_FLAGS=(-Q "${MODULAR_DIR}" ThieleMachine.Modular_Proofs)
UNIVERSAL_FLAGS=(-Q "${UNIVERSAL_DIR}" ThieleUniversal)
LEGACY_FLAGS=(-Q "${LEGACY_DIR}" ThieleMachine)

if coqc -help 2>&1 | grep -q -- "-vio"; then
  COQ_FAST_FLAG="-vio"
else
  COQ_FAST_FLAG="-quick"
fi

run_quick() {
  local target="$1"
  shift
  echo "[quick-coq] coqc ${COQ_FAST_FLAG} $target"
  if coqc "${COQ_FAST_FLAG}" "$@"; then
    return 0
  fi
  if [ "${COQ_FAST_FLAG}" != "-quick" ]; then
    echo "[quick-coq] retrying $target with -quick"
    if coqc -quick "$@"; then
      return 0
    fi
  fi
  echo "[quick-coq] retrying $target with -vos"
  if coqc -vos "$@"; then
    return 0
  fi
  echo "[quick-coq] retrying $target with full coqc"
  coqc "$@"
}

cd "${COQ_DIR}"

run_quick "modular_proofs/TM_Basics.v" \
  "${MODULAR_FLAGS[@]}" \
  "${MODULAR_DIR}/TM_Basics.v"

run_quick "modular_proofs/EncodingBounds.v" \
  "${MODULAR_FLAGS[@]}" \
  "${MODULAR_DIR}/EncodingBounds.v"

run_quick "modular_proofs/Encoding.v" \
  "${MODULAR_FLAGS[@]}" \
  "${MODULAR_DIR}/Encoding.v"

run_quick "modular_proofs/Simulation.v" \
  "${MODULAR_FLAGS[@]}" \
  "${MODULAR_DIR}/Simulation.v"

# Build the universal TM helpers so legacy proofs have compiled dependencies.
run_quick "thieleuniversal/coqproofs/TM.v" \
  "${UNIVERSAL_FLAGS[@]}" \
  "${UNIVERSAL_DIR}/TM.v"

run_quick "thieleuniversal/coqproofs/CPU.v" \
  "${UNIVERSAL_FLAGS[@]}" \
  "${UNIVERSAL_DIR}/CPU.v"

run_quick "thieleuniversal/coqproofs/UTM_Encode.v" \
  "${UNIVERSAL_FLAGS[@]}" \
  "${UNIVERSAL_DIR}/UTM_Encode.v"

run_quick "thieleuniversal/coqproofs/UTM_Rules.v" \
  "${MODULAR_FLAGS[@]}" \
  "${UNIVERSAL_FLAGS[@]}" \
  "${UNIVERSAL_DIR}/UTM_Rules.v"

run_quick "thieleuniversal/coqproofs/UTM_Program.v" \
  "${UNIVERSAL_FLAGS[@]}" \
  "${UNIVERSAL_DIR}/UTM_Program.v"

run_quick "thieleuniversal/coqproofs/UTM_CoreLemmas.v" \
  "${UNIVERSAL_FLAGS[@]}" \
  "${UNIVERSAL_DIR}/UTM_CoreLemmas.v"

run_quick "thieleuniversal/coqproofs/ThieleUniversal.v" \
  "${UNIVERSAL_FLAGS[@]}" \
  "${UNIVERSAL_DIR}/ThieleUniversal.v"

# With modular and universal artefacts available, try the legacy witness.
set +e
run_quick "thielemachine/coqproofs/EncodingBridge.v" \
  "${MODULAR_FLAGS[@]}" \
  "${UNIVERSAL_FLAGS[@]}" \
  "${LEGACY_FLAGS[@]}" \
  "${LEGACY_DIR}/EncodingBridge.v"

run_quick "thielemachine/coqproofs/ThieleMachine.v" \
  "${MODULAR_FLAGS[@]}" \
  "${UNIVERSAL_FLAGS[@]}" \
  "${LEGACY_FLAGS[@]}" \
  "${LEGACY_DIR}/ThieleMachine.v"

run_quick "thielemachine/coqproofs/Simulation.v" \
  "${MODULAR_FLAGS[@]}" \
  "${UNIVERSAL_FLAGS[@]}" \
  "${LEGACY_FLAGS[@]}" \
  "${LEGACY_DIR}/Simulation.v"
if [ "$?" -ne 0 ]; then
  echo "[quick-coq] skipped thielemachine/coqproofs/Simulation.v (additional dependencies required)"
fi
set -e
