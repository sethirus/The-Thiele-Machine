#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COQ_DIR="${ROOT_DIR}/coq"

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
  -R modular_proofs ThieleMachine.Modular_Proofs \
  modular_proofs/TM_Basics.v

run_quick "modular_proofs/EncodingBounds.v" \
  -R modular_proofs ThieleMachine.Modular_Proofs \
  modular_proofs/EncodingBounds.v

run_quick "modular_proofs/Encoding.v" \
  -R modular_proofs ThieleMachine.Modular_Proofs \
  modular_proofs/Encoding.v

run_quick "modular_proofs/Simulation.v" \
  -R modular_proofs ThieleMachine.Modular_Proofs \
  modular_proofs/Simulation.v

# Build the universal TM helpers so legacy proofs have compiled dependencies.
run_quick "thieleuniversal/coqproofs/TM.v" \
  -R thieleuniversal/coqproofs ThieleUniversal \
  thieleuniversal/coqproofs/TM.v

run_quick "thieleuniversal/coqproofs/CPU.v" \
  -R thieleuniversal/coqproofs ThieleUniversal \
  thieleuniversal/coqproofs/CPU.v

run_quick "thieleuniversal/coqproofs/UTM_Encode.v" \
  -R thieleuniversal/coqproofs ThieleUniversal \
  thieleuniversal/coqproofs/UTM_Encode.v

run_quick "thieleuniversal/coqproofs/UTM_Rules.v" \
  -R modular_proofs ThieleMachine.Modular_Proofs \
  -R thieleuniversal/coqproofs ThieleUniversal \
  thieleuniversal/coqproofs/UTM_Rules.v

run_quick "thieleuniversal/coqproofs/UTM_Program.v" \
  -R thieleuniversal/coqproofs ThieleUniversal \
  thieleuniversal/coqproofs/UTM_Program.v

run_quick "thieleuniversal/coqproofs/UTM_CoreLemmas.v" \
  -R thieleuniversal/coqproofs ThieleUniversal \
  thieleuniversal/coqproofs/UTM_CoreLemmas.v

# With modular and universal artefacts available, try the legacy witness.
set +e
run_quick "thielemachine/coqproofs/EncodingBridge.v" \
  -R modular_proofs ThieleMachine.Modular_Proofs \
  -R thieleuniversal/coqproofs ThieleUniversal \
  -R thielemachine/coqproofs ThieleMachine \
  thielemachine/coqproofs/EncodingBridge.v

run_quick "thielemachine/coqproofs/ThieleMachine.v" \
  -R modular_proofs ThieleMachine.Modular_Proofs \
  -R thieleuniversal/coqproofs ThieleUniversal \
  -R thielemachine/coqproofs ThieleMachine \
  thielemachine/coqproofs/ThieleMachine.v

run_quick "thielemachine/coqproofs/Simulation.v" \
  -R modular_proofs ThieleMachine.Modular_Proofs \
  -R thieleuniversal/coqproofs ThieleUniversal \
  -R thielemachine/coqproofs ThieleMachine \
  thielemachine/coqproofs/Simulation.v
if [ "$?" -ne 0 ]; then
  echo "[quick-coq] skipped thielemachine/coqproofs/Simulation.v (additional dependencies required)"
fi
set -e
