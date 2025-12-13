#!/usr/bin/env bash
set -euo pipefail

# Foundry pipeline: Coq -> OCaml IR -> Python + Verilog -> compile -> pytest.
# This runs *real* toolchain steps and fails fast on any mismatch.

SCRIPT_PATH="$(readlink -f "${BASH_SOURCE[0]}")"
ROOT="$(cd "$(dirname "$SCRIPT_PATH")/.." && pwd)"

phase() {
  # Required visualization phases:
  # INIT → DISCOVER → CLASSIFY → DECOMPOSE → EXECUTE → MERGE → VERIFY → SUCCESS
  printf "\n[%s] %s\n" "$1" "$2"
}

die() {
  echo "error: $*" >&2
  exit 1
}

cd "$ROOT"

phase INIT "workspace=$ROOT"
mkdir -p build thielecpu/hardware thielecpu/generated

phase DISCOVER "checking toolchain availability"
command -v rocq >/dev/null || die "rocq not found on PATH"
command -v iverilog >/dev/null || die "iverilog not found on PATH"
command -v python3 >/dev/null || die "python3 not found on PATH"

phase CLASSIFY "building Coq extraction entrypoint (proof of compilation)"
make -C coq Extraction.vo

phase DECOMPOSE "verifying extracted OCaml IR exists"
IR="$ROOT/build/thiele_core.ml"
[ -f "$IR" ] || die "missing extracted IR: $IR"

phase DECOMPOSE "building Coq-extracted semantics runner (OCaml)"
command -v ocamlc >/dev/null || die "ocamlc not found on PATH"
ocamlc -I "$ROOT/build" -o "$ROOT/build/extracted_vm_runner" \
  "$ROOT/build/thiele_core.mli" \
  "$ROOT/build/thiele_core.ml" \
  "$ROOT/tools/extracted_vm_runner.ml" \
  >/dev/null

phase EXECUTE "generating Python + Verilog from extracted IR"
python3 scripts/forge.py \
  --input "$IR" \
  --out-python "$ROOT/thielecpu/generated/generated_core.py" \
  --out-verilog "$ROOT/thielecpu/hardware/generated_opcodes.vh"

phase MERGE "sanity importing generated Python"
python3 -c "from thielecpu.generated import generated_core as g; g.sanity_check(); print(len(g.COQ_INSTRUCTION_TAGS))" \
  >/dev/null

phase VERIFY "compiling real RTL (thiele_cpu + testbench)"
pushd "$ROOT/thielecpu/hardware" >/dev/null
iverilog -g2012 -o "$ROOT/build/thiele_cpu_tb.out" \
  thiele_cpu.v \
  thiele_cpu_tb.v \
  mu_alu.v \
  mu_core.v
popd >/dev/null

phase VERIFY "running real RTL simulation (thiele_cpu_tb)"
vvp "$ROOT/build/thiele_cpu_tb.out" >/dev/null

phase VERIFY "running pytest gate"
pytest -q \
  tests/test_foundry_generated_surface.py \
  tests/test_opcode_alignment.py \
  tests/test_extracted_vm_runner.py

phase VERIFY "running Python↔Verilog behavioral smoke test"
pytest -q tests/adversarial_fuzzing.py -k manual_simple_program

phase SUCCESS "Foundry pipeline green"
