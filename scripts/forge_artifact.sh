#!/usr/bin/env bash
set -euxo pipefail

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

# Ensure OCaml bytecode runtime has sufficient stack for extracted code
export OCAMLRUNPARAM="${OCAMLRUNPARAM:-l=64M}"

phase INIT "workspace=$ROOT"
mkdir -p build thielecpu/hardware thielecpu/generated

phase DISCOVER "checking toolchain availability"
command -v coqc >/dev/null || die "coqc not found on PATH"
command -v iverilog >/dev/null || die "iverilog not found on PATH"
command -v python3 >/dev/null || die "python3 not found on PATH"

phase CLASSIFY "building Coq extraction entrypoint (proof of compilation)"
make -C coq Extraction.vo

phase CLASSIFY "patching extracted Nat module for native int performance"
python3 scripts/patch_extracted_nat.py "$ROOT/build/thiele_core.ml"

phase CLASSIFY "running Inquisitor (Coq proof-smell audit)"
INQUISITOR_REPORT_PATH="$ROOT/artifacts/INQUISITOR_REPORT.md"
INQUISITOR_STRICT="${INQUISITOR_STRICT:-0}"
INQUISITOR_ARGS=(--coq-root coq --report "$INQUISITOR_REPORT_PATH")
if [ "$INQUISITOR_STRICT" = "1" ]; then
  INQUISITOR_ARGS+=(--strict)
fi
# Inquisitor findings are informational in the forge pipeline;
# the dedicated proof-audit CI job enforces strict compliance.
python3 scripts/inquisitor.py "${INQUISITOR_ARGS[@]}" || {
  echo "warning: Inquisitor reported findings (see $INQUISITOR_REPORT_PATH)" >&2
}

phase DECOMPOSE "verifying extracted OCaml IR exists"
IR="$ROOT/build/thiele_core.ml"
[ -f "$IR" ] || die "missing extracted IR: $IR"

phase DECOMPOSE "building Coq-extracted semantics runner (OCaml)"
command -v ocamlc >/dev/null || die "ocamlc not found on PATH"
command -v ocamlfind >/dev/null || die "ocamlfind not found on PATH"
ocamlfind ocamlc -I "$ROOT/build" -package str -linkpkg -o "$ROOT/build/extracted_vm_runner" \
  "$ROOT/build/thiele_core.mli" \
  "$ROOT/build/thiele_core.ml" \
  "$ROOT/build/extracted_vm_runner.ml" \
  >/dev/null

phase EXECUTE "generating Python from extracted IR"
python3 scripts/forge.py \
  --input "$IR" \
  --out-python "$ROOT/thielecpu/generated/generated_core.py"

phase EXECUTE "generating Python VM from Coq-extracted OCaml IR (forge_vm.py → thielecpu/vm.py)"
python3 scripts/forge_vm.py \
  --input "$IR" \
  --output "$ROOT/thielecpu/vm.py"

phase MERGE "sanity importing generated Python"
python3 -c "from thielecpu.generated import generated_core as g; g.sanity_check(); print(len(g.COQ_INSTRUCTION_TAGS))" \
  >/dev/null

phase VERIFY "compiling extracted RTL (thiele_cpu_kami + testbench)"
pushd "$ROOT/thielecpu/hardware" >/dev/null
iverilog -g2012 -I./rtl -o "$ROOT/build/thiele_cpu_tb.out" \
  rtl/thiele_cpu_kami.v \
  rtl/RegFile.v \
  testbench/thiele_cpu_kami_tb.v
popd >/dev/null

phase VERIFY "synthesizability check (yosys)"
command -v yosys >/dev/null || die "yosys not found on PATH"

cat > "$ROOT/synth_cpu.ys" << EOF
read_verilog -sv -DSYNTHESIS $ROOT/thielecpu/hardware/rtl/RegFile.v $ROOT/thielecpu/hardware/rtl/thiele_cpu_kami.v $ROOT/thielecpu/hardware/rtl/thiele_cpu_top.v
prep -top mkModule1
check
stat
EOF

yosys -q -s "$ROOT/synth_cpu.ys" >/dev/null

phase VERIFY "running real RTL regression"
python3 -m pytest -q tests/test_verilog_cosim.py --tb=line -x

phase VERIFY "running Verilator bridge regression"
THIELE_RTL_SIM=verilator python3 -m pytest -q \
  tests/test_chsh_verilator_hardware_bridge.py \
  tests/test_logic_stall_liveness.py --tb=line

phase VERIFY "running pytest gate"
pytest -q \
  tests/test_foundry_generated_surface.py \
  tests/test_opcode_alignment.py \
  tests/test_cross_layer_adversarial_fuzz.py
pytest -q tests/test_completeness_gate.py -k TestOCamlLayer

phase VERIFY "running Python↔Verilog behavioral smoke test"
pytest -q tests/test_cross_layer_bisimulation.py -k "bisim"

phase SUCCESS "Foundry pipeline green"
