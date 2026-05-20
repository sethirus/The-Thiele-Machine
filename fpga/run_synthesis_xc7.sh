#!/usr/bin/env bash
# ============================================================================
# Thiele CPU — Xilinx Kintex-7 K325T (ffg900) open-source synthesis driver.
# ============================================================================
#
# Required tools:
#   - yosys             (apt: yosys; provides synth_xilinx -family xc7)
#   - nextpnr-xilinx    (built from github.com/openXC7/nextpnr-xilinx)
#   - bbasm             (built alongside nextpnr-xilinx)
#   - xc7frames2bit     (built from github.com/SymbiFlow/prjxray tools)
#   - prjxray-db        (kintex7 portion; submodule of nextpnr-xilinx)
#   - python3 with: simplejson, intervaltree, fasm
#
# Inputs:
#   - thielecpu/hardware/rtl/{RegFile.v, thiele_cpu_kami.v,
#                             thiele_cpu_top_min.v, thiele_cpu_top_genesys2.v}
#   - thielecpu/hardware/rtl/synth_xc7.ys
#   - fpga/thiele_genesys2.xdc
#
# Chipdb (xc7k325tffg900-2.bin) is generated at run-time via bbaexport +
# bbasm — too large (~90MB) to commit per part.
#
# Why K325T with `-nodsp`: yosys's DSP48E1 inference for
# column_contractive_check_witness maps onto more DSP slices than K325T's 840
# (and the wider operand widths force chained DSPs that slow openXC7's
# nextpnr-xilinx placer to 1-2+ hours, sometimes timing out). Rather than
# escalating to a bigger part (K420T has no parent-dir tilegrid in openXC7's
# prjxray-db; K480T fits but its placer takes 1-2+ hours and sometimes
# doesn't finish at all on the open-source nextpnr-xilinx), we use two
# complementary changes:
#   (1) instr_chsh_lassert's witness check is implemented in Kami as a
#       23-phase FSM (`chsh_lassert_fsm` rule in
#       coq/kami_hw/ThieleCPUCore.v) that time-shares one 384×384 SignUU
#       multiplier across the 22 wide multiplications it needs, so only one
#       wide multiply is live per cycle (Coq spec is still single-step;
#       multi-cycle execution is a Kami-implementation detail invisible to
#       the spec — same pattern as instr_lassert).
#   (2) DSP inference is disabled in synth_xc7.ys (`-nodsp`) so yosys maps
#       the multiplier to LUTs.
# The result fits in ~151K LUT6 (~74% of K325T's 203K LUT6 budget) and the
# placer finishes in ~10 min. DSP vs LUT is a silicon-utilisation choice,
# not a correctness one; the proof chain (Coq → OCaml → Bluespec → Verilog)
# is identical either way. We accept the LUT cost in exchange for an
# open-source flow that finishes in CI.
#
# Outputs in build/:
#   - thiele_xc7k325t.json     (yosys post-synthesis netlist)
#   - thiele_xc7k325t.fasm     (placed-and-routed FPGA assembly)
#   - thiele_xc7k325t.frames   (frame-level bit positions)
#   - thiele_xc7k325t.bit      (binary bitstream)
#
# Usage:
#   bash fpga/run_synthesis_xc7.sh
#
# Environment overrides:
#   NEXTPNR_XILINX  — path to nextpnr-xilinx binary
#   NEXTPNR_DIR     — root of the built openXC7 nextpnr-xilinx tree (needs
#                     xilinx/python/bbaexport.py + build/bbasm)
#   BBASM           — path to the bbasm binary
#   XC7FRAMES2BIT   — path to xc7frames2bit binary
#   PRJXRAY_DIR     — path to a prjxray checkout containing utils/fasm2frames.py
#   PRJXRAY_DB      — path to the kintex7 prjxray-db root

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
RTL_DIR="${ROOT}/thielecpu/hardware/rtl"
BUILD_DIR="${ROOT}/build"
PART="xc7k325tffg900-2"
TOP="thiele_cpu_top_genesys2"
JSON="${BUILD_DIR}/thiele_xc7k325t.json"
FASM="${BUILD_DIR}/thiele_xc7k325t.fasm"
FRAMES="${BUILD_DIR}/thiele_xc7k325t.frames"
BIT="${BUILD_DIR}/thiele_xc7k325t.bit"
CHIPDB="${BUILD_DIR}/${PART}.bin"
XDC="${ROOT}/fpga/thiele_genesys2.xdc"

NEXTPNR_XILINX="${NEXTPNR_XILINX:-nextpnr-xilinx}"
NEXTPNR_DIR="${NEXTPNR_DIR:-/opt/nextpnr-xilinx}"
BBASM="${BBASM:-${NEXTPNR_DIR}/bbasm}"
XC7FRAMES2BIT="${XC7FRAMES2BIT:-xc7frames2bit}"
PRJXRAY_DIR="${PRJXRAY_DIR:-/opt/prjxray}"
PRJXRAY_DB="${PRJXRAY_DB:-${NEXTPNR_DIR}/xilinx/external/prjxray-db/kintex7}"

mkdir -p "${BUILD_DIR}"

echo "=== [1/5] Generate chipdb for ${PART} (bbaexport + bbasm) ==="
if [ ! -s "${CHIPDB}" ]; then
    ( cd "${NEXTPNR_DIR}" && \
      python3 xilinx/python/bbaexport.py --device "${PART}" --bba "${BUILD_DIR}/${PART}.bba" && \
      "${BBASM}" -l "${BUILD_DIR}/${PART}.bba" "${CHIPDB}" )
    echo "    chipdb: ${CHIPDB} ($(wc -c < "${CHIPDB}") bytes)"
else
    echo "    chipdb already present, skipping regeneration"
fi

echo "=== [2/5] yosys synth_xilinx -family xc7 (top=${TOP}) ==="
( cd "${RTL_DIR}" && yosys -ql "${BUILD_DIR}/yosys_xc7.log" synth_xc7.ys )
echo "    netlist: ${JSON}"

echo "=== [3/5] nextpnr-xilinx place-and-route (${PART}) ==="
"${NEXTPNR_XILINX}" \
    --chipdb "${CHIPDB}" \
    --xdc "${XDC}" \
    --json "${JSON}" \
    --fasm "${FASM}" \
    --timing-allow-fail \
    2>&1 | tee "${BUILD_DIR}/nextpnr_xc7.log"
echo "    fasm:   ${FASM}"

echo "=== [4/5] fasm2frames (Project X-Ray, kintex7) ==="
PYTHONPATH="${PRJXRAY_DIR}:${PYTHONPATH:-}" python3 \
    "${PRJXRAY_DIR}/utils/fasm2frames.py" \
    --part "${PART}" \
    --db-root "${PRJXRAY_DB}" \
    "${FASM}" > "${FRAMES}"
echo "    frames: ${FRAMES}"

echo "=== [5/5] xc7frames2bit (Project X-Ray) ==="
"${XC7FRAMES2BIT}" \
    --part_file "${PRJXRAY_DB}/${PART}/part.yaml" \
    --part_name "${PART}" \
    --frm_file "${FRAMES}" \
    --output_file "${BIT}"

echo
echo "✓ Bitstream: ${BIT} ($(wc -c < "${BIT}") bytes)"
echo "  Program board: openFPGALoader --board genesys2 ${BIT}"
