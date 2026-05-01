#!/usr/bin/env bash
# ============================================================================
# Thiele CPU — Xilinx Artix-7 (xc7a35t) open-source synthesis driver.
# ============================================================================
#
# Required tools:
#   - yosys             (apt: yosys; provides synth_xilinx -family xc7)
#   - nextpnr-xilinx    (built from github.com/openXC7/nextpnr-xilinx)
#   - xc7frames2bit     (built from github.com/SymbiFlow/prjxray tools)
#   - prjxray-db        (artix7 portion; submodule of nextpnr-xilinx)
#   - python3 with: simplejson, intervaltree, fasm
#
# Inputs:
#   - thielecpu/hardware/rtl/{RegFile.v, thiele_cpu_kami.v, thiele_cpu_top_min.v}
#   - thielecpu/hardware/rtl/synth_xc7.ys
#   - fpga/thiele_arty35.xdc
#   - fpga/chipdb/xc7a35t.bin                 (committed chip database)
#
# Outputs in build/:
#   - thiele_xc7a35t.json     (yosys post-synthesis netlist)
#   - thiele_xc7a35t.fasm     (placed-and-routed FPGA assembly)
#   - thiele_xc7a35t.frames   (frame-level bit positions)
#   - thiele_xc7a35t.bit      (binary bitstream loadable on Arty A7-35T)
#
# Usage:
#   bash fpga/run_synthesis_xc7.sh
#
# Environment overrides:
#   NEXTPNR_XILINX  — path to nextpnr-xilinx binary
#   XC7FRAMES2BIT   — path to xc7frames2bit binary
#   PRJXRAY_DIR     — path to a prjxray checkout containing utils/fasm2frames.py
#   PRJXRAY_DB      — path to the artix7 prjxray-db root

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
RTL_DIR="${ROOT}/thielecpu/hardware/rtl"
BUILD_DIR="${ROOT}/build"
PART="xc7a35tcsg324-1"
TOP="thiele_cpu_top"
JSON="${BUILD_DIR}/thiele_xc7a35t.json"
FASM="${BUILD_DIR}/thiele_xc7a35t.fasm"
FRAMES="${BUILD_DIR}/thiele_xc7a35t.frames"
BIT="${BUILD_DIR}/thiele_xc7a35t.bit"
CHIPDB="${ROOT}/fpga/chipdb/xc7a35t.bin"
XDC="${ROOT}/fpga/thiele_arty35.xdc"

NEXTPNR_XILINX="${NEXTPNR_XILINX:-nextpnr-xilinx}"
XC7FRAMES2BIT="${XC7FRAMES2BIT:-xc7frames2bit}"
PRJXRAY_DIR="${PRJXRAY_DIR:-/opt/prjxray}"
PRJXRAY_DB="${PRJXRAY_DB:-${PRJXRAY_DIR}/prjxray-db/artix7}"

mkdir -p "${BUILD_DIR}"

echo "=== [1/4] yosys synth_xilinx -family xc7 (top=${TOP}) ==="
( cd "${RTL_DIR}" && yosys -ql "${BUILD_DIR}/yosys_xc7.log" synth_xc7.ys )
echo "    netlist: ${JSON}"

echo "=== [2/4] nextpnr-xilinx place-and-route (${PART}) ==="
"${NEXTPNR_XILINX}" \
    --chipdb "${CHIPDB}" \
    --xdc "${XDC}" \
    --json "${JSON}" \
    --fasm "${FASM}" \
    --timing-allow-fail \
    2>&1 | tee "${BUILD_DIR}/nextpnr_xc7.log"
echo "    fasm:   ${FASM}"

echo "=== [3/4] fasm2frames (Project X-Ray) ==="
PYTHONPATH="${PRJXRAY_DIR}:${PYTHONPATH:-}" python3 \
    "${PRJXRAY_DIR}/utils/fasm2frames.py" \
    --part "${PART}" \
    --db-root "${PRJXRAY_DB}" \
    "${FASM}" > "${FRAMES}"
echo "    frames: ${FRAMES}"

echo "=== [4/4] xc7frames2bit (Project X-Ray) ==="
"${XC7FRAMES2BIT}" \
    --part_file "${PRJXRAY_DB}/${PART}/part.yaml" \
    --part_name "${PART}" \
    --frm_file "${FRAMES}" \
    --output_file "${BIT}"

echo
echo "✓ Bitstream: ${BIT} ($(wc -c < "${BIT}") bytes)"
echo "  Program board: openFPGALoader -b arty_35t ${BIT}"
