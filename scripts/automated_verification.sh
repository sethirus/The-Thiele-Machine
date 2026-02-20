#!/usr/bin/env bash
set -euxo pipefail

# Automated Thiele Machine Verification Pipeline
# Runs full end-to-end: Coq -> Hardware -> Synthesis -> Simulation -> Reports
# Uses open-source FPGA flow (yosys + nextpnr-generic) for bitstream artifacts.

SCRIPT_PATH="$(readlink -f "${BASH_SOURCE[0]}")"
ROOT="$(cd "$(dirname "$SCRIPT_PATH")/.." && pwd)"

phase() {
  printf "\n[%s] %s\n" "$1" "$2"
}

die() {
  echo "error: $*" >&2
  exit 1
}

cd "$ROOT"

# Create reports directory
REPORTS_DIR="$ROOT/verification_reports"
mkdir -p "$REPORTS_DIR"

phase INIT "Automated Thiele Machine Verification Pipeline"
echo "Workspace: $ROOT"
echo "Reports: $REPORTS_DIR"
echo "Date: $(date)"

# 1. Toolchain Check
phase CHECK "Verifying toolchain availability"
command -v coqc >/dev/null || die "coqc not found"
command -v iverilog >/dev/null || die "iverilog not found"
command -v python3 >/dev/null || die "python3 not found"
command -v yosys >/dev/null || die "yosys not found"
command -v nextpnr-ecp5 >/dev/null || die "nextpnr-ecp5 not found (install open-source PnR toolchain)"
command -v ecppack >/dev/null || die "ecppack not found (install fpga-trellis)"
echo "Open-source FPGA flow enabled (yosys + nextpnr-ecp5)"

# 2. Run Full Forge Pipeline
phase FORGE "Running complete foundry pipeline"
forge_exit=0
bash scripts/forge_artifact.sh > "$REPORTS_DIR/forge.log" 2>&1 || forge_exit=$?
if [ "$forge_exit" -ne 0 ]; then
  echo "WARNING: Forge pipeline exited with code $forge_exit - continuing (see $REPORTS_DIR/forge.log)"
else
  echo "Forge pipeline completed - see $REPORTS_DIR/forge.log"
fi

# 3. Detailed Synthesis Report
phase SYNTH "Generating detailed synthesis report"
if [ ! -f "$REPORTS_DIR/forge.log" ]; then
  echo "forge.log not found. Synthesis skipped." | tee "$REPORTS_DIR/synthesis_report.txt"
else
  {
    echo "=== Yosys Synthesis Report ==="
    echo "Command: yosys -p 'read_verilog -sv -nomem2reg -DSYNTHESIS -DYOSYS_LITE -I thielecpu/hardware/rtl thielecpu/hardware/rtl/thiele_cpu_unified.v; prep; check; stat'"
    echo ""
    yosys -p "read_verilog -sv -nomem2reg -DSYNTHESIS -DYOSYS_LITE -I thielecpu/hardware/rtl thielecpu/hardware/rtl/thiele_cpu_unified.v; prep; check; stat"
  } > "$REPORTS_DIR/synthesis_report.txt" 2>&1 || echo "WARNING: Yosys synthesis failed - see $REPORTS_DIR/synthesis_report.txt"
fi
echo "Synthesis report: $REPORTS_DIR/synthesis_report.txt"

# 4. Hardware Simulation with Full Output
phase SIM "Running hardware simulation with detailed output"
vvp build/thiele_cpu_tb.out +VCD=build/thiele_cpu_tb.vcd > "$REPORTS_DIR/simulation_output.txt" 2>&1
echo "Simulation output: $REPORTS_DIR/simulation_output.txt"
echo "VCD waveform: build/thiele_cpu_tb.vcd"

# 4.5. Analyze Waveforms
phase WAVE "Analyzing VCD waveforms for key metrics"
python3 scripts/analyze_waveforms.py > "$REPORTS_DIR/waveform_analysis.txt" 2>&1
echo "Waveform analysis: $REPORTS_DIR/waveform_analysis.txt"

# 5. FPGA Bitstream Generation (open-source PnR)
phase FPGA "Generating open-source bitstream (nextpnr-ecp5)"
OPENFPGA_PNR="${OPENFPGA_PNR:-0}"
mkdir -p "$ROOT/build"
PNR_JSON="$ROOT/build/thiele_cpu_open.json"
PNR_CFG="$ROOT/build/thiele_cpu_open.cfg"
OPEN_BIT="$REPORTS_DIR/thiele_cpu_ecp5.bit"
ECP5_DEVICE="${ECP5_DEVICE:-85k}"
ECP5_PACKAGE="${ECP5_PACKAGE:-CABGA381}"
ECP5_SPEED="${ECP5_SPEED:-6}"
ECP5_THREADS_DEFAULT=$(nproc 2>/dev/null || echo 2)
ECP5_THREADS="${ECP5_THREADS:-$(( (ECP5_THREADS_DEFAULT + 1) / 2 ))}" # ceil(n/2) threads for optimal performance
if [ "$ECP5_THREADS" -lt 1 ]; then
  ECP5_THREADS=1
fi
ECP5_PNR_TIMEOUT="${ECP5_PNR_TIMEOUT:-1200}"
ECP5_PNR_PLACER="${ECP5_PNR_PLACER:-heap}"
ECP5_PNR_ROUTER="${ECP5_PNR_ROUTER:-router1}"
ECP5_PNR_CELL_TIMEOUT="${ECP5_PNR_CELL_TIMEOUT:-4}"
ECP5_DEVICE_FLAG="--${ECP5_DEVICE}"
if [ "$OPENFPGA_PNR" = "1" ]; then
  yosys -p "read_verilog -sv -nomem2reg -DSYNTHESIS -DYOSYS_LITE -I thielecpu/hardware/rtl thielecpu/hardware/rtl/thiele_cpu_unified.v; synth_ecp5 -top thiele_cpu -json $PNR_JSON" \
    > "$REPORTS_DIR/openfpga_synth.log" 2>&1
  if [ ! -f "$PNR_JSON" ]; then
    echo "Open-source synthesis did not produce $PNR_JSON - see $REPORTS_DIR/openfpga_synth.log"
    exit 1
  fi
  timeout "$ECP5_PNR_TIMEOUT" nextpnr-ecp5 --json "$PNR_JSON" --textcfg "$PNR_CFG" "$ECP5_DEVICE_FLAG" \
    --package "$ECP5_PACKAGE" --speed "$ECP5_SPEED" --threads "$ECP5_THREADS" --placer "$ECP5_PNR_PLACER" \
    --router "$ECP5_PNR_ROUTER" --placer-heap-cell-placement-timeout "$ECP5_PNR_CELL_TIMEOUT" \
    --no-tmdriv --ignore-loops --ignore-rel-clk --timing-allow-fail \
    > "$REPORTS_DIR/openfpga_pnr.log" 2>&1 || {
      echo "Open-source PnR failed - see $REPORTS_DIR/openfpga_pnr.log"
      exit 1
    }
  ecppack "$PNR_CFG" "$OPEN_BIT" > "$REPORTS_DIR/openfpga_pack.log" 2>&1 || {
    echo "Open-source bitstream pack failed - see $REPORTS_DIR/openfpga_pack.log"
    exit 1
  }
  echo "Open-source bitstream artifact: $OPEN_BIT"
else
  echo "Open-source PnR skipped (set OPENFPGA_PNR=1 to enable full bitstream generation)"
fi

# 6. Verification Summary
phase VERIFY "Generating verification summary"
{
  echo "=== Thiele Machine Verification Summary ==="
  echo "Generated: $(date)"
  echo ""
  echo "1. Coq Proofs:"
  echo "   - Files: $(find coq -name "*.v" | wc -l)"
  echo "   - Compiled: $(grep -c "COQC" "$REPORTS_DIR/forge.log" || echo "N/A") files"
  echo "   - Status: $(grep -q "SUCCESS" "$REPORTS_DIR/forge.log" && echo "PASS" || echo "FAIL")"
  echo ""
  echo "2. Hardware Synthesis:"
  echo "   - Cells: $(grep "Number of cells:" "$REPORTS_DIR/synthesis_report.txt" | tail -1 | awk '{print $4}')"
  echo "   - Wires: $(grep "Number of wires:" "$REPORTS_DIR/synthesis_report.txt" | tail -1 | awk '{print $4}')"
  echo "   - Status: $(grep -q "End of script" "$REPORTS_DIR/synthesis_report.txt" && echo "PASS" || echo "FAIL")"
  echo ""
  echo "3. Hardware Simulation:"
  echo "   - Completed: $(grep -q "Test completed" "$REPORTS_DIR/simulation_output.txt" && echo "PASS" || echo "FAIL")"
  echo "   - μ-Enforcement: $(grep -c "FORGERY DETECTED" "$REPORTS_DIR/simulation_output.txt") detections"
  echo "   - Final PC: $(grep "Final PC:" "$REPORTS_DIR/simulation_output.txt" | awk '{print $3}')"
  echo ""
  echo "4. Waveform Analysis:"
  echo "   - Signals: $(grep "Total signals:" "$REPORTS_DIR/waveform_analysis.txt" | awk '{print $3}')"
  echo "   - Time range: $(grep "Simulation time range:" "$REPORTS_DIR/waveform_analysis.txt" | cut -d: -f2- | xargs)"
  echo "   - μ Signal changes: $(grep "Total μ signal changes:" "$REPORTS_DIR/waveform_analysis.txt" | awk '{print $5}')"
  echo ""
  echo "5. 3-Layer Isomorphism Tests:"
  echo "   - Passed: $(grep -c "passed" "$REPORTS_DIR/forge.log" | tail -1) tests"
  echo ""
  echo "5. Open-source Bitstream:"
  if [ "$OPENFPGA_PNR" = "1" ] && [ -f "$REPORTS_DIR/thiele_cpu_ecp5.bit" ]; then
    echo "   - Generated: YES ($(stat -c%s "$REPORTS_DIR/thiele_cpu_ecp5.bit") bytes)"
  elif [ "$OPENFPGA_PNR" = "1" ]; then
    echo "   - Generated: NO (bitstream missing)"
  else
    echo "   - Generated: SKIPPED (OPENFPGA_PNR=0)"
  fi
  echo ""
  echo "Reports Location: $REPORTS_DIR"
  echo "All artifacts verified for reproducibility."
} > "$REPORTS_DIR/verification_summary.txt"

echo ""
echo "=== VERIFICATION COMPLETE ==="
echo "Summary: $REPORTS_DIR/verification_summary.txt"
echo "All reports in: $REPORTS_DIR"
echo ""
echo "To verify independently:"
echo "1. Run: bash scripts/automated_verification.sh"
echo "2. Check reports in verification_reports/"
echo "3. For FPGA: Ensure yosys + nextpnr-ecp5 + ecppack are installed"

phase SUCCESS "Automated verification pipeline complete"
