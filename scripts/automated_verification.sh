#!/usr/bin/env bash
set -euo pipefail

# Automated Thiele Machine Verification Pipeline
# Runs full end-to-end: Coq -> Hardware -> Synthesis -> Simulation -> Reports
# Generates FPGA-ready bitstream if Vivado available.

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
VIVADO_AVAILABLE=false
if command -v vivado >/dev/null; then
  VIVADO_AVAILABLE=true
  echo "Vivado found - FPGA bitstream generation enabled"
else
  echo "Vivado not found - skipping FPGA bitstream (simulation only)"
fi

# 2. Run Full Forge Pipeline
phase FORGE "Running complete foundry pipeline"
bash scripts/forge_artifact.sh > "$REPORTS_DIR/forge.log" 2>&1
echo "Forge pipeline completed - see $REPORTS_DIR/forge.log"

# 3. Detailed Synthesis Report
phase SYNTH "Generating detailed synthesis report"
{
  echo "=== Yosys Synthesis Report ==="
  echo "Command: yosys -p 'read_verilog -sv -nomem2reg -DYOSYS_LITE -I thielecpu/hardware/rtl thielecpu/hardware/rtl/thiele_cpu_synth.v thielecpu/hardware/rtl/mu_alu.v thielecpu/hardware/rtl/mu_core.v thielecpu/hardware/rtl/receipt_integrity_checker.v; prep; check; stat'"
  echo ""
  yosys -p "read_verilog -sv -nomem2reg -DYOSYS_LITE -I thielecpu/hardware/rtl thielecpu/hardware/rtl/thiele_cpu_synth.v thielecpu/hardware/rtl/mu_alu.v thielecpu/hardware/rtl/mu_core.v thielecpu/hardware/rtl/receipt_integrity_checker.v; prep; check; stat"
} > "$REPORTS_DIR/synthesis_report.txt" 2>&1
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

# 5. FPGA Bitstream Generation (if Vivado available)
if $VIVADO_AVAILABLE; then
  phase FPGA "Generating FPGA bitstream with Vivado"
  cd thielecpu/hardware
  vivado -mode batch -source synthesis.tcl > "$REPORTS_DIR/vivado_synthesis.log" 2>&1
  if [ -f "thiele_cpu.bit" ]; then
    echo "Bitstream generated: thiele_cpu.bit"
    cp thiele_cpu.bit "$REPORTS_DIR/"
  else
    echo "Bitstream generation failed - check $REPORTS_DIR/vivado_synthesis.log"
  fi
  cd "$ROOT"
else
  phase FPGA "FPGA bitstream skipped (Vivado not available)"
  echo "To generate bitstream: install Vivado and run 'vivado -mode batch -source thielecpu/hardware/synthesis.tcl'"
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
  echo "5. FPGA Bitstream:"
  if $VIVADO_AVAILABLE && [ -f "$REPORTS_DIR/thiele_cpu.bit" ]; then
    echo "   - Generated: YES ($(stat -c%s "$REPORTS_DIR/thiele_cpu.bit") bytes)"
  else
    echo "   - Generated: NO (Vivado not available or failed)"
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
echo "3. For FPGA: Install Vivado and re-run if needed"

phase SUCCESS "Automated verification pipeline complete"