#!/bin/bash
# ============================================================================
# Thiele CPU FPGA Synthesis Runner
# ============================================================================

set -e

echo "Thiele CPU FPGA Synthesis"
echo "========================="

# Check if Vivado is available
if ! command -v vivado &> /dev/null; then
    echo "❌ Vivado not found in PATH"
    echo ""
    echo "To run FPGA synthesis, you need:"
    echo "1. Xilinx Vivado Design Suite installed"
    echo "2. Vivado binary in your PATH"
    echo ""
    echo "For cloud synthesis options:"
    echo "- AWS F1 FPGA instances"
    echo "- Microsoft Azure FPGA VMs"
    echo "- Google Cloud FPGA instances"
    echo ""
    echo "Local installation:"
    echo "- Download Vivado from Xilinx website"
    echo "- Install and add to PATH"
    echo ""
    echo "Synthesis files are ready:"
    echo "✅ thiele_cpu.v (main design)"
    echo "✅ synthesis.tcl (synthesis script)"
    echo "✅ constraints.xdc (timing constraints)"
    echo "✅ README.md (documentation)"
    exit 1
fi

echo "✅ Vivado found: $(which vivado)"

# Check required files
required_files=("thiele_cpu.v" "synthesis.tcl" "constraints.xdc")
missing_files=()

for file in "${required_files[@]}"; do
    if [ ! -f "$file" ]; then
        missing_files+=("$file")
    fi
done

if [ ${#missing_files[@]} -ne 0 ]; then
    echo "❌ Missing required files:"
    for file in "${missing_files[@]}"; do
        echo "   - $file"
    done
    exit 1
fi

echo "✅ All required files present"

# Run synthesis
echo ""
echo "Starting FPGA synthesis..."
echo "This may take several minutes..."
echo ""

vivado -mode batch -source synthesis.tcl

echo ""
echo "🎉 Synthesis completed!"
echo ""
echo "Generated files:"
echo "- thiele_cpu_vivado/thiele_cpu.runs/impl_1/thiele_cpu.bit (bitstream)"
echo "- utilization.rpt (resource usage)"
echo "- timing.rpt (timing analysis)"
echo "- power.rpt (power consumption)"
echo ""
echo "Next steps:"
echo "1. Program the bitstream to your FPGA board"
echo "2. Run hardware validation tests"
echo "3. Execute supra-quantum experiments"