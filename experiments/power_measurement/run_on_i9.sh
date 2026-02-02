#!/bin/bash
# =============================================================================
# POWER MEASUREMENT ON i9-9900K
# =============================================================================
# 
# Run this script after booting Ubuntu from USB on your i9-9900K.
# 
# Steps:
#   1. Boot from Ubuntu Live USB (select "Try Ubuntu")
#   2. Open terminal (Ctrl+Alt+T)
#   3. Run: curl -sL https://raw.githubusercontent.com/sethirus/The-Thiele-Machine/main/experiments/power_measurement/run_on_i9.sh | bash
#
# Or manually:
#   1. Copy this script to USB
#   2. Run: bash run_on_i9.sh
#
# =============================================================================

set -e

echo "============================================================"
echo "THIELE MACHINE - REAL POWER MEASUREMENT"
echo "============================================================"
echo ""

# Check if running as root (needed for RAPL)
if [ "$EUID" -ne 0 ]; then 
    echo "Need root for RAPL access. Re-running with sudo..."
    exec sudo bash "$0" "$@"
fi

# Check RAPL
echo "[1/5] Checking RAPL availability..."
if [ -f /sys/class/powercap/intel-rapl/intel-rapl:0/energy_uj ]; then
    echo "  ✓ RAPL available"
    cat /sys/class/powercap/intel-rapl/intel-rapl:0/energy_uj
else
    echo "  ✗ RAPL not found!"
    echo "  Make sure you're on bare metal Linux with Intel CPU"
    exit 1
fi

# Install dependencies
echo ""
echo "[2/5] Installing dependencies..."
apt-get update -qq
apt-get install -y -qq python3 python3-pip python3-venv git > /dev/null

# Clone repo
echo ""
echo "[3/5] Cloning repository..."
cd /tmp
rm -rf thiele-machine
git clone --depth 1 https://github.com/sethirus/The-Thiele-Machine.git thiele-machine
cd thiele-machine

# Setup Python
echo ""
echo "[4/5] Setting up Python environment..."
python3 -m venv .venv
source .venv/bin/activate
pip install --quiet --upgrade pip
pip install --quiet numpy scipy

# Run experiment
echo ""
echo "[5/5] Running power measurement..."
echo "============================================================"
echo ""

python3 experiments/power_measurement/measure_real_power.py

echo ""
echo "============================================================"
echo "COMPLETE"
echo "============================================================"
echo ""
echo "Results saved to: /tmp/thiele-machine/experiments/power_measurement/power_results.json"
echo ""
echo "To copy results, run:"
echo "  cat /tmp/thiele-machine/experiments/power_measurement/power_results.json"
echo ""
