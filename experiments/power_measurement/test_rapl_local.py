#!/usr/bin/env python3
"""
Test if local machine supports Intel RAPL power measurement.
Run this FIRST before any cloud spending.

If this works, you can get energy data for FREE.
"""

import sys
from pathlib import Path

def check_rapl_support():
    """Check for RAPL availability and return path if found."""
    
    print("=" * 60)
    print("RAPL POWER MEASUREMENT SUPPORT CHECK")
    print("=" * 60)
    print()
    
    # Check CPU type
    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.exists():
        content = cpuinfo.read_text()
        if "Intel" in content:
            print("✓ Intel CPU detected")
        elif "AMD" in content:
            print("⚠ AMD CPU detected (RAPL support varies)")
        else:
            print("? Unknown CPU vendor")
    
    # Check virtualization
    try:
        import subprocess
        result = subprocess.run(['lscpu'], capture_output=True, text=True)
        if 'Hypervisor' in result.stdout:
            for line in result.stdout.split('\n'):
                if 'Hypervisor' in line:
                    print(f"⚠ {line.strip()}")
            print("  (VMs usually don't expose RAPL)")
    except:
        pass
    
    print()
    print("Checking RAPL paths...")
    print("-" * 40)
    
    rapl_paths = [
        # Intel paths
        "/sys/class/powercap/intel-rapl/intel-rapl:0/energy_uj",
        "/sys/devices/virtual/powercap/intel-rapl/intel-rapl:0/energy_uj",
        # AMD paths (RAPL-like)
        "/sys/class/powercap/amd-rapl/amd-rapl:0/energy_uj",
    ]
    
    found_path = None
    
    for path in rapl_paths:
        p = Path(path)
        if p.exists():
            print(f"✓ Found: {path}")
            try:
                energy = int(p.read_text().strip())
                print(f"  Reading: {energy} μJ")
                found_path = path
            except PermissionError:
                print(f"  ✗ Permission denied (try: sudo chmod a+r {path})")
            except Exception as e:
                print(f"  ✗ Error: {e}")
        else:
            print(f"✗ Not found: {path}")
    
    print()
    
    # Check powercap directory
    powercap = Path("/sys/class/powercap")
    if powercap.exists():
        contents = list(powercap.iterdir())
        if contents:
            print("Powercap directory contents:")
            for item in contents:
                print(f"  {item.name}")
        else:
            print("Powercap directory exists but is empty")
    
    print()
    print("=" * 60)
    
    if found_path:
        print("✓✓✓ RAPL AVAILABLE - YOU CAN MEASURE POWER FOR FREE ✓✓✓")
        print()
        print("Run: python experiments/power_measurement/measure_real_power.py")
        return found_path
    else:
        print("✗ RAPL NOT AVAILABLE ON THIS MACHINE")
        print()
        print("Options:")
        print("  1. Run on bare-metal Linux with Intel CPU")
        print("  2. Use AWS c6i.metal spot instance (~$1.20/hr)")
        print("  3. Use perf stat (approximate, may work in VMs)")
        return None


def test_perf_alternative():
    """Test if perf can measure energy (works on some systems without RAPL)."""
    print()
    print("Checking perf alternative...")
    print("-" * 40)
    
    import subprocess
    try:
        # Check if perf is available
        result = subprocess.run(['perf', 'list'], capture_output=True, text=True)
        if 'energy' in result.stdout.lower() or 'power' in result.stdout.lower():
            print("✓ perf has energy/power events")
            
            # List available events
            for line in result.stdout.split('\n'):
                if 'energy' in line.lower() or 'power' in line.lower():
                    print(f"  {line.strip()}")
            return True
        else:
            print("✗ perf doesn't have energy events on this system")
            return False
    except FileNotFoundError:
        print("✗ perf not installed")
        print("  Install with: apt install linux-tools-common linux-tools-generic")
        return False
    except Exception as e:
        print(f"✗ Error: {e}")
        return False


if __name__ == "__main__":
    rapl_path = check_rapl_support()
    perf_available = test_perf_alternative()
    
    print()
    print("=" * 60)
    print("RECOMMENDATION")
    print("=" * 60)
    
    if rapl_path:
        print("Use RAPL for direct energy measurement")
        sys.exit(0)
    elif perf_available:
        print("Use perf stat for approximate energy measurement")
        sys.exit(0)
    else:
        print("Need different hardware for power measurement")
        print("See: experiments/power_measurement/aws_setup.sh")
        sys.exit(1)
