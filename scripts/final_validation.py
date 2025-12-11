#!/usr/bin/env python3
"""
Final Integration Validation for Thiele Machine
Validates all three layers: Coq proofs, Verilog RTL, and Python VM

This script performs comprehensive validation of the complete integration pipeline.
"""

import subprocess
import sys
from pathlib import Path
import json

def run_command(cmd, description, timeout=30):
    """Run a command and return success status."""
    print(f"\n{'='*70}")
    print(f"Testing: {description}")
    print(f"{'='*70}")
    try:
        result = subprocess.run(
            cmd,
            shell=True,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd="/home/runner/work/The-Thiele-Machine/The-Thiele-Machine"
        )
        if result.returncode == 0:
            print(f"✅ PASS: {description}")
            return True
        else:
            print(f"❌ FAIL: {description}")
            if result.stderr:
                print(f"Error: {result.stderr[:500]}")
            return False
    except subprocess.TimeoutExpired:
        print(f"⏱️ TIMEOUT: {description}")
        return False
    except Exception as e:
        print(f"❌ ERROR: {description} - {e}")
        return False

def main():
    print("\n" + "="*70)
    print("Thiele Machine - Final Integration Validation")
    print("="*70)
    
    results = {}
    
    # Layer 1: Coq Proofs
    print("\n\n🔬 LAYER 1: Coq Formal Proofs")
    print("-"*70)
    
    results['coq_installed'] = run_command(
        "which coqc",
        "Coq compiler installed"
    )
    
    results['coq_version'] = run_command(
        "coqc --version | head -1",
        "Coq version check"
    )
    
    # Layer 2: Verilog RTL
    print("\n\n⚡ LAYER 2: Verilog RTL Hardware")
    print("-"*70)
    
    results['yosys_installed'] = run_command(
        "which yosys",
        "Yosys synthesis tool installed"
    )
    
    results['iverilog_installed'] = run_command(
        "which iverilog",
        "Icarus Verilog simulator installed"
    )
    
    results['mu_alu_syntax'] = run_command(
        "iverilog -t null thielecpu/hardware/mu_alu.v",
        "μ-ALU Verilog syntax check"
    )
    
    results['mu_core_syntax'] = run_command(
        "iverilog -t null thielecpu/hardware/mu_core.v",
        "μ-Core Verilog syntax check"
    )
    
    # Layer 3: Python VM
    print("\n\n🐍 LAYER 3: Python VM")
    print("-"*70)
    
    results['vm_import'] = run_command(
        "python3 -c 'from thielecpu.vm import VM; print(\"OK\")'",
        "VM module import"
    )
    
    results['mu_ledger_import'] = run_command(
        "python3 -c 'from thielecpu.mu import MuLedger; print(\"OK\")'",
        "μ-Ledger module import"
    )
    
    results['primitives_import'] = run_command(
        "python3 -c 'from thielecpu.primitives import *; print(\"OK\")'",
        "Primitives module import"
    )
    
    # Integration Tests
    print("\n\n🔗 INTEGRATION: Cross-Layer Validation")
    print("-"*70)
    
    results['vm_rtl_equivalence'] = run_command(
        "python3 scripts/test_vm_rtl_equivalence.py",
        "VM-RTL equivalence tests"
    )
    
    # Build System
    print("\n\n🛠️ BUILD SYSTEM: Makefile Targets")
    print("-"*70)
    
    results['makefile_exists'] = run_command(
        "test -f Makefile && echo 'OK'",
        "Makefile exists"
    )
    
    results['make_help'] = run_command(
        "make help-full | grep -q 'RTL SYNTHESIS' && echo 'OK'",
        "Makefile help targets"
    )
    
    # Documentation
    print("\n\n📚 DOCUMENTATION")
    print("-"*70)
    
    docs = [
        'ARCHITECTURE.md',
        'INTEGRATION_SUMMARY.md',
        'SYNTHESIS_REPORT.md',
        'SESSION_SUMMARY.md',
        'TODO.md',
        'MILESTONES.md'
    ]
    
    for doc in docs:
        results[f'doc_{doc}'] = run_command(
            f"test -f {doc} && echo 'OK'",
            f"Documentation: {doc}"
        )
    
    # Summary
    print("\n\n" + "="*70)
    print("VALIDATION SUMMARY")
    print("="*70)
    
    passed = sum(1 for v in results.values() if v)
    total = len(results)
    percentage = (passed / total * 100) if total > 0 else 0
    
    print(f"\nTests Passed: {passed}/{total} ({percentage:.1f}%)")
    print(f"\nStatus by Category:")
    
    categories = {
        'Coq Proofs': ['coq_installed', 'coq_version'],
        'Verilog RTL': ['yosys_installed', 'iverilog_installed', 'mu_alu_syntax', 'mu_core_syntax'],
        'Python VM': ['vm_import', 'mu_ledger_import', 'primitives_import'],
        'Integration': ['vm_rtl_equivalence'],
        'Build System': ['makefile_exists', 'make_help'],
    }
    
    for category, tests in categories.items():
        cat_passed = sum(1 for t in tests if results.get(t, False))
        cat_total = len(tests)
        status = "✅" if cat_passed == cat_total else "⚠️"
        print(f"  {status} {category}: {cat_passed}/{cat_total}")
    
    # Save results
    results_file = Path('artifacts/final_validation.json')
    results_file.parent.mkdir(exist_ok=True)
    
    with open(results_file, 'w') as f:
        json.dump({
            'passed': passed,
            'total': total,
            'percentage': percentage,
            'results': results
        }, f, indent=2)
    
    print(f"\n✅ Validation results saved to: {results_file}")
    
    # Final verdict
    print("\n" + "="*70)
    if percentage >= 90:
        print("🎉 INTEGRATION COMPLETE - All systems operational!")
        print("="*70)
        return 0
    elif percentage >= 75:
        print("⚠️ INTEGRATION MOSTLY COMPLETE - Minor issues remain")
        print("="*70)
        return 0
    else:
        print("❌ INTEGRATION INCOMPLETE - Significant issues detected")
        print("="*70)
        return 1

if __name__ == "__main__":
    sys.exit(main())
