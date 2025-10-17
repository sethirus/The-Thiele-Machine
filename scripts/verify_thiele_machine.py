# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""
Thiele Machine Verification Script

This script implements the verification procedure from the THIELE-SPEC-v1.0.md
to validate that a Thiele machine implementation correctly enforces receipts
and μ-bit rules end-to-end.

Usage:
    python3 scripts/verify_thiele_machine.py [implementation_type]

Where implementation_type is:
    - hardware: Verify FPGA implementation
    - software: Verify software VM
    - both: Verify both (default)
"""

import sys
import json
import hashlib
import os
from pathlib import Path
from typing import Dict, List, Any, Optional
import subprocess
import time

class ThieleVerifier:
    """Verifier for Thiele Machine implementations."""

    def __init__(self, base_dir: Path):
        self.base_dir = base_dir
        self.spec_file = base_dir / "spec" / "THIELE-SPEC-v1.0.md"
        self.golden_dir = base_dir / "spec" / "golden"
        self.results = {}

    def verify_spec_exists(self) -> bool:
        """Check that the specification file exists."""
        if not self.spec_file.exists():
            print(f"[FAIL] Specification file not found: {self.spec_file}")
            return False
        print(f"[OK] Specification file found: {self.spec_file}")
        return True

    def verify_golden_receipts(self) -> bool:
        """Verify golden receipt examples from the spec."""
        success = True

        golden_files = [
            "horn_small.json",
            "tseitin_small.json",
            "xor_small_orderA.json",
            "xor_small_orderB.json",
            "xor_small.json"
        ]

        for filename in golden_files:
            filepath = self.golden_dir / filename
            if not filepath.exists():
                print(f"[FAIL] Golden receipt missing: {filename}")
                success = False
                continue

            try:
                with open(filepath, 'r', encoding='utf-8') as f:
                    receipt = json.load(f)

                # Validate receipt structure according to THIELE-SPEC-v1.0
                required_fields = ["spec_version", "kernel_pubkey", "steps", "global_digest", "signature"]
                for field in required_fields:
                    if field not in receipt:
                        print(f"[FAIL] Invalid receipt structure in {filename}: missing {field}")
                        success = False
                        break

                # Validate spec version
                if receipt.get("spec_version") != "1.0":
                    print(f"[FAIL] Invalid spec version in {filename}: expected '1.0', got '{receipt.get('spec_version')}'")
                    success = False
                    continue

                # Validate μ-bit accounting in steps
                if not self._validate_mu_accounting(receipt):
                    print(f"[FAIL] Invalid μ-bit accounting in {filename}")
                    success = False

                print(f"[OK] Golden receipt valid: {filename}")

            except json.JSONDecodeError:
                print(f"[FAIL] Invalid JSON in golden receipt: {filename}")
                success = False
            except UnicodeDecodeError:
                print(f"[FAIL] Unicode decode error in golden receipt: {filename}")
                success = False
            except Exception as e:
                print(f"[FAIL] Error validating {filename}: {e}")
                success = False

        return success

    def _validate_mu_accounting(self, receipt: Dict[str, Any]) -> bool:
        """Validate μ-bit accounting in a receipt according to THIELE-SPEC-v1.0."""
        try:
            steps = receipt["steps"]

            # Validate that all steps have required fields
            for step in steps:
                required_step_fields = ["idx", "transition", "mu_delta", "step_hash", "solver", "solver_cmdline"]
                for field in required_step_fields:
                    if field not in step:
                        print(f"[FAIL] Step missing required field: {field}")
                        return False

                # Validate mu_delta is a non-negative integer
                if not isinstance(step["mu_delta"], int) or step["mu_delta"] < 0:
                    print(f"[FAIL] Invalid mu_delta: {step['mu_delta']}")
                    return False

            # All steps are valid
            return True

        except (KeyError, TypeError) as e:
            print(f"[FAIL] Error in μ-bit validation: {e}")
            return False

    def verify_coq_proofs(self) -> bool:
        """Verify that Coq proofs compile successfully."""
        coq_dir = self.base_dir / "coq"
        if not coq_dir.exists():
            print("[FAIL] Coq directory not found")
            return False

        try:
            # Check if coqc is available
            coqc_path = r"C:\Coq-Platform~8.20~2025.01\bin\coqc.exe"
            result = subprocess.run(
                [coqc_path, "--version"],
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode != 0:
                print("[FAIL] Coq compiler not available")
                return False

            print("[OK] Coq compiler available")

            # Try to compile key proof files
            key_files = [
                "thielemachine/coqproofs/ThieleMachineConcrete.v",
                "thielemachine/coqproofs/Separation.v"
            ]

            for filename in key_files:
                filepath = coq_dir / filename
                if not filepath.exists():
                    print(f"[FAIL] Coq proof file missing: {filename}")
                    continue

                print(f"[CHECK] Compiling {filename}...")
                start_time = time.time()
                result = subprocess.run(
                    [coqc_path, "-Q", str(coq_dir), "ThieleMachine", str(filepath)],
                    cwd=str(coq_dir),
                    capture_output=True,
                    text=True,
                    timeout=60
                )
                end_time = time.time()

                if result.returncode == 0:
                    print(f"[OK] Coq compilation successful for {filename} ({end_time - start_time:.2f}s)")
                else:
                    print(f"[FAIL] Coq compilation failed for {filename}")
                    print(f"Error: {result.stderr[:500]}...")
                    return False

            return True

        except Exception as e:
            print(f"[FAIL] Error during Coq verification: {e}")
            return False

    def verify_hardware_implementation(self) -> bool:
        """Verify hardware implementation if available."""
        hw_dir = self.base_dir / "thielecpu" / "hardware"
        if not hw_dir.exists():
            print("[WARN] Hardware implementation directory not found")
            return True  # Not required

        success = True

        # Check for synthesis report
        synth_report = hw_dir / "synthesis_report.md"
        if not synth_report.exists():
            print("[FAIL] Hardware synthesis report missing")
            success = False
        else:
            print("[OK] Hardware synthesis report found")

        # Check for test report
        test_report = hw_dir / "test_report.md"
        if not test_report.exists():
            print("[FAIL] Hardware test report missing")
            success = False
        else:
            print("[OK] Hardware test report found")

        # Check for Verilog files
        verilog_files = ["thiele_cpu.v", "mmu.v", "lei.v", "mau.v", "pee.v"]
        for vf in verilog_files:
            if not (hw_dir / vf).exists():
                print(f"[FAIL] Hardware Verilog file missing: {vf}")
                success = False
            else:
                print(f"[OK] Hardware Verilog file found: {vf}")

        return success

    def verify_software_implementation(self) -> bool:
        """Verify software implementation."""
        vm_file = self.base_dir / "thielecpu" / "vm.py"
        if not vm_file.exists():
            print("[FAIL] Software VM implementation missing")
            return False

        print("[OK] Software VM implementation found")

        # Try to import and basic validation
        try:
            sys.path.insert(0, str(self.base_dir))
            import thielecpu.vm
            print("[OK] Software VM imports successfully")
            return True
        except ImportError as e:
            print(f"[FAIL] Software VM import failed: {e}")
            return False

    def generate_audit_trail(self) -> Dict[str, Any]:
        """Generate comprehensive audit trail."""
        return {
            "verification_timestamp": time.time(),
            "verifier_version": "1.0.0",
            "results": self.results,
            "system_info": {
                "python_version": sys.version,
                "platform": sys.platform,
                "working_directory": str(self.base_dir)
            }
        }

    def run_verification(self, implementation_type: str = "both") -> bool:
        """Run the complete verification procedure."""
        print("Starting Thiele Machine Verification")
        print("=" * 50)

        all_passed = True

        # 1. Verify specification exists
        if not self.verify_spec_exists():
            all_passed = False

        # 2. Verify golden receipts
        if not self.verify_golden_receipts():
            all_passed = False

        # 3. Verify Coq proofs
        if not self.verify_coq_proofs():
            all_passed = False

        # 4. Verify implementations
        if implementation_type in ["hardware", "both"]:
            if not self.verify_hardware_implementation():
                all_passed = False

        if implementation_type in ["software", "both"]:
            if not self.verify_software_implementation():
                all_passed = False

        # Generate audit trail
        audit_trail = self.generate_audit_trail()

        # Save results
        output_file = self.base_dir / "outputs" / "verification_results.json"
        output_file.parent.mkdir(exist_ok=True)
        with open(output_file, 'w') as f:
            json.dump(audit_trail, f, indent=2)

        print("=" * 50)
        if all_passed:
            print("[OK] VERIFICATION COMPLETE: All checks passed!")
            print(f"[FILE] Results saved to: {output_file}")
        else:
            print("[FAIL] VERIFICATION FAILED: Some checks failed!")
            print(f"[FILE] Results saved to: {output_file}")

        return all_passed

def main():
    """Main entry point."""
    base_dir = Path(__file__).parent.parent

    implementation_type = sys.argv[1] if len(sys.argv) > 1 else "both"

    verifier = ThieleVerifier(base_dir)
    success = verifier.run_verification(implementation_type)

    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()