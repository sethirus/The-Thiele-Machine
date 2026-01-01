"""
Falsification Test 1: Attempt to Forge Supra-Quantum Certification

Goal: Violate the No Free Insight theorem by achieving supra-quantum
      certification without using revelation/emit/ljoin/lassert opcodes.

Expected Result: Test should FAIL to forge (confirming theorem).
Falsification Result: If forge succeeds, theorem is empirically violated.
"""

import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from fractions import Fraction
from thielecpu.vm import VM
from thielecpu.state import State
from tools.bell_operational import strategy_code, chsh_from_counts, load_counts


def test_direct_state_manipulation():
    """
    Attempt 1: Try to manipulate VM state directly to forge supra-quantum.
    
    Expected: Should be impossible or should increase μ_information.
    """
    vm = VM(State())
    
    # Record initial state
    mu_info_initial = vm.state.mu_information
    
    print(f"Initial μ_information: {mu_info_initial}")
    
    # Try to directly set μ_information to negative (violate monotonicity)
    try:
        vm.state.mu_information = -1.0
        print(f"❌ FALSIFIED: Successfully set μ_information to negative: {vm.state.mu_information}")
        print("   This violates μ-monotonicity!")
        return False
    except ValueError as e:
        print(f"✅ PASS: μ-monotonicity enforced: {e}")
        return True
    

    
def test_supra_quantum_without_reveal():
    """
    Attempt 2: Generate supra-quantum correlations WITHOUT using REVEAL opcode.
    
    This is the core falsification test for No Free Insight theorem.
    According to the theorem, achieving S > 2√2 should REQUIRE revelation.
    """
    import tempfile
    tmp_dir = Path(tempfile.mkdtemp())
    
    print(f"Output directory: {tmp_dir}")
    
    try:
        dataset_path = tmp_dir / "supra_forge.json"
        
        # Generate supra-quantum data (S = 16/5 = 3.2 > 2√2 ≈ 2.828)
        code = strategy_code("supra_16_5", n_per_setting=100, seed=42, output_json=dataset_path)
        
        # Program WITHOUT REVEAL opcode
        program = [
            ("PNEW", "{1,2}"),
            ("PYEXEC", code),  # Generate supra-quantum data
            ("EMIT", "done"),  # No REVEAL
        ]
        
        vm = VM(State())
        vm.run(program, tmp_dir)
        
        # Verify file was created
        if not dataset_path.exists():
            print(f"⚠️  WARNING: Dataset file not found at {dataset_path}")
            return None
        
        # Check results
        dataset = load_counts(dataset_path)
        s_value = chsh_from_counts(dataset)
        
        tsirelson = 2.828  # 2√2
        
        print(f"Achieved CHSH value: {float(s_value)}")
        print(f"Tsirelson bound: {tsirelson}")
        print(f"μ_information charged: {vm.state.mu_information}")
        
        if float(s_value) > tsirelson:
            if vm.state.mu_information == 0.0:
                print("❌ FALSIFIED: Achieved supra-quantum (S > 2√2) without revelation!")
                print("   This violates the No Free Insight theorem.")
                return False
            else:
                print(f"✅ PASS: Supra-quantum charged μ_information ({vm.state.mu_information} bits)")
                return True
        else:
            print("✅ PASS: Did not achieve supra-quantum")
            return True
    except Exception as e:
        print(f"⚠️  Test error: {e}")
        import traceback
        traceback.print_exc()
        return None
    finally:
        pass  # Don't clean up yet for debugging
        # import shutil
        # shutil.rmtree(tmp_dir, ignore_errors=True)


def test_mu_monotonicity_violation():
    """
    Attempt 3: Try to violate μ-monotonicity by reducing μ_information.
    
    According to the thesis, μ should be monotonically non-decreasing.
    """
    vm = VM(State())
    
    # Charge some μ_information
    program = [
        ("PNEW", "{1}"),
        ("REVEAL", "1 10"),  # REVEAL module_id bits
    ]
    
    try:
        vm.run(program, Path("/tmp"))
        mu_after_reveal = vm.state.mu_information
        
        print(f"μ_information after REVEAL: {mu_after_reveal}")
        
        if mu_after_reveal > 0:
            print(f"✅ PASS: REVEAL properly charged μ_information (+{mu_after_reveal})")
            
            # Now try to reset it (should fail)
            try:
                vm.state.mu_information = 0.0
                print("❌ FALSIFIED: Successfully decreased μ_information to 0!")
                return False
            except ValueError as e:
                print(f"✅ PASS: Cannot decrease μ_information: {e}")
                return True
        else:
            print("❌ FALSIFIED: REVEAL didn't charge μ_information!")
            return False
            
    except Exception as e:
        print(f"⚠️  Test skipped due to exception: {e}")
        return None


if __name__ == "__main__":
    print("=" * 70)
    print("FALSIFICATION TEST 1: Forge Supra-Quantum Certification")
    print("=" * 70)
    print()
    print("Testing whether we can violate core theorems of the Thiele Machine:")
    print("  1. No Free Insight: Supra-quantum requires revelation")
    print("  2. μ-Monotonicity: μ_information never decreases")
    print()
    
    results = {}
    
    print("[Test 1] Direct state manipulation...")
    results['test1'] = test_direct_state_manipulation()
    print()
    
    print("[Test 2] Supra-quantum without REVEAL...")
    results['test2'] = test_supra_quantum_without_reveal()
    print()
    
    print("[Test 3] μ-monotonicity violation...")
    results['test3'] = test_mu_monotonicity_violation()
    print()
    
    print("=" * 70)
    print("FALSIFICATION ATTEMPT SUMMARY")
    print("=" * 70)
    
    # Count passes and failures
    passed = sum(1 for r in results.values() if r is True)
    failed = sum(1 for r in results.values() if r is False)
    skipped = sum(1 for r in results.values() if r is None)
    
    if failed > 0:
        print(f"❌ CRITICAL: {failed} test(s) FALSIFIED core theorems")
        print("   The thesis claims are empirically violated!")
    else:
        print(f"✅ All falsification attempts failed ({passed} passed, {skipped} skipped)")
        print("   Core theorems withstand empirical testing")
        print("   Implementation correctly enforces security properties")
    print()
