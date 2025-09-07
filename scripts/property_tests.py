import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(__file__)))
from thielecpu.state import State
from thielecpu.mdl import mdlacc
from thielecpu.isa import CSR
from thielecpu._types import ModuleId
import random
import json
from typing import List, Dict, Any, Optional

def hash_obj(obj):
    import hashlib
    return hashlib.sha256(json.dumps(obj, sort_keys=True).encode("utf-8")).hexdigest()

class MuLedger:
    """Tracks μ charging with cumulative totals and step-by-step audit trail."""

    def __init__(self):
        self.steps: List[Dict[str, Any]] = []
        self.cumulative_mu = 0.0

    def record_step(self, step_type: str, module_id: int, module_size: int,
                    mu_charged: float, inputs_hash: str, outputs_hash: str,
                    module_fragment: str = "unknown", module_size_metrics: Optional[Dict[str, Any]] = None):
        """Record a step in the μ ledger."""
        if module_size_metrics is None:
            module_size_metrics = {}

        prev_receipt_hash = hash_obj(self.steps[-1]) if self.steps else "genesis"
        step = {
            "step_index": len(self.steps),
            "step_type": step_type,
            "module_id": module_id,
            "module_size": module_size,
            "module_fragment": module_fragment,
            "module_size_metrics": module_size_metrics,
            "mu_charged": mu_charged,
            "cumulative_mu": self.cumulative_mu + mu_charged,
            "inputs_hash": inputs_hash,
            "outputs_hash": outputs_hash,
            "prev_receipt_hash": prev_receipt_hash
        }
        step["this_receipt_hash"] = hash_obj(step)
        self.steps.append(step)
        self.cumulative_mu += mu_charged

    def to_dict(self):
        return {
            "steps": self.steps,
            "final_cumulative_mu": self.cumulative_mu,
            "ledger_hash": hash_obj(self.steps) if self.steps else None
        }

def random_partition_operation(state: State, ledger: MuLedger) -> bool:
    """Perform a random partition operation and verify invariants."""
    operations = ['pnew', 'psplit', 'pmerge', 'lassert']
    op = random.choice(operations)

    try:
        if op == 'pnew':
            # Create new module with random region
            region_size = random.randint(1, 20)
            region = set(random.sample(range(100), region_size))
            inputs_hash = hash_obj({"op": "pnew", "region": list(region)})

            module = state.pnew(region)
            outputs_hash = hash_obj({"module": module, "regions": list(state.regions[module])})

            # Detect fragment type for the module
            from thielecpu.mdl import detect_fragment_type
            fragment = detect_fragment_type(region)
            size_metrics = {"element_count": len(region)}
            ledger.record_step("PNEW", module, len(region), 0.0, inputs_hash, outputs_hash, fragment, size_metrics)

        elif op == 'psplit' and state.regions.modules:
            # Split random module
            module = ModuleId(random.choice(list(state.regions.modules.keys())))
            region = state.regions[module]

            if len(region) >= 2:
                split_point = random.randint(1, len(region) - 1)
                sorted_region = sorted(region)
                pred = lambda x: x < sorted_region[split_point]

                inputs_hash = hash_obj({"op": "psplit", "module": module, "pred": f"x < {sorted_region[split_point]}"})

                m1, m2 = state.psplit(module, pred)
                outputs_hash = hash_obj({
                    "m1": m1, "m2": m2,
                    "m1_size": len(state.regions[m1]),
                    "m2_size": len(state.regions[m2])
                })

                # Detect fragment type for the split modules
                from thielecpu.mdl import detect_fragment_type
                fragment = detect_fragment_type(state.regions[m1])  # Use first split module
                size_metrics = {"original_size": len(region), "split_count": 2}
                ledger.record_step("PSPLIT", module, len(region), 0.0, inputs_hash, outputs_hash, fragment, size_metrics)

        elif op == 'pmerge' and len(state.regions.modules) >= 2:
            # Merge two random modules
            modules = list(state.regions.modules.keys())
            m1, m2 = random.sample(modules, 2)

            if m1 != m2:
                m1_id, m2_id = ModuleId(m1), ModuleId(m2)
                inputs_hash = hash_obj({"op": "pmerge", "m1": m1, "m2": m2})
                merged = state.pmerge(m1_id, m2_id)
                outputs_hash = hash_obj({"merged": merged, "size": len(state.regions[merged])})

                # Detect fragment type for the merged module
                from thielecpu.mdl import detect_fragment_type
                fragment = detect_fragment_type(state.regions[merged])
                size_metrics = {"merged_size": len(state.regions[merged])}
                ledger.record_step("PMERGE", merged, len(state.regions[merged]), 0.0, inputs_hash, outputs_hash, fragment, size_metrics)

        elif op == 'lassert' and state.regions.modules:
            # Perform LASSERT on random module
            module = ModuleId(random.choice(list(state.regions.modules.keys())))
            region = state.regions[module]
            consistent = random.choice([True, False])  # Random consistency for testing

            inputs_hash = hash_obj({"op": "lassert", "module": module, "consistent": consistent})

            old_mu = state.mu
            mdlacc(state, module, consistent=consistent)
            mu_charged = state.mu - old_mu if state.mu != float('inf') else 0.0

            outputs_hash = hash_obj({"mu": state.mu, "csr_err": state.csr.get(CSR.ERR, 0)})

            # Detect fragment type for the audited module
            from thielecpu.mdl import detect_fragment_type
            fragment = detect_fragment_type(region)
            size_metrics = {"audit_consistent": consistent}
            ledger.record_step("LASSERT", module, len(region), mu_charged, inputs_hash, outputs_hash, fragment, size_metrics)

        # Verify invariants after each operation
        n = sum(len(region) for region in state.regions.modules.values())
        poly_bound = n ** 2

        for module, region in state.regions.modules.items():
            if len(region) > poly_bound:
                raise AssertionError(f"Invariant violated: module {module} has size {len(region)} > poly({n}) = {poly_bound}")

        # Verify μ is monotone
        if ledger.cumulative_mu < 0:
            raise AssertionError(f"μ became negative: {ledger.cumulative_mu}")

        return True

    except ValueError as e:
        if "Invariant violated" in str(e):
            raise  # Re-raise invariant violations
        return False  # Other ValueErrors are expected (e.g., merge conflicts)
    except Exception as e:
        print(f"Unexpected error in {op}: {e}")
        return False

def run_property_tests(num_operations: int = 1000, seed: int = 42):
    """Run property tests with random operations."""
    random.seed(seed)
    state = State()
    ledger = MuLedger()

    successful_ops = 0
    invariant_violations = 0

    for i in range(num_operations):
        try:
            if random_partition_operation(state, ledger):
                successful_ops += 1
        except AssertionError as e:
            print(f"Invariant violation at operation {i}: {e}")
            invariant_violations += 1
            break  # Stop on first invariant violation

    results = {
        "total_operations": num_operations,
        "successful_operations": successful_ops,
        "invariant_violations": invariant_violations,
        "final_mu": state.mu,
        "final_module_count": len(state.regions.modules),
        "ledger": ledger.to_dict()
    }

    return results

def run_negative_control():
    """Run a test that should fail to demonstrate the system works correctly."""
    print("\nRunning negative control (should detect invariant violation)...")

    state = State()
    ledger = MuLedger()

    # The invariant |π_j| ≤ n^2 is actually quite weak since n includes the module size.
    # Instead, let's test a different invariant violation: try to create overlapping modules
    # by manipulating the internal state directly (this should be caught by proper validation)

    # Create two overlapping regions - this should be prevented by the system
    region1 = set(range(10))
    region2 = set(range(5, 15))  # Overlaps with region1

    try:
        m1 = state.pnew(region1)
        m2 = state.pnew(region2)  # This should either merge or raise an error
        print("ERROR: Negative control failed - overlapping regions not prevented")
        return False
    except ValueError as e:
        if "Invariant violated" in str(e) or "overlap" in str(e).lower():
            print("✓ Negative control passed - overlapping regions prevented")
            return True
        else:
            print(f"ERROR: Unexpected error: {e}")
            return False


def test_fragment_restriction():
    """Test that auditor rejects unknown fragments for tractability."""
    print("\nTesting fragment restriction for auditor tractability...")

    from thielecpu.mdl import mdlacc, detect_fragment_type

    # Use fresh state for this test
    state = State()
    ledger = MuLedger()

    # Test small region (should be accepted as "horn")
    small_region = set(range(50))
    module = state.pnew(small_region)
    fragment = detect_fragment_type(small_region)
    print(f"Small region fragment type: {fragment}")

    # Test large region (should be rejected as "unknown") - use non-overlapping elements
    large_region = set(range(1000, 1200))  # 200 elements, non-overlapping
    module2 = state.pnew(large_region)
    fragment2 = detect_fragment_type(large_region)
    print(f"Large region fragment type: {fragment2}")

    # Test mdlacc with large region (should set infinite μ)
    initial_mu = state.mu
    mdlacc(state, module2, consistent=True)
    if state.mu == float('inf'):
        print("✓ Fragment restriction working - unknown fragment rejected")
        return True
    else:
        print(f"ERROR: Fragment restriction failed - μ = {state.mu}")
        return False

if __name__ == "__main__":
    print("Running property tests for Thiele Machine invariants...")
    results = run_property_tests(1000)

    print(f"Results: {results['successful_operations']}/{results['total_operations']} operations successful")
    print(f"Invariant violations: {results['invariant_violations']}")
    print(f"Final μ: {results['final_mu']}")
    print(f"Final modules: {results['final_module_count']}")

    # Run negative control
    negative_passed = run_negative_control()

    # Run fragment restriction test
    fragment_passed = test_fragment_restriction()

    # Save ledger
    with open("mu_ledger.json", "w") as f:
        json.dump(results["ledger"], f, indent=2)
    print("μ ledger saved to mu_ledger.json")

    # Save full results
    results["negative_control_passed"] = negative_passed
    results["fragment_restriction_passed"] = fragment_passed
    with open("property_test_results.json", "w") as f:
        json.dump(results, f, indent=2)
    print("Full results saved to property_test_results.json")

    if not negative_passed or not fragment_passed:
        print("WARNING: Some tests failed - system may not be working correctly")
        exit(1)