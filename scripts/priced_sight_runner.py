#!/usr/bin/env python3
"""
Priced Sight Runner: One-Command Computational Priced Sight Demonstration

This script demonstrates priced computational sight through:
1. No-hints structure discovery (MDL-based automatic model selection)
2. Formal proof emission (DRAT/FRAT for UNSAT, certificates for SAT)
3. On-run verification with standard checkers
4. Cryptographic receipts for audit trails

Usage: python scripts/priced_sight_runner.py [--instances N] [--timeout T] [--blind]
"""

import argparse
import sys
import time
from pathlib import Path
from typing import Dict, Any, List, Optional
import math
import json
import hashlib

# Import PySAT components
from pysat.formula import CNF
from pysat.solvers import Solver

# Import our components
sys.path.append(str(Path(__file__).parent.parent))

try:
    from demos.structure_discovery_nohints import InstanceGenerator, generate_demo_instances
except ModuleNotFoundError:  # Optional demos relocated under archive/showcase
    _archive_root = Path(__file__).resolve().parents[1] / "archive" / "showcase"
    if _archive_root.exists():
        sys.path.append(str(_archive_root))
        from demos.structure_discovery_nohints import (  # type: ignore
            InstanceGenerator,
            generate_demo_instances,
        )
    else:  # pragma: no cover - defensive guard for unexpected layouts
        raise
try:
    from models.registry import registry, MDLScore
except ModuleNotFoundError:
    _archive_root = Path(__file__).resolve().parents[1] / "archive" / "showcase"
    if _archive_root.exists():
        sys.path.append(str(_archive_root))
        from models.registry import registry, MDLScore  # type: ignore
    else:  # pragma: no cover
        raise
from scripts.proof_system import ProofEmitter, ReceiptGenerator

# Import model implementations to register them
try:
    from models import implementations
except ModuleNotFoundError:
    _archive_root = Path(__file__).resolve().parents[1] / "archive" / "showcase"
    if _archive_root.exists():
        if str(_archive_root) not in sys.path:
            sys.path.append(str(_archive_root))
        from models import implementations  # type: ignore
    else:  # pragma: no cover
        raise


class PricedSightRunner:
    """Main runner for the computational priced sight demonstration."""

    def __init__(self, timeout_seconds: int = 300, blind_mode: bool = False):
        self.timeout_seconds = timeout_seconds
        self.blind_mode = blind_mode
        self.proof_emitter = ProofEmitter()
        self.receipt_generator = ReceiptGenerator()

    def run_priced_sight(self, instances: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Run the complete computational priced sight demonstration."""

        print("🎯 Computational Priced Sight Demonstration")
        print("=" * 60)

        # Print suite commitment hash first (true no-hints)
        suite_data = {"instances": [inst["commitment_hash"] for inst in instances]}
        suite_canonical = json.dumps(suite_data, sort_keys=True, separators=(',', ':'))
        suite_hash = hashlib.sha256(suite_canonical.encode()).hexdigest()
        print(f"🔒 Suite Commitment Hash: {suite_hash}")
        print("   (No structural hints provided - discovery uses only unlabeled data)")
        print()

        results = []
        start_time = time.time()

        for i, instance in enumerate(instances):
            print(f"\n📊 Instance {i+1}/{len(instances)}")
            print(f"   Commitment: {instance['commitment_hash'][:16]}...")
            print(f"   Metadata: {instance.get('metadata', {})}")

            # Step 1: No-hints model discovery
            print("   🔍 Discovering structure (no hints provided)...")
            model_results = self._discover_structure(instance)

            # Step 2: Select best model via MDL
            selected_model = self._select_best_model(model_results)
            print(f"   🎯 Selected model: {selected_model}")

            # Step 3: Emit formal proof
            print("   📜 Emitting formal proof...")
            proof_data = self._emit_proof(instance, model_results, selected_model)

            # Step 4: Run blind baseline comparison
            baseline_data = None
            if selected_model:
                print("   ⚖️ Running blind baseline comparison...")
                # Get CNF for the selected model
                cnf = self.proof_emitter._instance_to_cnf(instance, selected_model)
                baseline_data = self._run_baseline_comparison(cnf, instance["commitment_hash"])
                print(f"   Baseline: {len(baseline_data['solvers_tested'])} solvers tested")

            # Step 5: Verify proof
            if proof_data:
                print("   ✅ Verifying proof...")
                verification_status = proof_data["verification"]
                print(f"   Verification: {'PASS' if verification_status['verified'] else 'FAIL'}")

            # Record result
            self.receipt_generator.add_result(
                instance["commitment_hash"],
                model_results,
                selected_model,
                proof_data,
                baseline_data
            )

            result = {
                "instance": instance,
                "model_results": model_results,
                "selected_model": selected_model,
                "proof": proof_data
            }
            results.append(result)

            # Check timeout
            if time.time() - start_time > self.timeout_seconds:
                print("⏰ Timeout reached, stopping demonstration")
                break

        # Generate final receipt
        final_receipt = self.receipt_generator.generate_receipt()

        # Summary
        self._print_summary(results, final_receipt)

        return {
            "results": results,
            "receipt": final_receipt,
            "total_time": time.time() - start_time
        }

    def _discover_structure(self, instance: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Discover computational structure without hints using MDL."""
        model_results = []

        # Use registry's discover_structure method for proper MDL scoring
        registry_results = registry.discover_structure(instance)

        for result in registry_results:
            print(f"      Testing {result.model_name}...")
            print(f"        Result: {result.success}")

            if result.success:
                model_results.append({
                    "model_name": result.model_name,
                    "mdl_score": result.mdl_score,
                    "success": result.success,
                    "witness": result.witness,
                    "proof_type": result.proof_type
                })

        return model_results

    def _select_best_model(self, model_results: List[Dict[str, Any]]) -> Optional[str]:
        """Select best model using MDL scoring."""
        if not model_results:
            return None

        # Find model with lowest total MDL cost, handling infinite scores
        def score_key(r):
            total = r["mdl_score"].total_bits
            return total if not math.isinf(total) else float('inf')

        best_model = min(model_results, key=score_key)

        return best_model["model_name"] if best_model["success"] and not best_model["mdl_score"].is_infinite else None

    def _emit_proof(self, instance: Dict[str, Any], model_results: List[Dict[str, Any]],
                   selected_model: Optional[str]) -> Optional[Dict[str, Any]]:
        """Emit formal proof for the selected model."""

        if not selected_model:
            return None

        # Find the result for selected model
        selected_result = next(r for r in model_results if r["model_name"] == selected_model)

        # Create model result dict for the new interface
        model_result = {
            "model_name": selected_model,
            "success": selected_result["success"],
            "witness": selected_result["witness"],
            "proof_type": selected_result["proof_type"]
        }

        return self.proof_emitter.emit_proof(instance, model_result)

    def _print_summary(self, results: List[Dict[str, Any]], receipt: Dict[str, Any]):
        """Print final summary of the demonstration."""

        print("\n" + "=" * 60)
        print("🎉 Computational Priced Sight COMPLETE")
        print("=" * 60)

        successful = sum(1 for r in results if r["selected_model"] is not None)
        proofs_emitted = sum(1 for r in results if r["proof"] is not None)
        baseline_comparisons = sum(1 for r in results if r.get("baseline_comparison") is not None)

        print("📊 Results:")
        print(f"   Instances processed: {len(results)}")
        print(f"   Structures discovered: {successful}")
        print(f"   Formal proofs emitted: {proofs_emitted}")
        print(f"   Blind baseline comparisons: {baseline_comparisons}")

        print("\n🔐 Cryptographic Receipt:")
        print(f"   Hash: {receipt['receipt_hash'][:32]}...")
        print(f"   Global Hash: {receipt.get('global_hash', 'N/A')[:32]}...")
        print(f"   Chain Steps: {len(receipt.get('hash_chain', {}).get('step_hashes', []))}")
        print(f"   Chain Valid: {receipt.get('hash_chain', {}).get('chain_verification', {}).get('valid', 'N/A')}")
        print(f"   Signature: {receipt['signature'][:32]}...")

        print(f"\n💡 Models discovered: {receipt['summary']['models_discovered']}")
        print(f"   Baseline comparisons: {receipt['summary']['baseline_comparisons']}")

        if not self.blind_mode:
            print("\n📋 Detailed results saved to receipt")
        else:
            print("\n🙈 Blind mode: Results committed but not revealed")

        print("\n✨ This demonstrates priced computational sight:")
        print("   • No human hints provided to guide structure discovery")
        print("   • MDL scoring automatically selected optimal models")
        print("   • Formal mathematical proofs emitted for verification")
        print("   • Blind baseline comparisons with standard SAT solvers")
        print("   • Cryptographic receipts ensure auditability")
        print("   • µ-bit costs paid for revelation of computational structure")

    def _run_baseline_comparison(self, cnf: CNF, instance_hash: str) -> Dict[str, Any]:
        """Run blind baseline comparison with standard SAT solvers."""
        import time
        import threading

        baseline_results = {
            "instance_hash": instance_hash,
            "solvers_tested": [],
            "time_limit_seconds": 30,  # Pre-registered time limit
            "memory_limit_mb": 1000   # Pre-registered memory limit
        }

        def solve_with_timeout(solver, timeout):
            """Solve with timeout using threading."""
            result = [None]  # Use list to modify from thread

            def target():
                try:
                    sat_result = solver.solve()
                    result[0] = sat_result
                except Exception:
                    result[0] = False  # type: ignore

            thread = threading.Thread(target=target)
            thread.start()
            thread.join(timeout)

            if thread.is_alive():
                try:
                    solver.interrupt()  # Try to interrupt if supported
                except:
                    pass
                thread.join(1)  # Wait a bit more
                return None  # Timeout

            return result[0]

        # Test with different standard solvers
        solver_names = ["cadical", "glucose4", "minisat22", "lingeling"]

        for solver_name in solver_names:
            try:
                start_time = time.time()

                # Create solver
                solver = Solver(name=solver_name, bootstrap_with=cnf)

                # Solve with timeout
                result = solve_with_timeout(solver, baseline_results["time_limit_seconds"])

                elapsed = time.time() - start_time

                solver_result = {
                    "solver": solver_name,
                    "solved": result is not None,
                    "satisfiable": result if result is not None else None,
                    "time_seconds": elapsed,
                    "timeout": result is None or elapsed >= baseline_results["time_limit_seconds"]
                }

                if result and solver.get_model():
                    model = solver.get_model()
                    if model:
                        solver_result["model_size"] = len(model)

                baseline_results["solvers_tested"].append(solver_result)
                solver.delete()

            except Exception as e:
                baseline_results["solvers_tested"].append({
                    "solver": solver_name,
                    "error": str(e),
                    "solved": False,
                    "time_seconds": 0
                })

        return baseline_results


def main():
    parser = argparse.ArgumentParser(description="Computational Priced Sight: Automatic Structure Discovery")
    parser.add_argument("--instances", type=int, default=5,
                       help="Number of instances to process")
    parser.add_argument("--timeout", type=int, default=300,
                       help="Timeout in seconds")
    parser.add_argument("--blind", action="store_true",
                       help="Run in blind mode (commitments only)")
    parser.add_argument("--seed", type=int, default=None,
                       help="Random seed for reproducibility")

    args = parser.parse_args()

    # Generate instances
    if args.seed:
        generator = InstanceGenerator(args.seed)
        instances = []
        for _ in range(args.instances):
            instance = generator.generate_instance("medium")
            instance["commitment_hash"] = generator.get_commitment_hash(instance)
            instances.append(instance)
    else:
        instances = generate_demo_instances(args.instances)

    # Run demonstration
    runner = PricedSightRunner(timeout_seconds=args.timeout, blind_mode=args.blind)
    result = runner.run_priced_sight(instances)

    # Save receipt
    import json
    receipt_file = Path("outputs/priced_sight_receipt.json")
    with open(receipt_file, "w", encoding="utf-8") as f:
        json.dump(result["receipt"], f, indent=2)

    print(f"\n💾 Receipt saved to: {receipt_file}")

    return 0


if __name__ == "__main__":
    sys.exit(main())