#!/usr/bin/env python3
"""
Computational Priced Sight Demonstration

This script provides a complete demonstration of priced computational sight
through formal mathematical artifacts that cannot be hand-waved away.

The demonstration shows:
1. No-hints structure discovery via MDL-based automatic model selection
2. Formal proof emission (DRAT/FRAT for UNSAT, certificates for SAT)
3. On-run verification with standard checkers
4. Cryptographic receipts for audit trails
5. µ-bit accounting for computational pricing

Usage:
    python scripts/priced_sight_demo.py              # Full demonstration
    python scripts/priced_sight_demo.py --blind      # Blind mode (commitments only)
    python scripts/priced_sight_demo.py --instances 5  # Custom instance count
"""

import sys
import json
from pathlib import Path

# Import our components
sys.path.append(str(Path(__file__).parent.parent))

from scripts.priced_sight_runner import PricedSightRunner
from demos.structure_discovery_nohints import generate_demo_instances


def print_header():
    """Print the demonstration header."""
    print("🎯 Computational Priced Sight Demonstration")
    print("=" * 60)
    print()
    print("This demonstration produces undeniable mathematical artifacts")
    print("showing that computational structure can be discovered and")
    print("priced without human hints, using formal proofs.")
    print()
    print("Key innovations:")
    print("• MDL-based automatic model selection (no hints required)")
    print("• Formal proof emission (DRAT/FRAT + certificates)")
    print("• On-run verification with standard SAT checkers")
    print("• Cryptographic receipts with SHA-256 commitments")
    print("• µ-bit accounting for computational pricing")
    print()


def print_technical_details():
    """Print technical implementation details."""
    print("🔧 Technical Implementation:")
    print("-" * 40)
    print("• Model Registry: Pluggable architecture for structure discovery")
    print("• MDL Scoring: Information-theoretic model selection")
    print("• Proof Systems: DRAT/FRAT emission with standard verification")
    print("• Cryptographic Receipts: SHA-256 hashes + Ed25519 signatures")
    print("• Thiele Machine VM: µ-bit accounting via MDLACC/PNEW instructions")
    print()


def run_demonstration(instances_count: int = 3, blind_mode: bool = False):
    """Run the complete computational priced sight demonstration."""

    print("🚀 Running Demonstration...")
    print("-" * 40)

    # Generate instances
    instances = generate_demo_instances(instances_count)
    print(f"Generated {len(instances)} unlabeled instances")

    # Run the priced sight demonstration
    runner = PricedSightRunner(timeout_seconds=60, blind_mode=blind_mode)
    result = runner.run_priced_sight(instances)

    # Show results
    receipt = result["receipt"]
    print()
    print("📊 Final Results:")
    print(f"   Instances processed: {receipt['summary']['total_instances']}")
    print(f"   Structures discovered: {len(receipt['summary']['models_discovered'])}")
    print(f"   Proofs emitted: {receipt['summary']['successful_proofs']}")
    print(f"   Receipt hash: {receipt['receipt_hash'][:32]}...")

    return result


def analyze_receipt(receipt_file: str):
    """Analyze and display receipt contents."""
    try:
        with open(receipt_file, 'r', encoding='utf-8') as f:
            receipt = json.load(f)

        print()
        print("🔍 Receipt Analysis:")
        print("-" * 40)

        for i, entry in enumerate(receipt['receipts'], 1):
            print(f"Instance {i}:")
            print(f"  Commitment: {entry['instance_commitment'][:16]}...")
            print(f"  Models tried: {len(entry['model_candidates'])}")
            print(f"  Selected: {entry['selected_model']}")
            print(f"  Proof emitted: {entry['proof_emitted']}")
            if entry['proof_emitted']:
                print(f"  Verification: {entry['verification_status']['verified']}")
            print()

        print("💡 Models discovered across all instances:")
        for model in receipt['summary']['models_discovered']:
            print(f"  • {model}")

    except FileNotFoundError:
        print(f"Receipt file {receipt_file} not found")


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Computational Priced Sight Demonstration")
    parser.add_argument("--instances", type=int, default=3,
                       help="Number of instances to process")
    parser.add_argument("--blind", action="store_true",
                       help="Run in blind mode")
    parser.add_argument("--analyze", type=str,
                       help="Analyze existing receipt file")

    args = parser.parse_args()

    print_header()

    if args.analyze:
        analyze_receipt(args.analyze)
        return 0

    print_technical_details()
    result = run_demonstration(args.instances, args.blind)

    # Save the receipt
    receipt_file = "outputs/priced_sight_receipt.json"
    with open(receipt_file, "w", encoding="utf-8") as f:
        json.dump(result["receipt"], f, indent=2)

    print(f"\n💾 Receipt saved to: {receipt_file}")

    # Analyze the generated receipt
    analyze_receipt(receipt_file)

    print()
    print("✨ Computational Priced Sight Complete!")
    print()
    print("This demonstration provides:")
    print("• Self-verifying mathematical artifacts (formal proofs)")
    print("• Automatic structure discovery without human hints")
    print("• Priced computation via µ-bit accounting")
    print("• Cryptographic audit trail for reproducibility")
    print()
    print("The artifacts in priced_sight_receipt.json cannot be hand-waved away.")
    print("They represent priced computational sight - the ability to")
    print("automatically discover and pay for revealing hidden structure.")

    return 0


if __name__ == "__main__":
    sys.exit(main())