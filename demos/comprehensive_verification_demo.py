#!/usr/bin/env python3
"""
Thiele Machine - COMPREHENSIVE LLM VERIFICATION DEMONSTRATION

This script demonstrates how the Thiele Machine verifies ALL types of LLM output:

1. MATHEMATICAL CLAIMS - Arithmetic, factorization, constants
2. FACTUAL CLAIMS - Known facts database + misinformation detection
3. FILE SYSTEM CLAIMS - File existence, code references
4. COMPARATIVE CLAIMS - Numeric comparisons
5. CODE CLAIMS - Syntax validation
6. FUTURE CLAIMS - Detects unverifiable predictions
7. UNVERIFIABLE - Marks conversational content appropriately

Run: python demos/comprehensive_verification_demo.py
"""

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.comprehensive_verify import (
    ComprehensiveVerifier,
    print_comprehensive_result,
)


def demo_category(verifier, title: str, tests: list):
    """Run a demo category."""
    print(f"\n\033[1;35m{'='*70}\033[0m")
    print(f"\033[1;35m  {title}\033[0m")
    print(f"\033[1;35m{'='*70}\033[0m")
    
    for label, text in tests:
        print(f"\n\033[1;33m{label}:\033[0m")
        print(f"  Input: {text}")
        result = verifier.verify_text(text)
        print_comprehensive_result(result, verbose=True)


def main():
    print("\033[1;36m")
    print("╔════════════════════════════════════════════════════════════════════╗")
    print("║     THIELE MACHINE - COMPREHENSIVE LLM VERIFICATION               ║")
    print("║                                                                    ║")
    print("║  Total verification of ALL LLM output types:                      ║")
    print("║  • Mathematical claims (arithmetic, constants, factorization)     ║")
    print("║  • Factual claims (capitals, creators, science facts)             ║")
    print("║  • Misinformation detection (flat earth, vaccines, etc)           ║")
    print("║  • File system verification (file exists, code refs)              ║")
    print("║  • Future claim detection (cannot verify predictions)             ║")
    print("║  • Code syntax validation                                         ║")
    print("║                                                                    ║")
    print("║  μ-cost economics: True=1.0μ, False=2.0μ (penalty for lies)       ║")
    print("╚════════════════════════════════════════════════════════════════════╝")
    print("\033[0m")
    
    verifier = ComprehensiveVerifier()
    
    # === Mathematical Claims ===
    demo_category(verifier, "MATHEMATICAL CLAIMS", [
        ("Arithmetic (correct)", "1+1=2"),
        ("Arithmetic (false)", "2+2=5"),
        ("Factorization", "77 = 7 × 11"),
        ("Power", "2^10 = 1024"),
        ("Constant (pi)", "pi = 3.14159"),
        ("Constant (false)", "pi = 4"),
    ])
    
    # === Factual Claims ===
    demo_category(verifier, "FACTUAL CLAIMS (Known Facts)", [
        ("Capital", "The capital of France is Paris"),
        ("Capital (Japan)", "The capital of Japan is Tokyo"),
        ("Creator", "Python was created by Guido van Rossum"),
        ("Creator (Linux)", "Linux was created by Linus Torvalds"),
        ("Science", "The earth is round"),
    ])
    
    # === Misinformation Detection ===
    demo_category(verifier, "MISINFORMATION DETECTION", [
        ("Flat Earth", "The earth is flat"),
        ("Vaccines", "Vaccines cause autism"),
        ("Moon Cheese", "The moon is made of cheese"),
        ("Great Wall", "The Great Wall is visible from space"),
        ("France Monarchy", "France has a queen"),
    ])
    
    # === Future Claims ===
    demo_category(verifier, "FUTURE CLAIMS (Unverifiable)", [
        ("Near future", "In 2030 AI will be sentient"),
        ("Far future", "By 2050 humans will live on Mars"),
    ])
    
    # === File System Claims ===
    demo_category(verifier, "FILE SYSTEM CLAIMS", [
        ("Exists (true)", "The file `thielecpu/vm.py` exists"),
        ("Exists (false)", "The file `nonexistent/fake.py` exists"),
    ])
    
    # === Comparative Claims ===
    demo_category(verifier, "COMPARATIVE CLAIMS", [
        ("Greater (true)", "5 > 3"),
        ("Greater (false)", "3 > 5"),
        ("Less (true)", "10 < 20"),
    ])
    
    # === Code Claims ===
    demo_category(verifier, "CODE CLAIMS", [
        ("Valid Python", "```python\ndef hello():\n    return 'world'\n```"),
        ("Invalid Python", "```python\ndef broken(\n```"),
    ])
    
    # === Conversational ===
    demo_category(verifier, "UNVERIFIABLE (Conversational)", [
        ("Question", "Can you help me with something?"),
        ("Greeting", "Hello world!"),
    ])
    
    # === Final Statistics ===
    print("\n\033[1;36m")
    print("╔════════════════════════════════════════════════════════════════════╗")
    print("║                    SESSION STATISTICS                              ║")
    print("╚════════════════════════════════════════════════════════════════════╝")
    print("\033[0m")
    
    stats = verifier.get_stats()
    print(f"  Total verifications: {stats['total_verifications']}")
    print(f"  Total claims analyzed: {stats['total_claims']}")
    print(f"  \033[32m✓ Verified:\033[0m {stats['verified']}")
    print(f"  \033[31m✗ Failed:\033[0m {stats['failed']}")
    print(f"  \033[33m○ Unverifiable:\033[0m {stats['unverifiable']}")
    print(f"  Verification rate: {stats['verification_rate']:.1%}")
    print(f"  Total μ consumed: {stats['total_mu_consumed']:.1f}")
    
    print("\n\033[1;36mThe Thiele Machine: Total Verification of ALL LLM Output\033[0m")
    print("\nUsage:")
    print("  python tools/verify_copilot.py --interactive    # Interactive mode")
    print("  python tools/verify_copilot.py \"claim text\"     # Direct verification")
    print()


if __name__ == "__main__":
    main()
