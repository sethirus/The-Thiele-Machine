#!/usr/bin/env python3
"""
Thiele Machine - HONEST Structural LLM Output Verification for VS Code

This script provides STRUCTURAL verification of Copilot outputs following
the Thiele Machine thesis principles.

**WHAT WE CAN VERIFY (Structural/Computational):**
- Mathematical claims: 1+1=2, 15=3×5 (we COMPUTE the answer)
- Code syntax: Python/JS (we PARSE the AST)
- Code execution: Does it run? (we EXECUTE it)
- File claims: Does file exist? (we CHECK the filesystem)
- Import claims: Can we import it? (we TRY the import)
- Logical claims: SAT/SMT (we use SOLVER)

**WHAT WE CANNOT VERIFY WITHOUT EXTERNAL ORACLE:**
- Factual claims about the world ("Capital of France is Paris")
- Scientific claims ("Earth is round")
- Historical claims ("WWII ended in 1945")
- Future predictions

The Thiele Machine is HONEST about what requires external verification.
μ-cost tracks computational work - no computation = no cost.

USAGE:
    # Interactive mode (recommended)
    python tools/verify_copilot.py --interactive
    
    # Verify a claim
    python tools/verify_copilot.py "15 = 3 × 5"
    
    # Verify file exists
    python tools/verify_copilot.py --file-exists thielecpu/vm.py
"""

import argparse
import json
import sys
from pathlib import Path

# Add repo root
REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from thielecpu.structural_verify import (
    StructuralVerifier,
    StructuralResult,
    print_structural_result,
    VerificationCategory,
)


def print_banner():
    """Print the verification banner."""
    print("\033[1;36m")
    print("╔════════════════════════════════════════════════════════════════╗")
    print("║       THIELE MACHINE - STRUCTURAL VERIFICATION                ║")
    print("║                                                                ║")
    print("║  We verify what we can COMPUTE. We're honest about what we    ║")
    print("║  can't verify without external oracles (web, databases).      ║")
    print("╚════════════════════════════════════════════════════════════════╝")
    print("\033[0m")


def verify_text(text: str, verifier: StructuralVerifier, verbose: bool = True):
    """Verify text and print results."""
    print(f"\n\033[90mAnalyzing: {text[:80]}{'...' if len(text) > 80 else ''}\033[0m")
    result = verifier.verify_text(text)
    print_structural_result(result, verbose)
    return result


def interactive_mode(verifier: StructuralVerifier):
    """Run in interactive mode for real-time verification."""
    print_banner()
    print("\033[1mHonest Structural Verification Mode\033[0m")
    print()
    print("VERIFIABLE (we compute):  Math, code syntax, file existence, imports")
    print("NEEDS ORACLE (external):  Real-world facts, science, history")
    print("UNVERIFIABLE:             Opinions, questions, future predictions")
    print()
    print("Commands: :file <path>, :import <mod>, :run <code>, :stats, :quit")
    print()
    
    while True:
        try:
            text = input("\033[1;36mVerify>\033[0m ")
            if text.lower() in ("quit", "exit", "q", ":quit", ":q"):
                # Print final stats
                stats = verifier.get_stats()
                print(f"\n\033[1mSession Statistics:\033[0m")
                print(f"  Total claims: {stats['total_claims']}")
                print(f"  Structurally verified: {stats['structurally_verified']}")
                print(f"  Structurally failed: {stats['structurally_failed']}")
                print(f"  Requires external: {stats['requires_external_oracle']}")
                print(f"  μ consumed: {stats['total_mu_consumed']:.1f}")
                break
            if not text.strip():
                continue
            
            # Handle special commands
            if text.startswith(":file "):
                path = text[6:].strip()
                result = verifier.verify_text(f"The file `{path}` exists")
                print_structural_result(result)
            elif text.startswith(":import "):
                module = text[8:].strip()
                try:
                    __import__(module)
                    print(f"  \033[32m✓\033[0m Import: {module} is available (VERIFIED)")
                except ImportError as e:
                    print(f"  \033[31m✗\033[0m Import: {module} - {e} (FAILED)")
            elif text.startswith(":run "):
                code = text[5:]
                try:
                    result = eval(code)
                    print(f"  \033[32m✓\033[0m Result: {result} (COMPUTED)")
                except Exception as e:
                    print(f"  \033[31m✗\033[0m Error: {e}")
            elif text.startswith(":stats"):
                stats = verifier.get_stats()
                print(f"\n\033[1mSession Statistics:\033[0m")
                print(f"  Total claims: {stats['total_claims']}")
                print(f"  Structurally verified: {stats['structurally_verified']}")
                print(f"  Structurally failed: {stats['structurally_failed']}")
                print(f"  Requires external: {stats['requires_external_oracle']}")
                print(f"  Unverifiable: {stats['unverifiable']}")
                print(f"  μ consumed: {stats['total_mu_consumed']:.1f}")
            elif text.startswith(":help"):
                print("\nCommands:")
                print("  :file <path>   - Verify file exists (STRUCTURAL)")
                print("  :import <mod>  - Verify import available (STRUCTURAL)")
                print("  :run <expr>    - Evaluate Python expression (STRUCTURAL)")
                print("  :stats         - Show session statistics")
                print("  :quit          - Exit")
                print("\nOr type any text to analyze claims.")
                print("\nClaim types:")
                print("  ✓ Math, code, files, imports = STRUCTURALLY VERIFIABLE")
                print("  ? Facts about world = NEEDS EXTERNAL ORACLE")
                print("  ○ Opinions, questions = UNVERIFIABLE")
            else:
                verify_text(text, verifier, verbose=True)
                
        except (KeyboardInterrupt, EOFError):
            print("\nExiting...")
            break


def main():
    parser = argparse.ArgumentParser(
        description="Thiele Machine - Honest Structural Verification",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("text", nargs="*", help="Text to verify")
    parser.add_argument("--file", "-f", help="File containing text to verify")
    parser.add_argument("--file-exists", help="Verify file exists")
    parser.add_argument("--import", dest="import_module", help="Verify import is valid")
    parser.add_argument("--interactive", "-i", action="store_true", help="Interactive mode")
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    
    args = parser.parse_args()
    
    verifier = StructuralVerifier()
    
    if args.interactive:
        interactive_mode(verifier)
        return
    
    # Direct verification commands
    if args.file_exists:
        result = verifier.verify_text(f"The file `{args.file_exists}` exists")
        if args.json:
            print(json.dumps(result.to_dict(), indent=2))
        else:
            print_structural_result(result)
        return
    
    if args.import_module:
        try:
            __import__(args.import_module)
            print(f"✓ Import: {args.import_module} is available (STRUCTURALLY VERIFIED)")
        except ImportError as e:
            print(f"✗ Import: {args.import_module} - {e} (FAILED)")
        return
    
    # Collect text to verify
    text = None
    
    if args.text:
        text = " ".join(args.text)
    elif args.file:
        text = Path(args.file).read_text()
    elif not sys.stdin.isatty():
        text = sys.stdin.read()
    
    if not text:
        parser.print_help()
        sys.exit(1)
    
    if not args.json:
        print_banner()
    
    result = verifier.verify_text(text)
    
    if args.json:
        print(json.dumps(result.to_dict(), indent=2))
    else:
        print_structural_result(result, args.verbose or True)


if __name__ == "__main__":
    main()
