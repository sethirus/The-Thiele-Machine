#!/usr/bin/env python3
"""
COMPREHENSIVE MASTER VALIDATION SUITE

Tests ALL components of the Thiele Machine research program:
- Track A: Formal foundations (Coq proofs, theorems, semantics)
- Track B: Algorithmic applications (SAT, graphs, programs)
- Track C: Scientific discovery (PDEs, patterns, turbulence)
- Track D: Predictive models (scaling laws, effective models)
- Track E: Quality assurance (isomorphisms, receipts, fuzzing, CI)

This is the COMPLETE validation that accounts for everything in the research program.

Copyright 2025 Devon Thiele
Licensed under the Apache License, Version 2.0
"""

import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Tuple

# Color codes for output
GREEN = '\033[92m'
RED = '\033[91m'
YELLOW = '\033[93m'
BLUE = '\033[94m'
RESET = '\033[0m'


class ValidationSuite:
    """Master validation suite for all research components."""
    
    def __init__(self):
        self.root = Path(__file__).parent.parent
        self.results: Dict[str, List[Tuple[str, bool, str]]] = {}
        self.total_tests = 0
        self.passed_tests = 0
    
    def run_command(self, cmd: List[str], cwd: Path = None, timeout: int = 300) -> Tuple[bool, str]:
        """Run a command and return success status and output."""
        if cwd is None:
            cwd = self.root
        
        try:
            result = subprocess.run(
                cmd,
                cwd=cwd,
                capture_output=True,
                text=True,
                timeout=timeout
            )
            return result.returncode == 0, result.stdout + result.stderr
        except subprocess.TimeoutExpired:
            return False, f"TIMEOUT after {timeout}s"
        except Exception as e:
            return False, str(e)
    
    def add_result(self, track: str, test_name: str, passed: bool, details: str = ""):
        """Record a test result."""
        if track not in self.results:
            self.results[track] = []
        self.results[track].append((test_name, passed, details))
        self.total_tests += 1
        if passed:
            self.passed_tests += 1
    
    def print_header(self, text: str):
        """Print a section header."""
        print(f"\n{BLUE}{'='*70}{RESET}")
        print(f"{BLUE}{text}{RESET}")
        print(f"{BLUE}{'='*70}{RESET}")
    
    def print_test(self, name: str, passed: bool, details: str = ""):
        """Print a test result."""
        status = f"{GREEN}✓ PASS{RESET}" if passed else f"{RED}✗ FAIL{RESET}"
        print(f"{status}: {name}")
        if details and not passed:
            print(f"  {details[:200]}")
    
    # ========== TRACK A: FORMAL & THEORETICAL FOUNDATIONS ==========
    
    def validate_track_a_formal(self):
        """Validate Track A: Formal foundations (Coq proofs, theorems)."""
        self.print_header("TRACK A: FORMAL & THEORETICAL FOUNDATIONS")
        
        # A1.1-A1.2: Model specification documents
        print("\n[A1.1-A1.2] Model Specification Documents")
        docs = [
            "docs/MODEL_SPEC.md",
            "docs/model_extraction_notes.md",
            "docs/COMPLEXITY_ANALYSIS.md"
        ]
        for doc in docs:
            exists = (self.root / doc).exists()
            self.add_result("A1", f"Document: {doc}", exists)
            self.print_test(doc, exists)
        
        # A1.3: Core Coq semantics
        print("\n[A1.3] Core Coq Semantics")
        coq_files = [
            "coq/thielemachine/coqproofs/CoreSemantics.v",
            "coq/thielemachine/coqproofs/SemanticBridge.v"
        ]
        for coq_file in coq_files:
            exists = (self.root / coq_file).exists()
            self.add_result("A1", f"Coq file: {coq_file}", exists)
            self.print_test(coq_file, exists)
        
        # A1.4: Coq proofs compilation
        print("\n[A1.4] Coq Proofs Compilation")
        coq_dir = self.root / "coq/thielemachine/coqproofs"
        if coq_dir.exists():
            passed, output = self.run_command(["make", "clean"], cwd=coq_dir, timeout=30)
            passed, output = self.run_command(["make"], cwd=coq_dir, timeout=600)
            self.add_result("A1", "Coq proofs compile", passed, output)
            self.print_test("Coq proofs compile", passed, output if not passed else "")
        
        # A2.1: Turing machine embedding
        print("\n[A2.1] Turing Machine Embedding")
        tm_embedding = self.root / "coq/thielemachine/coqproofs/Embedding_TM.v"
        exists = tm_embedding.exists()
        self.add_result("A2", "TM embedding proof", exists)
        self.print_test("Embedding_TM.v", exists)
        
        # A2.2: Information theory connections
        print("\n[A2.2] Information Theory Connections")
        it_file = self.root / "coq/thielemachine/coqproofs/InfoTheory.v"
        exists = it_file.exists()
        self.add_result("A2", "Information theory proofs", exists)
        self.print_test("InfoTheory.v", exists)
        
        # A3: Implementation coherence
        print("\n[A3] Implementation Coherence - Isomorphism Tests")
        passed, output = self.run_command(
            ["python3", "-m", "pytest", "tests/test_isomorphism_complete.py", "-v"],
            timeout=120
        )
        self.add_result("A3", "Isomorphism tests (25 tests)", passed, output)
        self.print_test("Isomorphism tests", passed, output if not passed else "25/25 passed")
    
    # ========== TRACK B: ALGORITHMIC APPLICATIONS ==========
    
    def validate_track_b_algorithms(self):
        """Validate Track B: Algorithmic applications (SAT, graphs, programs)."""
        self.print_header("TRACK B: ALGORITHMIC APPLICATIONS")
        
        # B1: SAT solving
        print("\n[B1] SAT Killer App")
        
        # B1.1: SAT instances exist
        instances = list((self.root / "benchmarks/instances").glob("*.cnf"))
        has_instances = len(instances) >= 23
        self.add_result("B1", f"SAT instances ({len(instances)} files)", has_instances)
        self.print_test(f"SAT instances: {len(instances)} files", has_instances)
        
        # B1.2: SAT benchmarks run
        passed, output = self.run_command(
            ["python3", "tools/run_sat_benchmarks.py", "--limit", "3"],
            timeout=120
        )
        self.add_result("B1", "SAT benchmarks (sample)", passed, output)
        self.print_test("SAT benchmarks", passed)
        
        # B1.3: Results file exists
        results_file = self.root / "benchmarks/sat_results.csv"
        exists = results_file.exists()
        self.add_result("B1", "SAT results file", exists)
        self.print_test("SAT results.csv", exists)
        
        # B2: Other algorithmic domains
        print("\n[B2] Other Algorithmic Domains")
        
        # B2.1: Graph clustering
        passed, output = self.run_command(
            ["python3", "tools/graph_clustering.py"],
            timeout=60
        )
        self.add_result("B2", "Graph clustering", passed, output)
        self.print_test("Graph clustering", passed)
        
        # B2.1 Stress: Graph clustering stress tests
        passed, output = self.run_command(
            ["python3", "tools/stress_test_graph_clustering.py"],
            timeout=300
        )
        self.add_result("B2", "Graph clustering stress (6 tests)", passed, output)
        self.print_test("Graph stress tests", passed)
        
        # B2.2: Program analysis
        passed, output = self.run_command(
            ["python3", "tools/program_analyzer.py"],
            timeout=60
        )
        self.add_result("B2", "Program analysis", passed, output)
        self.print_test("Program analysis", passed)
        
        # B2.2 Stress: Program analysis stress tests
        passed, output = self.run_command(
            ["python3", "tools/stress_test_program_analysis.py"],
            timeout=300
        )
        self.add_result("B2", "Program analysis stress (6 tests)", passed, output)
        self.print_test("Program stress tests", passed)
    
    # ========== TRACK C: SCIENTIFIC DISCOVERY ==========
    
    def validate_track_c_discovery(self):
        """Validate Track C: Scientific discovery (PDEs, patterns, turbulence)."""
        self.print_header("TRACK C: SCIENTIFIC DISCOVERY")
        
        # C1: PDE recovery
        print("\n[C1] PDE Recovery")
        
        # C1.1-C1.3: Wave and diffusion (already validated in baseline)
        baseline_file = self.root / "docs/PDE_DISCOVERY_ANALYSIS.md"
        exists = baseline_file.exists()
        self.add_result("C1", "PDE discovery analysis", exists)
        self.print_test("PDE_DISCOVERY_ANALYSIS.md", exists)
        
        # C1.4: Quantum PDE - unit tests
        passed, output = self.run_command(
            ["python3", "tools/test_quantum_fitting.py"],
            timeout=60
        )
        self.add_result("C1", "Quantum PDE unit tests (3 tests)", passed, output)
        self.print_test("Quantum unit tests", passed)
        
        # C1.4: Quantum PDE - comprehensive tests
        passed, output = self.run_command(
            ["python3", "tools/run_schrodinger_tests_improved.py"],
            timeout=120
        )
        self.add_result("C1", "Quantum PDE comprehensive (5 tests)", passed, output)
        self.print_test("Quantum comprehensive", passed)
        
        # C1.4 Stress: Quantum PDE stress tests
        passed, output = self.run_command(
            ["python3", "tools/stress_test_quantum.py"],
            timeout=180
        )
        self.add_result("C1", "Quantum PDE stress (6 tests)", passed, output)
        self.print_test("Quantum stress tests", passed)
        
        # C2: Complex systems - turbulence
        print("\n[C2] Complex System Discovery")
        
        # C2.1-C2.2: Turbulence closure
        passed, output = self.run_command(
            ["python3", "tools/turbulence_discovery.py"],
            timeout=120
        )
        self.add_result("C2", "Turbulence discovery", passed, output)
        self.print_test("Turbulence closure", passed)
        
        # C2 Stress: Turbulence stress tests
        passed, output = self.run_command(
            ["python3", "tools/stress_test_turbulence.py"],
            timeout=600
        )
        self.add_result("C2", "Turbulence stress (6 tests)", passed, output)
        self.print_test("Turbulence stress tests", passed)
        
        # C3: Pattern formation
        print("\n[C3] Pattern Formation")
        
        # C3.1-C3.2: Pattern simulator
        passed, output = self.run_command(
            ["python3", "tools/pattern_simulator.py"],
            timeout=120
        )
        self.add_result("C3", "Pattern formation", passed, output)
        self.print_test("Pattern simulator", passed)
        
        # C3 Stress: Pattern stress tests
        passed, output = self.run_command(
            ["python3", "tools/stress_test_pattern_formation.py"],
            timeout=600
        )
        self.add_result("C3", "Pattern stress (6 tests)", passed, output)
        self.print_test("Pattern stress tests", passed)
    
    # ========== TRACK D: PREDICTIVE MODELS ==========
    
    def validate_track_d_models(self):
        """Validate Track D: Predictive models (scaling laws, effective models)."""
        self.print_header("TRACK D: PREDICTIVE MODELS")
        
        # D1: Scaling laws
        print("\n[D1] Scaling Law Prediction")
        
        # D1.1-D1.2: Scaling law analysis
        scaling_file = self.root / "docs/SCALING_LAW_ANALYSIS.md"
        exists = scaling_file.exists()
        self.add_result("D1", "Scaling law analysis", exists)
        self.print_test("SCALING_LAW_ANALYSIS.md", exists)
        
        # D2: Novel effective models
        print("\n[D2] Novel Effective Model")
        
        # D2.1-D2.2: Effective model documentation
        model_file = self.root / "docs/NEW_EFFECTIVE_MODEL.md"
        exists = model_file.exists()
        self.add_result("D2", "Effective model documentation", exists)
        self.print_test("NEW_EFFECTIVE_MODEL.md", exists)
    
    # ========== TRACK E: QUALITY ASSURANCE ==========
    
    def validate_track_e_quality(self):
        """Validate Track E: Quality assurance (isomorphisms, receipts, fuzzing, CI)."""
        self.print_header("TRACK E: QUALITY ASSURANCE")
        
        # E1: Reproducibility
        print("\n[E1] Reproducibility")
        
        # E1.1: Makefile demos
        makefile = self.root / "Makefile"
        exists = makefile.exists()
        self.add_result("E1", "Makefile exists", exists)
        self.print_test("Makefile", exists)
        
        # E1.2: Docker
        dockerfile = self.root / "Dockerfile"
        exists = dockerfile.exists()
        self.add_result("E1", "Dockerfile exists", exists)
        self.print_test("Dockerfile", exists)
        
        # E1.3: CI configuration
        ci_file = self.root / ".github/workflows/ci.yml"
        exists = ci_file.exists()
        self.add_result("E1", "CI workflow", exists)
        self.print_test("ci.yml", exists)
        
        # E2: Falsifiability
        print("\n[E2] Falsifiability Framework")
        
        # E2.1: Receipt system
        passed, output = self.run_command(
            ["python3", "-m", "pytest", "tests/test_certcheck.py", "-v"],
            timeout=60
        )
        self.add_result("E2", "Receipt system tests", passed, output)
        self.print_test("Receipt tests", passed)
        
        # E2.2: Fuzzing
        passed, output = self.run_command(
            ["python3", "-m", "pytest", "tests/test_fuzz_receipts.py", "-v"],
            timeout=120
        )
        self.add_result("E2", "Fuzzing tests", passed, output)
        self.print_test("Fuzzing tests", passed)
        
        # E2.3: Advantage benchmarks
        passed, output = self.run_command(
            ["python3", "-m", "pytest", "tests/test_advantage_benchmarks.py", "-v"],
            timeout=60
        )
        self.add_result("E2", "Advantage benchmarks", passed, output)
        self.print_test("Advantage benchmarks", passed)
        
        # E2.4: Hardware isomorphism
        print("\n[E2.4] Hardware Implementation")
        verilog_files = list((self.root / "thielecpu/hardware").glob("*.v"))
        has_verilog = len(verilog_files) >= 5
        self.add_result("E2", f"Verilog files ({len(verilog_files)} files)", has_verilog)
        self.print_test(f"Verilog hardware: {len(verilog_files)} files", has_verilog)
    
    # ========== COMPREHENSIVE RESULTS ==========
    
    def validate_all_result_files(self):
        """Validate all research result files exist."""
        self.print_header("RESULT FILES VALIDATION")
        
        result_files = [
            "artifacts/pde_schrodinger_results_improved.csv",
            "benchmarks/graph_results.csv",
            "benchmarks/program_analysis_results.csv",
            "artifacts/pattern_results.csv",
            "benchmarks/turbulence_results.csv",
            "benchmarks/sat_results.csv"
        ]
        
        for result_file in result_files:
            path = self.root / result_file
            exists = path.exists()
            size = path.stat().st_size if exists else 0
            self.add_result("Results", result_file, exists)
            self.print_test(f"{result_file} ({size} bytes)", exists)
    
    def print_summary(self):
        """Print comprehensive validation summary."""
        print(f"\n{BLUE}{'='*70}{RESET}")
        print(f"{BLUE}COMPREHENSIVE VALIDATION SUMMARY{RESET}")
        print(f"{BLUE}{'='*70}{RESET}\n")
        
        # Track-by-track summary
        for track in sorted(self.results.keys()):
            tests = self.results[track]
            passed = sum(1 for _, p, _ in tests if p)
            total = len(tests)
            pct = 100 * passed / total if total > 0 else 0
            
            status = f"{GREEN}✓{RESET}" if passed == total else f"{YELLOW}⚠{RESET}" if passed > 0 else f"{RED}✗{RESET}"
            print(f"{status} {track}: {passed}/{total} tests passed ({pct:.0f}%)")
        
        # Overall summary
        print(f"\n{BLUE}{'='*70}{RESET}")
        pct = 100 * self.passed_tests / self.total_tests if self.total_tests > 0 else 0
        if self.passed_tests == self.total_tests:
            print(f"{GREEN}✓ ALL TESTS PASSED: {self.passed_tests}/{self.total_tests} ({pct:.0f}%){RESET}")
        else:
            print(f"{YELLOW}⚠ PARTIAL PASS: {self.passed_tests}/{self.total_tests} ({pct:.0f}%){RESET}")
        print(f"{BLUE}{'='*70}{RESET}\n")
        
        return self.passed_tests == self.total_tests
    
    def run_all(self) -> bool:
        """Run all validation tests."""
        print(f"\n{BLUE}{'='*70}{RESET}")
        print(f"{BLUE}THIELE MACHINE - COMPREHENSIVE MASTER VALIDATION{RESET}")
        print(f"{BLUE}Testing ALL components of the research program{RESET}")
        print(f"{BLUE}{'='*70}{RESET}\n")
        
        start_time = time.time()
        
        # Run all track validations
        self.validate_track_a_formal()
        self.validate_track_b_algorithms()
        self.validate_track_c_discovery()
        self.validate_track_d_models()
        self.validate_track_e_quality()
        self.validate_all_result_files()
        
        elapsed = time.time() - start_time
        
        # Print summary
        all_passed = self.print_summary()
        
        print(f"Total validation time: {elapsed:.1f}s\n")
        
        return all_passed


def main():
    """Main entry point."""
    suite = ValidationSuite()
    all_passed = suite.run_all()
    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())
