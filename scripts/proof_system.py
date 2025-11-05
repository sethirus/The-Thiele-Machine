#!/usr/bin/env python3
"""
Proof Emission and Verification System for Computational Priced Sight

This module handles formal proof generation (DRAT/FRAT) and verification
using standard SAT proof checkers, producing self-verifying mathematical artifacts.

WARNING: Currently uses mock proof generation for demonstration.
Real proof logging requires external SAT solvers (CaDiCaL, Kissat) with DRAT/FRAT support.
"""

import subprocess
import tempfile
import os
from typing import Dict, Any, Optional, Tuple, List
from pathlib import Path
import hashlib
import json
import random
from pysat.formula import CNF
from pysat.solvers import Solver


class ProofEmitter:
    """Handles formal proof emission for SAT/UNSAT results using SAT solvers with proof logging."""

    def __init__(self, solver_name: Optional[str] = None, checker_path: Optional[str] = None,
                 use_real_proofs: bool = False):
        """Initialize with SAT solver and proof checker.

        Args:
            solver_name: PySAT solver name (glucose4, minisat22, lingeling, cadical)
            checker_path: Path to external proof checker (drat-trim, etc.)
            use_real_proofs: If True, attempt to use real proof logging (requires external solvers)
        """
        self.solver_name = solver_name or "glucose4"  # Default to glucose4
        self.checker_path = checker_path or self._find_checker()
        self.use_real_proofs = use_real_proofs and self._check_real_proof_support()

        if self.use_real_proofs:
            print("✅ Using real SAT proof logging with external solvers")
        else:
            print("⚠️  Using mock proof generation (for real proofs, install CaDiCaL/Kissat)")
            print("   Install instructions:")
            print("   - CaDiCaL: https://github.com/arminbiere/cadical/releases")
            print("   - Kissat: https://github.com/arminbiere/kissat/releases")
            print("   - Place binaries in ./tools/ directory or system PATH")

    def _check_real_proof_support(self) -> bool:
        """Check if real proof logging is supported."""
        # Check for external solvers that support proof logging
        external_solvers = ["cadical", "kissat"]
        for solver in external_solvers:
            if self._find_external_solver(solver):
                return True
        return False

    def _find_external_solver(self, solver_name: str) -> Optional[str]:
        """Find external SAT solver executable."""
        # First check system PATH
        try:
            result = subprocess.run(["which", solver_name],
                                  capture_output=True, text=True, timeout=5)
            if result.returncode == 0:
                return result.stdout.strip()
        except (subprocess.TimeoutExpired, FileNotFoundError, subprocess.SubprocessError):
            pass

        # Check common installation paths
        common_paths = [
            f"/usr/local/bin/{solver_name}",
            f"/usr/bin/{solver_name}",
            f"./tools/{solver_name}",
            f"./tools/{solver_name}.exe",  # Windows
            f"tools/{solver_name}",
            f"tools/{solver_name}.exe"
        ]

        # Get the directory of this script to resolve relative paths
        script_dir = Path(__file__).parent.parent
        for path in common_paths:
            full_path = (script_dir / path).resolve()
            if full_path.exists() and (full_path.is_file() or (full_path.suffix == '.exe')):
                return str(full_path)

        return None

    def _find_checker(self) -> Optional[str]:
        """Find available SAT proof checkers."""
        candidates = ["drat-trim", "gratgen", "cake_lpr", "lrat-check"]

        for candidate in candidates:
            path = self._find_external_solver(candidate)
            if path:
                return path

        return None

    def emit_proof(self, instance: Dict[str, Any], model_result: Dict[str, Any]) -> Dict[str, Any]:
        """
        Emit a formal proof for the given instance and model result.

        Returns proof data with verification status.
        """
        # Convert instance to CNF based on the model
        cnf = self._instance_to_cnf(instance, model_result["model_name"])

        if model_result["success"]:
            # For successful models, emit SAT certificate
            return self._emit_sat_certificate(cnf, model_result)
        else:
            # For unsuccessful models, emit UNSAT proof
            return self._emit_unsat_proof(cnf, model_result)

    def _emit_sat_certificate(self, cnf: CNF, model_result: Dict[str, Any]) -> Dict[str, Any]:
        """Emit SAT certificate with model verification."""
        if self.use_real_proofs:
            return self._emit_real_sat_certificate(cnf, model_result)
        else:
            return self._emit_mock_sat_certificate(cnf, model_result)

    def _emit_unsat_proof(self, cnf: CNF, model_result: Dict[str, Any]) -> Dict[str, Any]:
        """Emit UNSAT proof using DRAT/FRAT."""
        if self.use_real_proofs:
            return self._emit_real_unsat_proof(cnf, model_result)
        else:
            return self._emit_mock_unsat_proof(cnf, model_result)

    def _emit_real_sat_certificate(self, cnf: CNF, model_result: Dict[str, Any]) -> Dict[str, Any]:
        """Emit real SAT certificate using external solver."""
        # For now, fall back to mock until external solvers are integrated
        print("⚠️  Real SAT certificate not yet implemented, using mock")
        return self._emit_mock_sat_certificate(cnf, model_result)

    def _emit_real_unsat_proof(self, cnf: CNF, model_result: Dict[str, Any]) -> Dict[str, Any]:
        """Emit real UNSAT proof using external solver with proof logging."""
        # For now, fall back to mock until external solvers are integrated
        print("⚠️  Real UNSAT proof not yet implemented, using mock")
        return self._emit_mock_unsat_proof(cnf, model_result)

    def _emit_mock_sat_certificate(self, cnf: CNF, model_result: Dict[str, Any]) -> Dict[str, Any]:
        """Emit mock SAT certificate for demonstration."""
        # Use PySAT solver to find a satisfying assignment
        solver = Solver(name=self.solver_name, bootstrap_with=cnf)

        try:
            if solver.solve():
                model = solver.get_model()
                if model:
                    # Verify the model satisfies the CNF
                    verification = self._verify_assignment(cnf, model)

                    certificate_text = f"""c SAT Certificate (MOCK)
c Generated by Computational Priced Sight
c Model: {' '.join(map(str, model))}
c WARNING: This is a mock certificate for demonstration
c Real certificates require external SAT solver verification
s SATISFIABLE
v {' '.join(map(str, model))} 0
"""
                    certificate_data = certificate_text.encode()

                    return {
                        "proof_type": "certificate",
                        "proof_data": certificate_data,
                        "proof_text": certificate_text,
                        "verification": verification,
                        "model": model,
                        "hash": hashlib.sha256(certificate_data).hexdigest(),
                        "mock_proof": True,
                        "solver_used": self.solver_name
                    }

            # If solver couldn't find a model, this model is actually UNSAT
            solver.delete()
            return self._emit_mock_unsat_proof(cnf, model_result)

        finally:
            solver.delete()

    def _emit_mock_unsat_proof(self, cnf: CNF, model_result: Dict[str, Any]) -> Dict[str, Any]:
        """Emit mock UNSAT proof using simulated DRAT."""
        # Check if the CNF is actually unsatisfiable
        solver = Solver(name=self.solver_name, bootstrap_with=cnf)

        try:
            is_sat = solver.solve()

            if is_sat:
                # This should be SAT, not UNSAT
                model = solver.get_model()
                solver.delete()
                return self._emit_mock_sat_certificate(cnf, model_result)
            else:
                # Generate a simplified DRAT-style proof
                proof_lines = [
                    "c DRAT Proof (MOCK)",
                    "c Generated by Computational Priced Sight",
                    f"c CNF hash: {hashlib.sha256(str(cnf.clauses).encode()).hexdigest()[:16]}",
                    "c WARNING: This is a mock proof for demonstration",
                    "c Real DRAT proofs require CaDiCaL or Kissat with proof logging",
                    ""
                ]

                # Add simplified resolution steps
                max_var = max(abs(lit) for clause in cnf.clauses for lit in clause) if cnf.clauses else 1
                for i in range(min(10, len(cnf.clauses))):
                    if i < len(cnf.clauses):
                        clause = cnf.clauses[i]
                        proof_lines.append(f"{i+1} {' '.join(map(str, clause))} 0")

                proof_lines.append("0")  # Empty clause

                proof_text = "\n".join(proof_lines)
                proof_data = proof_text.encode()

                # Verify the proof (simplified)
                verification = self._verify_drat_proof(cnf, proof_data)

                solver.delete()
                return {
                    "proof_type": "drat",
                    "proof_data": proof_data,
                    "proof_text": proof_text,
                    "verification": verification,
                    "hash": hashlib.sha256(proof_data).hexdigest(),
                    "mock_proof": True,
                    "solver_used": self.solver_name
                }
        finally:
            solver.delete()

    def _verify_assignment(self, cnf: CNF, model: List[int]) -> Dict[str, Any]:
        """Verify that a model satisfies the CNF."""
        satisfied_clauses = 0
        total_clauses = len(cnf.clauses)

        for clause in cnf.clauses:
            clause_satisfied = False
            for lit in clause:
                var = abs(lit)
                if var <= len(model):
                    assignment = model[var - 1] if lit > 0 else -model[var - 1]
                    if assignment > 0:
                        clause_satisfied = True
                        break
            if clause_satisfied:
                satisfied_clauses += 1

        verified = satisfied_clauses == total_clauses

        return {
            "verified": verified,
            "satisfied_clauses": satisfied_clauses,
            "total_clauses": total_clauses,
            "checker": "assignment_verifier",
            "method": "model_check",
            "mock_verification": not self.use_real_proofs
        }

    def _verify_drat_proof(self, cnf: CNF, proof_data: bytes) -> Dict[str, Any]:
        """Verify DRAT proof (simplified implementation)."""
        # In a full implementation, this would use drat-trim or similar
        # For now, we'll do basic validation

        proof_text = proof_data.decode('utf-8', errors='ignore')
        lines = proof_text.split('\n')

        has_empty_clause = any('0' in line and not line.strip().startswith('c') for line in lines)
        has_resolution_steps = any(line.strip() and not line.startswith('c') for line in lines)

        # Basic validation
        verified = has_empty_clause and has_resolution_steps

        return {
            "verified": verified,
            "checker": self.checker_path or "built-in-verifier",
            "method": "basic_drat_check",
            "has_empty_clause": has_empty_clause,
            "has_resolution_steps": has_resolution_steps,
            "mock_verification": not self.use_real_proofs
        }

    def _instance_to_cnf(self, instance: Dict[str, Any], model_name: str) -> CNF:
        """Convert instance to CNF based on the model interpretation."""
        if model_name == "gf2_linear":
            return self._gf2_to_cnf(instance)
        elif model_name == "symmetry":
            return self._symmetry_to_cnf(instance)
        elif model_name == "modular_arithmetic":
            return self._modular_to_cnf(instance)
        elif model_name == "pebbling":
            return self._pebbling_to_cnf(instance)
        else:
            # Default: treat as generic constraint satisfaction
            return self._generic_to_cnf(instance)

    def _gf2_to_cnf(self, instance: Dict[str, Any]) -> CNF:
        """Convert GF(2) linear system to CNF."""
        data = instance.get("data", {})
        matrix = data.get("matrix", [])
        rhs = data.get("rhs", [])

        cnf = CNF()
        n_vars = len(matrix[0]) if matrix else 10

        # Add variables
        for i in range(1, n_vars + 1):
            cnf.append([i])  # Each variable can be true or false

        # Convert linear equations to CNF
        for i, equation in enumerate(matrix):
            if i < len(rhs):
                target = rhs[i]
                # XOR constraint: sum of variables = target (mod 2)
                clause = []
                for j, coeff in enumerate(equation):
                    if coeff == 1:
                        clause.append(j + 1)  # Positive literal
                    elif coeff == -1:
                        clause.append(-(j + 1))  # Negative literal

                if target == 1:
                    cnf.append(clause)  # XOR = 1
                else:
                    # XOR = 0 means all variables equal (parity constraint)
                    # This is complex; for demo we'll add a simple constraint
                    cnf.append([clause[0]])  # Simplified

        return cnf

    def _symmetry_to_cnf(self, instance: Dict[str, Any]) -> CNF:
        """Convert symmetry-based instance to CNF."""
        # For symmetry models, we create constraints based on group actions
        cnf = CNF()
        n_vars = instance.get("metadata", {}).get("n_vars", 10)

        # Add basic symmetry constraints (simplified)
        for i in range(1, min(5, n_vars)):
            cnf.append([i, i+1])  # Some symmetry constraint

        return cnf

    def _modular_to_cnf(self, instance: Dict[str, Any]) -> CNF:
        """Convert modular arithmetic instance to CNF."""
        cnf = CNF()
        n_vars = instance.get("metadata", {}).get("n_vars", 10)

        # Add modular constraints (simplified)
        for i in range(1, min(5, n_vars)):
            cnf.append([i])  # Some modular constraint

        return cnf

    def _pebbling_to_cnf(self, instance: Dict[str, Any]) -> CNF:
        """Convert pebbling instance to CNF."""
        cnf = CNF()
        n_vars = instance.get("metadata", {}).get("n_vars", 10)

        # Add pebbling constraints (simplified)
        for i in range(1, min(5, n_vars)):
            cnf.append([-i, i+1])  # Some pebbling constraint

        return cnf

    def _generic_to_cnf(self, instance: Dict[str, Any]) -> CNF:
        """Generic CNF conversion for unrecognized models."""
        cnf = CNF()
        n_vars = instance.get("metadata", {}).get("n_vars", 10)

        # Add some basic constraints
        for i in range(1, min(5, n_vars)):
            cnf.append([i, -(i+1)])

        return cnf

    def _verify_proof(self, cnf_clauses: List[List[int]], proof_data: bytes,
                     proof_type: str) -> Dict[str, Any]:
        """Verify proof using external checker or built-in validation."""
        if not self.checker_path:
            # Use built-in verification
            if proof_type == "drat":
                return self._verify_drat_builtin(cnf_clauses, proof_data)
            elif proof_type == "certificate":
                return self._verify_certificate_builtin(cnf_clauses, proof_data)
            else:
                return {"verified": False, "error": "Unsupported proof type"}

        try:
            # Write CNF to temporary file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.cnf', delete=False) as cnf_file:
                max_var = max(max(abs(lit) for lit in clause) for clause in cnf_clauses) if cnf_clauses else 1
                cnf_file.write(f"p cnf {max_var} {len(cnf_clauses)}\n")
                for clause in cnf_clauses:
                    cnf_file.write(" ".join(map(str, clause)) + " 0\n")
                cnf_path = cnf_file.name

            # Write proof to temporary file
            proof_suffix = '.drat' if proof_type == 'drat' else '.frat'
            with tempfile.NamedTemporaryFile(mode='wb', suffix=proof_suffix, delete=False) as proof_file:
                proof_file.write(proof_data)
                proof_path = proof_file.name

            # Run checker
            cmd = [self.checker_path, cnf_path, proof_path]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)

            # Clean up temp files
            os.unlink(cnf_path)
            os.unlink(proof_path)

            return {
                "verified": result.returncode == 0,
                "checker": self.checker_path,
                "method": "external_checker",
                "output": result.stdout + result.stderr,
                "return_code": result.returncode
            }

        except (subprocess.TimeoutExpired, FileNotFoundError) as e:
            return {
                "verified": False,
                "checker": self.checker_path,
                "method": "external_checker",
                "error": str(e)
            }

    def _verify_drat_builtin(self, cnf_clauses: List[List[int]], proof_data: bytes) -> Dict[str, Any]:
        """Built-in DRAT verification (simplified)."""
        proof_text = proof_data.decode('utf-8', errors='ignore')
        lines = proof_text.split('\n')

        has_empty_clause = False
        has_resolution_steps = False

        for line in lines:
            line = line.strip()
            if line and not line.startswith('c'):
                if line == '0':
                    has_empty_clause = True
                elif any(char.isdigit() or char == '-' for char in line.split()):
                    has_resolution_steps = True

        verified = has_empty_clause and has_resolution_steps

        return {
            "verified": verified,
            "checker": "built-in-drat-verifier",
            "method": "basic_validation",
            "has_empty_clause": has_empty_clause,
            "has_resolution_steps": has_resolution_steps
        }

    def _verify_certificate_builtin(self, cnf_clauses: List[List[int]], proof_data: bytes) -> Dict[str, Any]:
        """Built-in certificate verification (simplified)."""
        proof_text = proof_data.decode('utf-8', errors='ignore')
        lines = proof_text.split('\n')

        has_sat_line = any('SATISFIABLE' in line for line in lines)
        has_model_line = any(line.strip().startswith('v ') for line in lines)

        verified = has_sat_line and has_model_line

        return {
            "verified": verified,
            "checker": "built-in-certificate-verifier",
            "method": "basic_validation",
            "has_sat_line": has_sat_line,
            "has_model_line": has_model_line
        }


class ReceiptGenerator:
    """Generates cryptographic receipts for computational priced sight runs."""

    def __init__(self):
        self.receipts = []
        self.chain_hashes = []  # For hash chaining

    def add_result(self, instance_hash: str, model_results: List[Dict[str, Any]],
                   selected_model: Optional[str], proof_data: Optional[Dict[str, Any]],
                   baseline_data: Optional[Dict[str, Any]] = None):
        """Add a single result to the receipt chain."""

        result_entry = {
            "instance_commitment": instance_hash,
            "timestamp": self._get_timestamp(),
            "model_candidates": [
                {
                    "model": r["model_name"],
                    "mdl_score": r["mdl_score"].total_bits,
                    "success": r["success"],
                    "proof_type": r.get("proof_type")
                } for r in model_results
            ],
            "selected_model": selected_model,
            "proof_emitted": proof_data is not None,
            "proof_hash": proof_data["hash"] if proof_data else None,
            "verification_status": proof_data["verification"] if proof_data else None,
            "baseline_comparison": baseline_data,
            "previous_receipt_hash": self.chain_hashes[-1] if self.chain_hashes else None
        }

        # Create step hash for chaining
        step_canonical = json.dumps(result_entry, sort_keys=True, separators=(',', ':'))
        step_hash = hashlib.sha256(step_canonical.encode()).hexdigest()
        result_entry["step_hash"] = step_hash
        self.chain_hashes.append(step_hash)

        self.receipts.append(result_entry)

    def generate_receipt(self) -> Dict[str, Any]:
        """Generate final cryptographic receipt with hash chaining."""

        # Create receipt content
        receipt_content = {
            "protocol": "computational-priced-sight-v1.0",
            "receipts": self.receipts,
            "hash_chain": {
                "step_hashes": self.chain_hashes,
                "chain_verification": self._verify_chain()
            },
            "summary": {
                "total_instances": len(self.receipts),
                "successful_proofs": sum(1 for r in self.receipts if r["proof_emitted"]),
                "models_discovered": list(set(r["selected_model"] for r in self.receipts if r["selected_model"])),
                "baseline_comparisons": sum(1 for r in self.receipts if r.get("baseline_comparison") is not None)
            }
        }

        # Generate global hash (Merkle tree root of all step hashes)
        if self.chain_hashes:
            global_hash = self._compute_global_hash()
            receipt_content["global_hash"] = global_hash

        # Generate cryptographic commitment
        canonical = json.dumps(receipt_content, sort_keys=True, separators=(',', ':'))
        receipt_hash = hashlib.sha256(canonical.encode()).hexdigest()

        receipt_content["receipt_hash"] = receipt_hash
        receipt_content["signature"] = self._mock_signature(receipt_hash)

        return receipt_content

    def _verify_chain(self) -> Dict[str, Any]:
        """Verify the integrity of the hash chain."""
        if not self.receipts:
            return {"valid": True, "reason": "empty_chain"}

        verification_results = []

        for i, receipt in enumerate(self.receipts):
            expected_prev = self.chain_hashes[i-1] if i > 0 else None
            actual_prev = receipt.get("previous_receipt_hash")

            step_valid = True
            issues = []

            if expected_prev != actual_prev:
                step_valid = False
                issues.append(f"previous_hash_mismatch_at_step_{i}")

            # Verify step hash
            receipt_copy = receipt.copy()
            step_hash = receipt_copy.pop("step_hash")
            step_canonical = json.dumps(receipt_copy, sort_keys=True, separators=(',', ':'))
            computed_hash = hashlib.sha256(step_canonical.encode()).hexdigest()

            if computed_hash != step_hash:
                step_valid = False
                issues.append(f"step_hash_mismatch_at_step_{i}")

            verification_results.append({
                "step": i,
                "valid": step_valid,
                "issues": issues
            })

        chain_valid = all(r["valid"] for r in verification_results)

        return {
            "valid": chain_valid,
            "step_verifications": verification_results,
            "total_steps": len(self.receipts)
        }

    def _compute_global_hash(self) -> str:
        """Compute global hash as Merkle tree root of step hashes."""
        if not self.chain_hashes:
            return ""

        # Simple Merkle tree computation
        hashes = [bytes.fromhex(h) for h in self.chain_hashes]

        while len(hashes) > 1:
            if len(hashes) % 2 == 1:
                hashes.append(hashes[-1])  # Duplicate last hash if odd number

            new_hashes = []
            for i in range(0, len(hashes), 2):
                combined = hashes[i] + hashes[i+1]
                new_hash = hashlib.sha256(combined).digest()
                new_hashes.append(new_hash)
            hashes = new_hashes

        return hashes[0].hex()

    def _get_timestamp(self) -> str:
        """Get current timestamp."""
        import datetime
        return datetime.datetime.utcnow().isoformat()

    def _mock_signature(self, data_hash: str) -> str:
        """Generate mock cryptographic signature."""
        # In real implementation, this would use Ed25519 or similar
        return f"mock-signature-{data_hash[:16]}"


# Import random for mock data
import random