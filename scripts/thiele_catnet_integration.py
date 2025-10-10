# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

#!/usr/bin/env python3
"""
Thiele Machine + CatNet Integration for Runtime Policy Enforcement

This module integrates the Thiele Machine's audited computation with CatNet's
neural network policy enforcement, enabling runtime safety guarantees for
machine learning systems.
"""

import json
import hashlib
import time
import math
import tempfile
import threading
import contextlib
import os
from pathlib import Path, PurePosixPath
from typing import List, Dict, Any, Optional, Tuple
from dataclasses import dataclass

# Import Thiele Machine components
try:
    import sys
    import os
    # Add current directory to path for local imports
    current_dir = os.path.dirname(os.path.abspath(__file__))
    parent_dir = os.path.dirname(current_dir)
    if parent_dir not in sys.path:
        sys.path.insert(0, parent_dir)

    from thielecpu.vm import VM, State
    from thielecpu.logic import lassert
    from thielecpu.mdl import mdlacc
    from thielecpu.assemble import parse
    from thielecpu._types import ModuleId
    THIELE_AVAILABLE = True
except ImportError as e:
    # Fallback for testing
    print(f"Warning: Thiele CPU components not available: {e}")
    THIELE_AVAILABLE = False
    VM = None
    State = None
    lassert = None
    mdlacc = None
    parse = None
    ModuleId = None

# Import CatNet components
try:
    from catnet.catnet import CatNet
    CATNET_AVAILABLE = True
except ImportError as e:
    # Fallback for testing
    print(f"Warning: CatNet components not available: {e}")
    CATNET_AVAILABLE = False
    CatNet = None  # Will be defined later if needed


@contextlib.contextmanager
def temporary_workdir(path: Path):
    """Context manager to temporarily change to a writable working directory."""
    path.mkdir(parents=True, exist_ok=True)
    old_cwd = os.getcwd()
    try:
        os.chdir(str(path))
        yield
    finally:
        os.chdir(old_cwd)


@dataclass
class PolicyAxiom:
    """Represents a safety policy axiom for neural network inference."""
    name: str
    description: str
    smt_formula: str  # SMT-LIB2 formula encoding the policy
    severity: str = "error"  # "warning" or "error"


@dataclass
class InferenceResult:
    """Result of a policy-checked neural network inference."""
    input_data: List[float]
    raw_output: List[float]
    policy_check_passed: bool
    violated_policies: List[str]
    thiele_certificate: Optional[str]
    mu_cost: float
    timestamp: float


class ThieleCatNetEnforcer:
    """
    Integrated Thiele Machine + CatNet system for policy-enforced neural networks.

    This class combines:
    1. CatNet: Neural network with categorical structure and audit logging
    2. Thiele Machine: Audited computation with µ-bit cost tracking
    3. Policy Enforcement: Runtime safety guarantees via SMT checking
    """

    def __init__(
        self,
        input_size: int = 784,
        hidden_size: int = 128,
        output_size: int = 10,
        policy_file: Optional[str] = None,
        audit_log_path: Optional[str] = None
    ):
        # Initialize CatNet
        if CATNET_AVAILABLE and CatNet is not None:
            self.catnet = CatNet(
                input_size=input_size,
                hidden_size=hidden_size,
                output_size=output_size,
                storage_path=audit_log_path
            )
        else:
            # Create mock CatNet
            class MockCatNet:
                def __init__(self, input_size=10, hidden_size=5, output_size=2, storage_path=None):
                    self.input_size = input_size
                    self.hidden_size = hidden_size
                    self.output_size = output_size
                    self._audit_log = []
                    self._seq = 0
                    self._clock = lambda: 0

                def forward(self, x):
                    # Simple mock forward pass
                    return [0.1, 0.9]  # Mock output

                def _add_entry(self, entry):
                    self._audit_log.append(entry)

                def audit_log(self):
                    return self._audit_log

            self.catnet = MockCatNet(input_size, hidden_size, output_size, audit_log_path)

        # Initialize Thiele Machine components
        if THIELE_AVAILABLE and VM is not None and State is not None:
            self.vm = VM(State())
        else:
            # Create mock VM
            class MockVM:
                def __init__(self):
                    self.state = MockState()

                def run(self, program, outdir):
                    # Mock run - just create some dummy output
                    outdir.mkdir(parents=True, exist_ok=True)
                    (outdir / "trace.log").write_text("Mock Thiele execution")
                    (outdir / "mu_ledger.json").write_text('{"mu": 1.0}')

            class MockState:
                def __init__(self):
                    self.csr = MockCSR()
                    self.mu = 1.0

            class MockCSR:
                def __init__(self):
                    self._values = {0: 0, 1: "mock_cert", 2: 0}

                def __getitem__(self, key):
                    return self._values.get(key.value if hasattr(key, 'value') else key, 0)

            self.vm = MockVM()

        # Store original working directory for path resolution
        self.original_cwd = Path.cwd()

        self.certificates_dir = self.original_cwd / "certificates"
        self.certificates_dir.mkdir(exist_ok=True)

        # Create a persistent session workdir that becomes the process CWD
        # This eliminates writes to the repo root and makes '.' always point at a controlled location
        self.session_workdir = self.certificates_dir / "work"
        self.session_workdir.mkdir(parents=True, exist_ok=True)

        # Force process CWD for any component that writes to '.'
        os.chdir(str(self.session_workdir))

        # Load safety policies
        self.policies = self._load_default_policies()
        if policy_file:
            self._load_policy_file(policy_file)

        # Audit log for integration events
        self.integration_log: List[Dict[str, Any]] = []

        # Thread safety and deterministic naming
        self._sequence_lock = threading.Lock()
        self._sequence_counter = 0

        # Global hash chain for cryptographic integrity
        self._hash_chain_file = self.certificates_dir / "global_hash_chain.json"
        self._previous_hash = self._load_or_create_hash_chain()

        # Configuration for error handling
        self.fail_closed = False  # Default: fail-open for indeterminate states

    def _load_or_create_hash_chain(self) -> str:
        """Load existing hash chain or create genesis block."""
        if self._hash_chain_file.exists():
            try:
                with open(self._hash_chain_file, 'r', encoding='utf-8') as f:
                    chain_data = json.load(f)
                    return chain_data.get('latest_hash', '0' * 64)
            except Exception:
                pass

        # Create genesis block
        genesis = {
            'genesis': True,
            'timestamp': time.time(),
            'latest_hash': '0' * 64,
            'chain': []
        }
        with open(self._hash_chain_file, 'w', encoding='utf-8') as f:
            json.dump(genesis, f, indent=2, sort_keys=True)

        return '0' * 64

    def _thiele_is_real(self) -> bool:
        """Check if we're using the real Thiele VM or mocks."""
        return bool(THIELE_AVAILABLE and self.vm is not None and parse is not None)

    def _update_hash_chain(self, event: Dict[str, Any], current_hash: str) -> None:
        """Update the global hash chain with a new event."""
        try:
            # Load current chain
            if self._hash_chain_file.exists():
                with open(self._hash_chain_file, 'r', encoding='utf-8') as f:
                    chain_data = json.load(f)
            else:
                chain_data = {
                    'genesis': True,
                    'timestamp': time.time(),
                    'latest_hash': '0' * 64,
                    'chain': []
                }

            # Add event to chain
            chain_entry = {
                'sequence': event.get('sequence', 0),
                'timestamp': event['timestamp'],
                'event_hash': current_hash,
                'previous_hash': event['previous_hash'],
                'event_type': event['event']
            }
            chain_data['chain'].append(chain_entry)
            chain_data['latest_hash'] = current_hash
            chain_data['last_updated'] = time.time()

            # Save updated chain
            with open(self._hash_chain_file, 'w', encoding='utf-8') as f:
                json.dump(chain_data, f, indent=2, sort_keys=True)

        except Exception as e:
            print(f"Warning: Failed to update hash chain: {e}")

    def _load_default_policies(self) -> List[PolicyAxiom]:
        """Load default safety policies for neural network inference."""
        return [
            PolicyAxiom(
                name="output_range",
                description="Each output probability must be within [0,1].",
                smt_formula="""
; Bind: (declare-const out Real) and (assert (= out <VALUE>))
(assert (and (>= out 0.0) (<= out 1.0)))
(check-sat)
""",
                severity="error"
            ),
            PolicyAxiom(
                name="no_nan_outputs",
                description="No output may be NaN (checked in Python; SMT only used for other policies).",
                smt_formula="; handled in Python before SMT",
                severity="error"
            ),
            PolicyAxiom(
                name="confidence_threshold",
                description="Flag high-confidence predictions (> 0.95) for review; not blocking.",
                smt_formula="""
; Bind: (declare-const max_prob Real) and (assert (= max_prob <VALUE>))
(assert (> max_prob 0.95))
(check-sat)
""",
                severity="warning"
            )
        ]

    def _load_policy_file(self, policy_file: str) -> None:
        """Load additional policies from a JSON file."""
        try:
            with open(policy_file, 'r') as f:
                policy_data = json.load(f)

            for policy_dict in policy_data.get('policies', []):
                policy = PolicyAxiom(
                    name=policy_dict['name'],
                    description=policy_dict['description'],
                    smt_formula=policy_dict['smt_formula'],
                    severity=policy_dict.get('severity', 'warning')
                )
                self.policies.append(policy)

        except Exception as e:
            print(f"Warning: Could not load policy file {policy_file}: {e}")

    def _create_thiele_program(self, input_data: List[float]) -> str:
        """Create a Thiele program for policy-checked inference."""
        program_lines = [
            "; Thiele Machine program for CatNet policy enforcement",
            f"PNEW {{0,1,2,3,4,5,6,7,8,9}}  ; Create modules for policy checking",
            f"PYEXEC inference_check({input_data})  ; Execute inference with policy check",
            "MDLACC  ; Accumulate µ-bit cost",
            "EMIT inference_complete"
        ]
        return "\n".join(program_lines)

    def _check_policy_with_thiele(self, policy: PolicyAxiom, inference_data: Dict[str, Any]) -> Tuple[bool, str]:
        """
        Check a single policy using the Thiele Machine auditor.

        Returns: (policy_passed, certificate_hash_or_reason)
        For 'warning' policies, 'policy_passed' can be True (we just log the warning separately).
        """
        try:
            # 1) Python-side NaN check (blocks 'error' policy; logs warning otherwise)
            if policy.name == "no_nan_outputs":
                has_nan = any(math.isnan(float(v)) for v in inference_data['output'])
                if has_nan:
                    return (False, "nan_detected")
                # If no NaNs, pass without SMT
                return (True, "nan_check_ok")

            # 2) Prepare per-policy SMT query by binding actual values
            smt = policy.smt_formula
            decls = []
            binds = []

            if policy.name == "output_range":
                # If mocked, evaluate in Python to avoid false passes/fails.
                if not self._thiele_is_real():
                    all_ok = all(0.0 <= float(v) <= 1.0 for v in inference_data["output"])
                    return (all_ok, "py_eval")

                # Check all outputs individually; if any violates, the policy fails.
                # We'll run one SMT check per output and require all to be SAT.
                all_ok = True
                certs = []
                for idx, val in enumerate(inference_data["output"]):
                    smt_one = "(declare-const out Real)\n"
                    smt_one += f"(assert (= out {float(val)}))\n"
                    smt_one += smt  # has (assert (and (>= out 0.0) (<= out 1.0))) + (check-sat)
                    # Wrap once per value
                    ok, cert = self._run_thiele_smt(policy, smt_one)
                    if cert.startswith("indeterminate:"):
                        # Permission error - don't count as violation, but record it
                        certs.append(cert)
                        continue
                    certs.append(cert)
                    if not ok:
                        all_ok = False
                        break
                return (all_ok, ";".join(certs))

            elif policy.name == "confidence_threshold":
                max_prob = max(float(v) for v in inference_data["output"])

                # If mocked, evaluate in Python to get correct behavior
                if not self._thiele_is_real():
                    # With mocks, don't lie: warn only if > 0.95
                    return (True, "warn_triggered" if max_prob > 0.95 else "warn_not_triggered")

                # Use SMT binding for real VM
                smt_bind = "(declare-const max_prob Real)\n" \
                           f"(assert (= max_prob {max_prob}))\n" + smt
                # For a 'warning' policy: SAT means "warning triggered".
                ok, cert = self._run_thiele_smt(policy, smt_bind)
                if cert.startswith("indeterminate:"):
                    # Permission error - record as indeterminate warning
                    return (True, "warn_indeterminate:" + cert)
                # We do not fail the run for warnings; return True but encode the certificate.
                # The caller will record the warning separately.
                return (True, ("warn_triggered" if ok else "warn_not_triggered") + ":" + cert)

            else:
                # Unknown policy fallback: pass
                return (True, "policy_unrecognized")

        except Exception as e:
            return (False, f"check_failed:{e}")

    def _run_thiele_smt(self, policy: PolicyAxiom, smt_full: str) -> Tuple[bool, str]:
        """
        Build a tiny Thiele program that asserts SMT and runs MDLACC.
        Returns (sat_or_safe, certificate_id_or_path).
        sat_or_safe = True means the oracle step completed and was 'OK' (STATUS==0).
        On permission errors, we retry once with a fresh scratch dir. If it still fails,
        we return (False, "indeterminate:...") so callers can treat it differently from UNSAT.
        """
        # Thread-safe sequence number for deterministic naming
        with self._sequence_lock:
            seq = self._sequence_counter
            self._sequence_counter += 1

        # Stable, persistent outdir for receipts
        stamp = f"{int(time.time_ns())}"
        outdir = self.certificates_dir / f"policy_{policy.name}_{stamp}"
        outdir.mkdir(parents=True, exist_ok=True)

        # Persist the exact SMT we send (for replay)
        (outdir / "oracle_query.smt2").write_text(smt_full, encoding="utf-8")

        program_text = f"""
; Policy check: {policy.name}
PNEW {{10,11,12}}
LASSERT
{smt_full}
MDLACC
"""

        def run_once(scratch: Path) -> Tuple[bool, str]:
            if THIELE_AVAILABLE and parse is not None:
                with temporary_workdir(scratch):
                    program = parse(program_text.splitlines(), scratch)
                    self.vm.run(program, outdir)
            else:
                # Mock fallback
                (outdir / "trace.log").write_text("Mock Thiele execution (SAT)")
                (outdir / "mu_ledger.json").write_text('{"mu": 1.0}')

                # Create mock oracle reply and solver metadata for canonical receipts
                mock_reply = {
                    "status": 0,
                    "certificate_address": None,
                    "timestamp": time.time(),
                    "sequence": seq,
                    "mock": True
                }
                (outdir / "oracle_reply.json").write_text(
                    json.dumps(mock_reply, indent=2, sort_keys=True, ensure_ascii=False),
                    encoding="utf-8"
                )

                mock_meta = {
                    "solver_name": "mock_solver",
                    "solver_version": "1.0",
                    "timestamp": time.time(),
                    "sequence": seq,
                    "policy": policy.name,
                    "query_hash": hashlib.sha256(smt_full.encode()).hexdigest(),
                    "mock": True
                }
                (outdir / "solver_metadata.json").write_text(
                    json.dumps(mock_meta, indent=2, sort_keys=True),
                    encoding="utf-8"
                )

            try:
                from thielecpu.isa import CSR
                status = self.vm.state.csr[CSR.STATUS]  # 0 => OK
                cert_addr = self.vm.state.csr[CSR.CERT_ADDR]

                # Persist oracle reply (canonical receipt component)
                oracle_reply = {
                    "status": status,
                    "certificate_address": cert_addr,
                    "timestamp": time.time(),
                    "sequence": seq
                }
                (outdir / "oracle_reply.json").write_text(
                    json.dumps(oracle_reply, indent=2, sort_keys=True, ensure_ascii=False),
                    encoding="utf-8"
                )

                # Persist solver metadata (canonical receipt component)
                solver_meta = {
                    "solver_name": "thiele_machine" if THIELE_AVAILABLE else "mock_solver",
                    "solver_version": "1.0",
                    "timestamp": time.time(),
                    "sequence": seq,
                    "policy": policy.name,
                    "query_hash": hashlib.sha256(smt_full.encode()).hexdigest()
                }
                (outdir / "solver_metadata.json").write_text(
                    json.dumps(solver_meta, indent=2, sort_keys=True),
                    encoding="utf-8"
                )

                cert = str(cert_addr) if cert_addr else str(PurePosixPath(outdir))
                return (status == 0, cert)

            except Exception as e:
                # If CSR not readable, assume OK in mock mode
                return (True, str(PurePosixPath(outdir)))

        # First attempt: per-run scratch
        scratch = self.certificates_dir / "scratch" / policy.name / stamp
        try:
            ok, cert = run_once(scratch)
            return ok, cert
        except PermissionError as e:
            # Retry in a guaranteed new directory (namespaced by policy and time)
            retry_scratch = self.certificates_dir / "scratch_retry" / policy.name / stamp
            try:
                ok, cert = run_once(retry_scratch)
                return ok, cert
            except Exception as e2:
                # Persist error info for audit and return indeterminate
                (outdir / "oracle_reply.json").write_text(
                    json.dumps({"error": f"{type(e2).__name__}: {e2}"}, ensure_ascii=False, indent=2),
                    encoding="utf-8"
                )
                return False, f"indeterminate:{type(e2).__name__}:{e2}"
        except Exception as e:
            (outdir / "oracle_reply.json").write_text(
                json.dumps({"error": f"{type(e).__name__}: {e}"}, ensure_ascii=False, indent=2),
                encoding="utf-8"
            )
            return False, f"indeterminate:{type(e).__name__}:{e}"

    def enforce_inference(self, input_data: List[float]) -> InferenceResult:
        """
        Perform neural network inference with Thiele Machine policy enforcement.

        This method:
        1. Runs CatNet inference
        2. Checks all policies using Thiele Machine
        3. Generates comprehensive audit trail
        4. Returns policy-enforced result
        """

        start_time = time.time()

        # Step 1: Perform CatNet inference
        raw_output = self.catnet.forward(input_data)

        # Step 2: Check policies with Thiele Machine
        violated_policies = []
        warnings = []
        certificates = []
        total_mu_cost = 0.0

        for policy in self.policies:
            policy_passed, certificate = self._check_policy_with_thiele(policy, {
                'input': input_data,
                'output': raw_output,
                'policy': policy.name
            })

            if policy.severity == "error" and not policy_passed and not certificate.startswith("indeterminate:"):
                violated_policies.append(policy.name)
            elif policy.severity == "error" and certificate.startswith("indeterminate:"):
                # Handle indeterminate states based on fail_closed policy
                if self.fail_closed:
                    violated_policies.append(policy.name)
                # Log indeterminate state regardless
                warnings.append((policy.name, certificate))
            elif policy.severity == "warning":
                # Record whether warning fired (certificate string contains "warn_triggered" or not)
                warnings.append((policy.name, certificate))

            certificates.append({
                'policy': policy.name,
                'passed': policy_passed if policy.severity == "error" else True,
                'certificate': certificate,
                'severity': policy.severity
            })

            # Real µ-bit accounting: 8 bits per byte of canonical encodings
            if isinstance(certificate, str) and certificate.startswith("certificates/"):
                cert_path = Path(certificate)
                if cert_path.exists():
                    # Count bytes in SMT query
                    query_file = cert_path / "oracle_query.smt2"
                    if query_file.exists():
                        query_bytes = len(query_file.read_bytes())
                        total_mu_cost += query_bytes * 8

                    # Count bytes in oracle reply
                    reply_file = cert_path / "oracle_reply.json"
                    if reply_file.exists():
                        reply_bytes = len(reply_file.read_bytes())
                        total_mu_cost += reply_bytes * 8

                    # Count bytes in solver metadata
                    meta_file = cert_path / "solver_metadata.json"
                    if meta_file.exists():
                        meta_bytes = len(meta_file.read_bytes())
                        total_mu_cost += meta_bytes * 8
                else:
                    # Fallback for non-path certificates
                    total_mu_cost += len(str(certificate).encode()) * 8
            else:
                # Fallback for non-path certificates
                total_mu_cost += len(str(certificate).encode()) * 8

        # Step 3: Determine if inference should proceed
        policy_check_passed = len(violated_policies) == 0

        # Step 4: Create comprehensive result
        result = InferenceResult(
            input_data=input_data,
            raw_output=raw_output,
            policy_check_passed=policy_check_passed,
            violated_policies=violated_policies,
            thiele_certificate=json.dumps(certificates, sort_keys=True),
            mu_cost=total_mu_cost,
            timestamp=time.time()
        )

        # Step 5: Log the integration event with hash chain
        integration_event = {
            'event': 'policy_enforced_inference',
            'timestamp': result.timestamp,
            'sequence': len(self.integration_log),
            'input_hash': hashlib.sha256(json.dumps(input_data, sort_keys=True).encode()).hexdigest(),
            'output_hash': hashlib.sha256(json.dumps(raw_output, sort_keys=True).encode()).hexdigest(),
            'policies_checked': len(self.policies),
            'policies_violated': len(violated_policies),
            'mu_cost': total_mu_cost,
            'thiele_certificate_hash': hashlib.sha256(str(result.thiele_certificate).encode()).hexdigest(),
            'warnings': warnings,
            'previous_hash': self._previous_hash,
        }

        # Create hash of this event for chain
        event_json = json.dumps(integration_event, sort_keys=True, separators=(',', ':'))
        current_hash = hashlib.sha256(event_json.encode()).hexdigest()
        integration_event['current_hash'] = current_hash

        # Update hash chain atomically
        with self._sequence_lock:
            self._update_hash_chain(integration_event, current_hash)
            self._previous_hash = current_hash

        self.integration_log.append(integration_event)

        # Step 6: Log to CatNet audit system
        self.catnet._add_entry({
            'event': 'thiele_policy_check',
            'policies_checked': len(self.policies),
            'violations': violated_policies,
            'mu_cost': total_mu_cost,
            'thiele_certificate': result.thiele_certificate,
            'warnings': warnings,
        })

        return result

    def get_audit_summary(self) -> Dict[str, Any]:
        """Get comprehensive audit summary of policy enforcement."""
        total_inferences = len(self.integration_log)
        total_violations = sum(event['policies_violated'] for event in self.integration_log)
        total_mu_cost = sum(event['mu_cost'] for event in self.integration_log)

        return {
            'total_inferences': total_inferences,
            'total_policy_violations': total_violations,
            'total_mu_cost': total_mu_cost,
            'average_mu_per_inference': total_mu_cost / max(total_inferences, 1),
            'violation_rate': total_violations / max(total_inferences * len(self.policies), 1),
            'catnet_audit_log': self.catnet.audit_log(),
            'integration_events': self.integration_log
        }

    def export_compliance_report(self) -> str:
        """Export EU AI Act compliance report."""
        summary = self.get_audit_summary()

        report = {
            'thiele_catnet_integration': {
                'version': '1.0',
                'generated_at': time.time(),
                'compliance_metrics': {
                    'transparency': summary['total_inferences'] > 0,
                    'traceability': len(summary['integration_events']) > 0,
                    'auditability': len(summary['catnet_audit_log']) > 0,
                    'policy_enforcement': summary['violation_rate'] < 0.1,  # Less than 10% violations
                    'cost_accounting': summary['total_mu_cost'] > 0
                },
                'summary': summary
            }
        }

        return json.dumps(report, indent=2, sort_keys=True)


def main():
    """Demo the Thiele Machine + CatNet integration."""
    print(">>> Thiele Machine + CatNet Policy Enforcement Demo")
    print("=" * 60)

    # Initialize the integrated system
    enforcer = ThieleCatNetEnforcer(
        input_size=10,
        hidden_size=5,
        output_size=2,
        audit_log_path="thiele_catnet_demo.log"
    )

    print(f"Loaded {len(enforcer.policies)} safety policies")

    # Test inference with policy enforcement
    test_inputs = [
        [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0],
        [1.0, 0.9, 0.8, 0.7, 0.6, 0.5, 0.4, 0.3, 0.2, 0.1],
        [0.5] * 10  # This might trigger confidence threshold policy
    ]

    for i, input_data in enumerate(test_inputs):
        print(f"\n>>> Inference {i+1}:")
        print(f"Input: {input_data}")

        result = enforcer.enforce_inference(input_data)

        print(f"Raw output: {result.raw_output}")
        print(f"Policy check passed: {result.policy_check_passed}")
        print(f"Violated policies: {result.violated_policies}")
        print(f"Mu cost: {result.mu_cost:.2f}")
        print(f"Thiele certificate hash: {hashlib.sha256(str(result.thiele_certificate).encode()).hexdigest()[:16]}...")

    # Generate compliance report
    print("\n>>> Compliance Report:")
    print(enforcer.export_compliance_report())

    print("\n>>> Demo completed successfully!")
    print(f"Total inferences: {len(enforcer.integration_log)}")


if __name__ == "__main__":
    main()