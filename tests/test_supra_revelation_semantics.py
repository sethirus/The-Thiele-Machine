"""Priority 3: Falsifiability test for supra-quantum revelation requirement.

CRITICAL TEST: Semantic enforcement of information revelation for nonlocal correlations.

This test suite verifies the core claim: "Any program producing S>2√2 must invoke
an explicit revelation primitive (REVEAL opcode) or trigger a partition violation."

Current status (Dec 16, 2025): MIXED
- Coq kernel contains an explicit REVEAL primitive in coq/kernel/VMStep.v
- Python VM exposes REVEAL for explicit μ-information charging + certificate capture
- Python VM enforces a semantic gate for CHSH_TRIAL *receipts*: if balanced trials imply
    S>2√2 and no prior REVEAL occurred, CSR.ERR is set.
- A policy-only bypass baseline still exists for dataset-only workflows (PYEXEC writing
    a dataset file without CHSH_TRIAL receipts).

Falsifiability: any claimed “supra without revelation” path must be explicit about
which channel it uses (receipts vs dataset files) and what is being enforced.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import pytest

from thielecpu.isa import CSR
from thielecpu.state import State
from thielecpu.vm import VM
from tools.bell_receipts import load_probability_table_csv, program_from_trials, trials_from_probability_table
from tools.chsh_receipts import chsh_from_receipts_path
from tools.bell_operational import chsh_from_counts, load_counts, strategy_code


TSIRELSON_BOUND = Fraction(5657, 2000)  # ≈ 2.828 (2√2)


@pytest.fixture
def tmp_outdir(tmp_path: Path) -> Path:
    """Create temporary output directory for VM traces."""
    outdir = tmp_path / "supra_revelation_test"
    outdir.mkdir(parents=True, exist_ok=True)
    return outdir


def test_lhv_no_revelation_required(tmp_outdir: Path) -> None:
    """LHV strategy (S=2) should NOT require revelation primitive."""
    dataset_path = tmp_outdir / "lhv_dataset.json"
    code = strategy_code("lhv", n_per_setting=100, seed=1, output_json=dataset_path)

    program = [
        ("PNEW", "{1,2}"),
        ("PYEXEC", code),
        ("EMIT", "done"),  # No REVEAL - should succeed
    ]

    vm = VM(State())
    vm.run(program, tmp_outdir)

    dataset = load_counts(dataset_path)
    s_value = chsh_from_counts(dataset)

    assert s_value == Fraction(2, 1), "LHV should yield S=2"
    assert vm.state.mu_information == 0.0, "LHV should not charge μ_info"


def test_tsirelson_no_revelation_required(tmp_outdir: Path) -> None:
    """Tsirelson-like strategy (S≈2.828) should NOT require revelation."""
    dataset_path = tmp_outdir / "tsirelson_dataset.json"
    code = strategy_code("tsirelson", n_per_setting=2000, seed=42, output_json=dataset_path)

    program = [
        ("PNEW", "{1,2}"),
        ("PYEXEC", code),
        ("EMIT", "done"),  # No REVEAL - should succeed
    ]

    vm = VM(State())
    vm.run(program, tmp_outdir)

    dataset = load_counts(dataset_path)
    s_value = chsh_from_counts(dataset)

    # Tsirelson bound: allow numerical tolerance
    assert abs(float(s_value) - 2.828) < 0.05, f"Expected S≈2.828, got {float(s_value)}"
    assert vm.state.mu_information == 0.0, "Tsirelson should not charge μ_info (within quantum set)"


def test_supra_without_revelation_bypass_confirmed(tmp_outdir: Path) -> None:
    """Baseline (policy-only): Supra-quantum WITHOUT REVEAL still succeeds today.

    This is a falsifiability *baseline* demonstrating the current bypass:
    PYEXEC can write a supra dataset, and unless we add semantic enforcement,
    the VM will not automatically charge μ_info or halt.
    """
    dataset_path = tmp_outdir / "supra_no_reveal.json"
    code = strategy_code("supra_16_5", n_per_setting=100, seed=99, output_json=dataset_path)

    program = [
        ("PNEW", "{1,2}"),
        ("PYEXEC", code),
        ("EMIT", "done"),  # Deliberately omit REVEAL
    ]

    vm = VM(State())
    
    # Once semantic enforcement is implemented, this should raise:
    # with pytest.raises(PartitionViolationError):
    #     vm.run(program, tmp_outdir)
    
    vm.run(program, tmp_outdir)
    
    # Verify the bypass happened (proving policy-only enforcement)
    dataset = load_counts(dataset_path)
    s_value = chsh_from_counts(dataset)
    
    # Under policy-only: S=3.2, no charge
    assert s_value == Fraction(16, 5), "Supra yields S=3.2 under policy-only"
    assert vm.state.mu_information == 0.0, "No charge without REVEAL (policy bypass)"
    
    # Once semantic enforcement works, this assertion will fail, making test pass


def test_supra_with_explicit_revelation_succeeds(tmp_outdir: Path) -> None:
    """Supra-quantum WITH explicit REVEAL opcode should succeed and charge μ_info.
    
    This tests the intended explicit semantic path: REVEAL performs the μ_info
    charge and writes a cert address.
    """
    dataset_path = tmp_outdir / "supra_with_reveal.json"
    code = strategy_code("supra_16_5", n_per_setting=100, seed=123, output_json=dataset_path)

    program = [
        ("PNEW", "{1,2}"),
        ("PYEXEC", code),
        ("REVEAL", "1 64 supra_16_5"),
        ("EMIT", "done"),
    ]

    vm = VM(State())
    vm.run(program, tmp_outdir)

    dataset = load_counts(dataset_path)
    s_value = chsh_from_counts(dataset)

    assert s_value == Fraction(16, 5), "Supra yields S=3.2"
    assert vm.state.mu_information >= 64.0, "Explicit revelation charges ≥64 bits"
    assert str(vm.state.csr.get(CSR.CERT_ADDR, "")), "REVEAL should write a cert address"


def test_pr_box_without_revelation_bypass_confirmed(tmp_outdir: Path) -> None:
    """Baseline (policy-only): PR box WITHOUT REVEAL still succeeds today."""
    dataset_path = tmp_outdir / "pr_no_reveal.json"
    code = strategy_code("pr", n_per_setting=50, seed=7, output_json=dataset_path)

    program = [
        ("PNEW", "{1,2}"),
        ("PYEXEC", code),
        ("EMIT", "done"),  # No REVEAL
    ]

    vm = VM(State())
    vm.run(program, tmp_outdir)

    dataset = load_counts(dataset_path)
    s_value = chsh_from_counts(dataset)

    # Under policy-only: succeeds with S=4, no charge
    assert s_value == Fraction(4, 1), "PR box yields S=4 under policy-only"
    assert vm.state.mu_information == 0.0, "Policy bypass confirmed"


@pytest.mark.parametrize("strategy,expected_chsh", [
    ("lhv", Fraction(2, 1)),
    ("tsirelson", None),  # Approx 2.828
    ("supra_16_5", Fraction(16, 5)),
    ("pr", Fraction(4, 1)),
])
def test_operational_policy_enforcement(tmp_outdir: Path, strategy: str, expected_chsh: Fraction | None) -> None:
    """Verify current operational policy behavior (baseline for semantic migration)."""
    dataset_path = tmp_outdir / f"{strategy}_policy_test.json"
    code = strategy_code(strategy, n_per_setting=200, seed=0xCAFE, output_json=dataset_path)

    # Operational scan policy: charge nonlocal via EMIT
    program = [("PNEW", "{1,2}"), ("PYEXEC", code)]
    if strategy in {"supra_16_5", "pr"}:
        program.append(("EMIT", "0 64"))  # Policy charge
    program.append(("EMIT", "done"))

    vm = VM(State())
    vm.run(program, tmp_outdir)

    dataset = load_counts(dataset_path)
    s_value = chsh_from_counts(dataset)

    if expected_chsh is not None:
        assert s_value == expected_chsh, f"{strategy}: expected S={float(expected_chsh)}"
    else:
        assert abs(float(s_value) - 2.828) < 0.1, f"{strategy}: expected S≈2.828"

    if strategy in {"supra_16_5", "pr"}:
        assert vm.state.mu_information >= 64.0, f"{strategy}: policy charge verified"
    else:
        assert vm.state.mu_information == 0.0, f"{strategy}: no charge for quantum-compatible"


# =============================================================================
# REGRESSION TESTS FOR SEMANTIC MIGRATION
# =============================================================================

def test_reveal_opcode_signature(tmp_outdir: Path) -> None:
    """Test REVEAL opcode signature once implemented in VM.
    
    Expected signature: REVEAL <module_id> <bits> [certificate]
    """
    program = [
        ("PNEW", "{1,2}"),
        ("REVEAL", "1 64 cert_placeholder"),
        ("EMIT", "done"),
    ]
    vm = VM(State())
    vm.run(program, tmp_outdir)
    assert vm.state.mu_information >= 64.0
    assert str(vm.state.csr.get(CSR.CERT_ADDR, "")), "REVEAL should write a cert address"


def test_coq_vm_step_reveal_rule() -> None:
    """Verify Coq VMStep.v includes REVEAL instruction variant.
    
    This is a META-TEST: checks that Coq proof infrastructure exists.
    """
    from pathlib import Path
    
    vmstep_path = Path(__file__).parents[1] / "coq" / "kernel" / "VMStep.v"
    content = vmstep_path.read_text(encoding="utf-8")
    
    assert "instr_reveal" in content, "REVEAL opcode missing from coq/kernel/VMStep.v"
    assert "step_reveal" in content, "REVEAL step rule missing from coq/kernel/VMStep.v"


# =============================================================================
# FALSIFIABILITY DOCUMENTATION
# =============================================================================

def test_falsifiability_claim_documented() -> None:
    """Ensure the falsifiable claim is clearly stated in scan tool."""
    scan_path = Path(__file__).parents[1] / "tools" / "mu_chsh_operational_scan.py"
    content = scan_path.read_text(encoding="utf-8")
    
    assert "POLICY DISCLOSURE" in content, "Policy disclosure missing"
    assert "Falsifiable claim" in content, "Falsifiable claim not documented"
    assert "semantic enforcement" in content.lower() or "SEMANTIC ENFORCEMENT" in content.upper()


# =============================================================================
# SEMANTIC ENFORCEMENT (CHSH_TRIAL RECEIPTS)
# =============================================================================


def test_supra_chsh_trial_without_reveal_sets_err(tmp_outdir: Path) -> None:
    """Supra-quantum CHSH trials must set ERR without REVEAL (semantic enforcement)."""

    prob_csv = Path(__file__).parents[1] / "artifacts" / "bell" / "supra_quantum_16_5.csv"
    table = load_probability_table_csv(prob_csv)
    trials = trials_from_probability_table(table)
    program = program_from_trials(trials)

    vm = VM(State())
    vm.run(program, tmp_outdir)

    assert int(vm.state.csr.get(CSR.ERR, 0)) == 1

    receipts_path = tmp_outdir / "step_receipts.json"
    s_value = chsh_from_receipts_path(receipts_path)
    assert s_value == Fraction(16, 5)


def test_supra_chsh_trial_with_reveal_succeeds(tmp_outdir: Path) -> None:
    """Supra-quantum CHSH trials are allowed with explicit REVEAL + μ_info charge."""

    prob_csv = Path(__file__).parents[1] / "artifacts" / "bell" / "supra_quantum_16_5.csv"
    table = load_probability_table_csv(prob_csv)
    trials = trials_from_probability_table(table)
    program = program_from_trials(trials)
    program.insert(1, ("REVEAL", "1 64 supra_16_5"))

    vm = VM(State())
    vm.run(program, tmp_outdir)

    assert int(vm.state.csr.get(CSR.ERR, 0)) == 0
    assert float(vm.state.mu_information) >= 64.0
    assert str(vm.state.csr.get(CSR.CERT_ADDR, "")), "REVEAL should write a cert address"

    receipts_path = tmp_outdir / "step_receipts.json"
    s_value = chsh_from_receipts_path(receipts_path)
    assert s_value == Fraction(16, 5)
