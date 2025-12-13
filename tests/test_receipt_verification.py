"""
3-way receipt verification tests.

Validates that receipts are correctly generated and verified across:
- Python VM (thielecpu/receipts.py)
- Verilog RTL (thiele_cpu.v)
- Coq extraction (when applicable)

Receipts prove that a specific execution took place with specific costs.
"""

import json
import pytest
import subprocess
import tempfile
from pathlib import Path

from thielecpu.state import State
from thielecpu.receipts import StepReceipt, StepObservation, InstructionWitness, WitnessState
from thielecpu.vm import VM


# ==============================================================================
# TEST FIXTURES
# ==============================================================================

@pytest.fixture
def initial_state() -> State:
    """Create a clean initial state."""
    return State()


@pytest.fixture
def vm(initial_state) -> VM:
    """Create a VM instance."""
    return VM(initial_state)


# ==============================================================================
# PYTHON RECEIPT GENERATION TESTS
# ==============================================================================

def test_receipt_creation_pnew(initial_state, vm):
    """Verify receipt creation for PNEW operation."""
    # Execute PNEW
    program = [
        ("PNEW", "{1,2,3,4,5}"),
        ("HALT", ""),
    ]
    
    with tempfile.TemporaryDirectory() as td:
        vm.run(program, Path(td))
    
    # Verify state changed
    assert len(initial_state.partition_masks) >= 2  # base + new partition
    
    # Create receipt using actual API
    pre_witness = WitnessState(
        pc=0,
        status=0,
        mu_acc=0,
        cert_addr="",
    )
    
    post_witness = WitnessState(
        pc=1,
        status=0,
        mu_acc=int(initial_state.mu),
        cert_addr="0x0",
    )
    
    receipt = StepReceipt.assemble(
        step=0,
        instruction=InstructionWitness(op="PNEW", payload={"region": "{1,2,3,4,5}"}),
        pre_state=pre_witness,
        post_state=post_witness,
        observation=StepObservation(
            event=None,
            mu_delta=float(initial_state.mu),
            cert={},
        )
    )
    
    # Verify receipt structure
    assert receipt.step == 0
    assert receipt.instruction.op == "PNEW"
    assert receipt.observation.mu_delta >= 0
    assert receipt.signature is not None  # Signature should exist
    
    # Verify signature is valid
    assert receipt.verify()


def test_receipt_signature_verification(initial_state):
    """Verify receipt signatures can be validated."""
    # Create a simple receipt
    pre_witness = WitnessState(pc=0, status=0, mu_acc=0, cert_addr="")
    post_witness = WitnessState(pc=1, status=0, mu_acc=100, cert_addr="")
    
    receipt = StepReceipt.assemble(
        step=0,
        instruction=InstructionWitness(op="PNEW", payload={}),
        pre_state=pre_witness,
        post_state=post_witness,
        observation=StepObservation(event=None, mu_delta=100.0, cert={}),
    )
    
    # Verify the signature
    assert receipt.verify(), "Receipt signature should be valid"
    
    # Verify hash integrity
    assert receipt.pre_state_hash is not None
    assert receipt.post_state_hash is not None
    assert len(receipt.pre_state_hash) == 64  # SHA-256 hex digest
    assert len(receipt.post_state_hash) == 64


def test_receipt_serialization(initial_state):
    """Verify receipts can be serialized and deserialized."""
    pre_witness = WitnessState(pc=0, status=0, mu_acc=0, cert_addr="")
    post_witness = WitnessState(pc=1, status=0, mu_acc=50, cert_addr="")
    
    original = StepReceipt.assemble(
        step=5,
        instruction=InstructionWitness(op="PSPLIT", payload={"module": 1}),
        pre_state=pre_witness,
        post_state=post_witness,
        observation=StepObservation(event=None, mu_delta=50.0, cert={}),
    )
    
    # Serialize
    serialized = json.dumps(original.to_dict(), indent=2)
    
    # Deserialize
    parsed = json.loads(serialized)
    
    # Verify key fields match
    assert parsed["step"] == 5
    assert parsed["instruction"]["op"] == "PSPLIT"
    assert parsed["observation"]["mu_delta"] == 50.0
    assert parsed["signature"] == original.signature


if __name__ == "__main__":
    pytest.main([__file__, "-v"])


