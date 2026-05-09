"""E6 — VMState field audit test.

Asserts that Python VMState has exactly the 12 canonical fields defined in the
Coq VMState record (VMState.v lines 1697-1709).  Fails if a field is added or
removed without updating both the bridge and this test.

The canonical 12-field set:
  vm_graph, vm_csrs, vm_regs, vm_mem, vm_pc, vm_mu,
  vm_mu_tensor, vm_err, vm_logic_acc, vm_mstatus, vm_witness, vm_certified

Coq source: coq/kernel/foundation/VMState.v (Record VMState)
Python source: thielecpu/vm.py (class VMState)
Bridge: coq/kami_hw/FullAbstraction.v (abs_full_snapshot)
"""

import dataclasses
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]

# Canonical field set — update BOTH here AND in VMState.v / vm.py if a field
# is added.  This test is the trip-wire.
CANONICAL_VM_STATE_FIELDS: frozenset[str] = frozenset({
    "vm_graph",
    "vm_csrs",
    "vm_regs",
    "vm_mem",
    "vm_pc",
    "vm_mu",
    "vm_mu_tensor",
    "vm_err",
    "vm_logic_acc",
    "vm_mstatus",
    "vm_witness",
    "vm_certified",
})


# ---------------------------------------------------------------------------
# Python layer
# ---------------------------------------------------------------------------

def test_python_vmstate_field_count() -> None:
    """VMState has exactly 12 fields — no more, no less."""
    from thielecpu.vm import VMState
    fields = {f.name for f in dataclasses.fields(VMState)}
    assert fields == CANONICAL_VM_STATE_FIELDS, (
        f"Python VMState fields diverged from canonical set.\n"
        f"  Extra fields:   {fields - CANONICAL_VM_STATE_FIELDS}\n"
        f"  Missing fields: {CANONICAL_VM_STATE_FIELDS - fields}\n"
        f"Update CANONICAL_VM_STATE_FIELDS in this test AND the Coq/bridge"
        f" sources."
    )


def test_python_vmstate_no_extra_vm_prefixed_fields() -> None:
    """No new vm_* fields snuck in outside the canonical set."""
    from thielecpu.vm import VMState
    all_vm_fields = {
        f.name for f in dataclasses.fields(VMState) if f.name.startswith("vm_")
    }
    assert all_vm_fields <= CANONICAL_VM_STATE_FIELDS, (
        f"Unexpected vm_* field(s) in Python VMState: "
        f"{all_vm_fields - CANONICAL_VM_STATE_FIELDS}"
    )


# ---------------------------------------------------------------------------
# Coq source layer
# ---------------------------------------------------------------------------

def test_coq_vmstate_record_fields() -> None:
    """Coq VMState record contains exactly the 12 canonical fields."""
    flat = ROOT / "coq" / "kernel" / "VMState.v"
    if flat.exists():
        vmstate_v = flat
    else:
        kernel_root = ROOT / "coq" / "kernel"
        candidates = list(kernel_root.rglob("VMState.v")) if kernel_root.exists() else []
        if not candidates:
            pytest.skip("VMState.v not found")
        vmstate_v = candidates[0]

    text = vmstate_v.read_text()

    # Find the Record VMState block
    record_match = re.search(
        r"Record VMState\s*:=\s*\{(.*?)\}\s*\.",
        text,
        re.DOTALL,
    )
    assert record_match, "Could not locate 'Record VMState := { ... }.' in VMState.v"

    record_body = record_match.group(1)
    # Extract field names: lines like "  vm_foo : SomeType;"
    found_fields = frozenset(re.findall(r"^\s*(vm_\w+)\s*:", record_body, re.MULTILINE))

    assert found_fields == CANONICAL_VM_STATE_FIELDS, (
        f"Coq VMState record fields diverged from canonical set.\n"
        f"  Extra fields:   {found_fields - CANONICAL_VM_STATE_FIELDS}\n"
        f"  Missing fields: {CANONICAL_VM_STATE_FIELDS - found_fields}\n"
        f"Update CANONICAL_VM_STATE_FIELDS in this test AND vm.py / bridge."
    )


# ---------------------------------------------------------------------------
# Bridge consistency
# ---------------------------------------------------------------------------

def test_coq_bridge_covers_all_fields() -> None:
    """abs_full_snapshot in FullAbstraction.v references all 12 canonical fields."""
    full_abs = ROOT / "coq" / "kami_hw" / "FullAbstraction.v"
    if not full_abs.exists():
        pytest.skip("FullAbstraction.v not found")

    text = full_abs.read_text()

    # Every canonical field should appear at least once in the bridge file.
    missing = {f for f in CANONICAL_VM_STATE_FIELDS if f not in text}
    assert not missing, (
        f"Canonical VMState field(s) absent from FullAbstraction.v: {missing}\n"
        f"The bridge may not cover all fields."
    )
