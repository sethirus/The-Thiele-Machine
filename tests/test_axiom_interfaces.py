"""Executable checks corresponding to documented axioms."""

from __future__ import annotations

from pathlib import Path

import pytest
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

from tools.receipts import (
    ReceiptValidator,
    ReceiptValidationError,
    compute_step_hash,
    compute_global_digest,
)
from thielecpu.isa import CSR, Opcode, encode, decode
from thielecpu.mdl import mdlacc
from thielecpu.receipts import WitnessState, hash_snapshot
from thielecpu.state import State
from thielecpu.vm import VM


def _build_step(mu_delta: int | float = 1) -> dict:
    return {
        "idx": 0,
        "transition": "unit_test",
        "mu_delta": mu_delta,
        "solver": "unit-solver",
        "solver_cmdline": "pytest",
    }


def _assemble_receipt(mutator=None) -> dict:
    private_key = Ed25519PrivateKey.generate()
    public_hex = private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    ).hex()

    step = _build_step()
    step_hash = compute_step_hash(step)
    step_with_hash = dict(step)
    step_with_hash["step_hash"] = step_hash

    digest = compute_global_digest([step_hash])
    signature = private_key.sign(bytes.fromhex(digest)).hex()

    receipt = {
        "spec_version": "1.0",
        "kernel_pubkey": public_hex,
        "steps": [step_with_hash],
        "global_digest": digest,
        "signature": signature,
    }

    if mutator is not None:
        mutator(receipt)

    return receipt


def test_axiom_check_step_sound_rejects_invalid_receipt():
    """Unsound receipts (negative μ charge) must be rejected."""

    receipt = _assemble_receipt(
        mutator=lambda data: data["steps"][0].update({"mu_delta": -1})
    )
    validator = ReceiptValidator()
    with pytest.raises(ReceiptValidationError):
        validator.validate(receipt)


def test_axiom_check_step_complete_accepts_valid_receipt():
    """A canonically formed step is accepted by the checker."""

    receipt = _assemble_receipt()
    validator = ReceiptValidator()
    mu_total = validator.validate(receipt)
    assert mu_total == pytest.approx(1.0)


def test_axiom_mu_lower_bound_matches_certificate_bits(tmp_path):
    """μ-accounting must charge at least the size of attached certificates."""

    cert_path = tmp_path / "cert.txt"
    cert_bytes = b"solver-certificate"
    cert_path.write_bytes(cert_bytes)

    state = State()
    module = state.pnew({1, 2, 3})
    state.csr[CSR.CERT_ADDR] = str(cert_path)

    before = state.mu_operational
    mdlacc(state, module, consistent=True)
    delta = state.mu_operational - before

    assert delta >= len(cert_bytes) * 8


def test_axiom_state_eqb_refl_hash_consistency():
    """Witness state hashing behaves reflexively for identical snapshots."""

    witness = WitnessState(pc=7, status=1, mu_acc=42, cert_addr="addr")
    first_snapshot = witness.snapshot()
    second_snapshot = witness.snapshot()

    assert first_snapshot == second_snapshot
    assert hash_snapshot(first_snapshot) == hash_snapshot(second_snapshot)

    mutated = dict(second_snapshot)
    mutated["pc"] += 1
    assert hash_snapshot(first_snapshot) != hash_snapshot(mutated)


@pytest.mark.parametrize("op", list(Opcode))
@pytest.mark.parametrize("a", [0, 17, 255])
@pytest.mark.parametrize("b", [0, 23, 255])
def test_axiom_decode_encode_id_roundtrip(op: Opcode, a: int, b: int):
    """Encoding then decoding instructions preserves the payload."""

    word = encode(op, a, b)
    decoded = decode(word)
    assert decoded == (op, a & 0xFF, b & 0xFF)


def test_axiom_utm_simulation_steps_receipts_bounded(tmp_path):
    """Each VM instruction yields one witness receipt (bounded simulation)."""

    vm = VM(State())
    program = [("EMIT", "hello"), ("EMIT", "world")]
    vm.run(program, Path(tmp_path))

    assert len(vm.step_receipts) == len(program)
    for receipt in vm.step_receipts:
        assert receipt.post_state["pc"] == receipt.pre_state["pc"] + 1


def test_axiom_pc29_definition_documented():
    """Documentation retains the rule-table linkage for PC=29."""

    backup_path = (
        Path(__file__)  # tests directory
        .resolve()
        .parents[1]
        / "coq"
        / "thieleuniversal"
        / "coqproofs"
        / "ThieleUniversal.v.backup"
    )
    text = backup_path.read_text(encoding="utf-8")
    assert "Definition IS_ApplyRule_Start (pc : nat) : Prop := pc = 29." in text
    assert "Lemma pc_29_implies_registers_from_rule_table" in text


def test_axiom_find_rule_from_memory_components_consistency():
    """Reconstructing a rule from memory components matches table lookup."""

    def find_rule_py(rules, q_cur, sym_cur):
        for rule in rules:
            if rule[0] == q_cur and rule[1] == sym_cur:
                return rule[2], rule[3], rule[4]
        return None

    rules = [
        (0, 0, 1, 1, 0),
        (1, 1, 2, 0, -1),
        (2, 0, 3, 1, 1),
    ]
    RULES_START_ADDR = 32
    memory = [0] * (RULES_START_ADDR + len(rules) * 5 + 5)

    encoded_rules: list[int] = []
    for idx, rule in enumerate(rules):
        base = RULES_START_ADDR + idx * 5
        memory[base : base + 5] = list(rule)
        encoded_rules.extend(rule)

    i = 1
    base = RULES_START_ADDR + i * 5
    q_prime = memory[base + 2]
    write_value = memory[base + 3]
    move_value = memory[base + 4]

    # Memory slice matches the encoded rule list.
    memory_slice = []
    for idx in range(len(rules)):
        start = RULES_START_ADDR + idx * 5
        memory_slice.extend(memory[start : start + 5])
    assert memory_slice == encoded_rules

    lookup = find_rule_py(rules, rules[i][0], rules[i][1])
    assert lookup == (q_prime, write_value, move_value)

    backup_path = (
        Path(__file__).resolve().parents[1]
        / "coq"
        / "thieleuniversal"
        / "coqproofs"
        / "ThieleUniversal.v.backup"
    )
    text = backup_path.read_text(encoding="utf-8")
    assert "Lemma find_rule_from_memory_components" in text
