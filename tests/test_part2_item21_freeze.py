"""Freeze checks for Part 2 Item 2.1, monotone multi-valued records."""

from hashlib import sha256
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "coq/kernel/foundation/GrowingRecordCore.v"
FREEZE = ROOT / "research/rounds/2026-10-01-part2-item2.1-round1-freeze.md"
INPUTS = {
    "coq/kernel/foundation/GrowingRecordCore.v":
        "8f43e6636d5c7f32c9a32d01755749648ffe0bcc125d15f22d4a54b708e61530",
    "coq/kernel/foundation/StructuralCore.v":
        "d42903fb4e1645a5f9eb5ebfe08fe44a469c7fee5c3a316924069a5049f2c07b",
    "coq/kernel/foundation/StructuralCoreRound4.v":
        "45d1dc9496629f4b5e392492851f361e7d9ace047322e4e2bf5d56df5615f9fe",
}


def test_item21_freeze_pins_exact_definition_source() -> None:
    assert CORE.exists()
    assert FREEZE.exists()
    text = FREEZE.read_text()
    for relative, expected in INPUTS.items():
        assert sha256((ROOT / relative).read_bytes()).hexdigest() == expected
        assert f"`{relative}` | `{expected}`" in text


def test_item21_freezes_exact_targets_before_results() -> None:
    core = CORE.read_text()
    freeze = FREEZE.read_text()
    for target in (
        "growing_record_decomposes",
        "thresholds_determine_record",
        "record_price_iff_threshold_price",
        "one_latch_suffices",
        "chain_needs_bits",
    ):
        assert f"Definition {target}" in core
        assert f"`{target}`" in freeze
    assert freeze.count("| PROVED |") == 4
    assert "one_latch_suffices` | REFUTED" in freeze
    assert "Outcome: PROVED" not in freeze
    assert "Outcome: REFUTED" not in freeze
