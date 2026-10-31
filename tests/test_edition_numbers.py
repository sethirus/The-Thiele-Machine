"""Edition-dependent numbers match the receipt.

The release record names the audit report by its SHA-256 and corpus digest.
Both come from the receipt; this test reads it and checks the published copy, so
a change to either side fails here.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BOOK = ROOT / "monograph" / "monograph.tex"
COMPANION_CHECKS = ROOT / "monograph" / "COMPANION_CHECKS.txt"
RECEIPT = ROOT / "artifacts" / "print_assumptions_all_proofs.json"


def _release_block() -> str:
    text = COMPANION_CHECKS.read_text(encoding="utf-8")
    start = text.index("Companion sources:")
    return text[start:text.index("END RELEASE RECORD", start)]


def _joined_hex(block: str, label: str) -> str:
    """The hex string after `label`, which the block wraps over two lines."""
    tail = block[block.index(label) + len(label):]
    parts = re.findall(r"[0-9a-f]{16,}", tail)
    return parts[0] + parts[1]



def test_release_block_names_the_committed_receipt() -> None:
    block = _release_block()
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    assert _joined_hex(block, "corpus digest") == receipt["corpus_digest"]
    assert _joined_hex(block, "SHA-256") == hashlib.sha256(RECEIPT.read_bytes()).hexdigest()
