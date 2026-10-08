"""Edition-dependent numbers in the book match the receipt and the Coq sources.

The release block names the audit report by its SHA-256 and corpus digest,
and the text quotes the universal programs' lengths and paid-site counts.
Each of those comes from one source of truth; this test reads that source
and checks the book's copy, so a change to either side fails here.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BOOK = ROOT / "monograph" / "monograph.tex"
RECEIPT = ROOT / "artifacts" / "print_assumptions_all_proofs.json"
U_LAYOUT = ROOT / "coq" / "kernel" / "foundation" / "UniversalLayout.v"
UP_LAYOUT = ROOT / "coq" / "kernel" / "foundation" / "UniversalPLayout.v"


def _release_block() -> str:
    text = BOOK.read_text(encoding="utf-8")
    start = text.index("Companion sources:")
    return text[start:text.index("\\end{verbatim}", start)]


def _joined_hex(block: str, label: str) -> str:
    """The hex string after `label`, which the block wraps over two lines."""
    tail = block[block.index(label) + len(label):]
    parts = re.findall(r"[0-9a-f]{16,}", tail)
    return parts[0] + parts[1]


def _coq_number(path: Path, name: str) -> int:
    match = re.search(rf"{re.escape(name)} = (\d+)", path.read_text(encoding="utf-8"))
    assert match, f"{name} not found in {path.name}"
    return int(match.group(1))


def test_release_block_names_the_committed_receipt() -> None:
    block = _release_block()
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    assert _joined_hex(block, "corpus digest") == receipt["corpus_digest"]
    assert _joined_hex(block, "SHA-256") == hashlib.sha256(RECEIPT.read_bytes()).hexdigest()


def test_universal_program_lengths_and_paid_sites_match_coq() -> None:
    text = BOOK.read_text(encoding="utf-8")
    u_len = _coq_number(U_LAYOUT, "U_len")
    up_len = _coq_number(UP_LAYOUT, "pu_U_len")
    u_paid = _coq_number(U_LAYOUT, "length paid_sites")
    up_paid = _coq_number(UP_LAYOUT, "length pu_paid_sites")
    assert f"{u_len} instructions" in text
    assert f"{up_len} instructions" in text
    assert f"the {u_paid} paid sites" in text
    assert f"{up_paid} paid sites, the {u_paid}" in text
    for doc in ("README.md", "THIELE_MACHINE.txt"):
        quoted = {int(n) for n in re.findall(r"\b(\d{4}) instructions",
                                             (ROOT / doc).read_text(encoding="utf-8"))}
        assert quoted <= {u_len, up_len}, f"{doc} quotes {sorted(quoted)}"
