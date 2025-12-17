from __future__ import annotations

"""Receipt-defined DI-randomness transcript.

This is the D1 building block in MASTER_MILESTONES:
- decode a deterministic, canonical transcript from *VM step receipts* only
- do not consult stdout/logs or unreceipted side channels

For now we treat the CHSH trial stream as the canonical DI-randomness transcript.
"""

from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Tuple

from thielecpu.receipts import load_receipts

from tools.chsh_receipts import ReceiptTrial, decode_trials_from_receipts


@dataclass(frozen=True)
class RNGTranscript:
    trials: Tuple[ReceiptTrial, ...]
    has_structure_addition: bool


def _has_structure_addition_from_receipts(receipts_path: Path) -> bool:
    for receipt in load_receipts(receipts_path):
        pre_cert = str(receipt.pre_state.get("cert_addr", ""))
        post_cert = str(receipt.post_state.get("cert_addr", ""))
        if (not pre_cert) and post_cert:
            return True
    return False


def decode_rng_transcript(receipts_path: Path) -> RNGTranscript:
    """Decode a DI-randomness transcript from step receipts.

    Current canonicalization:
    - Trials are extracted via `tools.chsh_receipts.decode_trials_from_receipts`.
    - Structure-addition is detected as a cert_addr transition from empty -> non-empty.
    """

    receipts_path = Path(receipts_path)
    trials: List[ReceiptTrial] = list(decode_trials_from_receipts(receipts_path))
    has_structure_addition = _has_structure_addition_from_receipts(receipts_path)
    return RNGTranscript(trials=tuple(trials), has_structure_addition=has_structure_addition)


__all__ = [
    "RNGTranscript",
    "decode_rng_transcript",
]
