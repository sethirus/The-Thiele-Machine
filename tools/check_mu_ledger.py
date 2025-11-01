"""Cross-check μ-ledger fields for internal consistency."""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path


def _iter_receipts(root: Path) -> Iterable[Path]:
    for path in root.rglob("receipt_*.json"):
        yield path
    receipts_dir = root / "receipts"
    if receipts_dir.exists():
        for path in receipts_dir.glob("*.json"):
            yield path


def _check_receipt(path: Path) -> list[str]:
    payload = json.loads(path.read_text())
    if not isinstance(payload, dict):
        return []
    errors: list[str] = []

    mu_question = payload.get("mu_question")
    mu_answer = payload.get("mu_answer")
    counters = payload.get("counters", {})
    info_gain = counters.get("info_gain")

    if mu_question is not None:
        question_bits = float(mu_question)
        if question_bits < 0:
            errors.append(f"{path}: mu_question is negative")
        remainder = math.fmod(question_bits, 8.0)
        if not math.isclose(remainder, 0.0, abs_tol=1e-6):
            errors.append(
                f"{path}: mu_question={mu_question} is not an 8-bit multiple"
            )

    if mu_answer is not None:
        if not math.isfinite(mu_answer):
            errors.append(f"{path}: mu_answer is not finite")
        if mu_answer < 0:
            errors.append(f"{path}: mu_answer is negative")
    if info_gain is not None and mu_answer is not None:
        if not math.isclose(float(mu_answer), float(info_gain), rel_tol=1e-9, abs_tol=1e-9):
            errors.append(
                f"{path}: info_gain ({info_gain}) does not match mu_answer ({mu_answer})"
            )

    mu_question_bits = payload.get("mu_question_bits")
    if mu_question_bits is not None and mu_question is not None:
        if not math.isclose(float(mu_question_bits), float(mu_question), rel_tol=1e-9, abs_tol=1e-9):
            errors.append(
                f"{path}: mu_question_bits ({mu_question_bits}) does not match mu_question ({mu_question})"
            )

    return errors


def main(argv: list[str]) -> int:
    root = Path(argv[1]) if len(argv) > 1 else Path(".")
    errors: list[str] = []
    for receipt_path in _iter_receipts(root):
        try:
            errors.extend(_check_receipt(receipt_path))
        except json.JSONDecodeError as exc:
            errors.append(f"{receipt_path}: invalid JSON ({exc})")
    if errors:
        for err in errors:
            print(f"ERROR: {err}")
        return 1
    print("μ-ledger validation passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
