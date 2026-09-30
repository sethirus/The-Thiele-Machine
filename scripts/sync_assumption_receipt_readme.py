#!/usr/bin/env python3
"""Synchronize README proof-hygiene counters with the assumption receipt."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re


def formatted(value: int) -> str:
    return f"{value:,}"


def replace_exact(text: str, pattern: str, replacement: str, count: int) -> str:
    updated, actual = re.subn(pattern, replacement, text)
    if actual != count:
        raise ValueError(
            f"README receipt pattern matched {actual} times, expected {count}: {pattern}"
        )
    return updated


def synchronize(readme: Path, receipt: Path) -> None:
    summary = json.loads(receipt.read_text(encoding="utf-8"))["summary"]
    axioms = summary["unique_axioms_used"]
    theorem_count = formatted(summary["theorems_probed"])
    file_count = formatted(summary["files_probed"])
    closed = formatted(summary["closed_under_global_context"])
    dependent = formatted(summary["depend_on_axioms"])

    text = readme.read_text(encoding="utf-8")
    text = replace_exact(
        text,
        r"committed assumption receipt: [\d,]+ theorems probed",
        f"committed assumption receipt: {theorem_count} theorems probed",
        1,
    )
    text = replace_exact(
        text,
        r"[\d,]+ of those theorems are closed under the global context outright; "
        r"the remaining [\d,]+ use only Coq standard-library assumptions",
        f"{closed} of those theorems are closed under the global context outright; "
        f"the remaining {dependent} use only Coq standard-library assumptions",
        1,
    )
    text = replace_exact(
        text,
        r"records [\d,]+ addressable theorems probed across [\d,]+ files",
        f"records {theorem_count} addressable theorems probed across {file_count} files",
        1,
    )
    text = replace_exact(
        text,
        r"reports [\d,]+ addressable theorems probed across [\d,]+ files",
        f"reports {theorem_count} addressable theorems probed across {file_count} files",
        1,
    )
    text = replace_exact(
        text,
        r"The split: [\d,]+ close under the global context outright, and the remaining "
        r"[\d,]+ lean only on Coq-stdlib axiom families",
        f"The split: {closed} close under the global context outright, and the remaining "
        f"{dependent} lean only on Coq-stdlib axiom families",
        1,
    )

    labels = {
        "functional_extensionality_dep":
            "FunctionalExtensionality.functional_extensionality_dep",
        "eq_rect_eq": "Eqdep.Eq_rect_eq.eq_rect_eq",
        "sig_forall_dec": "ClassicalDedekindReals.sig_forall_dec",
        "sig_not_dec": "ClassicalDedekindReals.sig_not_dec",
        "classic": "Classical_Prop.classic",
    }
    for label, qualified in labels.items():
        text = replace_exact(
            text,
            rf"`{label}` \([\d,]+\)",
            f"`{label}` ({formatted(axioms[qualified])})",
            1,
        )

    readme.write_text(text, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--receipt",
        type=Path,
        default=Path("artifacts/print_assumptions_all_proofs.json"),
    )
    parser.add_argument("--readme", type=Path, default=Path("README.md"))
    args = parser.parse_args()
    synchronize(args.readme, args.receipt)


if __name__ == "__main__":
    main()
