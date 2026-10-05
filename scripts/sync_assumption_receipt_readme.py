#!/usr/bin/env python3
"""Synchronize published proof-hygiene counters with the assumption receipt."""

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
            f"receipt pattern matched {actual} times, expected {count}: {pattern}"
        )
    return updated


def synchronize(readme: Path, receipt: Path, monograph: Path | None = None,
                distillation: Path | None = None,
                citation: Path | None = None) -> None:
    payload = json.loads(receipt.read_text(encoding="utf-8"))
    summary = payload["summary"]
    axioms = summary["unique_axioms_used"]
    theorem_count = formatted(summary["theorems_probed"])
    file_count = formatted(payload["files_probed"])
    closed = formatted(summary["closed_under_global_context"])
    dependent = formatted(summary["depend_on_axioms"])

    text = readme.read_text(encoding="utf-8")
    text = replace_exact(
        text,
        r"[Aa]ssumption receipt: [\d,]+ theorems probed",
        f"assumption receipt: {theorem_count} theorems probed",
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
            f"`{label}` ({formatted(axioms.get(qualified, 0))})",
            1,
        )

    readme.write_text(text, encoding="utf-8")

    if monograph is not None:
        text = monograph.read_text(encoding="utf-8")
        text = replace_exact(
            text,
            r"full-corpus probe covers [\d,]+ named theorems across [\d,]+ files: "
            r"[\d,]+ close under the global Coq context outright, and [\d,]+ use only "
            r"Coq standard-library assumptions",
            f"full-corpus probe covers {theorem_count} named theorems across "
            f"{file_count} files: {closed} close under the global Coq context outright, "
            f"and {dependent} use only Coq standard-library assumptions",
            1,
        )
        text = replace_exact(
            text,
            r"Zero project-local axioms appear in any of the [\d,]+ dependency trees",
            f"Zero project-local axioms appear in any of the {theorem_count} dependency trees",
            1,
        )
        monograph.write_text(text, encoding="utf-8")

    if distillation is not None:
        text = distillation.read_text(encoding="utf-8")
        text = replace_exact(
            text,
            r"[Aa]ssumption receipt covers [\d,]+ statements across [\d,]+ files: "
            r"[\d,]+ closed under the global context and [\d,]+ depending on "
            r"standard-library assumptions",
            f"assumption receipt covers {theorem_count} statements across "
            f"{file_count} files: {closed} closed under the global context and "
            f"{dependent} depending on standard-library assumptions",
            1,
        )
        distillation.write_text(text, encoding="utf-8")

    if citation is not None:
        text = citation.read_text(encoding="utf-8")
        text = replace_exact(
            text,
            r"assumption receipt covers [\d,]+\n\s+statements across [\d,]+ files: "
            r"[\d,]+ are closed under the global context, [\d,]+ depend on",
            f"assumption receipt covers {theorem_count}\n  statements across {file_count} "
            f"files: {closed} are closed under the global context, {dependent} depend on",
            1,
        )
        citation.write_text(text, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--receipt",
        type=Path,
        default=Path("artifacts/print_assumptions_all_proofs.json"),
    )
    parser.add_argument("--readme", type=Path, default=Path("README.md"))
    parser.add_argument("--monograph", type=Path, default=Path("monograph/monograph.tex"))
    parser.add_argument("--distillation", type=Path, default=Path("THIELE_MACHINE.txt"))
    parser.add_argument("--citation", type=Path, default=Path("CITATION.cff"))
    args = parser.parse_args()
    synchronize(args.readme, args.receipt, args.monograph,
                args.distillation, args.citation)


if __name__ == "__main__":
    main()
