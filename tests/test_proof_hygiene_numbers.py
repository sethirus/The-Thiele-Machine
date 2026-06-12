"""README Proof Hygiene numbers must equal the committed assumption receipt.

The README publishes the probe split (theorems probed, closed under the
global context, stdlib-axiom dependents, per-family counts, zero
project-local findings). This test holds that prose to
artifacts/print_assumptions_all_proofs.json so the two cannot drift apart
silently.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
README = REPO_ROOT / "README.md"
RECEIPT = REPO_ROOT / "artifacts" / "print_assumptions_all_proofs.json"


def _readme_proof_hygiene_section() -> str:
    text = README.read_text(encoding="utf-8")
    start = text.index("## Proof Hygiene")
    end = text.index("\n## ", start + 1)
    return text[start:end]


def _number_near(section: str, pattern: str) -> int:
    """Extract the integer matched by pattern's single capture group."""
    match = re.search(pattern, section)
    assert match, f"README Proof Hygiene section lost the number for: {pattern}"
    return int(match.group(1).replace(",", ""))


def test_readme_proof_hygiene_numbers_match_receipt() -> None:
    summary = json.loads(RECEIPT.read_text(encoding="utf-8"))["summary"]
    section = _readme_proof_hygiene_section()

    expected = {
        "theorems probed": (
            r"([\d,]+) addressable theorems\s+probed",
            summary["theorems_probed"],
        ),
        "closed under global context": (
            r"([\d,]+) close under the global\s+context",
            summary["closed_under_global_context"],
        ),
        "stdlib-axiom dependents": (
            r"remaining ([\d,]+) lean only on Coq-stdlib",
            summary["depend_on_axioms"],
        ),
        "functional_extensionality_dep": (
            r"`functional_extensionality_dep`\s+\(([\d,]+)\)",
            summary["unique_axioms_used"][
                "FunctionalExtensionality.functional_extensionality_dep"
            ],
        ),
        "sig_forall_dec": (
            r"`sig_forall_dec` \(([\d,]+)\)",
            summary["unique_axioms_used"]["ClassicalDedekindReals.sig_forall_dec"],
        ),
        "sig_not_dec": (
            r"`sig_not_dec`\s+\(([\d,]+)\)",
            summary["unique_axioms_used"]["ClassicalDedekindReals.sig_not_dec"],
        ),
        "classic": (
            r"`classic` \(([\d,]+)\)",
            summary["unique_axioms_used"]["Classical_Prop.classic"],
        ),
    }

    mismatches = []
    for label, (pattern, want) in expected.items():
        got = _number_near(section, pattern)
        if got != want:
            mismatches.append(f"{label}: README says {got}, receipt says {want}")
    assert not mismatches, "; ".join(mismatches)

    assert summary["user_or_third_party_axiom_findings"] == 0, (
        "receipt reports project-local/third-party axiom findings; "
        "the README's zero-project-local claim no longer holds"
    )
