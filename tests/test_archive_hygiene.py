from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

ACTIVE_ROOT_MARKDOWN = {
    "FULL_REFINEMENT_GUIDE.md",
    "INQUISITOR_REPORT.md",
    "ISA_V2_SPEC.md",
    "README.md",
    "REPO_CLOSEOUT_NO_SHORTCUTS_PLAN.md",
}

ARCHIVED_ALTERNATE_EXTRACTION_FILES = {
    "archive/build_artifacts/alternate_extraction_lineage/thiele_core_complete.ml",
    "archive/build_artifacts/alternate_extraction_lineage/thiele_core_complete.mli",
    "archive/build_artifacts/alternate_extraction_lineage/kami_hw/Target_complete.ml",
    "archive/build_artifacts/alternate_extraction_lineage/kami_hw/Target_complete.mli",
}

FORBIDDEN_ACTIVE_ALTERNATE_EXTRACTION_FILES = {
    "build/thiele_core_complete.ml",
    "build/thiele_core_complete.mli",
    "build/kami_hw/Target_complete.ml",
    "build/kami_hw/Target_complete.mli",
}


def test_root_markdown_surface_is_allowlisted() -> None:
    root_markdown = {path.name for path in ROOT.glob("*.md")}

    assert root_markdown == ACTIVE_ROOT_MARKDOWN


def test_alternate_extraction_lineage_is_archive_only() -> None:
    active = [
        rel
        for rel in sorted(FORBIDDEN_ACTIVE_ALTERNATE_EXTRACTION_FILES)
        if (ROOT / rel).exists()
    ]
    archived = [
        rel
        for rel in sorted(ARCHIVED_ALTERNATE_EXTRACTION_FILES)
        if not (ROOT / rel).exists()
    ]

    assert not active, "alternate extraction artifacts remain active:\n" + "\n".join(active)
    assert not archived, "archived alternate extraction artifacts missing:\n" + "\n".join(archived)
