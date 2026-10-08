"""Every proof file is under the kernel-conversion vacuity gate.

scripts/vacuity_targets.json lists the files the vacuity gate probes. A file
in coq/_CoqProject or minimal/ that is not listed would carry theorems the gate
never checks, so this test fails when one is missing, when a target names a file
that does not exist, and when a logical module name does not match the file's
place in the project. The one exempt file is a fixture whose theorems are
vacuous on purpose, to test the gate itself.
"""

from __future__ import annotations

import json
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
MANIFEST = REPO_ROOT / "scripts" / "vacuity_targets.json"
COQ_PROJECT = REPO_ROOT / "coq" / "_CoqProject"

VACUITY_EXEMPT = {
    "coq/test_fixtures/VacuitySmoke.v": "its theorems are vacuous on purpose; the gate's own test reads them",
}


def project_proof_files() -> set[str]:
    """Repo-relative paths of every proof file: _CoqProject entries and minimal/*.v."""
    files: set[str] = set()
    for line in COQ_PROJECT.read_text().splitlines():
        line = line.strip()
        if line.endswith(".v") and not line.startswith("-"):
            files.add((COQ_PROJECT.parent / line).resolve().relative_to(REPO_ROOT).as_posix())
    for path in (REPO_ROOT / "minimal").glob("*.v"):
        files.add(path.relative_to(REPO_ROOT).as_posix())
    return files


def manifest_targets() -> dict[str, str]:
    data = json.loads(MANIFEST.read_text())
    return {entry["path"]: entry["logical"] for entry in data["targets"]}


def test_every_proof_file_is_a_vacuity_target() -> None:
    targets = manifest_targets()
    missing = sorted(
        path for path in project_proof_files()
        if path not in targets and path not in VACUITY_EXEMPT
    )
    assert not missing, "proof files outside the vacuity manifest:\n" + "\n".join(missing)


def test_vacuity_targets_exist_and_are_unique() -> None:
    data = json.loads(MANIFEST.read_text())
    paths = [entry["path"] for entry in data["targets"]]
    assert len(paths) == len(set(paths)), "duplicate vacuity targets"
    absent = sorted(path for path in paths if not (REPO_ROOT / path).is_file())
    assert not absent, "vacuity targets naming no file:\n" + "\n".join(absent)


def test_vacuity_logical_names_follow_the_project_layout() -> None:
    wrong = []
    for path, logical in manifest_targets().items():
        stem = Path(path).stem
        expected = ("Minimal." if path.startswith("minimal/") else "Kernel.") + stem
        if path.startswith("coq/test_fixtures/"):
            expected = "TestFixtures." + stem
        if logical != expected:
            wrong.append(f"{path}: {logical} (expected {expected})")
    assert not wrong, "logical names off the project layout:\n" + "\n".join(wrong)


def test_the_exempt_set_is_only_the_gate_fixture() -> None:
    assert set(VACUITY_EXEMPT) == {"coq/test_fixtures/VacuitySmoke.v"}
    assert all(VACUITY_EXEMPT.values()), "an exemption needs a reason"
