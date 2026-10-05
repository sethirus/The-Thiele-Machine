"""A restored Coq build cache rebuilds exactly the sources that changed."""
from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "coq_build_manifest.py"
SPEC = importlib.util.spec_from_file_location("coq_build_manifest", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


@pytest.fixture
def tree(tmp_path, monkeypatch):
    monkeypatch.setattr(MODULE, "ROOT", tmp_path)
    for name, text in {
        "coq/_CoqProject": "-R kernel Kernel\n",
        "coq/Makefile.local": "",
        "coq/kernel/A.v": "Definition a := 0.\n",
        "coq/kernel/B.v": "Require Kernel.A.\n",
        "vendor/coq-undecidability/theories/_CoqProject": "-Q . Undecidability\n",
        "vendor/coq-undecidability/theories/L/L.v": "Inductive term := var.\n",
    }.items():
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    for name in ("coq/kernel/A.vo", "coq/kernel/B.vo", "coq/kernel/B.glob",
                 "vendor/coq-undecidability/theories/L/L.vo"):
        (tmp_path / name).write_bytes(b"compiled " + name.encode())
    return tmp_path


def mtime(root: Path, name: str) -> float:
    return (root / name).stat().st_mtime


def test_unchanged_sources_are_older_than_their_outputs(tree):
    manifest = tree / "build/manifest.json"
    MODULE.write(manifest)
    assert MODULE.apply(manifest) == 0
    for source, output in (("coq/kernel/A.v", "coq/kernel/A.vo"),
                           ("coq/kernel/B.v", "coq/kernel/B.vo"),
                           ("vendor/coq-undecidability/theories/L/L.v",
                            "vendor/coq-undecidability/theories/L/L.vo")):
        assert mtime(tree, source) < mtime(tree, output)
    # Project files are older than anything generated from them.
    assert mtime(tree, "coq/_CoqProject") < mtime(tree, "coq/kernel/A.vo")


def test_changed_source_is_newer_than_every_output(tree):
    manifest = tree / "build/manifest.json"
    MODULE.write(manifest)
    (tree / "coq/kernel/A.v").write_text("Definition a := 1.\n")
    assert MODULE.apply(manifest) == 0
    assert mtime(tree, "coq/kernel/A.v") > mtime(tree, "coq/kernel/A.vo")
    assert mtime(tree, "coq/kernel/A.v") > mtime(tree, "coq/kernel/B.vo")
    assert mtime(tree, "coq/kernel/B.v") < mtime(tree, "coq/kernel/B.vo")


def test_new_source_counts_as_changed(tree):
    manifest = tree / "build/manifest.json"
    MODULE.write(manifest)
    (tree / "coq/kernel/C.v").write_text("Definition c := 0.\n")
    assert MODULE.apply(manifest) == 0
    assert mtime(tree, "coq/kernel/C.v") > mtime(tree, "coq/kernel/A.vo")


def test_output_without_source_is_removed(tree):
    manifest = tree / "build/manifest.json"
    MODULE.write(manifest)
    (tree / "coq/kernel/B.v").unlink()
    assert MODULE.apply(manifest) == 0
    assert not (tree / "coq/kernel/B.vo").exists()
    assert not (tree / "coq/kernel/B.glob").exists()
    assert (tree / "coq/kernel/A.vo").exists()


COQ_SOURCES = ("coq/kernel/A.v", "coq/kernel/B.v")
VENDOR_SOURCES = ("vendor/coq-undecidability/theories/L/L.v",)


@pytest.mark.parametrize("name", ["coq/_CoqProject", "coq/Makefile.local",
                                  "vendor/coq-undecidability/theories/L/L.vo"])
def test_coq_flag_or_library_change_marks_coq_sources_only(tree, name):
    manifest = tree / "build/manifest.json"
    MODULE.write(manifest)
    with (tree / name).open("ab") as stream:
        stream.write(b"\n")
    assert MODULE.apply(manifest) == 0
    for source in COQ_SOURCES:
        assert mtime(tree, source) > mtime(tree, "coq/kernel/A.vo")
    # The vendored library is not rebuilt for a change above it.
    for source in VENDOR_SOURCES:
        assert mtime(tree, source) < mtime(tree, "vendor/coq-undecidability/theories/L/L.vo")


def test_vendor_flag_change_marks_vendor_sources(tree):
    manifest = tree / "build/manifest.json"
    MODULE.write(manifest)
    with (tree / "vendor/coq-undecidability/theories/_CoqProject").open("ab") as stream:
        stream.write(b"\n")
    assert MODULE.apply(manifest) == 0
    for source in VENDOR_SOURCES:
        assert mtime(tree, source) > mtime(tree, "vendor/coq-undecidability/theories/L/L.vo")
    for source in COQ_SOURCES:
        assert mtime(tree, source) < mtime(tree, "coq/kernel/A.vo")


@pytest.mark.parametrize("content", [None, "not json", '{"schema": 0}'])
def test_missing_or_foreign_manifest_asks_for_a_full_build(tree, content):
    manifest = tree / "build/manifest.json"
    if content is not None:
        manifest.parent.mkdir(parents=True, exist_ok=True)
        manifest.write_text(content)
    assert MODULE.apply(manifest) == 2


def test_schema_one_manifest_still_starts_an_incremental_build(tree):
    import json
    manifest = tree / "build/manifest.json"
    manifest.parent.mkdir(parents=True, exist_ok=True)
    sources = {MODULE.rel(p): MODULE.sha256(p)
               for scope in MODULE.SCOPES for p in MODULE.sources(scope)}
    manifest.write_text(json.dumps({"schema": 1, "config": MODULE.legacy_config_digest(),
                                    "sources": sources}))
    assert MODULE.apply(manifest) == 0
    assert mtime(tree, "coq/kernel/A.v") < mtime(tree, "coq/kernel/A.vo")


def test_schema_one_manifest_from_other_libraries_asks_for_a_full_build(tree):
    import json
    manifest = tree / "build/manifest.json"
    manifest.parent.mkdir(parents=True, exist_ok=True)
    manifest.write_text(json.dumps({"schema": 1, "config": "other", "sources": {}}))
    assert MODULE.apply(manifest) == 2


def test_minimal_proof_is_cached_and_invalidated_with_its_source(tree):
    source = tree / "minimal/EarnedCore.v"
    source.parent.mkdir()
    source.write_text("Definition earned := 0.\n")
    output = source.with_suffix(".vo")
    output.write_bytes(b"compiled minimal proof")
    manifest = tree / "build/manifest.json"
    MODULE.write(manifest)
    assert output in MODULE.outputs()
    assert MODULE.apply(manifest) == 0
    assert source.stat().st_mtime < output.stat().st_mtime
    source.write_text("Definition earned := 1.\n")
    assert MODULE.apply(manifest) == 0
    assert source.stat().st_mtime > output.stat().st_mtime
