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
        "vendor/kami/Kami/Syntax.v": "Definition k := 0.\n",
    }.items():
        path = tmp_path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    for name in ("coq/kernel/A.vo", "coq/kernel/B.vo", "coq/kernel/B.glob",
                 "vendor/coq-undecidability/theories/L/L.vo", "vendor/kami/Kami/Syntax.vo"):
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
                            "vendor/coq-undecidability/theories/L/L.vo"),
                           ("vendor/kami/Kami/Syntax.v", "vendor/kami/Kami/Syntax.vo")):
        assert mtime(tree, source) < mtime(tree, output)
    # Libraries below the tree are older than every output above them.
    assert mtime(tree, "vendor/kami/Kami/Syntax.vo") < mtime(tree, "coq/kernel/A.vo")
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


@pytest.mark.parametrize("name", ["coq/_CoqProject", "coq/Makefile.local",
                                  "vendor/coq-undecidability/theories/_CoqProject",
                                  "vendor/kami/Kami/Syntax.vo",
                                  "vendor/coq-undecidability/theories/L/L.vo"])
def test_flag_or_library_change_marks_every_source(tree, name):
    manifest = tree / "build/manifest.json"
    MODULE.write(manifest)
    with (tree / name).open("ab") as stream:
        stream.write(b"\n")
    assert MODULE.apply(manifest) == 0
    for source in ("coq/kernel/A.v", "coq/kernel/B.v",
                   "vendor/coq-undecidability/theories/L/L.v"):
        assert mtime(tree, source) > mtime(tree, "coq/kernel/A.vo")


@pytest.mark.parametrize("content", [None, "not json", '{"schema": 0}'])
def test_missing_or_foreign_manifest_asks_for_a_full_build(tree, content):
    manifest = tree / "build/manifest.json"
    if content is not None:
        manifest.parent.mkdir(parents=True, exist_ok=True)
        manifest.write_text(content)
    assert MODULE.apply(manifest) == 2
