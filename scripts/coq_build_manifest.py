#!/usr/bin/env python3
"""Make a restored Coq build cache rebuild exactly what changed.

`make` decides staleness by modification time. A cache restored onto a fresh
checkout has arbitrary times, so a changed source can look older than its
stale compiled file. This script records a content digest of every Coq
source next to the cached outputs (`write`), and on restore (`apply`) sets
times from content: every unchanged source is older than every restored
output, and every source whose digest differs from the record is newer. Make
then rebuilds the changed files and, through coqdep, everything that depends
on them. A compiled file whose source is absent is deleted, so a
module without a source can never satisfy a Require. Sources are grouped in two
scopes, coq/, minimal/ and the vendored undecidability library. If a scope's project
files or the compiled libraries below it differ from the recorded build,
every source in that scope counts as changed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT_SUFFIXES = (".vo", ".vok", ".vos", ".glob")
# Each build scope has its own sources, the project files that set its
# compiler flags, and the compiled libraries below it. A change to a scope's
# flags or libraries marks only that scope's sources; outputs above it follow
# through make's own dependencies. The vendored library therefore rebuilds
# only when its own sources or project file change.
SCOPES = {
    "coq": {
        "root": "coq",
        "config": ("coq/_CoqProject", "coq/Makefile.local"),
        "libraries": ("vendor/coq-undecidability/theories",),
    },
    "minimal": {
        "root": "minimal",
        "config": ("coq/_CoqProject", "coq/Makefile.local"),
        "libraries": (),
    },
    "vendor": {
        "root": "vendor/coq-undecidability/theories",
        "config": ("vendor/coq-undecidability/theories/_CoqProject",),
        "libraries": (),
    },
}
# Libraries built and cached by their own steps (keyed on their sources).
# None at present: the vendored undecidability library is a build scope of
# its own above.
LIBRARY_ROOTS: tuple[str, ...] = ()
# Schema 3: the coq scope reads no kami or bbv library; a manifest of an
# earlier schema describes a different build and is not reused.
SCHEMA = 3


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources(scope: str) -> list[Path]:
    return sorted((ROOT / SCOPES[scope]["root"]).rglob("*.v"))


def outputs() -> list[Path]:
    found: list[Path] = []
    for scope in SCOPES.values():
        for suffix in OUTPUT_SUFFIXES:
            found.extend((ROOT / scope["root"]).rglob("*" + suffix))
    return found


def project_flags(path: Path) -> bytes:
    """A project file without its list of source files.

    Adding or removing a source changes no flag the other sources are
    compiled with; make's own dependencies and the orphan sweep cover the
    file itself. So the list is left out, and only the flags and other
    lines count."""
    lines = path.read_bytes().split(b"\n")
    return b"\n".join(line for line in lines if not line.strip().endswith(b".v"))


def config_digest(scope: str) -> str:
    """Project files and compiled libraries the scope's outputs were built with."""
    hasher = hashlib.sha256()
    for name in SCOPES[scope]["config"]:
        path = ROOT / name
        hasher.update(name.encode() + b"\0")
        if not path.exists():
            hasher.update(b"<missing>")
        elif path.name == "_CoqProject":
            hasher.update(project_flags(path))
        else:
            hasher.update(path.read_bytes())
        hasher.update(b"\0")
    for top in SCOPES[scope]["libraries"]:
        for path in sorted((ROOT / top).rglob("*.vo")):
            hasher.update(rel(path).encode() + b"\0" + sha256(path).encode() + b"\0")
    return hasher.hexdigest()


def legacy_config_digest() -> str:
    """The single configuration digest of schema 1 manifests."""
    hasher = hashlib.sha256()
    for name in ("coq/_CoqProject", "coq/Makefile.local",
                 "vendor/coq-undecidability/theories/_CoqProject"):
        path = ROOT / name
        hasher.update(name.encode() + b"\0")
        hasher.update(path.read_bytes() if path.exists() else b"<missing>")
        hasher.update(b"\0")
    roots = ("vendor/coq-undecidability/theories",)
    for path in sorted(p for top in roots for p in (ROOT / top).rglob("*.vo")):
        hasher.update(rel(path).encode() + b"\0" + sha256(path).encode() + b"\0")
    return hasher.hexdigest()


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def write(manifest: Path) -> None:
    record = {
        "schema": SCHEMA,
        "configs": {scope: config_digest(scope) for scope in SCOPES},
        "sources": {rel(p): sha256(p) for scope in SCOPES for p in sources(scope)},
    }
    manifest.parent.mkdir(parents=True, exist_ok=True)
    manifest.write_text(json.dumps(record, sort_keys=True))
    print(f"[coq-build-manifest] recorded {len(record['sources'])} sources")


def apply(manifest: Path) -> int:
    try:
        record = json.loads(manifest.read_text())
        recorded: dict[str, str] = record["sources"]
        if record.get("schema") == SCHEMA:
            same = {scope: record["configs"].get(scope) == config_digest(scope)
                    for scope in SCOPES}
        elif record.get("schema") == 1:
            # One digest over both scopes' project files and libraries. A
            # mismatch cannot say which scope changed, and marking the vendored
            # library changed would rebuild it, so it falls back to a clean
            # build of coq/ on the tracked library instead.
            if record["config"] != legacy_config_digest():
                raise ValueError("schema 1 manifest from other flags or libraries")
            same = {scope: True for scope in SCOPES}
        else:
            raise ValueError("schema mismatch")
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"[coq-build-manifest] no usable manifest ({exc}); rebuild everything",
              file=sys.stderr)
        return 2

    now = time.time()
    source_time, output_time = now - 7200, now - 3600

    # Libraries cached by their own steps match their sources (their own
    # cache is keyed on them); keep their own make quiet and keep them older
    # than every output above them.
    library_time = source_time - 3600
    for top in LIBRARY_ROOTS:
        for path in (ROOT / top).rglob("*.v"):
            os.utime(path, (library_time - 600, library_time - 600))
        for suffix in OUTPUT_SUFFIXES:
            for path in (ROOT / top).rglob("*" + suffix):
                os.utime(path, (library_time, library_time))

    # Unchanged project files must not look newer than the makefiles that
    # coq_makefile generated from them.
    for scope, unchanged in same.items():
        if unchanged:
            for name in SCOPES[scope]["config"]:
                path = ROOT / name
                if path.exists():
                    os.utime(path, (source_time, source_time))

    removed = 0
    for out in outputs():
        if not out.with_suffix(".v").exists():
            out.unlink()
            removed += 1
            continue
        os.utime(out, (output_time, output_time))

    for scope in SCOPES:
        changed = 0
        for src in sources(scope):
            if same[scope] and recorded.get(rel(src)) == sha256(src):
                os.utime(src, (source_time, source_time))
            else:
                os.utime(src, (now, now))
                changed += 1
        note = "" if same[scope] else " (flags or libraries changed: all of them)"
        print(f"[coq-build-manifest] {scope}: {changed} changed sources{note}")
    print(f"[coq-build-manifest] {removed} orphaned outputs removed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("write", "apply"))
    parser.add_argument("--manifest", default="build/coq-build-manifest.json")
    args = parser.parse_args()
    manifest = Path(args.manifest)
    if not manifest.is_absolute():
        manifest = ROOT / manifest
    if args.action == "write":
        write(manifest)
        return 0
    return apply(manifest)


if __name__ == "__main__":
    sys.exit(main())
