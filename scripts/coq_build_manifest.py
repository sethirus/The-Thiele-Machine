#!/usr/bin/env python3
"""Make a restored Coq build cache rebuild exactly what changed.

`make` decides staleness by modification time. A cache restored onto a fresh
checkout has arbitrary times, so a changed source can look older than its
stale compiled file. This script records a content digest of every Coq
source next to the cached outputs (`write`), and on restore (`apply`) sets
times from content: every unchanged source is older than every restored
output, and every source whose digest differs from the record is newer. Make
then rebuilds the changed files and, through coqdep, everything that depends
on them. A compiled file whose source no longer exists is deleted, so a
removed module can never satisfy a Require. If the project files that set
the compiler flags changed, or any compiled library below coq/ differs from
the recorded build, every source counts as changed.
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
SOURCE_ROOTS = ("coq", "vendor/coq-undecidability/theories")
CONFIG_FILES = (
    "coq/_CoqProject",
    "coq/Makefile.local",
    "vendor/coq-undecidability/theories/_CoqProject",
)
OUTPUT_SUFFIXES = (".vo", ".vok", ".vos", ".glob")
# Libraries built and cached by their own steps. Their compiled bytes are part
# of the configuration: if they differ from the recorded build, every cached
# output above them is suspect.
LIBRARY_ROOTS = ("vendor/bbv", "vendor/kami")
SCHEMA = 1


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources() -> list[Path]:
    found: list[Path] = []
    for top in SOURCE_ROOTS:
        found.extend(sorted((ROOT / top).rglob("*.v")))
    return found


def outputs() -> list[Path]:
    found: list[Path] = []
    for top in SOURCE_ROOTS:
        for suffix in OUTPUT_SUFFIXES:
            found.extend((ROOT / top).rglob("*" + suffix))
    return found


def config_digest() -> str:
    hasher = hashlib.sha256()
    for name in CONFIG_FILES:
        path = ROOT / name
        hasher.update(name.encode() + b"\0")
        hasher.update(path.read_bytes() if path.exists() else b"<missing>")
        hasher.update(b"\0")
    for path in library_outputs():
        hasher.update(rel(path).encode() + b"\0" + sha256(path).encode() + b"\0")
    return hasher.hexdigest()


def library_outputs() -> list[Path]:
    """Compiled libraries the cached outputs were built against: Kami and
    bbv, plus the vendored undecidability library, whose compiled files may
    come from the checkout rather than from the cache."""
    roots = LIBRARY_ROOTS + ("vendor/coq-undecidability/theories",)
    return sorted(p for top in roots for p in (ROOT / top).rglob("*.vo"))


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def write(manifest: Path) -> None:
    record = {
        "schema": SCHEMA,
        "config": config_digest(),
        "sources": {rel(p): sha256(p) for p in sources()},
    }
    manifest.parent.mkdir(parents=True, exist_ok=True)
    manifest.write_text(json.dumps(record, sort_keys=True))
    print(f"[coq-build-manifest] recorded {len(record['sources'])} sources")


def apply(manifest: Path) -> int:
    try:
        record = json.loads(manifest.read_text())
        if record.get("schema") != SCHEMA:
            raise ValueError("schema mismatch")
        recorded: dict[str, str] = record["sources"]
        same_config = record.get("config") == config_digest()
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"[coq-build-manifest] no usable manifest ({exc}); rebuild everything",
              file=sys.stderr)
        return 2

    now = time.time()
    source_time, output_time = now - 7200, now - 3600

    # The cached Kami and bbv builds match their sources (their own cache is
    # keyed on them); keep their own make quiet and keep them older than
    # every output above them.
    library_time = source_time - 3600
    for top in LIBRARY_ROOTS:
        for path in (ROOT / top).rglob("*.v"):
            os.utime(path, (library_time - 600, library_time - 600))
        for suffix in OUTPUT_SUFFIXES:
            for path in (ROOT / top).rglob("*" + suffix):
                os.utime(path, (library_time, library_time))

    # Unchanged project files must not look newer than the makefiles that
    # coq_makefile generated from them.
    if same_config:
        for name in CONFIG_FILES:
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

    changed = 0
    for src in sources():
        if same_config and recorded.get(rel(src)) == sha256(src):
            os.utime(src, (source_time, source_time))
        else:
            os.utime(src, (now, now))
            changed += 1

    scope = "" if same_config else " (compiler flags changed: all sources)"
    print(f"[coq-build-manifest] {changed} changed sources{scope}; "
          f"{removed} orphaned outputs removed")
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
