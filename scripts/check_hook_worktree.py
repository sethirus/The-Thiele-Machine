#!/usr/bin/env python3
"""Reject worktree-only inputs before a hook validates and stages generated files.

The generators and full pytest suite read the working tree. Require its tracked
files to match the index and no non-ignored untracked files, so they cannot
validate code absent from the commit or include unstaged edits in a manifest.
Ignored compiler outputs remain available for incremental builds.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path
import tempfile
import os


def git_output(*args: str) -> bytes:
    env = None
    if args[:1] == ("-C",):
        # Git sets GIT_INDEX_FILE (and possibly other repo-local variables) in
        # hooks. They belong to the parent index, not the submodule checkout.
        local_vars = subprocess.check_output(["git", "rev-parse", "--local-env-vars"]).decode().splitlines()
        env = {key: value for key, value in os.environ.items() if key not in local_vars}
    return subprocess.check_output(["git", *args], env=env)


def git_paths(*args: str) -> list[str]:
    return [p.decode("utf-8", errors="surrogateescape")
            for p in git_output(*args).split(b"\0") if p]


def expected_kami_patch(paths: set[str]) -> bool:
    """Allow only the compatibility patch CI applies to the pinned Kami source.

    Replay the committed/staged patch script on pristine vendor files, rather
    than ignoring dirty submodules or maintaining a second copy of its regexes.
    """
    allowed = {"Kami/Ex/Multiplier32.v", "Kami/Ex/Multiplier64.v"}
    if not paths <= allowed:
        return False
    with tempfile.TemporaryDirectory(prefix="thiele-kami-patch-") as directory:
        root = Path(directory)
        script = root / "scripts/fix_kami_coq18.sh"
        script.parent.mkdir()
        script.write_bytes(subprocess.check_output(["git", "show", ":scripts/fix_kami_coq18.sh"]))
        for name in allowed:
            target = root / "vendor/kami" / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(git_output("-C", "vendor/kami", "show", f"HEAD:{name}"))
        subprocess.run(["bash", str(script)], check=True, capture_output=True)
        return all((root / "vendor/kami" / name).read_bytes() ==
                   (Path("vendor/kami") / name).read_bytes() for name in paths)


def submodule_problems() -> list[str]:
    problems = []
    entries = git_paths("ls-files", "--stage", "-z")
    for entry in entries:
        metadata, name = entry.split("\t", 1)
        if not metadata.startswith("160000 "):
            continue
        if not (Path(name) / ".git").exists():
            problems.append(name + " (submodule is not initialized)")
            continue
        changed = set(git_paths("-C", name, "diff", "HEAD", "--name-only", "-z"))
        untracked = git_paths("-C", name, "ls-files", "--others", "--exclude-standard", "-z")
        if changed and not (name == "vendor/kami" and expected_kami_patch(changed)):
            problems.extend(name + "/" + path for path in changed)
        problems.extend(name + "/" + path for path in untracked)
    return problems


def main() -> int:
    conflicts = git_paths("diff", "--name-only", "--diff-filter=U", "-z")
    # Compare gitlink revisions here; inspect submodule contents separately.
    unstaged = git_paths("diff", "--name-only", "--ignore-submodules=dirty", "-z")
    untracked = git_paths("ls-files", "--others", "--exclude-standard", "-z")
    paths = sorted(set(conflicts + unstaged + untracked + submodule_problems()))
    if paths:
        print("[pre-commit] FAIL: working tree differs from the proposed commit.", file=sys.stderr)
        for path in paths:
            print(f"  {path!r}", file=sys.stderr)
        print("Stage intended changes or stash unrelated work (including untracked files), "
              "then retry. No source files are auto-staged by this check.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
