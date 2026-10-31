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
        if changed:
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
              "then retry. This check never stages files.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
