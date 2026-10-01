---
name: grep-wrapper-ignores-gitignored
description: "In this shell, `grep` is a function wrapping ugrep with --ignore-files, so it silently skips gitignored files like monograph.log"
metadata:
  node_type: memory
  type: reference
  originSessionId: d669abf4-46e6-4136-96bd-c94bb98a9b03
  modified: 2026-09-27T18:20:37.285Z
---

The Bash `grep` here is a shell function that runs ugrep with `--ignore-files`. It silently returns nothing for gitignored files such as `monograph/monograph.log`, so a LaTeX "undefined reference" check looks clean without having run.

**How to apply:** use `/usr/bin/grep` for build logs and any other ignored artifacts. Found 2026-09-27 while checking the monograph build. Related: [[guarded-coq-builds]].
