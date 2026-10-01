---
name: kill-by-pgid-not-pattern
description: Never kill jobs with pgrep -f / pkill -f on a pattern that appears in my own bash command; it kills my own shell (exit 144)
metadata:
  node_type: memory
  type: feedback
  originSessionId: f6985b3e-12aa-4174-8f86-800155332120
  modified: 2026-09-29T18:53:34.808Z
---

Twice (2026-09-28, 2026-09-29) `pgrep -f "<pattern>" | kill` or `pkill -f` matched the Bash tool's own shell because the pattern text was in the command line, killing the shell mid-command (exit 144) and dropping the rest of the command.

**Why:** the Bash tool runs the whole command string as one shell process whose argv contains the pattern.

**How to apply:** launch detached jobs with `setsid` and record their PGID in a file; kill with `kill -- -$PGID`. If a pattern is unavoidable, use a bracket trick (`pgrep -f "[s]can.py"`) and run the kill as its own tool call, never chained with edits. Related: [[orphan-claude-sessions]], [[guarded-coq-builds]].
