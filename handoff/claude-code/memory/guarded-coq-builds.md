---
name: guarded-coq-builds
description: User requires every Coq build monitored with time and memory guards; nothing may hang or run long unobserved
metadata:
  type: feedback
---
Every coqc/make run must be guarded: `coqc -time` with line-buffered output, a hard time limit, and an RSS ceiling (~1.8 GB on this 8 GB codespace) that kills coqc before the system OOM handler does (that handler sends SIGTERM, exit 143, at roughly 2.5 GB). Diagnose the exact slow sentence from the log and fix the proof; never just wait longer. Update artifacts/review_revision/STATUS.md "Live progress" section after each checked result.

**Why:** User said (2026-09-14) "I don't want anything hanging, I don't want anything taking forever to run... continually update the status document as we go."

**How to apply:** Guard scripts live in /home/codespace/.cache/thiele-guard/ (cq.sh, mk.sh; logs/). The session scratchpad is wiped when a session restarts, so never keep tooling or backups there. On 2026-09-14 a `make -j2` with a 2.8 GB per-coqc ceiling pushed the 8 GB codespace out of memory and killed the VS Code server and the Claude session. Always build with -j1 and also stop when MemAvailable drops below 1.2 GB. Known trap: a closing tactic that keeps Nat.add opaque in cbv leaves fuel like `2*k+3` unreduced, so run_vm_u expands without bound; normalize fuel with vm_compute first. Related: [[v322-review-fixes-inflight]].
