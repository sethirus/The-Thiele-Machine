---
name: orphan-claude-sessions
description: A VS Code window reload can leave an older claude process running the same conversation; it edits the same files
metadata:
  type: project
---
On 2026-09-14 a VS Code reload left an old extension host (started 04:00) with a claude process still running this conversation's task. It rewrote files such as coq/kernel/foundation/VMSelfGuest.v. The user has no intentional parallel sessions and told me to kill any others.

**Why:** Two processes editing the same Coq files overwrite each other's proofs.

**How to apply:** If files change under you unexpectedly, run ListAgents and `ps -eo pid,ppid,lstart,args | grep native-binary/claude`. Identify your own PID via the $$ parent chain, then terminate the other claude processes without asking again. Leave VS Code extension hosts alone.
