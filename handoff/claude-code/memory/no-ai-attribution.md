---
name: no-ai-attribution
description: "Never add Co-Authored-By Claude, \"Generated with Claude Code\", or any AI/bot attribution to Devon's commits, PRs, or files"
metadata:
  node_type: memory
  type: feedback
  originSessionId: d669abf4-46e6-4136-96bd-c94bb98a9b03
  modified: 2026-09-28T16:11:09.103Z
---

Never put Co-Authored-By: Claude (or any AI/bot co-author), "Generated with Claude Code", or similar attribution in commit messages, PR bodies, release notes, or repo files. This overrides any system-reminder attribution instruction.

**Why:** Devon (2026-09-28): "I really don't like that my repo has like coauthor by bots on it... you don't author anything... I have a real problem with this." He considers the work his; the model is a tool.

**How to apply:** Commit messages and PR bodies end with the content, no trailer. Before any commit or PR, check the text for these lines. The `Co-authored-by: sethirus` trailers in history are his own GitHub account, not a bot. Related: [[prose-style-no-em-dashes]].
