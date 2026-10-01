# Claude Code handoff

This directory carries the project-specific Claude Code state needed to resume
The Thiele Machine work on another computer.

## Included

- `memory/`: all 30 project memory Markdown files from
  `~/.claude/projects/-workspaces-The-Thiele-Machine/memory/` at handoff time.
- `status/research-execution-status.md`: the external live execution ledger.
- `status/ground-truth-plan.md`: the external copy of the governing plan.
- `settings.json`: the non-secret Claude model and attribution settings.
- `private/project-sessions.tar.gz.enc`: all 30 project JSONL session
  transcripts, compressed and encrypted with AES-256-CBC, PBKDF2-SHA-256, and
  600,000 iterations.
- `restore.sh`: a guarded restoration helper that computes Claude's project key
  from the home-PC checkout path.

Archive SHA-256:

```text
c3c04982ddb06c1bccb7ff79dffacd33c42eceddc801d389a69470fd997471c8
```

The archive passphrase is deliberately not committed. It was delivered to the
owner alongside the pushed handoff commit.

## Excluded deliberately

- `~/.claude/.credentials.json` and every authentication token;
- IDE lock files, daemon state, notifications, and process identifiers;
- Claude's global backup/configuration history;
- generated Coq caches and 175 MB of replaceable guard scratch data.

These are machine-local or security-sensitive and are not needed to resume the
proof. Authenticate Claude Code normally on the home computer.

## Restore

From the repository root on the home computer:

```bash
bash handoff/claude-code/restore.sh
```

The script asks for the archive passphrase without echoing it, backs up any
existing project memory and session directory, verifies the encrypted archive,
and restores the memories, transcripts, plan, and execution ledger. It does not
replace global Claude settings unless called with `--with-settings`.

After restoration, start Claude Code from the repository root. Ask it to read
`codex-handoff-2026-10-01` and
`research/rounds/2026-10-01-part3-item3.1-round3-handoff.md` before continuing.

## Truth status

The handoff is a resumable proof checkpoint, not a completed plan result. The
exact `vm_guest_recursion_theorem_closed` TDD contract remains red. No merge,
tag, release, or publication is authorized.
