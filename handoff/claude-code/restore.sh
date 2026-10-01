#!/usr/bin/env bash
set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
bundle_root="$repo_root/handoff/claude-code"
project_key=$(printf '%s' "$repo_root" | sed 's#/#-#g')
claude_root="${HOME}/.claude"
project_root="$claude_root/projects/$project_key"
guard_root="${HOME}/.cache/thiele-guard"
stamp=$(date -u +%Y%m%dT%H%M%SZ)

archive="$bundle_root/private/project-sessions.tar.gz.enc"
expected_sha="c3c04982ddb06c1bccb7ff79dffacd33c42eceddc801d389a69470fd997471c8"
actual_sha=$(sha256sum "$archive" | awk '{print $1}')
if [[ "$actual_sha" != "$expected_sha" ]]; then
  echo "Encrypted session archive checksum mismatch." >&2
  exit 1
fi

mkdir -p "$project_root" "$guard_root"
if [[ -d "$project_root/memory" ]]; then
  cp -a "$project_root/memory" "$project_root/memory.backup-$stamp"
fi
mkdir -p "$project_root/memory"
cp -a "$bundle_root/memory/." "$project_root/memory/"

cp -a "$bundle_root/status/research-execution-status.md" \
  "$guard_root/research-execution-status.md"
cp -a "$bundle_root/status/ground-truth-plan.md" \
  "$guard_root/ground-truth-plan.md"

read -r -s -p "Claude session archive passphrase: " handoff_passphrase
printf '\n'
temporary_dir=$(mktemp -d)
trap 'rm -rf "$temporary_dir"' EXIT

openssl enc -d -aes-256-cbc -pbkdf2 -iter 600000 \
  -pass pass:"$handoff_passphrase" -in "$archive" \
  -out "$temporary_dir/project-sessions.tar.gz"
gzip -t "$temporary_dir/project-sessions.tar.gz"

mkdir -p "$temporary_dir/sessions"
tar -xzf "$temporary_dir/project-sessions.tar.gz" \
  -C "$temporary_dir/sessions"
session_count=$(find "$temporary_dir/sessions" -maxdepth 1 -type f \
  -name '*.jsonl' | wc -l)
if [[ "$session_count" -ne 30 ]]; then
  echo "Expected 30 session transcripts, found $session_count." >&2
  exit 1
fi

if compgen -G "$project_root/*.jsonl" >/dev/null; then
  mkdir -p "$project_root/session-backup-$stamp"
  cp -a "$project_root"/*.jsonl "$project_root/session-backup-$stamp/"
fi
cp -a "$temporary_dir/sessions"/*.jsonl "$project_root/"

if [[ "${1:-}" == "--with-settings" ]]; then
  if [[ -f "$claude_root/settings.json" ]]; then
    cp -a "$claude_root/settings.json" \
      "$claude_root/settings.json.backup-$stamp"
  fi
  cp -a "$bundle_root/settings.json" "$claude_root/settings.json"
fi

echo "Restored Claude project state to: $project_root"
echo "Restored plan/status state to: $guard_root"
echo "Start Claude Code from: $repo_root"
