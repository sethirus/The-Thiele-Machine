#!/usr/bin/env bash
set -euo pipefail

# Repair stale/duplicate VS Code workspaceStorage locks in Codespaces/remote sessions.
# Usage:
#   scripts/fix_vscode_locks.sh [workspace_id_prefix]
# Example:
#   scripts/fix_vscode_locks.sh 73042f60

WORKSPACE_PREFIX="${1:-73042f60}"
LOCK_ROOT="${HOME}/.vscode-remote/data/User/workspaceStorage"

if [[ ! -d "${LOCK_ROOT}" ]]; then
  echo "No workspaceStorage directory found: ${LOCK_ROOT}"
  exit 0
fi

mapfile -t LOCK_FILES < <(find "${LOCK_ROOT}" -maxdepth 2 -type f -name vscode.lock -path "${LOCK_ROOT}/${WORKSPACE_PREFIX}*/vscode.lock" | sort)

if [[ ${#LOCK_FILES[@]} -eq 0 ]]; then
  echo "No lock files found for prefix '${WORKSPACE_PREFIX}'."
  exit 0
fi

echo "Found ${#LOCK_FILES[@]} lock file(s) for prefix '${WORKSPACE_PREFIX}'."

live_count=0
declare -a LIVE_LOCKS=()
declare -a LIVE_PIDS=()

for lock in "${LOCK_FILES[@]}"; do
  pid="$(sed -n 's/.*"pid":\([0-9][0-9]*\).*/\1/p' "${lock}" || true)"
  if [[ -z "${pid}" ]]; then
    echo "Removing malformed lock: ${lock}"
    rm -f "${lock}"
    continue
  fi

  if ps -p "${pid}" >/dev/null 2>&1; then
    LIVE_LOCKS+=("${lock}")
    LIVE_PIDS+=("${pid}")
    live_count=$((live_count + 1))
    echo "Live lock: ${lock} (pid ${pid})"
  else
    echo "Removing stale lock: ${lock} (dead pid ${pid})"
    rm -f "${lock}"
  fi
done

if [[ ${live_count} -le 1 ]]; then
  echo "No duplicate live locks detected."
  exit 0
fi

# Keep the newest live lock by mtime and stop the other extension hosts.
newest_lock=""
newest_ts=0
for lock in "${LIVE_LOCKS[@]}"; do
  ts="$(stat -c %Y "${lock}")"
  if (( ts > newest_ts )); then
    newest_ts="${ts}"
    newest_lock="${lock}"
  fi
done

echo "Duplicate live locks detected (${live_count})."
echo "Keeping newest lock: ${newest_lock}"

for lock in "${LIVE_LOCKS[@]}"; do
  if [[ "${lock}" == "${newest_lock}" ]]; then
    continue
  fi

  pid="$(sed -n 's/.*"pid":\([0-9][0-9]*\).*/\1/p' "${lock}" || true)"
  if [[ -z "${pid}" ]]; then
    rm -f "${lock}"
    continue
  fi

  cmd="$(ps -p "${pid}" -o args= 2>/dev/null || true)"
  if [[ "${cmd}" == *"--type=extensionHost"* ]]; then
    echo "Stopping duplicate extension host pid ${pid}"
    kill "${pid}" 2>/dev/null || true
    sleep 1
    if ps -p "${pid}" >/dev/null 2>&1; then
      kill -9 "${pid}" 2>/dev/null || true
    fi
  else
    echo "Not killing pid ${pid}; command does not look like extensionHost"
  fi

  if [[ -f "${lock}" ]]; then
    pid_after="$(sed -n 's/.*"pid":\([0-9][0-9]*\).*/\1/p' "${lock}" || true)"
    if [[ -n "${pid_after}" ]] && ! ps -p "${pid_after}" >/dev/null 2>&1; then
      rm -f "${lock}"
      echo "Removed duplicate lock: ${lock}"
    fi
  fi
done

echo "Final lock status:"
find "${LOCK_ROOT}" -maxdepth 2 -type f -name vscode.lock -path "${LOCK_ROOT}/${WORKSPACE_PREFIX}*/vscode.lock" -print | sort | while read -r f; do
  printf "  %s -> %s\n" "${f}" "$(cat "${f}")"
done
