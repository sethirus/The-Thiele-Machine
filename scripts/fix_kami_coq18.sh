#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

for rel in vendor/kami/Kami/Ex/Multiplier32.v vendor/kami/Kami/Ex/Multiplier64.v; do
  f="$ROOT/$rel"
  if [[ ! -f "$f" ]]; then
    echo "[fix-kami-coq18] skip missing $rel"
    continue
  fi

  perl -0pi -e "s/Notation \"w ~ 0\" := \(BWS BZero w\): bword_scope\./Notation \"w ~ 0\" := \(BWS BZero w\) \(at level 7, left associativity\): bword_scope\./g" "$f"
  perl -0pi -e "s/Notation \"w ~ 'P'\" := \(BWS BPlus w\): bword_scope\./Notation \"w ~ 'P'\" := \(BWS BPlus w\) \(at level 7, left associativity\): bword_scope\./g" "$f"
  perl -0pi -e "s/Notation \"w ~ 'N'\" := \(BWS BMinus w\): bword_scope\./Notation \"w ~ 'N'\" := \(BWS BMinus w\) \(at level 7, left associativity\): bword_scope\./g" "$f"

done

echo "[fix-kami-coq18] compatibility notation patch applied"
