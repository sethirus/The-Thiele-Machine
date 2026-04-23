#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Patch 1: left-recursive notation levels in Multiplier32/64
# Coq 8.18+ requires explicit levels on left-recursive notations.
for rel in vendor/kami/Kami/Ex/Multiplier32.v vendor/kami/Kami/Ex/Multiplier64.v; do
  f="$ROOT/$rel"
  if [[ ! -f "$f" ]]; then
    echo "[fix-kami-coq18] skip missing $rel"
    continue
  fi

  perl -0pi -e "s/Notation \"w ~ 0\" := \(BWS BZero w\): bword_scope\./Notation \"w ~ 0\" := \(BWS BZero w\) \(at level 7, left associativity\): bword_scope\./g" "$f"
  perl -0pi -e "s/Notation \"w ~ 'P'\" := \(BWS BPlus w\): bword_scope\./Notation \"w ~ 'P'\" := \(BWS BPlus w\) \(at level 7, left associativity\): bword_scope\./g" "$f"
  perl -0pi -e "s/Notation \"w ~ 'N'\" := \(BWS BMinus w\): bword_scope\./Notation \"w ~ 'N'\" := \(BWS BMinus w\) \(at level 7, left associativity\): bword_scope\./g" "$f"

  echo "[fix-kami-coq18] notation levels patched: $rel"
done

# Patch 2: Nat.div_0_l deprecated since Coq 8.17 — use Div0.div_0_l instead.
for rel in vendor/kami/Kami/Ex/Divider32.v vendor/kami/Kami/Ex/Divider64.v; do
  f="$ROOT/$rel"
  if [[ ! -f "$f" ]]; then
    echo "[fix-kami-coq18] skip missing $rel"
    continue
  fi

  perl -0pi -e "s/Nat\.div_0_l/Div0.div_0_l/g" "$f"

  echo "[fix-kami-coq18] Nat.div_0_l -> Div0.div_0_l patched: $rel"
done

echo "[fix-kami-coq18] all compatibility patches applied"
