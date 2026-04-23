#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Patch 1: left-recursive notation levels in Multiplier32/64
# Coq 8.18+ requires explicit levels on left-recursive notations.
# Without this, the bword_scope notations cause a hard build error.
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

# Note: Divider32.v and Divider64.v use Nat.div_0_l, which is deprecated since
# Coq 8.17 but still compiles — it produces a warning, not an error. The
# suggested replacement (Div0.div_0_l) requires the Div0 module to be in scope,
# which it is not in these vendor files. Leave Nat.div_0_l as-is: the warning
# is harmless and the alternative causes a build failure.

echo "[fix-kami-coq18] all compatibility patches applied"
