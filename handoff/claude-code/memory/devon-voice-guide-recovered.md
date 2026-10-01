---
name: devon-voice-guide-recovered
description: "Devon's original 698-line voice guide was deleted 2026-04-23; recover with git show febfe5e9^:STYLE_GUIDE.md. READ before any prose work. Who he is, signature moves, anti-patterns"
metadata:
  type: reference
---

Source: `git show febfe5e9^:STYLE_GUIDE.md` ("Devon Thiele Voice & Style
Guide", 698 lines, deleted in febfe5e9 on 2026-04-23). Companions:
`git show d5d3d534^:CLAUDE.md`, `git show 595f56af^:.github/copilot-instructions.md`.
The guide's voice evidence came from `attempt.py` and the README in the first
commit `84b8ae7c` (2025-08-15). Do not recommit the guide; Devon does not want
style files in the repo ([[prose-style-no-em-dashes]]).

Core points (sections 1, 2, 5, 6, 8 of the guide):
- Who: "I'm a car salesman." Started January 2025 with LLM-directed
  development, did not know programming. Not an academic, not a genius. Learns
  by going deep and explains from first principles AS someone learning it.
  Trusts nothing unproven, his own arguments included; that is why Coq.
- Voice: a curious person working it out with you, not lecturing. Physical
  analogies anyone can picture (maze seen one floor tile at a time, centrifuge,
  crash-test dummy). Humor next to seriousness. Informal AND precise. Caps and
  bold for emphasis. Says "I think" / "I don't know yet" honestly.
- Signature moves: "First Principles Explanation" / "Set the Stage" blocks and
  Author's Notes ("They're the best parts. Keep them.").
- Anti-patterns: lecturing, expert posturing, "we present", passive voice that
  hides the actor, "obviously/clearly/trivially", boilerplate openers and closers.

Measured 2026-10-01: in the current monograph, "car salesman", "staring at this
problem", "blind by design", "floor tile", Author's Notes, First Principles
blocks, and "Set the Stage" all appear ZERO times. Only "obedient idiot"
survives. Rounds of edits erased his voice. See [[voice-audit-plan]].

Devon (2026-10-01): "I'm not trying to tell everyone I sell cars or anything,
it's just what I am." The biography is context for HOW he writes (plain,
practical, first principles, outsider, no credentials posture). It is not
content to insert. Never re-add "car salesman" lines, origin-story beats, or
self-description as a fix, and do not count missing biography lines as damage.
The zero counts above matter only as evidence that his way of explaining was
lost.
