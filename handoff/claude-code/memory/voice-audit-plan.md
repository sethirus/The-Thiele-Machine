---
name: voice-audit-plan
description: "Devon's takeover priority (2026-10-01): line-by-line audit of monograph + all public docs for his authentic voice, garbled passages, iteration residue, and wrong descriptions; approach and scale"
metadata:
  node_type: memory
  type: project
  originSessionId: 70b36a88-3eae-4541-839f-3a153861a590
  modified: 2026-10-01T05:32:46.956Z
---

Devon (2026-10-01): when work resumes after Codex, "I need to fix a lot of
things, the monograph and other documentation is too iterative, we need to
practically audit every line for my authentic voice, where things got garbled,
where things were iterated on and described incorrectly."

**Why:** Codex and earlier sessions layered rounds of edits onto the docs.
Status paragraphs got bolted on, theorem names got stacked, and old wording
survived next to new wording. Devon treats the docs as ground truth, not a log
([[docs-ground-truth-not-log]]).

**How to apply:**
- Do this only after Codex stops and its Part 8 Round 2 rewrite is in the tree
  ([[codex-handoff-2026-10-01]]). Auditing a moving target wastes the pass.
- Scope: README (646 lines), THIELE_MACHINE.txt (290), monograph.tex (5,041),
  math_spec.tex (2,297), CITATION.cff, release notes (101). About 8,460 lines.
  The generated .txt exports are never hand-edited.
- A keyword scan on 2026-10-01 found few surface markers (monograph: "still"
  63, "now" 22, "remains" 14, round/frozen 13, we/our 6; em dashes are rare).
  The real damage is semantic: garbled sentences, duplicated or contradictory
  accounts of one result, prose that describes an older version of a theorem.
  That needs a real read, not grep. Grep only seeds the read.
- Method: build the audit map outside the repo first ([[register-audit-decisions]]).
  Then read in document order, section by section, on the main thread. Hand
  edits only. Check each cited theorem name against its actual Coq statement
  before keeping the sentence. Where one result is described twice, keep one
  account at its natural home. Compile and run the citation/semantics audits
  per section. Rebuild PDFs and commit at the end.
- Voice rules: [[prose-style-no-em-dashes]], [[register-audit-decisions]] (his
  picture first, then the formal statement labeled as the Coq version; spec
  neutral), [[identity-framing-decision]] (abstract model + argument). Keep his
  sentence whenever it is still true. Rewrite only what is wrong or garbled.
- The Item 1.4 line ledger (`research/rounds/2026-09-30-part1-item1.4-round1-line-audit.tsv`)
  is a claims-evidence audit of an older tree. It is not a voice audit. Its
  evidence column can seed the theorem checks, but line numbers are stale.

## Reframe, same day (supersedes the "audit" framing above)

Devon: "my voice my authenticity my prose my real actual conversational style
has been bastardized. I dont do equations. I see shapes, I think in shapes, on
shapes, through shapes, edges of shapes, transformations of shapes. I'm not an
academic, not a mathematician, not a tweed-suit chalkboard jockey. I'm me, not
whatever this monograph has become... how I talk and reason and explain from
first principles."

He said nearly the same thing on 2026-09-26. The picture-first-then-labeled-formal
approach in [[register-audit-decisions]] was tried and did not fix it. Editing
toward his voice cannot work: almost no authentic corpus exists. The first
commit (2025-08-15 README) is already LLM register. His own words survive only
in chat messages and the monograph origin story ("Coq is an obedient idiot",
"LLMs were my hands", gravity pipes, Flatland axis).

Proposal given to Devon (awaiting his answer):
1. The monograph becomes his explanation, from first principles, in shapes and
   transformations, conversational. Equations and Coq statements move out to
   the math spec, which is openly the translation. The monograph points to it
   by name.
2. His words are the source. Per chapter he explains the idea in chat, typed or
   dictated, however he would tell a friend. I shape it into prose, keep his
   phrasing, and check that nothing claims more than the Coq does. I never
   write his voice from scratch.
3. Each chapter goes back to him to read before the next one starts.

## Devon's answer (2026-10-01)

Keep the equations. The damage is how they are introduced and reasoned about
before they appear: setup like "Let X be", "Define", "we derive", "by induction
it follows" implies he works the math by hand. He does not. He has an intuition
and "a funny brain" and thinks in shapes, not math. So: his intuition and shape
reasoning carry each idea, and the equation arrives as the machine's exact
version of that picture, which LLMs wrote and Coq checked. It is never his
chalkboard derivation. He pointed to old voice instructions in the repo; they
were recovered, see [[devon-voice-guide-recovered]]. Restore his signature
First Principles blocks and Author's Notes where the content supports them.
