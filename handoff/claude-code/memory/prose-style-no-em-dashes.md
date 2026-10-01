---
name: prose-style-no-em-dashes
description: "Devon's writing-style rules for all repo prose, measured from his own text; no em dashes, no we, no correction framing"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: 91e79210-3ced-442b-8b68-3cbcb21fda3e
  modified: 2026-08-12T22:08:00.909Z
---

Rules for every word a reader sees: README, monograph, math spec, disclosure,
Coq comment blocks, commit messages, test failure messages. Measured from his
own writing, not invented. He does not want a style guide file or a style
linter committed to the repo, so these rules live here.

- **No em dashes.** Not `---`, not the Unicode character. His monograph uses
  five in 73,000 words, which is 0.07 per thousand. Replace with a semicolon
  (he uses 8.17 per thousand), a full stop, a colon, or cut the clause. This
  is the tell he objects to most.
- **Write "I" and "you". Never "we".** `we`/`our` is 0.12 per thousand words
  in the monograph.
- **Short sentences.** Median 15 words; one in five under eight. The pattern
  is a long explanatory sentence followed by a short flat one that lands.
  Fragments are fine: "Including the error case." "Not even in principle."
- **State the thing, then state what it is not, as two sentences.** Never
  "not X but Y" in one sentence.
- **No correction framing.** Additions read as though they were always in the
  document. Banned: previously named, formerly called, renamed because, that
  is corrected here, an earlier version said, has been corrected.
- **Also banned:** triads of parallel items for rhythm, summary openers ("In
  short", "To be clear"), hedges (arguably, somewhat, fairly, bare rather),
  buzzwords (robust, powerful, elegant, leverage), adverb openers ("Notably,").

Two of his conventions that look like violations and are not: `--- \textbf{(S)}`
in math-spec theorem tags (32 uses at HEAD), and "rather X than Y" as a
comparison.

Stable vocabulary, where a synonym reads as a different claim: **substrate**
not framework; **the structural axis** not the third dimension; **priced** and
**metered** not charged; **irredundant** not minimal unless an order relation
is defined and leastness proved; **agreement** not isomorphism unless mutually
inverse maps are constructed; **waiver** for a suppressed Inquisitor finding,
with the count stated; **falsifier** for what would break a claim.

Never hand edit `monograph/monograph.txt` or
`monograph/math_spec_plaintext.txt`. Both are extracted from the PDFs with
`pdftotext -layout`; `monograph/build_monograph.sh` regenerates the monograph.

**Why:** the prose is a deliberate voice and it carries how a hostile reviewer
reads the project. Generic assistant phrasing undercuts it, and he spots it
immediately.

**How to apply:** write, then grep the diff for em dashes and the banned
phrasings before showing him anything. Calibrate against his existing text
rather than aiming for zero; the goal is that a diff adds no new violations.

**Added 2026-09-24 (Devon):** never apply prose changes by script or bulk replacement; read each passage and write the edit by hand in his voice. When a contract correction is needed, keep every author sentence that is still true and rewrite only the overclaim; do not replace his wording with neutral scope prose. Do not leave process documents (plans, ledgers, audits, inventories, iterative .md files) in the repo when work is finished.
