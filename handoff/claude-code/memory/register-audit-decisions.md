---
name: register-audit-decisions
description: "Devon is not a math person; decisions (2026-09-26) for auditing monograph/spec/README register — picture-first in his voice, formal layer as labeled translation"
metadata:
  node_type: memory
  type: user
  originSessionId: a5c67d8f-1460-46c9-bc1c-722d5b65416d
  modified: 2026-09-26T17:24:34.278Z
---

Devon thinks in shapes, diagrams, directions and connections, not equations, and does not want readers to take him for an equation-writing mathematician. LLMs did the math and translated his intuitions; the monograph origin story already says so ("The symbol-pushing, the actual Coq and the actual math, the models produced").

Decisions (Devon, 2026-09-26):
- Technical sections: he narrates the picture (shape/direction/connection) in his words; directly under it the formal statement appears, plainly labeled as the formal version checked by Coq. Math stays, but it is the machine's layer, not him at a chalkboard.
- Math spec: neutral reference register with no "I" at all, opened by a short preface in his voice saying it is the translation.
- Source of imagery: mine the existing origin-story sections (gravity pipes, directions and vectors, digital DNA, Flatland's other axis, picture resolving out of static, the shape was the substrate, receipt grew teeth, counter that only climbs). Do not invent new imagery and attribute it to him; he corrects what is wrong.
- Order: full section-by-section audit map first (kept outside the repo), then section work.

Measured baseline: monograph "I" density ~27/kw in the opening, ~1-2/kw with 38-72 inline-math/kw in the technical middle; only 8 TikZ figures in 74K words; math spec 57 math/kw, 0 figures.

Scope qualifiers were added because reviewers attacked overclaims; keep their precision, gather them per section rather than sprinkling. Hand edits only, no process docs in repo ([[prose-style-no-em-dashes]]).

**Progress (2026-09-26):** Devon rejected reusing old (v3.1.0) text: "I need a real pass over the current stuff", rewrite CURRENT content in his register, no copying old prose. THIELE_MACHINE.txt rewritten in working tree (uncommitted; he read it and moved on). Monograph pass in progress, in section order, via hand Edits: preface "our"s, abstract, and all of Section 1 done (prior-work scope block, Kami "proofs are mine", NPA item, confidence list, What this project is, three steps, substrate/scaffolding incl. caption, new-model block, uniqueness block). Sections 2-5 also done (plain readings moved ABOVE their theorems; fixed a wrong plain reading under structural_entitlement_representation that called it an entropy bound). Sections 6-13 also done (through knowledge receipt; added composition TikZ figure fig:composition in category section). Sections 14-16 also done (hardware, five minimal models, CHSH incl. Q1AB and elliptope). Monograph pass COMPLETE (voice 21->28%, guard 60->27, audits clean, compiles). Next: README, then math spec preface + de-I, then TECHNICAL_DISCLOSURE check, then rebuild PDFs and commit through hook. Checks after each section: scripts/audit_monograph_citations.py, scripts/audit_monograph_semantics.py monograph/monograph.tex (baseline: 1 pre-existing alias concern at level_k_verification_floor). Verify every Coq paraphrase against the actual definition before writing (e.g. WithShortcutPredicate = predicate + yes/no programs + extensionality; base Substrate has mu_monotone, encode/decode, recursion_theorem). Rebuild PDFs and commit at the end, not per section.
