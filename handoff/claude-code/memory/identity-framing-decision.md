---
name: identity-framing-decision
description: How every doc must say what the Thiele Machine IS (abstract model + argument; VM/opcodes/hardware/category theory are one build) — Devon 2026-09-27
metadata:
  node_type: memory
  type: project
  originSessionId: d669abf4-46e6-4136-96bd-c94bb98a9b03
  modified: 2026-09-27T19:28:56.184Z
---

Devon (2026-09-27) was fed up that every reader classifies the Thiele Machine as a CPU, VM, opcodes, category theory, a graph, or morphisms. His words: "it's an ARGUMENT, it's an ABSTRACT MODEL, certification is just one point not THE point."

Root causes found in the text: the monograph never stated what kind of thing the TM is ("abstract model" appeared 0 times, "VM" 498); the origin story said "category theory is the state itself"; the first technical section was "Bits, bytes, and what a CPU sees"; CHSH was the largest section and the conclusion's "first pillar"; theorems called VMState "Thiele states"; CITATION/.zenodo keywords led with category theory and hardware verification.

Fix applied (uncommitted at time of writing): monograph reorganized into Part I The argument / Part II Building it / Part III Checking it / Part IV What is still open, with vocabulary moved to an appendix. Front page states identity + the five-step argument with each step's status (proved / defined / proposed / open). README, THIELE_MACHINE.txt, CITATION.cff, .zenodo.json, spec preface, and disclosure summary all carry the same identity lines.

A follow-up overclaim audit ran on 2026-09-27, still uncommitted. It corrected titles and statements without deleting anything. Spec chapters (unitarity, no-cloning, CPTP, Lindblad, purification, taxonomy, gauge/Noether, spacetime, Landauer, manifold, Turing subsumption) now state their supplied premises. The disclosure's CHSH gate is described as sound one-way only. Monograph NoFI/CHSH paragraphs stop at what their theorems show. Rule: a title or sentence never promises more than its Coq statement; correct the claim, keep the author's sentence.

**Why:** readers classify by the first pages and by what dominates the bulk. The thesis sentence ("an argument about what an account of computation should preserve") already existed in the spec and CITATION and was missing from the monograph.

**How to apply:** in any new prose, "Thiele Machine" means the abstract model; say "the VM" or "VM state" for the build. Never let a section open by implying the model has opcodes, a CHSH step, or category theory. Certification is "one witness in the argument", never the argument. Related: [[register-audit-decisions]], [[prose-style-no-em-dashes]], [[research-open-question-plan]].
