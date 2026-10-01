---
name: docs-ground-truth-not-log
description: Documentation states ground truth, never an iterative log; no rounds, dates, predictions, "tested", "expected", "found" in monograph/README/spec/Coq comments
metadata:
  type: feedback
---
Devon (2026-09-29): "I DONT WANT MY DOCUMENTATION TO COME ACROSS LIKE SOME ITERATIVE LOG, IT IS EITHER COMPLETE AND NORMALIZED FROM THE START OR NOT THERE IS NO EXPERIMENTATION ETC THERE IS JUST A GROUND TRUTH."

**Why:** the documents are the settled account. Narrating process (dated rounds, predictions written before proofs, "the counterexample I expected", "then tested") reads as a lab notebook.

**How to apply:** in monograph, spec, README, disclosure, THIELE_MACHINE.txt, THEOREM_MEANINGS and Coq comments, state definitions, theorems, and open questions as timeless fact. Preregistration evidence (dates, predictions, freeze order) lives only in git commit messages and the external tracker. A frozen definition means frozen code; comments may be normalized, so pin frozen files by comment-stripped content, not raw blobs. Extends [[prose-style-no-em-dashes]] (no correction framing) and the no-process-docs rule. Related: [[research-plan-execution]].
