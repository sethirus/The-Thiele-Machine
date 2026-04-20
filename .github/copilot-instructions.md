When sweeping Coq comment blocks in this repository into Devon voice, preserve the full technical payload.

- Keep proof chains, algorithm steps, examples, physical interpretation, complexity notes, edge cases, caveats, and falsification hooks.
- Remove only bureaucratic scaffolding: banner walls, PART/SECTION dividers, repeated labels like WHY THIS MATTERS/THE CLAIM/THE PROOF, and duplicated helper-note spam.
- Compress scaffolding into direct prose; do not collapse substantive explanations into one-line summaries.
- Before sweeping a file, inspect existing staged sweeps such as coq/kernel/AbstractNoFI.v, coq/kernel/BornRule.v, coq/kernel/CertCheck.v, coq/kernel/Certification.v, coq/kernel/ClassicalBound.v, and coq/kernel/Closure.v, and match that pattern.
- If unsure whether text is substantive or scaffolding, keep it and rewrite it rather than deleting it.
