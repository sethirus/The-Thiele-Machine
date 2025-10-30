# Conservation of Compositional Information: Empirical Tests of the Thiele Law

This outline packages the material needed for a concise, citable preprint.  Populate each section with the accompanying data
before submission (e.g., arXiv).

## 1. Introduction

- Present the two falsifiable forms of the composition law (thermodynamic and complexity bounds).
- State the motivation: μ-ledger accounting unifies computation, information, and energy.
- Point to the live README dashboard and replication infrastructure as an open challenge to the community.

## 2. Background and Prior Work

- Summarise the Thiele Machine architecture (proposer/auditor, partitions, μ-spec).
- Cite classical Landauer limits, MDL, and complexity separations relevant to blind vs sighted reasoning.

## 3. Experimental Protocols

- Briefly describe the archived proofpacks (Landauer, turbulence, cross-domain, and any new domains).
- Reference `REPLICATION_GUIDE.md` for reproducibility details.
- Include a table listing each run, dataset, and manifest digest.

## 4. Results and Falsifiability Dashboard

- Embed the Markdown table produced by `python -m tools.falsifiability_analysis --write-markdown`.
- Highlight any negative slack or ratios ≤ 1 as counterexamples; otherwise, report current margins (e.g., Landauer slack 0.000 μ-bits, turbulence ratio 2.489×).
- Discuss how new data will be incorporated automatically via the CI integration.

## 5. Counterexample Campaigns

- Summarise the open `counterexample` issues and their status.
- Document unsuccessful attempts: conditions tested, observed slack, and why they failed to break the law.
- Invite domain experts (physics, compression, ML) to contribute new datasets or theoretical challenges.

## 6. Case Study: Turbulence

- Reference `documents/case_studies/turbulence_case_study.md` for a detailed exposition.
- Explain how μ-ledger predictions map to the observed 2.5× runtime gap.
- Discuss implications for future high-Reynolds experiments.

## 7. Discussion

- Address trust perimeter: remaining axioms, admissible lemmas, and automation of admit reports.
- Contrast empirical falsifiability with philosophical framing (which now lives in `documents/philosophy.md`).
- Lay out the roadmap for future domains and hardware experiments.

## 8. Conclusion

- Restate the falsifiable predictions and current experimental status.
- Emphasise the open invitation for replication and counterexample hunts.
- Provide links to the GitHub repository, replication guide, and issue tracker.

## Appendix A. Ledger and Receipt Formats

- Include excerpts of `landauer_steps.jsonl`, turbulence ledger schema, and manifest digests.
- Document the CLI interface for the falsifiability analysis tool.

Keep this outline in sync with the README dashboard and replication logs so the preprint stays current.
