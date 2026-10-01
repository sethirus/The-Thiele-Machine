# Part 4, round 2 freeze: corrected 4.1 parameterization

Date: 2026-10-01

Round 1 remains unedited. Its target did not typecheck because
`forced_priced` is parameterized by `step`, not by the instruction equality
decision. Round 2 changes only that application; the equality decision remains
an argument because `forced_priced_iff_merges` needs it.

- `part4-pricing-physics-target.v.sha256`:
  `5330997c08ab9df944cd6fbea61624865c73168c3df9c2fa124d4c4792f1081e`
- All other frozen source hashes, exact statements, predictions, success and
  failure criteria, and literature baselines are unchanged from round 1.

Predicted outcome: the corrected target typechecks and the Part 4 outcomes
remain 4.1 PROVED BUT KNOWN, 4.2 PARTIAL, 4.3 PARTIAL, and 4.4 PROVED BUT KNOWN.
