# Part 4, round 3 freeze: corrected numeric scopes

Date: 2026-10-01

Rounds 1 and 2 remain unedited. Round 2 exposed a parsing error caused by the
open real-number scope: the arguments to functions from `nat` were read as
reals. Round 3 adds `%nat` to those arguments and changes nothing semantic.

- `part4-pricing-physics-target.v.sha256`:
  `c32474eaa5ef721e94ac22530034b57d53f7d6dde4de7470a4e93696059df9a7`
- All other frozen source hashes, exact statements, predictions, success and
  failure criteria, and literature baselines are unchanged from round 1.

Predicted outcome: the corrected target typechecks and the Part 4 outcomes
remain 4.1 PROVED BUT KNOWN, 4.2 PARTIAL, 4.3 PARTIAL, and 4.4 PROVED BUT KNOWN.
