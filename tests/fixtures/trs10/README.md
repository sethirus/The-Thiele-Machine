# TRS-1.0 Fixture Corpus

This directory is the public corpus layout for TRS-1.0 verifier work.

The initial corpus is now populated with concrete signed receipts and adversarial variants so that:

- verifier work targets a stable directory layout
- fixture naming conventions are explicit
- verifier coverage is exercised by the maintained fixture and test set

## Layout

- `fileset/valid/`: valid fileset receipts and their on-disk input files
- `fileset/invalid/`: malformed or adversarial fileset receipts grouped by failure mode
- `execution/valid/`: valid execution receipts, source programs, and replay inputs
- `execution/invalid/`: malformed or adversarial execution receipts grouped by failure mode
- `compat/v1/golden/`: compatibility fixtures frozen for `TRS-1.0`

## Population rule

Every fixture set includes or should include:

- a `README.md` describing the fixture intent
- enough on-disk inputs to exercise verification realistically
- a manifest entry in `manifest.json`

The corpus covers signature, digest, payload-tamper, schema, kind-confusion,
path, metadata, content, size, source-tamper, fuel, replay, `mu`,
canonicalization-pair, basename-collision, JSON-edge, and stress checks. It is
the maintained focused fixture set exercised by the TRS tests and
`manifest.json`; the verifier contract is defined by those fixtures and the
corresponding test modules.
