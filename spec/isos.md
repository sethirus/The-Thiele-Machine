Isomorphism sketch: Logic ↔ Physics ↔ Composition ↔ Computation

This note sketches the working contract used by the project to make the
informal claim that logical proofs, physical measurement receipts,
compositional structure, and computation are coherent (isomorphic) in the
following engineering sense:

- Logical artifacts (CNF, LRAT/DRAT proofs, models) are canonicalised and
  hashed. These artifacts are the authoritative declarative descriptions of
  constraints and proof objects.
- Physical artifacts (receipt step observations, timestamps, solver replies)
  are captured as canonical JSON certificates and included in step receipts.
- Composition is represented by the pipeline: CNF + proof/model → certificate
  → canonical receipt → validator. Each transform preserves a canonical
  representation and a digest, enabling composition to be checked externally.
- Computation is the runtime behaviour of the VM and the proof-producing
  tools. The μ-spec pins the computational cost model in `tools/mu_spec.py`.

Minimal contract (operational)
------------------------------
1. Producers output: CNF blob, proof or model blob, and a step-level receipt
   that references those blobs by URI and includes `mu_delta` computed using
   the canonical μ-spec.
2. Canonicaliser: normalises receipts to spec v1.1, emits canonical models
   (if applicable), computes `*_sha256` digests, per-step signatures, and the
   `global_digest`.
3. Validator: checks step hashes, signature(s), verifies `cnf_sha256`/
   `proof_sha256`/`model_sha256` when present, recomputes μ via `tools/mu_spec`,
   and verifies satisfiability/proof using the canonical CNF and model.

How this supports an isomorphism claim
-------------------------------------
- Determinism & canonical encoding provide a unique representative for each
  artifact (CNF, model, proof). The canonical encoding + stable hashing is the
  glue between the logical artifact and its physical representation.
- The validator's computations (μ recomputation, proof/model checking) are a
  pure function on canonical representations, enabling offline, reproducible
  verification: a proofpack should be verifiable independent of the producer.
- Composition (stitching receipts into larger narratives) is achieved by
  concatenating canonical steps and aggregating their digests; tampering at
  any point breaks the chain.

Example mapping (concrete)
--------------------------
- CNF (DIMACS) <-> canonical CNF (sorted vars, renumbered) -> CNF SHA256
- Model (DIMACS literals over original vars) -> canonical model (remapped)
  -> model SHA256
- LRAT/DRAT proof file -> proof SHA256
- Step receipt (instruction, pre/post state, observation) -> canonical
  step_hash and signature

See `scripts/demo_isomorphism.py` for a runnable minimal demonstration.
