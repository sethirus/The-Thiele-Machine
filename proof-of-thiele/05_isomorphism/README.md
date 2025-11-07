# Pillar 5 – Physics ≅ Logic ≅ Computation ≅ Composition

`demonstrate_isomorphism.py` is the six-act runtime dissertation that couples the
Bell inequality experiment with the mechanised categorical proofs in
`coq/isomorphism/`. It generates the Markdown ledger
`BELL_INEQUALITY_VERIFIED_RESULTS.md`, whose sections document:

1. analytic derivations of π and √2 to pin the Tsirelson bound,
2. the exhaustive classical CHSH search establishing |S| ≤ 2,
3. the supra-quantum witness reaching S = 16/5 alongside the Coq artefacts,
4. the receipt bundle tying runtime to formal proof,
5. the verifier execution, and
6. Operation Cosmic Witness, which lifts physical data into the same cost model. The accompanying documentation now makes clear that this is a toy CHSH-style decision rule over 16 scalar CMB temperatures and does not claim cosmological inference.

Run the lightweight ledger check with:

```bash
make -C proof-of-thiele isomorphism
```

This confirms that the published ledger still records all six acts and the key
statements (Tsirelson bound, S = 16/5) that realise the physics ↔ logic ↔
computation ↔ composition equivalence.
