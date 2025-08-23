



# THE ARCHITECTURAL COLLAPSE OF NP

This folder contains a single formal artifact: a Coq proof demonstrating that, in the Thiele Machine model, the distinction between P and NP collapses structurally.

---

## Contents

- **proof.v**: The formal Coq proof that, in the Thiele Machine model, P=NP.

## The Collapse

The P vs NP problem is addressed not by a new algorithm, but by a new computational architecture. In the Thiele Machine, the certificate is part of the state, making the "solve" operation definitionally equivalent to the verifier. The distinction between P and NP collapses structurally, as demonstrated by the proof in this folder.

