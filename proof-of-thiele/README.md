# Proof of the Thiele Thesis

This directory curates a compact, auditable demonstration that the Thiele Machine
strictly contains classical Turing computation while remaining mechanically
verifiable. Each subsection links the repository artefacts that establish the
five pillars of the thesis and ships a minimal script or command sequence that
an auditor can execute end-to-end.

| Pillar | Evidence | How to replay it |
| --- | --- | --- |
| 1. **Containment** | Coq kernel proof `thiele_simulates_turing` and the subsumption wrapper | `make -C proof-of-thiele containment` |
| 2. **Separation** | Deterministic Tseitin experiment receipts with μ-ledgers | `make -C proof-of-thiele separation` |
| 3. **μ conservation** | μ-spec v2.0 and replay of the experiment receipts | `make -C proof-of-thiele cost-model` |
| 4. **Receipts & auditability** | Deterministic verification script checking the proofpack-ready receipts | `make -C proof-of-thiele receipts` |
| 5. **Isomorphism law** | Bell inequality runtime thesis tying physics ↔ logic ↔ computation ↔ composition | `make -C proof-of-thiele isomorphism`

Run `make -C proof-of-thiele all` to execute every pillar sequentially. Each
step references reproducible artefacts that already live in the repository; no
network access or external datasets are required.
