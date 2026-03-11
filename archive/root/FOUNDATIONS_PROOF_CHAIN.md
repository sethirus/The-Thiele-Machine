# Foundations Proof Chain Audit (Thiele Machine)

Date: 2026-03-01
Scope: `coq/**/*.v` (322 files), extraction, runtime wrapper, and canonical Kami/RTL bridge.

This document answers six required questions as an auditable chain from the bottom-most foundations to all higher proof/runtime surfaces.

## Q1. What is the Thiele Machine, constructively?
The Thiele Machine is a proof-first stack where executable behavior is derived from Coq kernel semantics, then propagated to extracted OCaml/Python runtime and canonical Kami/RTL surfaces.

Primary chain endpoints:
- Coq foundations: `coq/kernel/VMState.v`, `coq/kernel/VMStep.v`
- Cost/ledger/no-free-insight foundations: `coq/kernel/MuCostModel.v`, `coq/kernel/MuLedgerConservation.v`, `coq/kernel/NoFreeInsight.v`, `coq/kernel/MuInitiality.v`
- Extraction/runtime: `coq/Extraction.v`, `tools/extracted_vm_runner.ml`, `build/thiele_vm.py`
- Canonical hardware proof path: `coq/kami_hw/CanonicalCPUProof.v`, `coq/kami_hw/KamiExtraction.v`, `thielecpu/hardware/cosim.py`

Atlas chain section (generated): `artifacts/ATLAS.md:68`

## Q2. What are the foundational proofs?
Foundational theorem family anchors:
- State/partition kernel foundations: `coq/kernel/VMState.v:104`, `coq/kernel/VMState.v:113`, `coq/kernel/VMState.v:641`
- Operational semantics relation: `coq/kernel/VMStep.v:263`
- Mu-cost model and trace accumulation: `coq/kernel/MuCostModel.v:87`, `coq/kernel/MuCostModel.v:110`, `coq/kernel/MuCostModel.v:281`
- Mu-ledger conservation/monotonicity: `coq/kernel/MuLedgerConservation.v:165`, `coq/kernel/MuLedgerConservation.v:239`, `coq/kernel/MuLedgerConservation.v:373`
- No Free Insight theorem line: `coq/kernel/NoFreeInsight.v:275`
- Mu initiality/universality line: `coq/kernel/MuInitiality.v:812`, `coq/kernel/MuInitiality.v:799`

These are the constructive roots used by bridge/extraction/hardware proofs.

## Q3. What is the bottom-most layer?
Bottom-most layer is `coq/kernel/VMState.v`.

Why this is auditable:
- Explicitly declared as bottom layer in atlas chain output: `artifacts/ATLAS.md:70`
- Explicitly encoded in mesh generator canonical chain: `scripts/generate_full_mesh_audit.py:124`

## Q4. How are all proofs (including OCaml/Kami extraction) required to connect to foundations?
Mechanical enforcement exists in Inquisitor + Atlas generation:

Constructive/no-shortcut bans:
- `ADMITTED` ban: `scripts/inquisitor.py:743`
- `AXIOM_OR_PARAMETER`: `scripts/inquisitor.py:880`
- `HYPOTHESIS_ASSUME`: `scripts/inquisitor.py:887`
- `CONTEXT_ASSUMPTION`: `scripts/inquisitor.py:899`
- Assumption audit (`Print Assumptions`): `scripts/inquisitor.py:4964`, `scripts/inquisitor.py:5005`

Foundation connectivity rules:
- File-level foundation chain connectivity gate: `PROOF_CONNECTIVITY_GAP` at `scripts/inquisitor.py:1427`, `scripts/inquisitor.py:1499`, documented at `scripts/inquisitor.py:6195`
- OCaml/Kami shared-foundation consistency gate: `KAMI_OCAML_FOUNDATION_MISMATCH` at `scripts/inquisitor.py:1537`, `scripts/inquisitor.py:1612`, documented at `scripts/inquisitor.py:6196`
- End-to-end cross-layer gate: `CROSS_LAYER_FOUNDATION_DISCONNECT` at `scripts/inquisitor.py:5307`, documented at `scripts/inquisitor.py:6198`

Extraction faithfulness gate:
- `EXTRACTION_SEMANTIC_UNFAITHFUL`: `scripts/inquisitor.py:5981`, documented at `scripts/inquisitor.py:6140`

Current gate evidence (latest atlas run):
- Inquisitor gate PASS: `artifacts/ATLAS.md:31`
- Strict pass True: `artifacts/ATLAS.md:45`
- HIGH findings 0: `artifacts/ATLAS.md:49`
- MEDIUM findings 0: `artifacts/ATLAS.md:50`
- Proof connectivity gaps 0: `artifacts/ATLAS.md:52`
- Cross-layer foundation disconnects 0: `artifacts/ATLAS.md:53`

## Q5. Where are No Free Insight and mu-bits linked in the constructive chain?
Mu/no-free-insight chain anchors:
- Mu-cost semantics: `coq/kernel/MuCostModel.v:87`
- Ledger conservation theorem: `coq/kernel/MuLedgerConservation.v:165`
- Irreversibility lower bound relation: `coq/kernel/MuLedgerConservation.v:338`
- No Free Insight theorem: `coq/kernel/NoFreeInsight.v:275`
- Strengthening theorem (requires structure addition): `coq/kernel/NoFreeInsight.v:294`
- Mu initiality theorem: `coq/kernel/MuInitiality.v:812`

Interpretation for the chain:
- `MuCostModel` defines cost accumulation semantics.
- `MuLedgerConservation` constrains irreversible information accounting.
- `NoFreeInsight` proves strengthening cannot be free without structural addition.
- `MuInitiality` gives uniqueness/universality of the mu functional used as canonical cost witness.

## Q6. Are all Coq proofs fully constructive with no exceptions, and does every proof file flow to the bottom?
Current strongest auditable answer: almost, with one explicit exception to close before claiming absolute certainty.

What is already true now:
- Inquisitor strict gate is passing with no HIGH/MEDIUM findings: `artifacts/ATLAS.md:45`, `artifacts/ATLAS.md:49`, `artifacts/ATLAS.md:50`
- Foundation connectivity and cross-layer disconnect counters are zero: `artifacts/ATLAS.md:52`, `artifacts/ATLAS.md:53`
- Coq compile gate reports zero admitted proofs on compiled set: `artifacts/ATLAS.md:199`

Previously identified exception (`coq/kernel/Test.v`) has been resolved:
- `coq/kernel/Test.v` was a non-proof-bearing scratch file (only contained `Check einstein_tensor`).
- It has been removed from the repository as it is not part of the proof-bearing scope.
- All remaining Coq source files are compiled with matching `.vo` artifacts.

Therefore:
- The strict constructive chain covers all proof-bearing Coq files with no exceptions.

## Canonical Foundation Chain (auditable map)
1. `coq/kernel/VMState.v` - bottom state/partition foundations
2. `coq/kernel/VMStep.v` - operational step relation
3. `coq/kernel/MuCostModel.v` - mu-cost semantics
4. `coq/kernel/MuLedgerConservation.v` - ledger conservation/monotonicity
5. `coq/kernel/NoFreeInsight.v` - no-free-insight theorem
6. `coq/kernel/MuInitiality.v` - initiality/universality of mu
7. `coq/Extraction.v` - extraction entrypoint
8. `tools/extracted_vm_runner.ml` - extracted runner
9. `build/thiele_vm.py` - strict backend wrapper
10. `coq/kami_hw/CanonicalCPUProof.v` - canonical hardware refinement surface
11. `coq/kami_hw/KamiExtraction.v` - Kami extraction
12. `thielecpu/hardware/cosim.py` - canonical co-simulation harness

Generated diagram source: `artifacts/atlas/foundation_chain.mmd`

## Reproducible Verification Checklist (for certainty)
Run these and require all pass:
1. `make -C coq` (or equivalent full gate) and verify all proof-bearing `.v` are compiled.
2. `python3 scripts/inquisitor.py --report INQUISITOR_REPORT.md` and require:
   - HIGH = 0, MEDIUM = 0
   - `PROOF_CONNECTIVITY_GAP` = 0
   - `KAMI_OCAML_FOUNDATION_MISMATCH` = 0
   - `CROSS_LAYER_FOUNDATION_DISCONNECT` = 0
   - `EXTRACTION_SEMANTIC_UNFAITHFUL` = 0
3. `INQUISITOR_TIMEOUT=600 python3 scripts/generate_full_mesh_audit.py` and confirm:
   - `artifacts/ATLAS.md:31` shows Inquisitor PASS
   - `artifacts/ATLAS.md:52` and `artifacts/ATLAS.md:53` remain zero
4. Ensure no uncompiled proof-bearing files remain (RESOLVED: `coq/kernel/Test.v` removed as non-proof-bearing).

## Audit Verdict
- Constructive chain enforcement is implemented and passing for all proof-bearing Coq files.
- All Coq proof files compile with no exceptions. The previously identified gap (`coq/kernel/Test.v`) was a non-proof-bearing scratch file and has been removed.
