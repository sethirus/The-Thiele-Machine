# Independent Audit of *The Thiele Machine*

## 1. Engagement scope and approach
- **Objective.** Validate the repository's claims about partition-native computation by reproducing the flagship demonstrations, reviewing the published guarantees, and inspecting supporting artefacts.
- **Environment.** All checks were executed on Python 3.12 inside the repository's editable installation (`pip install -e .`) with Coq 8.18 bootstrapped through the supplied tooling, matching the prerequisites advertised in the README.【F:README.md†L13-L36】
- **Methodology.** I:
  1. Regenerated the Bell/CHSH “thesis run”.
  2. Replayed and verified signed receipts.
  3. Compiled the Coq witnesses via the project scripts.
  4. Ran the new graph-colouring cascade and the Engine of Discovery suite to observe blind-versus-sighted behaviour.
  5. Cross-referenced these results with the repository's stated guarantees and outstanding proof obligations.【F:README.md†L88-L159】

## 2. Reproduced demonstrations
### 2.1 Bell inequality thesis run
Running `python3 demonstrate_isomorphism.py` rebuilt the six-act transcript, including derivations of the Tsirelson bound, the exhaustive classical strategy audit, and the sighted witness that reaches \(S \approx 2.828426\). The script also regenerated sealed receipts, Operation Cosmic Witness proofs, and the SHA-256 manifest advertised by the project.【62d400†L1-L115】【62d400†L132-L207】

### 2.2 Receipt replay
`python scripts/challenge.py verify receipts` validated every published receipt (aggregate μ-cost 7.0) and confirmed that the Tsirelson witnesses ship with zero μ-debt, consistent with the ledger claims.【8823ee†L1-L8】

### 2.3 Coq replay
After installing the opam toolchain through `scripts/setup_coq_toolchain.sh` and sourcing `.coq-env`, the provided verifier `./scripts/verify_truth.sh examples/tsirelson_step_receipts.json` discharged the Coq obligations for the canonical Bell run without errors, confirming that the mechanised replay matches the runtime receipts.【5590b0†L1-L12】【9a7371†L1-L2】

## 3. Empirical investigations beyond the flagship run
### 3.1 Graph colouring cascade
Executing `python scripts/graph_coloring_demo.py` reproduced the three-act cascade on the shipped expander instances. Blind search enumerated tens to thousands of candidates, whereas the sighted solver maintained constant μ-cost until Act III, where the μ-ledger recorded the expected jump (e.g., 1302.3 bits for the 9-node triadic cascade, rising to 4351.5 bits for the 30-node instance). Receipts, scaling tables, and plots were written to `graph_demo_output/` for later audit.【56ff88†L1-L29】

### 3.2 Engine of Discovery and sight-debt ledger
Invoking `python attempt.py --help` runs the paradox reconstruction harness. The blind affine solver is formally refuted (Farkas certificate), while the partition-aware solver succeeds with zero μ-cost. The Engine of Discovery enumerates all viable partitions, locating six symmetric decompositions at 105 bits each. The closing batch experiment (50 Tseitin instances) logs the exponential gap: the GF(2) sighted solver resolves every case instantly, whereas the resolution-based solver exhausts its conflict budget as size grows, producing the censored receipts highlighted in the README’s separation claims.【4cfa70†L1-L84】【4cfa70†L85-L162】【b568ca†L1-L38】【229286†L1-L73】

## 4. Alignment with repository guarantees
- **Formal status.** The README accurately reports 19 admits and 10 axioms in the Coq development, and the `Repository Guarantees` section documents which kernel bridges still depend on them. My Coq replay confirms the published Bell receipts align with the mechanised witnesses, but no additional lemmas were discharged during this audit.【F:README.md†L3-L144】
- **Executable artefacts.** The regenerated transcripts match the repository’s promise of a self-verifying artifact: receipts are Ed25519-signed, μ-ledgers are emitted alongside analytic certificates, and the helper tooling (challenge/verifier scripts) function as described.【F:README.md†L133-L144】【62d400†L150-L207】【8823ee†L1-L8】
- **Empirical separation.** The observed μ-cost jumps in the cascade and the censored-vs-sighted outcomes in the Tseitin batch align with the hypothesis that classical blindness manifests as exponential information debt, consistent with the “No Unpaid Sight Debt” narrative published in the spec and README.【56ff88†L1-L29】【4cfa70†L85-L162】【229286†L1-L73】

## 5. Open issues and recommendations
1. **Document Coq bootstrap prerequisites.** The setup script currently assumes `opam` is available; surface this dependency (and disk footprint) alongside the Quick Start so auditors are not surprised by the 500 MB toolchain download.【1d7e01†L1-L3】【F:README.md†L13-L36】
2. **Summarise μ-ledger results.** The cascade and Tseitin experiments emit rich JSON and plots; consider adding a short narrative table to the README or RESULTS.md to help readers relate the raw receipts to the stated exponential separation claim.
3. **Track outstanding admits.** Publishing progress notes (e.g., in `ADMIT_REPORT.txt`) when admits are retired would tighten the formal story and make it easier for external reviewers to gauge remaining proof debt.

## 6. Conclusion
All reproduced experiments, receipt verifications, and Coq checks behaved exactly as advertised. The evidence collected here corroborates the repository’s core thesis—that partition-native reasoning with explicit μ-accounting can expose qualitative separations between blind and sighted computation—while leaving the documented admitted lemmas and axioms as the main outstanding formal work.
