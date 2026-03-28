# Thiele Machine Hardening Tracker

**Purpose**: Living checklist for systematic proof hardening. Work top-down. Each item gets checked off when formally done — not when "basically done."

**STATUS LEGEND**
- `[x]` Done — formal artifact exists and passes CI
- `[~]` Partial — exists but incomplete or untested
- `[ ]` Not started

---

## PHASE A — Immediate (cert story complete + CI gate)

- [x] **A1** `certification_requires_positive_mu` — master theorem, both channels (AbstractNoFI.v §11)
- [x] **A2** Cert channel audit — csr_cert_addr (5 ops), vm_certified (1 op), vm_witness (intentionally excluded) — documented in claim_ledger.md
- [x] **A3** `no_free_certification_trace_mu` — trace-level mu lower bound, closes "smuggling through a sequence" (AbstractNoFI.v §9)
- [x] **A4** CI gate: `scripts/check_isa_proof_freshness.sh` + `make isa-proof-freshness-check` + integrated into `make proof-undeniable`

---

## PHASE B — Core Generalization (NoFI beyond certification)

- [x] **B1** Insight taxonomy defined: CERT (cost≥1 enforced) vs STRUCTURAL (free creation) — in InsightTaxonomy.v
- [x] **B2** `pnew_can_be_free` + `pnew_not_cert_setter` + `pnew_preserves_cert_addr` — PNEW is free structural creation, not insight
- [x] **B3** `morph_can_be_free` + `morph_not_cert_setter` + `morph_preserves_cert_addr` — MORPH is free structural creation, not insight
- [x] **B4** `morph_assert_cost_pos` + `morph_assert_is_cert_setter` — MORPH_ASSERT is the structural CERTIFICATION (costs ≥ 1)
- [x] **B5** Negative cases: `morph_delete_not_cert_setter`, `morph_tensor_not_cert_setter`, `morph_get_not_cert_setter`, `compose_not_cert_setter` — all structural ops are cert-channel neutral
- [x] **B6** `no_free_certified_insight` — umbrella: any trace with cert evidence change contains cert-setter with cost ≥ 1 and mu grew ≥ 1

---

## PHASE C — Classical Shadow (formalize the projection)

- [x] **C1** `ClassicalState` record + `shadow_proj : VMState → ClassicalState` in ShadowProjection.v
- [x] **C2** `shadow_proj_forgets_graph` — separation_A and separation_B have identical shadows but different graphs
- [x] **C3** `shadow_separation_theorem` — ∃ s1 s2 probe: shadow_equal ∧ graph_distinct ∧ probe separates (err=false vs err=true)
- [x] **C4** `probe_succeeds_on_A` + `probe_fails_on_B` — MORPH_DELETE probe is proven by vm_apply computation, depends on real graph content
- [x] **C5** `shadow_strictly_lossy` + `no_classical_separation` — any f(ClassicalState) gives same result on both witness states

---

## PHASE D — Turing/Thiele Strictness

- [x] **D1** Define `ClassicalMachine` / "Turing notion" — `is_classical_program` + `ClassicalMachine` record in TuringClassicalEmbedding.v; links to KernelTM.v
- [x] **D2** Embedding theorem — `classical_to_thiele` (identity) + `D2_faithfulness` in TuringClassicalEmbedding.v; shadow_proj preserved + structural layer frozen
- [x] **D3** Conservativity: `D3_conservativity` in ClassicalConservativity.v — classical traces preserve vm_graph, csr_cert_addr, vm_certified
- [x] **D4** Strictness: `D4_strictness` in TuringStrictness.v — d4_base witness: MORPH_ID passes probe in 1 step; classical traces (any length) always fail
- [x] **D5** Safe wording theorem: `D5_thiele_strictly_extends_classical` in TuringStrictness.v — formal D3+D4 conjunction: extension ∧ strictness

---

## PHASE E — Implementation Reality

- [x] **E1** Semantic alignment doc: `artifacts/final_claim_audit/semantic_alignment.md` — layer hierarchy, normative = Coq, drift prevention CI gates, alignment proof table
- [x] **E2** RTL opcode regression: CERTIFY (test_isomorphism_enforcement.py), MORPH_ASSERT (test_rtl_morph_opcodes.py), CHSH_TRIAL (test_chsh_verilator_hardware_bridge.py) — all pass via Verilator
- [x] **E3** Extraction freshness gate: CI warns if build/thiele_core.ml older than VMStep.v / Extraction.v (in check_isa_proof_freshness.sh)
- [x] **E4** Label Python VM as harness: `# HARNESS — not normative semantics` added to thielecpu/vm.py and forge_vm.py HEADER template
- [x] **E5** ISA proof-impact checklist: `artifacts/final_claim_audit/isa_proof_impact.md` — all 47 opcodes classified
- [x] **E6** Red-flag diff gate: `make check-sensitive-files` warns on uncommitted changes to VMStep.v / VMState.v / Extraction.v

---

## PHASE F — Public Defensibility (one-page documents)

- [x] **F1** Claim ledger: `artifacts/final_claim_audit/claim_ledger.md` — 14 KERNEL / 5 BRIDGE / 6 ASPIRATIONAL
- [x] **F2** Master audit summary: `artifacts/final_claim_audit/master_audit_summary.md`
- [x] **F3** One-page kernel statement: what the machine is, what μ is, what certification means, what is proven
- [x] **F4** One-page "what remains": open obligations for honesty — `artifacts/final_claim_audit/what_remains.md`
- [x] **F5** One-page classical-shadow explanation: full state vs shadow state, what projection forgets, why it matters — `artifacts/final_claim_audit/classical_shadow_explanation.md`
- [x] **F6** One-page anti-overclaim memo: no theorem alone proves physics claims; staged results; safe claim ladder — `artifacts/final_claim_audit/anti_overclaim_memo.md`
- [x] **F7** Demo-to-theorem map: each Act in demo_knowledge_receipt.py mapped to exact theorem name + what it does NOT prove — `artifacts/final_claim_audit/demo_theorem_map.md`
- [x] **F8** Nontriviality annotations: for each major theorem, annotate whether it is definitional / case-analysis / algebraic / bridge — `artifacts/final_claim_audit/nontriviality_annotations.md`

---

## SUPPORTING ARTIFACTS (auto-generated or maintained)

- [x] Proof dependency graph (`artifacts/proof_dependency_dag.json`, `artifacts/proof_dependency_file_graph.mmd`)
- [x] ISA proof-impact report (`artifacts/final_claim_audit/isa_proof_impact.md`)
- [x] Demo-to-theorem map (`artifacts/final_claim_audit/demo_theorem_map.md`)
- [x] Open obligations report (`artifacts/final_claim_audit/what_remains.md`)
- [x] Shadow projection summary (`artifacts/final_claim_audit/classical_shadow_explanation.md`)

---

---

## PHASE H — Universal NoFI (substrate-independent)

The previous NoFI theorems were for the Thiele VM specifically. Phase H closes
the gap to "any sound certification mechanism in any computational substrate."

- [x] **H1** `CertificationSystem` record in `UniversalCertificationCost.v` — parameterized over BOTH state type AND instruction type. No reference to vm_instruction anywhere in the definition.
- [x] **H2** `universal_nfi_any_substrate` — for any CertificationSystem satisfying A2 (cert_costs), any trace from uncertified → certified has total cost ≥ 1. Proof: 8-line induction. Zero Admitted. Zero axioms.
- [x] **H3** Thiele cert_addr instantiation: `thiele_cert_addr_system` — A2 discharged by `no_free_certification`.
- [x] **H4** Thiele vm_certified instantiation: `thiele_certified_system` — A2 discharged by `no_free_certification_certified`.
- [x] **H5** Minimality: A2 is exactly the right condition. If A2 fails, free certification exists and the theorem is false. Documented in Part 6 of `UniversalCertificationCost.v`.
- [x] **H6** Axiom 5 framework: `QuantitativeCertificationSystem` (A2/A3/A5 + telescoping lemma + `universal_nfi_quantitative`) in `QuantitativeNoFI.v`. Zero Admitted. First non-trivial instantiation: CHSH channel with `chsh_trial_cost` + `chsh_cert` + `chsh_qcs` + `chsh_quantitative_nfi`. Key lemmas: `record_trial_total`, `vm_apply_witness`, `chsh_a3_obligation`.
- [x] **H7** W2 proper — `chsh_trial_count_lower_bound`: N accumulated CHSH trials require N valid `CHSH_TRIAL` instructions. Parameterized by arbitrary N. `chsh_cert_n N`, `chsh_a2_n`, `chsh_a5_n`, `chsh_a3_n`, `chsh_qcs_n`, corollary `chsh_qcs_n_1_matches`. Zero Admitted.
- [x] **H8** W2 statistical — `CHSHStatisticalBridge.v`: `chsh_stat_from_wc` (CHSH from aggregate WitnessCounts), `correlator_abs_le_1` (|E|≤1 via Z.abs_le + Pos.of_nat_succ), `chsh_stat_algebraic_bound` (|S|≤4, triangle inequality), `violation_wc` (S=4>2, vm_compute), `chsh_stat_violation_not_local` (S>2→no local strategy), `four_trials`/`n_trials_require_n_instructions` (W2 at n=4 and general n). Two named hypotheses documented: `local_bound_for_wc` (Bell 16-case, same structure as CHSH.v), `hoeffding_chsh_concentration` (Hoeffding 1963). Zero Admitted.

**What this means**: The theorem now applies to any system where "going from uncertified to certified in one step costs ≥ 1." Thiele is one instance. A proof assistant (cost = proof size), a consensus protocol (cost = work), a physical measurement (cost = thermodynamic work), or a neural network (cost = training compute) are all potential instances. The instruction type is fully abstract — it can be anything.

---

## PHASE G — Trust Gap Closure (maximum achievable)

Three residual trust gaps identified after Phase F. This phase closes each as far as
the formal tools allow.

### G1 — OCaml Extraction Gap

- [x] **G1a** `OCamlExtractionBridge.v` compiles with zero Admitted. Formally proven: mu-cost = apply_cost, mu nondecreasing, vm_apply total. Named axiom `ocaml_extraction_faithful` marks the trust boundary explicitly.
- [x] **G1b** `tests/test_ocaml_extraction_parity_47.py` — exhaustive parity test covering all 47 opcodes through `build/extracted_vm_runner`. Verifies: (a) every opcode arm is reachable in the OCaml runner; (b) μ-cost invariant holds per opcode; (c) `CERTIFY` cost-is-S invariant verified. 59 tests, all passing.
- [~] **G1c** IRREDUCIBLE GAP: OCaml operational semantics are not formalized in Coq. Closing this fully would require a certified OCaml compiler (CompCert for OCaml) — an open research problem. The named axiom + exhaustive tests are the maximum achievable without such a tool.

### G2 — Verilog RTL Gap

- [x] **G2a** `VerilogRTLCorrespondence.v` uses a Section Variable `rtl_step_correct` (not a global Axiom) — the RTL correspondence is a premise, not a postulate. After `End RTLCorrespondenceSection`, every theorem is universally quantified over it.
- [x] **G2b** `bsc_kami_compilation_trusted` Variable added to `VerilogRTLCorrespondence.v` — explicitly names the BSC compilation trust boundary (Kami OCaml → Bluespec → Verilog via BSC compiler). Backed by: 31/31 cosim tests, 11,049/11,049 fuzz tests, FPGA synthesis (0 errors).
- [~] **G2c** IRREDUCIBLE GAP: BSC compiler correctness is not machine-verified in Coq. This is analogous to G1c. The named Section Variable makes it auditable; simulation evidence backs it empirically.

### G3 — Physics Interpretation Gap

- [x] **G3a** Comprehensive audit: `artifacts/final_claim_audit/physics_interpretation_boundaries.md` — all 13 physics files classified: pure-math / named-hypothesis / analogy / negative-result.
- [x] **G3b** Updated `artifacts/final_claim_audit/physics_research_boundaries.json` — all 13 files listed with status, proven content, and interpretation gap.
- [x] **G3c** Key finding: physics files already had good disclaimers (`EinsteinEmergence.v` explicitly says "analogy", `BekensteinCalibration.v` names `mu_energy_unit_is_landauer` as a falsifiable hypothesis, `LorentzNotForced.v` explicitly proves Lorentz is NOT derivable). The audit documents this systematically.
- [~] **G3d** IRREDUCIBLE GAP: The interpretation step (assigning physical meaning to VMState objects) cannot be machine-checked. The one falsifiable physical claim is `mu_energy_unit_is_landauer`: run hardware traces, measure energy per vm_mu increment, compare to k_B × T_hardware × ln 2.

---

## DONE-MEANS-DONE CONDITIONS (§16 verbatim)

- [x] Every cert/evidence channel covered by non-free theorems
- [x] No Free Insight stated beyond a single cert field (InsightTaxonomy.v: no_free_certified_insight)
- [x] Classical shadow projection formalized (ShadowProjection.v: shadow_proj)
- [x] Separation theorem exists, not just a demo (ShadowProjection.v: shadow_separation_theorem)
- [x] Turing/classical embedding explicit (D2_faithfulness in TuringClassicalEmbedding.v)
- [x] Strictness phrased in theorem-grade way (D5_thiele_strictly_extends_classical in TuringStrictness.v)
- [x] Extraction and implementation preserve theorem-sensitive observables (OCamlExtractionBridge.v: extraction_trust_boundary — formal mu-cost/nondecreasing/totality; named axiom ocaml_extraction_faithful marks the trust boundary; empirical validation via CI parity tests)
- [x] CI fails on proof-sensitive semantic drift (A4 hard-fails on stale .vo; check-sensitive-files-strict hard-fails on uncommitted VMStep.v/VMState.v/Extraction.v; integrated into proof-undeniable)
- [x] Public documents cleanly separate proven from aspirational claims

---

## EXECUTION LOG

| Date | Item | Action |
|---|---|---|
| 2026-03-26 | A1-A3 | certification_requires_positive_mu + trace-level + vm_certified channel |
| 2026-03-26 | F1-F2 | claim_ledger.md + master_audit_summary.md created |
| 2026-03-27 | A4 | check_isa_proof_freshness.sh + Makefile isa-proof-freshness-check |
| 2026-03-27 | B1-B6 | InsightTaxonomy.v: insight taxonomy + umbrella no_free_certified_insight |
| 2026-03-27 | C1-C5 | ShadowProjection.v: shadow_proj + separation theorem + strictly lossy |
| 2026-03-27 | F3-F8 | one_page_kernel_statement + what_remains + classical_shadow + anti_overclaim + demo_theorem_map + nontriviality_annotations |
| 2026-03-27 | E3-E6 | extraction freshness check + harness label + isa_proof_impact.md + check-sensitive-files target |
| 2026-03-27 | D3 | ClassicalConservativity.v: D3_conservativity — graph/cert/certified preserved over classical traces |
| 2026-03-27 | D1+D2 | TuringClassicalEmbedding.v: ClassicalMachine + classical_to_thiele + D2_faithfulness |
| 2026-03-27 | D4+D5 | TuringStrictness.v: D4_strictness (d4_base witness) + D5_thiele_strictly_extends_classical |
| 2026-03-27 | E1 | artifacts/final_claim_audit/semantic_alignment.md — layer hierarchy + normative policy |
| 2026-03-27 | E2 | RTL regression confirmed: CERTIFY + MORPH_ASSERT + CHSH_TRIAL all pass in Verilator |
| 2026-03-27 | DONE | OCamlExtractionBridge.v: extraction_trust_boundary proven (mu-cost, nondecreasing, totality); ocaml_extraction_faithful named axiom |
| 2026-03-27 | DONE | check-sensitive-files-strict: hard-fail (exit 1) on uncommitted ISA changes; integrated into proof-undeniable |
| 2026-03-27 | G1 | OCamlExtractionBridge.v compiles clean; test_ocaml_extraction_parity_47.py 59/59 pass; all 47 opcode arms verified |
| 2026-03-27 | G2 | bsc_kami_compilation_trusted Section Variable added to VerilogRTLCorrespondence.v; BSC trust boundary named |
| 2026-03-27 | G3 | physics_interpretation_boundaries.md: all 13 physics files audited; physics_research_boundaries.json updated |
| 2026-03-27 | H1-H5 | UniversalCertificationCost.v: CertificationSystem (abstract state+instr), universal_nfi_any_substrate, Thiele dual instantiation |
| 2026-03-27 | H6 | QuantitativeNoFI.v: QCS + telescoping + universal_nfi_quantitative + CHSH W2 instantiation (zero Admitted) |
| 2026-03-27 | H7 | chsh_trial_count_lower_bound: N CHSH trials require N CHSH_TRIAL instructions (arbitrary N, zero Admitted) |
| 2026-03-27 | H8 | CHSHStatisticalBridge.v: chsh_stat_from_wc, |S|≤4, violation_wc (S=4), chsh_stat_violation_not_local, W2 at n=4 + general n; two named hypotheses (Bell local bound + Hoeffding); zero Admitted |
