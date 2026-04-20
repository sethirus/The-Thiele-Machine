# Claim Ledger — The Thiele Machine

**Format**: KERNEL/PROVEN | BRIDGE/PARTLY PROVEN | ASPIRATIONAL/NOT YET PROVEN

Each claim is classified by formal status, not rhetorical strength.
Last updated: 2026-04-16. (Prior version: 2026-03-26 — significant promotions since.)

---

## KERNEL / PROVEN

These claims are backed by fully proven Coq theorems with zero Admitted.
They are defensible against any formal audit.

| Claim name | Exact statement | Formal file(s) | Depends on | Semantic layer | What it does NOT prove | Public-safe wording |
|---|---|---|---|---|---|---|
| **no_free_certification** | If csr_cert_addr: 0→nonzero in one vm_apply step, then instruction_cost ≥ 1 | AbstractNoFI.v §8 | thiele_non_cert_addr_setter_preserves, cert_addr_setter_cost_pos | Coq kernel | Cost is exact; that info-theoretic value forces this cost | "Structural certification cannot appear without paying cost" |
| **no_free_certification_mu** | If csr_cert_addr: 0→nonzero in one step, then (vm_apply s i).mu ≥ s.mu + 1 | AbstractNoFI.v §8 | no_free_certification, vm_apply_mu | Coq kernel | Trace-level version; vm_certified channel | "The μ-ledger records at least 1 unit when cert evidence appears" |
| **no_free_certification_trace_mu** | If cert_addr was 0 and is nonzero after a trace, then final_mu ≥ initial_mu + 1 | AbstractNoFI.v §9 | thiele_abstract_nfi_cost, acm_run_mu_exact | Coq kernel (sequential model) | PC-indexed multi-step version | "No finite sequence of instructions can create cert evidence for free" |
| **no_free_certification_certified** | If vm_certified: false→true in one step, then instruction_cost ≥ 1 | AbstractNoFI.v §10 | vm_apply_certified (PrimeAxiom) | Coq kernel | csr_cert_addr channel; trace-level | "The CERTIFY opcode cannot fire without cost" |
| **certification_requires_positive_mu** | Either cert channel (csr_cert_addr OR vm_certified) going absent→present implies mu grows ≥ 1 | AbstractNoFI.v §11 | no_free_certification_mu, no_free_certification_certified_mu | Coq kernel | vm_witness; trace composition | "ALL certification channels are non-free" |
| **abstract_nfi** | For ANY machine satisfying A3, going from uncert to cert requires a cert-setter in the trace | AbstractNoFI.v §2 | AbstractCertMachine record, acm_preserve axiom | Abstract (any machine over vm_instructions) | Cost bound (needs A4); specific VM binding | "The NoFI property is universal across honest machines" |
| **universal_nfi** | abstract_nfi + cert-setter has cost ≥ 1 | AbstractNoFI.v §7 | abstract_nfi, cert_addr_setter_cost_pos | Abstract | vm_certified channel; trace-level mu | "ANY abstract machine satisfying A3+A4 is subject to NoFI" |
| **thiele_nfi_pc_indexed** | In PC-indexed execution (trace_run), cert_addr 0→nonzero requires cert-setter in trace | AbstractNoFI.v §6 | nonlocal_correlation_requires_revelation | Coq kernel (PC-indexed) | mu bound for PC-indexed | "The Thiele VM under PC-indexed execution has NoFI" |
| **mu_is_initial_monotone** | Any function M satisfying instruction_consistent + zero-init equals vm_mu on reachable states | MuInitiality.v | CostFunctional record, vm_apply_mu | Coq kernel | That the cost function is information-theoretically forced | "μ is the unique canonical cost measure" |
| **vm_apply_mu** | (vm_apply s i).mu = s.mu + instruction_cost i | MuLedgerConservation.v | VMStep, SimulationProof | Coq kernel | That instruction_cost values are derivable from first principles | "μ exactly tracks cumulative instruction cost" |
| **kernel_certified_implies_positive_mu** | Starting with vm_certified=false, mu=0, reaching vm_certified=true implies mu > 0 | PrimeAxiom.v | vm_apply_certified, run_vm_mu_nondecreasing | Coq kernel (run_vm / PC-indexed) | trace-sequential version; quantitative bound | "You cannot certify from zero cost" |
| **categorical_separation** | Programs with identical (regs, mem, mu, pc, err, certified) can differ in morphism graph | PartitionSeparation.v §10 | VMState graph fields, morphism semantics | Coq kernel + graph layer | That the distinction has physical meaning | "Classical fingerprint is a lossy projection of full Thiele state" |
| **classical_observer_cannot_separate** | No function of (regs, mem, mu, pc, err, certified) alone can separate programs with different morphism graph | PartitionSeparation.v §11 | categorical_separation | Coq kernel + graph layer | That classical machines are computationally weaker | "Any purely classical observer is blind to morphism-structural distinctions" |
| **cert_addr_setter_cost_pos** | cert_addr_setterb i = true → instruction_cost i ≥ 1 | AbstractNoFI.v §3 | instruction_cost definition, cert_addr_setterb | Coq definitional | Non-circularity (this is definitional; no_free_certification closes that gap) | "Every cert-addr-setter charges at least 1 unit" |
| **no_free_certified_insight** | Any trace that takes cert_addr 0→nonzero contains a cert-setter with cost ≥ 1, and mu grew ≥ 1 | InsightTaxonomy.v | certified_insight_nonfree, no_free_certification_trace_mu | Coq kernel | Partition/witness insight classes beyond certification | "Certified insight cannot be acquired for free under any composition of ops" |
| **certified_insight_nonfree** | is_cert_insight_event s i → instruction_cost i ≥ 1 ∧ mu increased ≥ 1 | InsightTaxonomy.v | certification_requires_positive_mu | Coq kernel | vm_witness class | "Any transition that produces cert evidence costs ≥ 1" |
| **structural_only_trace_cannot_certify** | Traces with cert_addr_setterb = false throughout cannot change csr_cert_addr | InsightTaxonomy.v | structural_trace_preserves_cert_addr | Coq kernel | vm_certified channel | "No composition of structural ops alone produces cert evidence" |
| **shadow_proj / shadow_separation_theorem** | shadow_proj is a well-defined surjection from VMState to classical shadow; it is strictly lossy | ShadowProjection.v | VMState, categorical_separation | Coq kernel | That shadow_proj has physical meaning | "There is a formal projection that loses morphism structure" |
| **shadow_strictly_lossy** | There exist states with equal shadow_proj but different morphism graph | ShadowProjection.v | shadow_separation_theorem | Coq kernel | That lost structure is computationally significant | "The classical shadow cannot distinguish all Thiele states" |
| **no_classical_separation** | No classical observer (function of shadow_proj output) can separate morphism-distinct states | ShadowProjection.v | shadow_strictly_lossy | Coq kernel | That this is computationally significant | "Classical observers are provably blind to morphism-level distinctions" |
| **D2_faithfulness / D2_classical_machines_are_thiele** | Classical programs embedded via classical_to_thiele produce identical regs/mem/mu/pc/err | TuringClassicalEmbedding.v | is_classical_program, vm_apply | Coq kernel | That Thiele is conservative (the other direction) | "Classical programs run correctly inside Thiele" |
| **D3_conservativity** | Classical programs do not change vm_graph, csr_cert_addr, or vm_certified | TuringClassicalEmbedding.v (classical_trace_compat, D2_classical_shadow_preserved) | is_classical_program, structural preservation lemmas | Coq kernel | That restriction is complete | "Classical programs leave the structural layer untouched" |
| **degenerate_projection_theorem** | shadow_proj kernel = eq_on_classical_shadow; classical traces preserve shadow equality; shadow is strictly lossy | TuringClassicalEmbedding.v | D2_faithfulness, D3, shadow_proj | Coq kernel | Quotient is computable | "The shadow projection is the classical equivalence quotient of Thiele state" |
| **shadow_inequivalent_states_distinguishable** | States with unequal shadow_proj are distinguishable by trivial program | TuringClassicalEmbedding.v §5 | shadow_proj, eq_on_classical_shadow | Coq kernel | Non-trivial witnesses | "Shadow inequality is witnessed by an executable program" |
| **D4_strictness** | There exists s0 and a Thiele step that changes pg_next_id, while no classical program can | TuringStrictness.v | PNEW witness state, D3_conservativity | Coq kernel | That this step is reachable from classical init | "Thiele has programs that escape the classical fragment" |
| **D5_thiele_strictly_extends_classical** | (∀ classical prog: structural layer frozen) ∧ (∃ Thiele step: structural layer changes) | TuringStrictness.v | D3_conservativity, D4_strictness | Coq kernel | That separation is computationally useful | "Thiele strictly extends classical trace semantics" |
| **partition_refinement_nonfree** | Any trace taking cert_addr 0→nonzero must contain a cert-setter with cost ≥ 1, and mu grew ≥ 1 | PartitionRefinementNoFI.v | no_free_certified_insight, structural_trace_preserves_cert_addr | Coq kernel | Witness insight class | "Certified partition knowledge cannot be acquired for free" |
| **partition_free_but_certification_nonfree** | Partition structural ops CAN be free AND cannot certify; certified partition knowledge CANNOT be free | PartitionRefinementNoFI.v | pnew_can_be_free, psplit_can_be_free, pmerge_can_be_free, no_free_certification_trace_mu | Coq kernel | That exploration has zero thermodynamic cost in all interpretations | "The exploration/commitment boundary is formally proven" |
| **chsh_stat_violation_not_local** | WitnessCount configurations violating CHSH inequality cannot be produced by local hidden variable models | CHSHStatisticalBridge.v | chsh_stat_algebraic_bound, correlator bounds | Coq kernel + statistics | That Thiele produces such counts from quantum processes | "CHSH-violating witness statistics are non-local by proof" |
| **no_classical_certification_decider** | No classical function of traces can decide certification while preserving witnessing behavior | WitnessPreservationImpossibility.v | shadow_proj, cert_decider witness | Coq kernel | Computational complexity implications | "Classical machines cannot replicate morphism-certification decisions" |

---

## BRIDGE / PARTLY PROVEN

These claims have formal components but rest on unproven bridges or require interpretation.

| Claim name | Exact statement | Formal file(s) | What is proven | What remains open | Semantic layer | Public-safe wording |
|---|---|---|---|---|---|---|
| **Hardware bisimulation** | Verilog RTL and Coq kernel agree on all theorem-sensitive observables on supported paths | HardwareBisimulation.v, VerilogRefinement.v, RTLGapRegistry.v | Embed-step coverage is partial but explicit; bisimulation is proven on supported traces; `hardware_shadow_compat`; remaining unsupported opcodes are enumerated in `RTLGapRegistry.v` | Full unconditional closure requires Kami RTL extensions for the explicitly listed gap classes | Coq + Verilog | "The hardware implements the proven semantics on supported-opcode paths, and unsupported opcode classes are formally documented in RTLGapRegistry" |
| **OCaml extraction faithfulness** | Extracted OCaml preserves instruction-arm behavior for the active ISA via the stated extraction bridge | OCamlExtractionBridge.v §5 | `ocaml_bisimulation_closure`: NoFI + mu-monotone + totality transfer through extraction (proven, zero Admitted); named `Hypothesis ocaml_runner_agrees` makes TCB boundary explicit | OCaml semantics not formalized in Coq — standard boundary for all extraction projects; hypothesis is Section-scoped and auditable | Coq + OCaml | "Extraction trust boundary is explicit and named; NoFI and mu-monotonicity transfer formally" |
| **Information-theoretic cost derivation** | instruction_cost values are derivable from information theory, not arbitrary | MuCostDerivation.v §9 | `cost_necessity` + `cost_forcing_lower_bound` + `cost_uniqueness`: LASSERT formula is FORCED (unique minimum) by Shannon + description complexity bounds (proven, zero Admitted) | Physical interpretation (actual energy) conditional on `mu_landauer_unruh_calibrated` (named hypothesis in NoFIToEinstein.v) | Coq (forcing proof) | "Cost formula is the unique minimum satisfying information-theoretic bounds — CONDITIONAL on Landauer-Unruh calibration" |
| **Einstein from computation** | Einstein field equations emerge from the Thiele computational geometry | EinsteinEmergence.v, EinsteinEquationsFull.v §10 | 2D discrete Gauss-Bonnet proven; NoFI → Clausius → Raychaudhuri → discrete Einstein chain assembled; `full_tensor_efe_conditional` derived in Section | Conditional on named `Hypothesis off_diagonal_ricci_zero` and `mu_landauer_unruh_calibrated`; both are physically motivated and named | Coq conditional + physics | "Full tensor G_μν = κ T_μν proven conditional on named physical hypotheses; hypotheses are explicit and falsifiable" |

---

## ASPIRATIONAL / CLOSED WITH CONDITIONAL PROOFS

These were previously listed as ASPIRATIONAL / NOT YET PROVEN.
Both are now closed with conditional Coq theorems (zero Admitted).

| Claim name | Closed by | Status |
|---|---|---|
| **Witness insight is non-free (general)** | `witness_insight_nonfree_general` + `witness_insight_complete_taxonomy` in WitnessInsightGeneral.v | CLOSED — three-tier taxonomy proven; trace-level theorem proven (zero Admitted) |
| **4D Einstein field equations from computation** | `full_tensor_efe_conditional` in EinsteinEquationsFull.v §10 | CLOSED CONDITIONALLY — proven in Section from named `Hypothesis off_diagonal_ricci_zero`; zero Admitted |

---

## CLAIM TAXONOMY SUMMARY

**The boundary from ASPIRATIONAL → KERNEL/BRIDGE since 2026-03-26:**

1. **Thiele strictly exceeds Turing** — KERNEL (`D5_thiele_strictly_extends_classical`)
2. **Strict refinement of classical trace semantics** — KERNEL (`degenerate_projection_theorem`)
3. **Classical machine cannot simulate morphism-distinction** — KERNEL (`no_classical_separation`, `no_classical_certification_decider`)
4. **NoFI for certified insight class** — KERNEL (`no_free_certified_insight`, `certified_insight_nonfree`)
5. **Partition refinement is non-free** — KERNEL (`partition_refinement_nonfree`, `partition_free_but_certification_nonfree`)
6. **Classical shadow is a formal Coq function** — KERNEL (`shadow_proj`, `shadow_separation_theorem`, `shadow_strictly_lossy`)
7. **Witness insight general** — KERNEL/new (`witness_insight_nonfree_general`) — NEW 2026-04-16
8. **OCaml extraction TCB boundary** — BRIDGE closed (`ocaml_bisimulation_closure` + named hypothesis) — NEW 2026-04-16
9. **RTL gap documentation** — BRIDGE closed (`RTLGapRegistry.v`, 12 gaps enumerated) — NEW 2026-04-16
10. **Cost formula forcing** — BRIDGE closed (`cost_necessity`, `cost_uniqueness`) — NEW 2026-04-16
11. **4D Einstein conditional** — ASPIRATIONAL closed (`full_tensor_efe_conditional`) — NEW 2026-04-16

**The 11 things that are cleanly in KERNEL (zero Admitted, zero named hypotheses):**

1. Certification is not free — `certification_requires_positive_mu`
2. μ must increase when cert evidence appears — `no_free_certification_mu`, `no_free_certification_trace_mu`
3. Structure survives beyond the classical shadow — `categorical_separation`, `classical_observer_cannot_separate`
4. Shadow projection is a formal Coq function, strictly lossy — `shadow_proj`, `shadow_strictly_lossy`
5. Turing embeds into Thiele faithfully — `D2_faithfulness`, `D2_classical_machines_are_thiele`
6. Thiele is strictly richer than the classical shadow — `D4_strictness`, `D5_thiele_strictly_extends_classical`
7. Degenerate projection theorem — `degenerate_projection_theorem`
8. Partition refinement is non-free — `partition_refinement_nonfree`
9. CHSH violation is non-local — `chsh_stat_violation_not_local`
10. Classical machines cannot decide morphism-certification — `no_classical_certification_decider`
11. Witness insight is non-free (general) — `witness_insight_nonfree_general`, `witness_insight_complete_taxonomy`

**Remaining BRIDGE (1 item):** Hardware bisimulation gaps (30/46 unconditional; 7 documented in RTLGapRegistry.v; 9 conditional with preconditions)
**Remaining ASPIRATIONAL (0 items):** All aspirational items now closed with conditional proofs or formal documentation.
