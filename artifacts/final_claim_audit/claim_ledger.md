# Claim Ledger — The Thiele Machine

**Format**: KERNEL/PROVEN | BRIDGE/PARTLY PROVEN | ASPIRATIONAL/NOT YET PROVEN

Each claim is classified by formal status, not rhetorical strength.
Last updated: 2026-03-26.

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

---

## BRIDGE / PARTLY PROVEN

These claims have formal components but rest on unproven bridges or require interpretation.

| Claim name | Exact statement | Formal file(s) | What is proven | What remains open | Semantic layer | Public-safe wording |
|---|---|---|---|---|---|---|
| **Classical shadow projection** | There exists a well-defined projection from Thiele state to classical observable state that is lossy | demo_knowledge_receipt.py (demo), PartitionSeparation.v (separation) | Separation demonstrated; classical fingerprint tested in CI | Formal projection function not defined as a Coq function; no `shadow_proj` morphism proven | Python demo + Coq informal | "The full Thiele state has structure invisible to any classical projection" |
| **Turing embedding** | Classical computation embeds faithfully into Thiele | KernelTM.v | Basic embedding structure present | Conservativity proof (Thiele restricted to classical ops = classical semantics) not formalized | Coq partial | "Classical programs run correctly on Thiele" |
| **Hardware bisimulation** | Verilog RTL and Coq kernel agree on all theorem-sensitive observables | HardwareBisimulation.v, VerilogRefinement.v | Key opcode paths tested via Verilator; bisimulation stated | Full bisimulation not proven for all programs; depends on kami_extract pipeline | Coq + Verilog | "The hardware implements the proven semantics on tested paths" |
| **Information-theoretic cost derivation** | instruction_cost values are derivable from information theory, not arbitrary | MuCostDerivation.v | cost_function_unique is stated but TAUTOLOGICAL (proved IF delta = formula THEN derived_cost = delta, but derived_cost returns delta by definition) | Need independent derivation that the formula forces S cost for cert-setters | Coq (weak) | "Cost bounds relate to information content — CONDITIONAL on interpretation bridge" |
| **Einstein from computation** | Einstein field equations emerge from the Thiele computational geometry | EinsteinEmergence.v, CurvedTensorPipeline.v, physics/ | Components proven: discrete Gauss-Bonnet, Raychaudhuri, metric from mu-costs | Full derivation chain not closed; physics interpretation is an interpretation, not a theorem | Coq partial + physics research | "This is a research direction, not yet a theorem" |

---

## ASPIRATIONAL / NOT YET PROVEN

These are real research goals but not yet formally proven. They should not appear in theorem-grade claims without explicit qualification.

| Claim name | Target statement | Why aspirational | Path to proof | Semantic layer |
|---|---|---|---|---|
| **Thiele strictly exceeds Turing** | There is a computable property in Thiele not recoverable from any classical Turing trace | Informal until: (a) shadow projection is formalized as a Coq function, (b) strictness theorem proven | Formalize shadow_proj, prove image is strictly smaller than full Thiele state space | Coq future |
| **NoFI for all insight classes** | Any transition that strictly strengthens admissible structural knowledge costs ≥ 1 | Currently proven only for certification insight; "structural knowledge" not formally defined | Define insight event taxonomy formally; prove one theorem per class | Coq future |
| **Partition refinement is non-free** | Any operation that strictly refines a partition module costs ≥ 1 | Not yet stated or proven | Identify which opcodes can refine partition; prove structural lower bound | Coq future |
| **Witness insight is non-free** | Any operation that strictly narrows the witness possibility space costs ≥ 1 | vm_witness counters are observational; no formal connection between counter update and cost | Define "witness insight event" formally; prove CHSH_TRIAL cost requirements if any | Coq future |
| **Classical machine cannot simulate morphism-distinction** | No classical machine with classical state can replicate the MORPH_DELETE probe separation | Intuitive from categorical_separation, but not stated as a simulation impossibility theorem | Formalize simulation relation, prove impossibility | Coq future |
| **Strict refinement of classical trace semantics** | Classical trace semantics is a strict quotient of Thiele trace semantics | Requires formal definition of both semantics and a quotient map | Define quotient; prove surjection but not bijection | Coq future |

---

## CLAIM TAXONOMY SUMMARY

**The 8 things that are cleanly separate (see §1.2):**

1. **certification is not free** — KERNEL/PROVEN (no_free_certification, certification_requires_positive_mu)
2. **μ must increase when certification evidence appears** — KERNEL/PROVEN (no_free_certification_mu, no_free_certification_trace_mu)
3. **structure survives beyond the classical shadow** — KERNEL/PROVEN (categorical_separation, classical_observer_cannot_separate)
4. **Thiele retains information lost by projection** — BRIDGE (formalized in demo, shadow_proj not yet a Coq function)
5. **Turing embeds into Thiele** — BRIDGE/PARTLY PROVEN (KernelTM.v, conservativity incomplete)
6. **Thiele is strictly richer than the Turing shadow** — ASPIRATIONAL
7. **implementation preserves semantics** — BRIDGE (tested on theorem-sensitive paths, full bisimulation open)
8. **hardware instantiates the proof-carrying model** — BRIDGE (Kami/Verilog path exists, full proof open)
