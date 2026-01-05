# Prior Art Search Log

Structured search for related work to position the Thiele Machine in the research landscape.

**Search Date**: 2025-12-19  
**Last Reviewed**: January 4, 2026  
**Scope**: $0 budget (free online resources only)  
**Note**: Solo project, informal literature review

---

## Search 1: Partition-Based Computing

### Query
"partition-based computing" OR "region-based computation" OR "spatial decomposition computing"

### Sources
- Google Scholar
- arXiv.org
- ACM Digital Library (open access only)
- IEEE Xplore (open access only)

### Results
- **Partition logic programming** (1990s): Logic programming with spatial partitions
  - Related but different: focuses on constraint solving, not quantum-like correlations
  - Citation: Schreye et al., "Partition-based logical reasoning"
  
- **Region-based memory management** (Tofte & Talpin, 1997)
  - Related but different: memory management, not computation model
  - Citation: "Region-based memory management", Information and Computation
  
- **Spatial computing** (Beal et al., 2006)
  - Related but different: distributed computing over spatial fields
  - Citation: "Infrastructure for Engineered Emergence on Sensor/Actuator Networks"

### Conclusion
No direct prior art for "partition-native computing" as defined in Thiele Machine.

---

## Search 2: Supra-Quantum Correlations

### Query
"supra-quantum" OR "post-quantum correlations" OR "beyond quantum" OR "Tsirelson bound violation"

### Sources
- arXiv.org (quant-ph)
- Google Scholar
- PhilSci Archive

### Results
- **Popescu-Rohrlich box** (1994): Original supra-quantum example (CHSH = 4)
  - Citation: Popescu & Rohrlich, "Quantum nonlocality as an axiom", Found. Phys. 24, 379
  - **Directly relevant**: PR box is the canonical non-signaling supra-quantum correlation
  
- **Almost-quantum correlations** (Navascués et al., 2015)
  - Citation: "Almost quantum correlations", Nat. Commun. 6, 6288
  - **Directly relevant**: Hierarchy between quantum and no-signaling sets
  
- **Macroscopic locality** (Navascués & Wunderlich, 2010)
  - Citation: "A glance beyond the quantum model", Proc. R. Soc. A 466, 881
  - **Directly relevant**: Principles that might forbid supra-quantum correlations
  
- **NPA hierarchy** (Navascués, Pironio, Acín, 2007)
  - Citation: "Bounding the set of quantum correlations", Phys. Rev. Lett. 98, 010401
  - **Directly relevant**: Mathematical tools for characterizing correlation sets

### Conclusion
Our 16/5 distribution fits in the known landscape:
- Classical: CHSH ≤ 2
- Quantum: CHSH ≤ 2√2 ≈ 2.828 (Tsirelson bound)
- **Thiele (claimed)**: CHSH = 16/5 = 3.2
- PR-box: CHSH = 4 (maximum no-signaling)

No prior claim of *silicon-enforced* supra-quantum correlations found.

---

## Search 3: Formal Verification of VMs

### Query
"formal verification virtual machine" OR "verified VM" OR "Coq virtual machine"

### Sources
- Coq GitHub
- POPL/PLDI/ICFP conference proceedings (open access)
- arXiv.org (cs.PL)

### Results
- **CompCert** (Leroy et al., 2006-present)
  - Citation: "Formal verification of a realistic compiler", CACM 2009
  - **Highly relevant**: Verified compiler from C to assembly
  - Difference: Thiele verifies VM *semantics*, not compiler correctness
  
- **CertiKOS** (Gu et al., 2016)
  - Citation: "Deep Specifications and Certified Abstraction Layers", POPL 2016
  - **Highly relevant**: Verified OS kernel
  - Difference: Thiele focuses on partition semantics, not OS
  
- **Jasmin** (Almeida et al., 2017)
  - Citation: "Jasmin: High-Assurance and High-Speed Cryptography", CCS 2017
  - **Relevant**: Verified crypto implementations
  - Difference: Jasmin is domain-specific (crypto), Thiele is general-purpose
  
- **seL4** (Klein et al., 2009)
  - Citation: "seL4: Formal Verification of an OS Kernel", SOSP 2009
  - **Relevant**: Verified microkernel
  - Difference: Different domain (OS vs. partition VM)

### Conclusion
Formal verification of low-level systems is well-established.  
Novelty: Partition-native semantics + 3-layer isomorphism (Coq ↔ OCaml ↔ Python ↔ Verilog).

---

## Search 4: Hardware/Software Co-Verification

### Query
"hardware software co-verification" OR "HW/SW isomorphism" OR "RTL verification Coq"

### Sources
- ACM/IEEE Hardware Verification Workshop
- arXiv.org (cs.AR)
- Formal Methods in CAD (FMCAD) proceedings

### Results
- **Kami** (Choi et al., 2017)
  - Citation: "Kami: A Platform for High-Level Parametric Hardware Specification", ICFP 2017
  - **Highly relevant**: Coq framework for hardware verification
  - Difference: Kami is a framework, Thiele is a specific verified system
  
- **RISCV-Formal** (Clifford Wolf, 2017)
  - Citation: https://github.com/SymbioticEDA/riscv-formal
  - **Relevant**: Formal verification of RISC-V CPUs
  - Difference: Thiele verifies custom partition ISA, not RISC-V
  
- **Chlipala's Fiat** (Delaware et al., 2015)
  - Citation: "Fiat: Deductive Synthesis of Abstract Data Types", POPL 2015
  - **Relevant**: Verified ADT synthesis from specs
  - Difference: Different abstraction level

### Conclusion
Co-verification exists in formal methods literature.  
Novelty: 3-layer isomorphism for partition-native VM (not standard ISA).

---

## Search 5: Thermodynamic Computing Models

### Query
"thermodynamic computing" OR "Landauer limit" OR "reversible computing" OR "energy-aware computation"

### Sources
- arXiv.org (cond-mat, cs.ET)
- Google Scholar
- IBM Research publications

### Results
- **Landauer's principle** (Landauer, 1961)
  - Citation: "Irreversibility and Heat Generation in the Computing Process", IBM J. Res. Dev.
  - **Relevant**: Energy cost of erasure (kT ln 2 per bit)
  - Connection: μ-ledger might model thermodynamic costs
  
- **Reversible computing** (Bennett, 1973)
  - Citation: "Logical Reversibility of Computation", IBM J. Res. Dev.
  - **Relevant**: Zero-energy computation in principle
  - Difference: Thiele is not reversible by design
  
- **Maxwell's demon** (Szilard, 1929; Bennett, 1982)
  - **Relevant**: Information-thermodynamic connection
  - Speculation: Partition operations might be "demon-like"

### Conclusion
μ-ledger has conceptual similarities to thermodynamic costs.  
No direct prior claim of "μ-conservation law" found.

---

## Search 6: No-Signaling Boxes and Information Causality

### Query
"no-signaling box" OR "information causality" OR "generalized probabilistic theories"

### Sources
- arXiv.org (quant-ph)
- Quantum Foundations conferences (open proceedings)
- Perimeter Institute recordings

### Results
- **Information causality** (Pawłowski et al., 2009)
  - Citation: "Information causality as a physical principle", Nature 461, 1101
  - **Highly relevant**: Principle that rules out some supra-quantum correlations
  - Question: Does 16/5 violate information causality? (Needs analysis)
  
- **Generalized probabilistic theories** (Barrett, 2007)
  - Citation: "Information processing in generalized probabilistic theories", Phys. Rev. A 75, 032304
  - **Relevant**: Framework for studying post-quantum theories
  - Connection: Thiele could be interpreted as a GPT
  
- **Device-independent quantum cryptography** (Acín et al., 2007)
  - Citation: "Device-Independent Security of Quantum Cryptography", Phys. Rev. Lett. 98, 230501
  - **Tangentially relevant**: Uses Bell violations for security
  - No direct connection to Thiele

### Conclusion
Our 16/5 distribution lies in the no-signaling polytope.  
Open question: Does it violate information causality?

---

## Search 7: Verified Extraction (Coq → OCaml)

### Query
"Coq extraction verified" OR "extraction correctness" OR "Coq OCaml extraction soundness"

### Sources
- Coq documentation
- TYPES mailing list archives
- PhD theses on Coq

### Results
- **Coq extraction mechanism** (Letouzey, 2002)
  - Citation: "A New Extraction for Coq", TYPES 2002
  - **Highly relevant**: Defines extraction correctness
  - Trust assumption: Extraction preserves semantics (widely trusted)
  
- **CertiCoq** (Anand et al., 2017)
  - Citation: "CertiCoq: A verified compiler for Coq", CoqPL 2017
  - **Highly relevant**: Verified extraction to CompCert C
  - Difference: Thiele uses standard extraction (not CertiCoq)
  
- **Extraction bugs** (historical)
  - Some extraction bugs fixed in Coq 8.x series
  - Current status: Extraction is mature and widely trusted

### Conclusion
Extraction correctness is a trust assumption (not proved within Coq).  
This is standard practice; we are not unusual in relying on extraction.

---

## Search 8: Partition Semantics in PL Theory

### Query
"partition semantics" OR "region calculus" OR "spatial types"

### Sources
- POPL/ICFP/PLDI proceedings
- PhD theses

### Results
- **Region calculus** (Tofte & Talpin, 1997)
  - Already noted in Search 1
  - Conclusion: Memory management, not our semantics
  
- **Separation logic** (Reynolds, 2002)
  - Citation: "Separation Logic: A Logic for Shared Mutable Data Structures", LICS 2002
  - **Tangentially relevant**: Spatial reasoning about memory
  - Difference: Separation logic is for *verification*, not a computation model
  
- **Spatial types** (Walker et al., 2000)
  - Citation: "Alias Types for Recursive Data Structures", TYPES 2000
  - **Tangentially relevant**: Type systems for aliasing
  - No direct connection

### Conclusion
No prior art for partition-as-computation (PNEW/PSPLIT/PMERGE) found.

---

## Summary: Positioning in the Landscape

### Direct Prior Art (Highly Related)
1. **Popescu-Rohrlich box** (1994): Supra-quantum correlations (CHSH = 4)
2. **NPA hierarchy** (2007): Tools for characterizing correlation sets
3. **CompCert** (2006): Verified compiler (extraction trust)
4. **Kami** (2017): Coq hardware verification framework

### Conceptual Connections (Related but Different)
1. **Region calculus** (1997): Memory management (not computation model)
2. **Landauer's principle** (1961): Thermodynamic costs (μ-ledger analogy)
3. **Information causality** (2009): Post-quantum bound (needs analysis)
4. **Reversible computing** (1973): Energy-efficient computation

### Novel Contributions (No Direct Prior Art Found)
1. **Partition-native computing model**: PNEW/PSPLIT/PMERGE as primitives
2. **3-layer isomorphism**: Coq ↔ extracted ↔ Python ↔ Verilog
3. **μ-ledger**: Thermodynamic-like accounting for computation
4. **Silicon-enforced isomorphism**: Hardware realization of supra-quantum correlations (conjectured)
5. **16/5 distribution**: Specific supra-quantum correlation between PR-box and Tsirelson bound
6. **Initiality Theorem** (January 2026): μ is the unique canonical monotone cost functional
7. **Necessity Theorem** (January 2026): μ is minimal among Landauer-valid cost models

### Open Questions from Literature
1. Does the 16/5 distribution violate information causality?
2. Can silicon hardware preserve no-signaling under realistic noise?
3. Is partition-native computing a new complexity class?

---

## Queries for Future Searches

- "partition complexity class"
- "silicon quantum advantage without quantum"
- "μ-ledger thermodynamics"
- "information causality CHSH 3.2"
- "verified hardware semantics isomorphism"

---

## References

### Core Citations
1. Popescu & Rohrlich (1994), "Quantum nonlocality as an axiom", Found. Phys. 24, 379
2. Navascués et al. (2015), "Almost quantum correlations", Nat. Commun. 6, 6288
3. Leroy et al. (2009), "Formal verification of a realistic compiler", CACM
4. Choi et al. (2017), "Kami: A Platform for High-Level Parametric Hardware Specification", ICFP
5. Pawłowski et al. (2009), "Information causality as a physical principle", Nature 461, 1101

### Peripheral Citations
6. Tofte & Talpin (1997), "Region-based memory management", Information and Computation
7. Landauer (1961), "Irreversibility and Heat Generation in the Computing Process", IBM J. Res. Dev.
8. Reynolds (2002), "Separation Logic", LICS
9. Letouzey (2002), "A New Extraction for Coq", TYPES
10. Klein et al. (2009), "seL4: Formal Verification of an OS Kernel", SOSP

---

**Last updated**: 2025-12-19  
**Last reviewed**: January 4, 2026
