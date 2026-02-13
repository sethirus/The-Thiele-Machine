# INQUISITOR REPORT
Generated: 2026-02-13 07:37:46Z (UTC)
Scanned: 292 Coq files across the repo
## Summary
- HIGH: 0
- MEDIUM: 317
- LOW: 0

## Rules
- `ADMITTED`: `Admitted.` (incomplete proof - FORBIDDEN)
- `ADMIT_TACTIC`: `admit.` (proof shortcut - FORBIDDEN)
- `GIVE_UP_TACTIC`: `give_up` (proof shortcut - FORBIDDEN)
- `AXIOM_OR_PARAMETER`: `Axiom` / `Parameter` (HIGH - unproven assumptions FORBIDDEN)
- `HYPOTHESIS_ASSUME`: `Hypothesis` (HIGH - functionally equivalent to Axiom, FORBIDDEN)
- `CONTEXT_ASSUMPTION`: `Context` with forall/arrow (HIGH - undocumented section-local axiom)
- `CONTEXT_ASSUMPTION_DOCUMENTED`: `Context` with INQUISITOR NOTE (LOW - documented dependency)
- `SECTION_BINDER`: `Context` / `Variable` / `Variables` (MEDIUM - verify instantiation)
- `MODULE_SIGNATURE_DECL`: `Axiom` / `Parameter` inside `Module Type` (informational)
- `COST_IS_LENGTH`: `Definition *cost* := ... length ... .`
- `EMPTY_LIST`: `Definition ... := [].`
- `ZERO_CONST`: `Definition ... := 0.` / `0%Z` / `0%nat`
- `TRUE_CONST`: `Definition ... := True.` or `:= true.`
- `PROP_TAUTOLOGY`: `Theorem ... : True.`
- `IMPLIES_TRUE_STMT`: statement ends with `-> True.`
- `LET_IN_TRUE_STMT`: statement ends with `let ... in True.`
- `EXISTS_TRUE_STMT`: statement ends with `exists ..., True.`
- `CIRCULAR_INTROS_ASSUMPTION`: tautology + `intros; assumption.`
- `TRIVIAL_EQUALITY`: theorem of form `X = X` with reflexivity-ish proof
- `CONST_Q_FUN`: `Definition ... := fun _ => 0%Q` / `1%Q`
- `EXISTS_CONST_Q`: `exists (fun _ => 0%Q)` / `exists (fun _ => 1%Q)`
- `CLAMP_OR_TRUNCATION`: uses `Z.to_nat`, `Z.abs`, `Nat.min`, `Nat.max`
- `ASSUMPTION_AUDIT`: unexpected axioms from `Print Assumptions`
- `SYMMETRY_CONTRACT`: missing equivariance lemma for declared symmetry
- `PAPER_MAP_MISSING`: paper ↔ Coq symbol map entry missing/broken
- `MANIFEST_PARSE_ERROR`: failed to parse Inquisitor manifest JSON
- `COMMENT_SMELL`: TODO/FIXME/WIP markers in Coq comments
- `UNUSED_HYPOTHESIS`: introduced hypothesis not used (heuristic)
- `DEFINITIONAL_INVARIANCE`: invariance lemma appears definitional/vacuous
- `Z_TO_NAT_BOUNDARY`: Z.to_nat without nearby nonnegativity guard
- `PHYSICS_ANALOGY_CONTRACT`: physics-analogy theorem lacks invariance or definitional label
- `SUSPICIOUS_SHORT_PROOF`: complex theorem has suspiciously short proof (critical files)
- `MU_COST_ZERO`: μ-cost definition is trivially zero
- `CHSH_BOUND_MISSING`: CHSH bound theorem may not reference proper Tsirelson bound
- `PROBLEMATIC_IMPORT`: import may introduce classical axioms
- `RECORD_FIELD_EXTRACTION`: theorem merely extracts a Record field it assumed as input (circular)
- `SELF_REFERENTIAL_RECORD`: Record embeds proposition as field AND a Theorem in the same file extracts it (circular)
- `PHANTOM_KERNEL_IMPORT`: imports Kernel modules but no proof engages with VM semantics
- `TRIVIAL_EXISTENTIAL`: trivially satisfiable existential (e.g. 'every list has a length')
- `ARITHMETIC_ONLY_PHYSICS`: physics-named theorem proved by pure arithmetic (lia/lra) only
- `PHANTOM_VM_STEP`: theorem takes vm_step as hypothesis but proof never uses it
- `CIRCULAR_DEFINITION`: theorem unfolds definition and proves by simple tactics (potentially restating definition)
- `EMERGENCE_CIRCULARITY`: 'emergence' claim where emergent property is in the definition (circular)
- `CONSTRUCTOR_ROUND_TRIP`: construct object, immediately extract property (not proving anything)
- `DEFINITIONAL_WITNESS`: existential witnessed by definition, then unfolds it (trivially proves definition exists)
- `VACUOUS_CONJUNCTION`: theorem has `True` as a conjunct leaf — likely a weakened/placeholder conclusion
- `TAUTOLOGICAL_IMPLICATION`: theorem conclusion is identical to one of its hypotheses (P -> P tautology)
- `HYPOTHESIS_RESTATEMENT`: proof destructures hypothesis and extracts one piece (restating assumption, not deriving)

## Vacuity Ranking (file-level)
Higher score = more likely unfinished/vacuous.

| score | tags | file |
|---:|---|---|
| 65 | const-fun | `coq/thielemachine/coqproofs/SpectralApproximation.v` |

## Findings
### MEDIUM

#### `archive/coq_with_axioms/TsirelsonBoundProof.v`
- L202: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hb\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x b Hb H.`

#### `archive/kernel_exploratory/MinorConstraints.v`
- L49: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hy\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x y Hy.`
- L216: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x H.`
- L253: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`He1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s e1 e2 Hminor He1 He2.`
- L253: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`He2\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s e1 e2 Hminor He1 He2.`

#### `archive/kernel_exploratory/TsirelsonBoundDirect.v`
- L40: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpsd\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros npa x b E00 E01 rho_BB Hpsd Hsym.`
- L40: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hsym\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros npa x b E00 E01 rho_BB Hpsd Hsym.`
- L81: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpsd\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros npa x y b E10 E11 rho_BB Hpsd Hsym.`
- L81: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hsym\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros npa x y b E10 E11 rho_BB Hpsd Hsym.`
- L190: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpsd\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros npa Hpsd Hsym.`
- L190: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hsym\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros npa Hpsd Hsym.`

#### `coq/bridge/BoxWorld_to_Kernel.v`
- L83: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hok\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p Hok.`

#### `coq/bridge/FiniteQuantum_to_Kernel.v`
- L126: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hok\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros t n Hok.`

#### `coq/bridge/PythonMuLedgerBisimulation.v`
- L127: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hbisim\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros ledger coq_mu delta_disc delta_exec Hbisim.`
- L179: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hmask_pos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros mask Hmask_pos.`
- L205: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hbisim\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros ledger coq_mu Hbisim delta_disc delta_exec.`

#### `coq/kernel/AlgebraicCoherence.v`
- L593: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hsum\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros e00 e01 e10 e11 He00 He01 He10 He11 Hsum.`
- L667: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hm1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros e He Hm1 Hm2.`
- L667: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hm2\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros e He Hm1 Hm2.`

#### `coq/kernel/ArrowOfTimeSynthesis.v`
- L160: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hcost\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s s' cost Hcost.`

#### `coq/kernel/BornRule.v`
- L120: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpure\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x y z Hpure.`
- L134: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hmixed\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x y z Hmixed.`
- L310: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hmu\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros P Hvalid Hlin Hmu x y z Hstate.`

#### `coq/kernel/BornRuleFromSymmetry.v`
- L258: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n Hn.`
- L282: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hxpos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x y Hxpos Hxy Hy1.`
- L282: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hxy\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x y Hxpos Hxy Hy1.`
- L311: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hxy\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x y Hx Hxy Hy.`
- L311: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hy\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x y Hx Hxy Hy.`
- L352: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hx0\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x Hx0 Hx1.`
- L352: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hx1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x Hx0 Hx1.`
- L379: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hx0\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x n Hx0 Hx1.`
- L390: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hx0\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x n Hx0 Hx1.`
- L390: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hx1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x n Hx0 Hx1.`

#### `coq/kernel/CausalSetAxioms.v`
- L269: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlen\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g1 g2 Hlen Heq.`

#### `coq/kernel/Certification.v`
- L376: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hrun\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros trace s_init s_final fuel Hrun Hinit Hcert.`
- L376: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hinit\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros trace s_init s_final fuel Hrun Hinit Hcert.`
- L399: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hrun\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros trace s_init s_final fuel Hrun Hinit Hcert.`
- L399: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hinit\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros trace s_init s_final fuel Hrun Hinit Hcert.`
- L424: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hrun\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros trace s_init s_final fuel Hrun Hinit Hadm Hcert.`
- L424: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hinit\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros trace s_init s_final fuel Hrun Hinit Hadm Hcert.`
- L424: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hadm\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros trace s_init s_final fuel Hrun Hinit Hadm Hcert.`
- L446: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hrun\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros q trace s_init s_final fuel Hrun Hinit Hadm Hcert.`
- L446: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hinit\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros q trace s_init s_final fuel Hrun Hinit Hadm Hcert.`
- L446: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hadm\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros q trace s_init s_final fuel Hrun Hinit Hadm Hcert.`
- L469: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hrun\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros q trace s_init s_final fuel Hrun Hinit Hcert.`
- L469: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hinit\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros q trace s_init s_final fuel Hrun Hinit Hcert.`
- L484: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hrun\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros trace s_init s_final fuel Hrun Hinit Hcert.`
- L484: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hinit\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros trace s_init s_final fuel Hrun Hinit Hcert.`
- L484: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hcert\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros trace s_init s_final fuel Hrun Hinit Hcert.`

#### `coq/kernel/ConeAlgebra.v`
- L604: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros mid t1 t2 n Hn.`

#### `coq/kernel/ConeDerivation.v`
- L150: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hin\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros trace1 trace2 x Hin.`

#### `coq/kernel/ConstructivePSD.v`
- L755: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlambda\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros M1 M2 lambda Hlambda Hpsd1 Hpsd2.`

#### `coq/kernel/EntropyImpossibility.v`
- L109: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Heq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s a b Heq.`

#### `coq/kernel/HardMathFactsProven.v`
- L110: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`HS\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros S a b Ha Hb HS.`
- L518: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`He\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros e He Hcoh.`
- L540: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`He\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros e He Hle1 Hcoh.`
- L540: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hle1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros e He Hle1 Hcoh.`

#### `coq/kernel/InformationCausality.v`
- L166: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hic\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros ic mu Heq Hic.`
- L222: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hequiv\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros ic mu Hequiv Hzero.`
- L222: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hzero\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros ic mu Hequiv Hzero.`

#### `coq/kernel/KernelNoether.v`
- L278: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n s Hpos.`
- L548: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 delta Hpos Heq.`
- L609: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpos1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 s3 d1 d2 Hpos1 Hpos2 H1 H2.`
- L609: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpos2\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 s3 d1 d2 Hpos1 Hpos2 H1 H2.`
- L687: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros mu cost delta Hpos.`
- L762: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 i delta Hpos Hstep.`
- L840: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hobs\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 Hobs Hgraph Hregs Hmem Hcsrs Hpc Herr.`
- L840: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hgraph\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 Hobs Hgraph Hregs Hmem Hcsrs Hpc Herr.`
- L840: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hregs\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 Hobs Hgraph Hregs Hmem Hcsrs Hpc Herr.`
- L840: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hmem\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 Hobs Hgraph Hregs Hmem Hcsrs Hpc Herr.`
- L840: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hcsrs\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 Hobs Hgraph Hregs Hmem Hcsrs Hpc Herr.`
- L840: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpc\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 Hobs Hgraph Hregs Hmem Hcsrs Hpc Herr.`
- L840: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Herr\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 Hobs Hgraph Hregs Hmem Hcsrs Hpc Herr.`

#### `coq/kernel/KernelPhysics.v`
- L309: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g mid mid' m Hneq.`
- L318: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g mid mid' ax Hneq.`
- L331: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g mid mid' ev Hneq.`
- L400: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g region axioms mid Hlt.`
- L440: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g mid mid' g' m' Hneq Hremove.`
- L490: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g region mid Hlt.`
- L519: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g mid_split left right g' l_id r_id mid Hneq Hlt Hpsplit.`
- L787: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hwf\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s s' instr mid Hwf Hmid_lt Hstep Hnotin.`

#### `coq/kernel/L2Derivation.v`
- L418: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n Hn.`
- L453: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hp\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p Hp Hp2.`
- L453: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hp2\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p Hp Hp2.`
- L523: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hp\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p Hp Hrot.`
- L623: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnorm\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros a b Hnorm.`

#### `coq/kernel/LocalInfoLoss.v`
- L314: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hwf\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s i s' Hstep Hwf.`
- L444: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Htrace\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s is s' Htrace Hwf.`
- L444: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hwf\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s is s' Htrace Hwf.`

#### `coq/kernel/Locality.v`
- L110: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g region g' new_id mid Hpnew Hlt.`

#### `coq/kernel/MuChaitin.v`
- L139: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s_init s_final k H.`

#### `coq/kernel/MuCostModel.v`
- L209: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hle\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros A l pc n Hpc Hle.`

#### `coq/kernel/MuInitiality.v`
- L766: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hcons\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros M Hcons Hinit s Hreach.`
- L766: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hinit\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros M Hcons Hinit s Hreach.`
- L766: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hreach\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros M Hcons Hinit s Hreach.`

#### `coq/kernel/MuLedgerConservation.v`
- L169: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hstep\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s instr s' Hstep.`

#### `coq/kernel/NPMuCostBound.v`
- L73: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hbits\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros vi Hvalid Hbits.`
- L132: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hp\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p q Hp Hq.`
- L132: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p q Hp Hq.`
- L151: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n Hn.`
- L187: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hv\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g Hv Hf.`
- L187: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hf\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g Hv Hf.`

#### `coq/kernel/NoArbitrage.v`
- L76: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`phi\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s0 apply_trace Hseq w phi Haddo Hmin Hforall.`

#### `coq/kernel/NoCloning.v`
- L311: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnontrivial\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros op Hnontrivial Hcons Hperfect Hzero.`
- L364: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnontrivial\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros op Hnontrivial Hcons Hperfect.`
- L932: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros op Hpos Hcons Hdel.`

#### `coq/kernel/NoCloningFromMuMonotonicity.v`
- L133: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros op Hnt Hmu Hp Hz.`
- L154: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros op Hnt Hmu Hp.`
- L216: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros op Hnt Hmu Hp.`

#### `coq/kernel/Persistence.v`
- L629: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n Hn.`

#### `coq/kernel/Purification.v`
- L259: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpure\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x y z Hpure.`

#### `coq/kernel/PythonBisimulation.v`
- L136: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hinv\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros coq_s coq_s' py_s instr Hinv Hstep.`
- L136: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hstep\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros coq_s coq_s' py_s instr Hinv Hstep.`

#### `coq/kernel/QuantumBound.v`
- L231: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnot\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s instr Hnot.`
- L267: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hqa\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros trace s_init s_final fuel Hinit Hqa Hrun.`

#### `coq/kernel/QuantumEquivalence.v`
- L225: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hns\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros ac Hns Hbound.`
- L225: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hbound\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros ac Hns Hbound.`

#### `coq/kernel/ReceiptIntegrity.v`
- L507: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros r claimed_mu_delta _ Hpost Hneq.`

#### `coq/kernel/SemanticMuCost.v`
- L231: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n Hn.`

#### `coq/kernel/SemidefiniteProgramming.v`
- L465: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n M i j Hn Hi Hj HPSD Hsym.`
- L465: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hi\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n M i j Hn Hi Hj HPSD Hsym.`
- L465: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hj\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n M i j Hn Hi Hj HPSD Hsym.`
- L590: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n M i j Hn Hi Hj HPSD Hsym Hii Hjj.`
- L590: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hi\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n M i j Hn Hi Hj HPSD Hsym Hii Hjj.`
- L590: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hj\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n M i j Hn Hi Hj HPSD Hsym Hii Hjj.`
- L590: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`HPSD\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n M i j Hn Hi Hj HPSD Hsym Hii Hjj.`
- L590: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hsym\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n M i j Hn Hi Hj HPSD Hsym Hii Hjj.`
- L590: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hii\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n M i j Hn Hi Hj HPSD Hsym Hii Hjj.`

#### `coq/kernel/SimulationProof.v`
- L68: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpc\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s_vm s_kernel Hpc Hmu Htape.`
- L68: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hmu\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s_vm s_kernel Hpc Hmu Htape.`
- L68: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Htape\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s_vm s_kernel Hpc Hmu Htape.`

#### `coq/kernel/SpacetimeEmergence.v`
- L48: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hwf\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s instr s' mid Hwf Hmid Hstep Hnot.`
- L48: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hmid\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s instr s' mid Hwf Hmid Hstep Hnot.`
- L48: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hstep\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s instr s' mid Hwf Hmid Hstep Hnot.`
- L48: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnot\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s instr s' mid Hwf Hmid Hstep Hnot.`
- L73: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hwf\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g mid m Hwf Hlt.`
- L73: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g mid m Hwf Hlt.`
- L351: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s instr s' mid Hlt Hstep.`

#### `coq/kernel/StateSpaceCounting.v`
- L99: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hcost\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s s' mid formula cert cost Hstep Hcost.`
- L223: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hstep\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s s' mid formula cert cost Hstep Hcost k.`
- L223: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hcost\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s s' mid formula cert cost Hstep Hcost k.`

#### `coq/kernel/ThreeLayerIsomorphism.v`
- L219: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hmu\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros spec1 spec2 s1 s2 instrs Hmu Hpc.`
- L219: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpc\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros spec1 spec2 s1 s2 instrs Hmu Hpc.`
- L253: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hmu\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros spec1 spec2 s1 s2 i Hmu Hpc.`
- L253: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpc\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros spec1 spec2 s1 s2 i Hmu Hpc.`

#### `coq/kernel/TsirelsonDerivation.v`
- L50: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x y H.`

#### `coq/kernel/TsirelsonFromAlgebra.v`
- L126: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hrow1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros e00 e01 e10 e11 Hrow1 Hrow2.`
- L126: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hrow2\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros e00 e01 e10 e11 Hrow1 Hrow2.`

#### `coq/kernel/TsirelsonUpperBound.v`
- L123: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnth\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros fuel trace Hcost n module formula cert mu Hnth.`
- L174: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnth\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros fuel trace Hcost n cert1 cert2 mu Hnth.`
- L209: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros q Hq.`
- L222: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros q Hq.`
- L483: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hmu\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros fuel trace s_init Hmu Hcoh.`

#### `coq/kernel/Unitarity.v`
- L485: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hgamma_pos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros E gamma Hgamma_pos Hlind Hcons Hmax_diss.`

#### `coq/kernel/VMEncoding.v`
- L149: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hdecode\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros A encode decode xs rest Hdecode.`

#### `coq/kernel/VMState.v`
- L209: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g region axioms mid Hlt.`
- L577: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g mid mid' g' m' Hneq Hremove.`
- L991: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g m1 m2 g' merged_id mid Hneq1 Hneq2 Hlt Hpmerge.`

#### `coq/kernel_toe/Persistence.v`
- L139: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n Hn.`

#### `coq/modular_proofs/EncodingBounds.v`
- L16: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Ha\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros a n Ha.`
- L96: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hle\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x Hle.`
- L105: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x Hlt.`
- L125: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hk\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros k a c Hk Ha Hc.`
- L125: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Ha\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros k a c Hk Ha Hc.`
- L125: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hc\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros k a c Hk Ha Hc.`
- L138: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlen\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros len code Hlen Hcode.`
- L138: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hcode\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros len code Hlen Hcode.`
- L158: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hdig\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros xs Hdig Hlen.`
- L158: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlen\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros xs Hdig Hlen.`
- L170: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hdig\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros xs Hdig Hlen.`
- L170: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlen\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros xs Hdig Hlen.`
- L199: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hdig\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros xs Hdig Hlen.`
- L199: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlen\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros xs Hdig Hlen.`

#### `coq/modular_proofs/Simulation.v`
- L38: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hok\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tm sem conf n Hok.`

#### `coq/modular_proofs/TM_to_Minsky.v`
- L103: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hx\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x xs Hx.`
- L115: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hx\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros x xs Hx.`

#### `coq/nofi/MuChaitinTheory_Theorem.v`
- L46: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hrun\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros fuel trace s_final Hrun Hinit Hsupra.`
- L46: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hinit\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros fuel trace s_final Hrun Hinit Hsupra.`
- L46: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hsupra\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros fuel trace s_final Hrun Hinit Hsupra.`
- L56: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s_init s_final k H.`

#### `coq/nofi/NoFreeInsight_Theorem.v`
- L19: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hclean\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tr s0 s1 strength weak Hclean Hrun Hstrict Hcert.`
- L19: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hrun\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tr s0 s1 strength weak Hclean Hrun Hstrict Hcert.`
- L19: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hstrict\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tr s0 s1 strength weak Hclean Hrun Hstrict Hcert.`
- L19: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hcert\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tr s0 s1 strength weak Hclean Hrun Hstrict Hcert.`

#### `coq/physics/DissipativeModel.v`
- L36: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l Hpos.`

#### `coq/physics/LandauerBridge.v`
- L160: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n Hn.`
- L191: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros i n Hi Hn.`
- L215: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hentropy\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros cfg i cfg' Hentropy.`
- L235: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hle\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros cfg n Hle.`

#### `coq/quantum_derivation/BornRuleUnique.v`
- L92: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn0\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n Hcons Hn0.`

#### `coq/quantum_derivation/ComplexNecessity.v`
- L164: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnorm\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros theta a b Hnorm.`

#### `coq/quantum_derivation/ObservationIrreversibility.v`
- L90: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hbits\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros vm bits cert_ref Hbits.`
- L102: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hbits\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros vm bits cert_ref Hbits.`
- L126: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hbits\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros vm_before vm_after bits cert_ref Heq Hbits.`

#### `coq/quantum_derivation/ProjectionFromPartitions.v`
- L77: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnodup\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p mid r Hnodup Hin Huniq.`
- L77: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hin\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p mid r Hnodup Hin Huniq.`
- L77: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Huniq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p mid r Hnodup Hin Huniq.`
- L91: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnodup\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p_before mid r Hnodup Hin Huniq Hlen.`
- L91: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hin\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p_before mid r Hnodup Hin Huniq Hlen.`
- L91: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Huniq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p_before mid r Hnodup Hin Huniq Hlen.`

#### `coq/quantum_derivation/SchrodingerFromPartitions.v`
- L154: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hder\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros v theta Hder.`

#### `coq/shor_primitives/PolylogConjecture.v`
- L75: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n p q Hn Hp Hq.`
- L75: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hp\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n p q Hn Hp Hq.`
- L75: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n p q Hn Hp Hq.`

#### `coq/theory/EvolutionaryForge.v`
- L24: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros A l1 l2 n Hn1 Hn2.`
- L24: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn2\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros A l1 l2 n Hn1 Hn2.`
- L113: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s g n1 n2 H1 H2.`
- L113: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H2\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s g n1 n2 H1 H2.`
- L201: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hparent\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros parent child g Hparent Hchild.`
- L201: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hchild\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros parent child g Hparent Hchild.`
- L215: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros parent1 parent2 H1 H2.`
- L215: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H2\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros parent1 parent2 H1 H2.`
- L262: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hv1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 cut Hv1 Hv2 Hcut1 Hcut2.`
- L262: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hv2\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 cut Hv1 Hv2 Hcut1 Hcut2.`
- L262: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hcut1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 cut Hv1 Hv2 Hcut1 Hcut2.`
- L262: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hcut2\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 cut Hv1 Hv2 Hcut1 Hcut2.`

#### `coq/theory/NoFreeLunch.v`
- L34: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p q Hneq.`

#### `coq/thermodynamic/LandauerDerived.v`
- L187: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`He\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros e He.`

#### `coq/thermodynamic/ThermodynamicBridge.v`
- L257: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n Hn.`

#### `coq/thiele_manifold/PhysicsIsomorphism.v`
- L120: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hfuel\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros Hpos fuel s_vm instr Hfuel Hlookup.`
- L169: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros Hpos Impl fuel s_hw instr Hfuel Htrace Hlookup.`
- L169: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hfuel\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros Hpos Impl fuel s_hw instr Hfuel Htrace Hlookup.`

#### `coq/thielemachine/coqproofs/AbstractLTS.v`
- L349: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hsame\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s s' Hstep Hsame.`
- L534: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hne\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros init_p final_p tot_mu ls id Hne.`

#### `coq/thielemachine/coqproofs/AmortizedAnalysis.v`
- L40: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H_structure\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros i instances' P H_structure.`
- L124: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H_size\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros small_inst large_inst P H_size H_large_struct H_small_struct.`
- L124: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`H_large_struct\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros small_inst large_inst P H_size H_large_struct H_small_struct.`

#### `coq/thielemachine/coqproofs/BellCheck.v`
- L87: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hb\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros a b Hb.`
- L98: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hb\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros a b Hb.`

#### `coq/thielemachine/coqproofs/BellInequality.v`
- L250: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Ha\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros a b c Ha Hbc.`
- L250: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hbc\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros a b c Ha Hbc.`
- L513: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Ha\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros a b Ha Hb.`
- L513: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hb\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros a b Ha Hb.`
- L660: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hwpos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros B w Hwpos Hsum Hwitness.`
- L660: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hsum\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros B w Hwpos Hsum Hwitness.`
- L660: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hwitness\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros B w Hwpos Hsum Hwitness.`
- L1375: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpre\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s frame Hpre Hvalid.`
- L1375: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hvalid\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s frame Hpre Hvalid.`

#### `coq/thielemachine/coqproofs/BellReceiptLocalGeneral.v`
- L180: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hcov\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros ts rA rB x y Hlocal Hcov.`
- L198: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlocal\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros ts rA rB x y a b Hlocal Hcov Hneq.`
- L198: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hcov\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros ts rA rB x y a b Hlocal Hcov Hneq.`
- L198: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros ts rA rB x y a b Hlocal Hcov Hneq.`

#### `coq/thielemachine/coqproofs/Confluence.v`
- L26: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hindep\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s c1 s1 c2 s2 Hstep1 Hstep2 Hindep Hok1 Hok2.`
- L26: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hok1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s c1 s1 c2 s2 Hstep1 Hstep2 Hindep Hok1 Hok2.`
- L26: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hok2\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s c1 s1 c2 s2 Hstep1 Hstep2 Hindep Hok1 Hok2.`

#### `coq/thielemachine/coqproofs/CoreSemantics.v`
- L475: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hdelta\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l delta Hdelta.`
- L486: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hdelta\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l delta Hdelta.`
- L1160: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpc\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s Hhalted Hpc.`

#### `coq/thielemachine/coqproofs/DiscoveryProof.v`
- L220: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlen\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l start len x Hlen Hrc Hin.`
- L438: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n Hn.`
- L635: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hkn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n k Hk Hn Hkn module_size sighted_cost blind_cost.`

#### `coq/thielemachine/coqproofs/InfoTheory.v`
- L269: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn_pos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n query_bytes Hn_pos Hbytes_pos.`
- L269: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hbytes_pos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n query_bytes Hn_pos Hbytes_pos.`

#### `coq/thielemachine/coqproofs/PhaseThree.v`
- L26: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hb\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros a b Hb.`

#### `coq/thielemachine/coqproofs/QuantumTheorems.v`
- L206: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hother\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p m_target m_other r_target r_other Htarget Hother Hneq.`

#### `coq/thielemachine/coqproofs/RepresentationTheorem.v`
- L155: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hl1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros i1 i2 l Hl1 Hl2.`
- L155: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hl2\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros i1 i2 l Hl1 Hl2.`

#### `coq/thielemachine/coqproofs/Simulation.v`
- L43: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hconf\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tm conf Hconf.`
- L132: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hall\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tm conf n Hall _.`

#### `coq/thielemachine/coqproofs/SpacelandCore.v`
- L247: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpart\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s s' Hstep Hpart.`

#### `coq/thielemachine/coqproofs/SpacelandProved.v`
- L76: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros p1 p2 m1 m2 Hneq Heq.`

#### `coq/thielemachine/coqproofs/SpectralApproximation.v`
- L409: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnonempty\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n cut Hnonempty.`
- L426: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hnonempty\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n cut Hnonempty.`
- L444: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hne\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n cut Hne Hproper.`
- L444: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hproper\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n cut Hne Hproper.`
- L483: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n cut Hn Hne Hproper.`
- L483: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hne\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n cut Hn Hne Hproper.`
- L483: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hproper\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros n cut Hn Hne Hproper.`

#### `coq/thielemachine/coqproofs/ThieleKernelCausality.v`
- L116: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g region axioms g' new_id other Hadd Hneq.`
- L157: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g mid g' removed other Hrm Hneq.`
- L173: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g region g' mid other Hpnew Hneq.`
- L189: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hmid\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros g mid left_region right_region g' left_id right_id other Hps Hmid Hleft Hright.`

#### `coq/thielemachine/coqproofs/ThieleSpaceland.v`
- L651: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hstep\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s m1 m2 s' Hstep.`
- L940: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hne\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros init_p final_p tot_mu ls Hne.`

#### `coq/thielemachine/verification/BridgeDefinitions.v`
- L150: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros A l n v d Hn.`
- L204: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hle\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l n Hle.`
- L262: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros A n l1 l2 Hn.`
- L273: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros A n l1 l2 Hn.`
- L283: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hk\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l n k Hk.`
- L292: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hk\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l n rest k Hk.`
- L302: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hle\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l n rest Hle.`
- L349: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hle\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l n rest Hle.`
- L358: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hk\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l n k Hk.`
- L373: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hfit\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros Hprog rules Hfit.`
- L418: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l n d k Hlt.`
- L511: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hbound\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tm conf pc Hbound.`
- L525: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hn\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros A l n v Hn.`
- L971: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hr\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros r v st Hr.`
- L1185: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l r r1 r2 v1 v2 Hneq1 Hneq2 Hr Hr1 Hr2.`
- L1185: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hr1\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l r r1 r2 v1 v2 Hneq1 Hneq2 Hr Hr1 Hr2.`

#### `coq/thielemachine/verification/Deliverable_SignalingLowerBound.v`
- L26: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hexec\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s trace s' mid Hexec Hwf Hmid Hneq.`
- L26: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hwf\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s trace s' mid Hexec Hwf Hmid Hneq.`
- L26: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hmid\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s trace s' mid Hexec Hwf Hmid Hneq.`

#### `coq/thielemachine/verification/PhysicsPillars.v`
- L204: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpart\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 Hpart Hans.`
- L204: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hans\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s1 s2 Hpart Hans.`

#### `coq/thielemachine/verification/Prediction.v`
- L193: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpos\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s m cost s' _ Hpos.`

#### `coq/thielemachine/verification/PredictionNoFI.v`
- L52: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hclean\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tr s0 s1 Hclean Hrun Hcert.`
- L52: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hrun\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tr s0 s1 Hclean Hrun Hcert.`
- L52: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hcert\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tr s0 s1 Hclean Hrun Hcert.`

#### `coq/thielemachine/verification/Symmetry.v`
- L55: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hadm\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros s prog k Hadm.`

#### `coq/thielemachine/verification/ThieleUniversalBridge_Axiom_Tests.v`
- L172: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlen\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros cpu addr_val Hlen.`
- L192: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlen\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros cpu new_pc Hlen.`
- L204: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlen\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros cpu new_pc Hlen.`

#### `coq/thielemachine/verification/modular/Bridge_BridgeCore.v`
- L129: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hle\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l n Hle.`
- L156: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hle\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l n Hle.`

#### `coq/thieleuniversal/coqproofs/ThieleUniversal.v`
- L78: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hall\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tm conf n Hall Hfit.`
- L78: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hfit\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tm conf n Hall Hfit.`
- L114: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hall\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tm conf n Hall Hfit.`
- L114: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hfit\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros tm conf n Hall Hfit.`

#### `coq/thieleuniversal/coqproofs/UTM_CoreLemmas.v`
- L199: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hr2\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l r1 r2 x d Hr1 Hr2 Hneq.`
- L199: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hneq\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros l r1 r2 x d Hr1 Hr2 Hneq.`
- L363: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hi\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros rules st i offset Htable Hi Hoffset.`
- L363: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hoffset\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros rules st i offset Htable Hi Hoffset.`
- L386: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hlt\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros a b Hlt.`
- L567: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hi\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros rules i j Hi Hj.`

#### `coq/thieleuniversal/coqproofs/UTM_Encode.v`
- L132: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hs\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros i Hs.`

#### `coq/thieleuniversal/coqproofs/UTM_Program.v`
- L392: **UNUSED_HYPOTHESIS** — Introduced hypothesis \`Hpc\` not referenced in proof body. (implicit consumer present — may be false positive)
  - `intros pc Hpc.`

