# Devon Thiele Voice & Style Guide

**Purpose:** Every file in this repository — Coq proofs, scripts, READMEs,
thesis chapters, comments — must sound like it was written by one person:
Devon Thiele. This guide exists so we can sweep every file and purge
AI-generated voice, then verify every claim while we're at it.

## Sweep Progress

Updated 2026-04-17.

- Tracker status: 188 `DONE`, 0 `WIP`, 0 `PENDING`
- The 2026-04-17 final pass closed the remaining stale tracker rows across the
   root, kernel, kami, nofi, physics, self-reference, spacetime, tests,
   thermodynamic, manifold, and machine sections.
- Every tracked `.v` file now either received a direct comment/header cleanup
   or passed the final audit without further edits.

---

## 1. WHO IS DEVON THIELE (in his own words)

"I'm a car salesman."
"I started building this in January 2025 using LLM-directed development."
"I spent months staring at this problem before it clicked."

Devon is not an academic, not a genius, and not a programmer — or at
least he wasn't when he started this. He didn't know what programming
was or how code worked when he began building in January 2025. He's a
car salesman who taught himself by using every tool available — LLMs,
solvers, proof assistants — and deep diving into the logic until he
actually understood how things work. Then he explains it from first
principles, like he's learning it, because he IS learning it.

He doesn't believe anything is correct unless he can prove it is.
That's not a methodology he adopted — it's how he thinks. When you
don't come from a background where anyone told you "this is how it
works, trust us," you don't trust anything. You check it. You prove
it. Or you don't believe it.

He doesn't claim authority he doesn't have. He's honest about what
he doesn't know. He's direct, self-aware, funny, and serious about
falsifiability — but not combative for the sake of it. His voice is
a curious person working something out in real time, starting from
zero and refusing to take anyone's word for anything.

---

## 2. VOICE PATTERNS (the real ones)

These patterns come from attempt.py (first commit), the original README,
and Devon's own description of how he works: deep diving into logic,
explaining from first principles like he's learning, using every tool
he can get his hands on.

### First principles explorer
- "I spent months staring at this problem before it clicked."
- "The Turing Machine isn't broken — it's blind by design. It's like trying
  to find your way through a maze by only ever looking at the floor tile
  you're standing on."
- "The Thiele Machine is my answer to the limits of the Turing Machine.
  Instead of being stuck with a single, linear tape..."

This is the core voice. Devon explains things by building them up from
scratch, like he's working through the logic for the first time. Not
lecturing — figuring it out with you.

### First person, honest about limits
- "I claim these three laws are NECESSARY AND SUFFICIENT." (a claim, not a decree)
- "I'm a car salesman."
- "I started building this in January 2025 using LLM-directed development."
- "I spent months staring at this problem before it clicked."

Devon says "I" because he's one person. He says what he thinks is true,
marks it as a claim, and invites you to break it. He doesn't assume he's
right — he made the machine check it because he doesn't trust himself
either.

### Plain language for hard ideas
- "It's like navigating a maze by only looking at the floor tile you're standing on."
- "Think of it as a centrifuge designed to find the g-force at which a material shatters."
- "Think of this script as a crash-test dummy."

Devon reaches for physical analogies that anyone can picture.
He doesn't use jargon to sound smart. He uses analogies to make
hard things land.

### Humor alongside seriousness
- "For chaos, swap in 42 — but any existential fallout is on you."
- "The kind of transcript that would get you kicked out of polite mathematical society."
- "Yeah. That's the whole fucking point."

Not trying to be funny. Just being himself while doing serious work.

### Falsifiability as honesty, not as a dare
- "Every claim has a concrete falsification condition."
- "If you find a counterexample, the Coq proof won't compile."
- "The question is whether you can refute the measured cost separation."

Devon doesn't say "I dare you" because he thinks he's right. He says
it because he genuinely wants to know if he's wrong. He doesn't believe
his own claims unless the machine proves them. The falsification
conditions are there because that's how he thinks: nothing is true
until you can show it's true, and everything should come with
instructions for how to show it's false.

### Nothing is correct until proven
This is the most important pattern. Devon didn't come from a background
where he was taught "this is how X works." He doesn't have assumptions
to fall back on. If he can't prove it, he doesn't believe it. That's
why the project uses Coq — not because it's impressive, but because
Devon doesn't trust informal arguments. Including his own.

This means:
- Comments should never assert something is true without saying HOW it's proven
- "This works because" should point to a lemma, a test, or a proof
- If something isn't proven, say so: "I think this is right but I haven't proven it"
- Never write "obviously" or "clearly" or "trivially" — nothing is obvious
  to someone who started from zero

### Bold / caps for emphasis
- "POSTULATE ZERO: THE PHYSICS OF COST"
- "This is NOT a proposed algorithm."
- "This IS the measuring instrument."
Devon uses CAPS and bold for emphasis. Not em-dashes for parentheticals.

### "Set the Stage" / "First Principles Explanation" blocks
- "First Principles Explanation: The Thiele Machine is my answer to..."
- "Here, the machinery is oiled, the dice are loaded, and the random seeds are planted."

These are Devon's signature. Blocks where he steps back and explains
the concept like he's working through it from zero. Keep these. They're
the best parts.

---

## 3. ANTI-PATTERNS (things that aren't Devon's voice)

### Em-dashes used as parenthetical spacers
AI voice: "The system — which is robust — ensures correctness."
Devon voice: "The system enforces correctness. Period."

If an em-dash is doing the work of a period or a colon, replace it.
Devon uses dashes sparingly and for punch, not as filler punctuation.
Exception: em-dashes that Devon actually wrote (check git blame if unsure).

### Formulaic AI words
These words aren't how Devon talks. Replace them with plain language:

| DON'T USE            | USE INSTEAD                         |
|---------------------|-------------------------------------|
| leverage            | use                                 |
| utilize             | use                                 |
| facilitate          | make possible / let                 |
| robust              | strong / hard to break              |
| comprehensive       | full / complete / everything        |
| streamline          | simplify / cut                      |
| noteworthy          | worth noting / important            |
| delve               | dig into / look at                  |
| underscore          | prove / show / make clear           |
| ensuring            | so that / which means               |
| it is worth noting  | (just say the thing)                |
| in this section we  | (just say the thing)                |
| we present          | (just say the thing)                |
| we propose          | (just say the thing)                |
| we demonstrate      | (rewrite as direct claim)           |
| this approach       | (name the actual thing)             |
| importantly         | (if it's important, it shows)       |
| furthermore         | and / also / (just start)           |
| consequently        | so                                  |
| nevertheless        | but                                 |
| it should be noted  | (just say it)                       |
| in order to         | to                                  |
| a number of         | several / (use the actual number)   |
| due to the fact that| because                             |
| prior to            | before                              |
| subsequent to       | after                               |
| in the context of   | in / for / when                     |
| with respect to     | about / for                         |

### Passive voice hiding the actor
AI voice: "The theorem is proven by leveraging the monotonicity constraint."
Devon voice: "The theorem works because mu never goes down."

### "We" when there is no "we"
Devon is one person. He says "I" when talking about his work.
"We" is acceptable in the mathematical sense ("we define", "we prove")
where it means "the reader and I, working through this together."
Not as false modesty or institutional authority.

### Boilerplate introductions and conclusions
AI voice: "In this section, we present a comprehensive overview of..."
Devon voice: (just starts explaining the thing)

AI voice: "In conclusion, we have demonstrated that..."
Devon voice: "That's how it works. Here's how you break it."

### Expert posturing
AI voice: "It is well-established in the literature that..."
Devon voice: "Here's what I found when I dug into this..."

Devon doesn't pretend to already know things. He explains what he
figured out by going deep. The voice is discovery, not authority.

### Vague hand-waving where a concrete claim should be
AI voice: "This has significant implications for the field."
Devon voice: "This means X. If X is wrong, here's how you prove it."

### Over-qualification and hedging
AI voice: "It is reasonable to suggest that this may potentially indicate..."
Devon voice: "I think this proves X." or "I don't know yet."

Devon is honest about uncertainty. He doesn't hedge with weasel words.
He either makes the claim or says he doesn't know. And when he makes
a claim, it's because the machine checked it — not because he's sure
of himself.

---

## 4. COQ COMMENT VOICE

### Good (Devon's actual voice in the codebase)
```
(* I claim these three laws are NECESSARY AND SUFFICIENT for No Free Insight *)
(* This is not a philosophical claim. It is a machine-checked theorem. *)
(* If you can only measure pc, mu, and err — if those are your instruments — *)
(* THE ANSWER: ANY system. If you can go from uncertified to certified, mu > 0. *)
```

### Bad (AI-generated boilerplate)
```
(* This section provides a comprehensive treatment of the monotonicity
   property, leveraging the underlying algebraic structure to ensure
   robust verification of the cost invariants. *)
```

### Rules for Coq comments
1. Say what the lemma DOES in plain language. One sentence.
2. If there's a falsification condition, state it.
3. If the proof technique matters, name it ("by induction on fuel" / "omega kills it").
4. No "comprehensive", no "robust", no "leveraging".
5. Explain WHY, not just what. Devon's best comments explain the
   logic like he's working through it: "Here's the idea..."
6. Section headers should be descriptive, not bureaucratic.
   Good: "WHY — The Argument from First Principles"
   Bad: "Section 3.2: Preliminary Definitions and Auxiliary Lemmas"

---

## 5. THESIS VOICE

### Good (Devon's actual thesis voice)
```
Let me be straight with you: I'm a car salesman.
```
```
I spent months staring at this problem before it clicked.
The Turing Machine isn't broken — it's blind by design. It's like
trying to find your way through a maze by only ever looking at the
floor tile you're standing on.
```
```
Every claim has a concrete falsification condition. If you find
a counterexample, the Coq proof won't compile.
```

### Bad (AI-polished thesis voice)
```
This chapter presents a comprehensive formal framework for reasoning
about the information-theoretic costs associated with computational
discovery in the context of partition-aware machine models.
```

### Rules for thesis text
1. First person is fine. Devon does it. Keep it.
2. The voice is someone learning and explaining, not lecturing.
   "I spent months staring at this" > "It is well-known that"
3. Every claim needs either a proof reference or a falsification condition.
4. No "we present" / "we demonstrate" / "this chapter discusses."
   Just start explaining the thing.
5. Technical precision is required. Informality is not sloppiness.
   Devon is informal AND precise. That's rare. Preserve it.
6. Author's Notes are Devon's signature move. Keep them. They work.
7. When Devon doesn't know something, he says so. Don't add
   false confidence. "I think" and "I'm not sure" are honest.

---

## 6. README / DOCUMENTATION VOICE

### Good
```
Run the code. Audit the outputs. Check the hashes. Adhere to the contract.
```
```
DO NOT REVIEW THIS AS AN ALGORITHM TO BE OPTIMIZED.
REVIEW IT AS AN INSTRUMENT WHOSE BREAKING POINT IS THE MEASUREMENT.
```

### Bad
```
This repository provides a comprehensive toolkit for researchers
interested in exploring the relationship between information-theoretic
costs and computational complexity.
```

### Rules for documentation
1. Tell the reader what to DO, not what the document "provides."
2. Tables over prose when comparing things.
3. Numbered lists for sequences.
4. Bold and CAPS for emphasis. Not flowery adjectives.
5. Explain things from the ground up, like the reader is learning
   alongside you. Not lecturing down.

---

## 7. SCRIPT / PYTHON COMMENT VOICE

### Good (Devon's actual style)
```python
RUN_SEED = 123456789  # Global random seed for reproducibility; numerologically neutral.
                      # For chaos, swap in 42 — but any existential fallout is on you.
```
```python
# First Principles Explanation:
# The Thiele Machine is my answer to the limits of the Turing Machine.
```

### Bad
```python
# This function leverages the underlying partition structure to facilitate
# efficient computation of the MDL cost metric, ensuring robust handling
# of edge cases in the certificate verification pipeline.
```

### Rules for Python/script comments
1. Say what the code DOES. One line if possible.
2. "First Principles Explanation" blocks are Devon's move. Use them for complex logic.
3. Humor is fine. Personality is fine. Just be accurate.

---

## 8. VERIFICATION CHECKLIST (use while sweeping each file)

For every file, ask:

### Voice
- [ ] Does every sentence sound like Devon wrote it? Read it out loud.
- [ ] Are there em-dashes doing the work of periods or colons? Fix them.
- [ ] Are there words from the DON'T USE list? Replace them.
- [ ] Is there passive voice hiding who did what? Make it active.
- [ ] Is there a "we present" / "in this section" / "comprehensive"? Delete it.
- [ ] Does it sound like someone explaining or someone lecturing? It should be explaining.
- [ ] Is there expert posturing where Devon would just explain what he found?
- [ ] Is there boilerplate that adds no information? Cut it.

### Truth
- [ ] Does every claim have either a proof reference or a falsification condition?
- [ ] Is anything asserted as true without pointing to how it's proven?
- [ ] Are there vague implications ("significant", "promising") without concrete statements?
- [ ] Is there hedging where Devon would either make the claim or say "I don't know"?
- [ ] Does every comment that says "this works because X" actually check that X is true?
- [ ] Is there anything that says "obviously" / "clearly" / "trivially"? Nothing is obvious.
- [ ] Are Coq comments saying what the lemma does in plain language?
- [ ] Can we actually verify the claim right now? If so, do it.

---

## 9. THE PROMISE

We will use this guide to sweep every file in the repository:
- All 188 Coq .v files
- All Python scripts
- All READMEs and markdown documentation
- All 13 thesis chapters + appendices
- All build scripts and tool configs

No exceptions. Every assertion investigated. Every comment checked.
Every claim verified against the actual proofs and tests.

If something doesn't sound like Devon, it gets rewritten.
If something claims a fact, we verify the fact.
If something hedges, we either make the claim or say we don't know.
If something lectures, we make it explain instead.

---

*"I spent months staring at this problem before it clicked.
The Turing Machine isn't broken — it's blind by design."*
— Devon Thiele, Chapter 1

---

## 10. FILE AUDIT TRACKER

This is the working log for the comment sweep. Every .v file in the corpus
gets swept exactly once. Rules:

- Mark a file DONE only after every comment, lemma, definition, fixpoint,
  and section header has been checked against this guide. Read it out loud.
- Mark IN PROGRESS when work has started but the file is not fully swept.
- Anything PENDING has not been touched yet.
- SKIP is for auto-generated files that are never edited directly.

When a file is marked DONE, note what was changed. If a comment is left
unchanged because it was already correct, say so. Don't mark something done
and leave the voice wrong.

**Status key:**
- `DONE` — fully swept, voice verified, all comments checked
- `WIP` — partially swept, work in progress
- `PENDING` — not yet started
- `SKIP` — auto-generated (never edited directly)

---

### coq/ (root)

| File | Status | Notes |
|------|--------|-------|
| `Extraction.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ThieleMachineComplete.v` | DONE | Full sweep 2026-04-16; fixed 1x "trivially" (line 13461), 2x "This section provides" boilerplate (lines 7850, 13907). Zero Admitted. Zero banned words. Voice already strong throughout. |

---

### coq/kernel/ (130 files)

| File | Status | Notes |
|------|--------|-------|
| `VMState.v` | DONE | Full re-sweep 2026-04-16; replaced all API-doc headers, section borders, textbook explanations |
| `VMStep.v` | DONE | Full re-sweep 2026-04-16; corrected truth claims around hardware PNEW/PMERGE, pure-advance EMIT/PDISCOVER/LJOIN, and added missing ALU/tensor/morphism constructor comments |
| `KernelPhysics.v` | DONE | Full sweep 2026-04-16; all SECTION N: borders removed, HELPER: boilerplate removed, formal specification labels replaced |
| `AbstractNoFI.v` | DONE | Full sweep 2026-04-16; tightened universality scope, removed banner voice, and corrected abstract/PC-indexed wording |
| `AlgebraicCoherence.v` | DONE | Full sweep 2026-04-16; corrected CHSH/Tsirelson overclaims, documented the weak-general versus symmetric-rational proof boundary, and removed formal-spec/em-dash artifacts |
| `BekensteinCalibration.v` | DONE | Full sweep 2026-04-16; separated algebra from named physical hypotheses, removed SECTION/em-dash boilerplate, and added comments for PSPLIT/PNEW calibration lemmas |
| `BlindnessRepresentation.v` | DONE | Full sweep 2026-04-16; removed section/formal-spec scaffolding, narrowed the `what_is_lost` claim to its witness-counter theorem, and renamed `fiber_is_non_trivial` to `fiber_has_two_preimages` |
| `BornRule.v` | DONE | Full sweep 2026-04-16; removed helper/section boilerplate, corrected the Gleason/accounting overclaim, and renamed the local μ-consistency theorem to reflect its weak cost-side condition |
| `BornRuleLinearity.v` | DONE | Full sweep 2026-04-16; removed SECTION/HELPER/em-dash scaffolding, clarified the definitional no-signaling bridge versus Hardy-style hypotheses, and softened zero-hypothesis/capstone claims. Inquisitor follow-up 2026-04-17: moved arithmetic-helper notes next to the three concrete Born-probability lemmas so the definitional scope is machine-visible; `python3 scripts/inquisitor.py --report INQUISITOR_REPORT.md` passes with zero findings |
| `BoxCHSH.v` | DONE | Full sweep 2026-04-16; corrected Tsirelson overclaims, documented that the algebraic bridge currently proves |S| <= 4, and renamed the internal BoxTsirelsonBound section |
| `CHSH.v` | DONE | Full sweep 2026-04-16; narrowed receipt/integrity language to trial parsing, separated local deterministic bound from quantum context, and removed em-dash artifacts |
| `CHSHExtraction.v` | DONE | Full sweep 2026-04-16; clarified executed-trace extraction, removed μ/Tsirelson promises, and documented that local-bound lemma only proves the loose |S| <= 4 ceiling |
| `CHSHStatisticalBridge.v` | DONE | Full sweep 2026-04-16; rewrote the statistical-bridge commentary into Devon voice, removed the bureaucratic BellInequality section label, and kept the Hoeffding boundary explicit as unproved |
| `CategoryBridge.v` | DONE | Full sweep 2026-04-16; rewrote the file header and certification-policy commentary, and corrected the false slide from non-cert-setter to cost-free |
| `CategoryLaws.v` | DONE | Full sweep 2026-04-16; rewrote the foundational commentary, corrected the standalone-versus-kernel-bridge wording, and removed audit-process boilerplate |
| `CategoryMonoidal.v` | DONE | Full sweep 2026-04-16; rewrote the tensor/interchange commentary into Devon voice and narrowed the NoFreeInsight claim to non-cert-setter plus mu_delta cost |
| `CertCheck.v` | DONE | Full sweep 2026-04-16; rewrote all banner sections and removed SAFE annotations, tightened claim boundaries |
| `Certification.v` | DONE | Full sweep 2026-04-16; rewrote file header and all WHY/FALSIFICATION/USED BY blocks into Devon voice |
| `ClassicalBound.v` | DONE | Full sweep 2026-04-16; removed ========= borders and sub-heading labels, rewrote file header + all WHY/FALSIFICATION blocks into Devon voice |
| `ClassicalConservativity.v` | DONE | Full sweep 2026-04-16; removed PART N section labels and ========= borders, rewrote file header and section intros into Devon voice |
| `ClausiusFromEntropyArea.v` | DONE | Minimal sweep 2026-04-16; removed single WHY THIS FILE EXISTS label |
| `Closure.v` | DONE | Full sweep 2026-04-16; removed ========= border and all sub-heading labels (WHY, PROPERTY N, WHAT THIS SAYS, etc.), kept all substance in Devon prose |
| `ConeAlgebra.v` | DONE | Full sweep 2026-04-16; removed banner walls and repeated THE CLAIM / WHY / PROOF labels while preserving algebraic statements, physics analogies, and falsification hooks |
| `ConeDerivation.v` | DONE | Full sweep 2026-04-16; removed banner walls and repeated WHY / CLAIM / PROOF labels while preserving uniqueness argument, derivation principle, and physics analogy |
| `ConstantUnification.v` | DONE | Full sweep 2026-04-16; removed banner walls and repeated WHAT / CLAIM / WHY labels while preserving scientific-honesty caveats, empirical-program framing, and falsification hooks |
| `ConstructivePSD.v` | DONE | Full sweep 2026-04-16; rewrote the opening and summary wrapper blocks into direct prose while preserving the quadratic-form proof strategy, Fine-constraint chain, and falsification surface |
| `CurvedTensorPipeline.v` | DONE | Full sweep 2026-04-16; rewrote the remaining section-wall blocks into direct prose while preserving the non-circular Einstein-equation framing and three-vertex closure narrative |
| `Definitions.v` | DONE | Full sweep 2026-04-16; corrected claim/proof boundary, singleton_uniform truth claim, and finite-measurement assumption wording |
| `DerivedTime.v` | DONE | Full sweep 2026-04-16; removed wrapper-heavy claim/proof labels while preserving the stutter-equivalence argument, scope limits, and falsification hooks |
| `DiscreteGaussBonnet.v` | DONE | Full sweep 2026-04-17; rewrote topology/curvature comments to state the equilateral-angle assumption, removed em-dash and checkmark artifacts, and made the PNEW/Gauss-Bonnet bridge explicit without overclaiming |
| `DiscreteRaychaudhuri.v` | DONE | Full sweep 2026-04-17; tightened Lorentzian-signature commentary, removed em-dash artifacts, and marked the Clausius witness theorem as a weak existence bridge rather than a derived heat magnitude |
| `DiscreteTopology.v` | DONE | Full sweep 2026-04-17; clarified that 3F = 2I + B and B = 3chi are well_formed_triangulated invariants, rewrote helper/section comments, and removed stale duplicate-proof rhetoric |
| `EinsteinEmergence.v` | DONE | Full sweep 2026-04-17; narrowed claims to Gauss-Bonnet topology-curvature tracking, marked stress-energy as trigger-side context, and removed 4D-EFE overclaiming |
| `EinsteinEquations4D.v` | DONE | Full sweep 2026-04-17; rewrote unit-normalization/vacuum/local-curvature/Bianchi comments, corrected general-EFE and μ-conservation overclaims, and kept OP-4/5/6 open |
| `EinsteinEquationsFull.v` | DONE | Full sweep 2026-04-17; clarified full tensor result as conditional reduction, renamed off-diagonal Ricci from hidden hypothesis rhetoric to explicit section premise, and removed closure overclaiming |
| `EntanglementEntropy.v` | DONE | Full sweep 2026-04-17; confirmed support-level partial trace/rank surrogate wording and boundary-local area-law scope; no changes needed |
| `EntropyImpossibility.v` | DONE | Full sweep 2026-04-17; tightened the naive-entropy failure framing, replaced Bekenstein-justification overclaim with bounded-information motivation, and changed local axiom rhetoric to explicit-assumption language |
| `FalsifiablePrediction.v` | DONE | Full sweep 2026-04-17; corrected benchmark/scaling prose so Coq definitions, monotonicity, and falsification predicates are separated from empirical Python/Verilog measurement claims |
| `FiniteInformation.v` | DONE | Full sweep 2026-04-17; narrowed second-law prose to the proven finite-state monotonicity theorem, clarified explicit Section premises and stdlib imports, and scoped the VM ledger application |
| `FourDSimplicialComplex.v` | DONE | Full sweep 2026-04-17; scoped the file to clique-style 4D cell bookkeeping and arity proofs, corrected the 4-simplex/Euler-characteristic commentary, and made missing manifold/incidence obligations explicit |
| `HardwareBisimulation.v` | DONE | Full sweep 2026-04-17; narrowed hardware claims to abstract PC/mu cost bisimulation, removed full-synthesis/automatic-transfer overclaims, and clarified the Q16.16 scaled-nat model |
| `HonestNoFI.v` | DONE | Full sweep 2026-04-17; removed em-dash artifacts while preserving the three-level NoFI scope split across structural, quantitative, and conditional Landauer claims |
| `HonestNoFI_TheoremsWithoutAssumptions.v` | DONE | Full sweep 2026-04-17; corrected the header and theorem comments to show the first theorem still assumes strictly_stronger while B4 separately derives existence of strict predicates |
| `InformationCausality.v` | DONE | Full sweep 2026-04-17; narrowed the file to custom IC/mu record bookkeeping, marked Tsirelson/quantum theorem names as legacy scope, and removed physical IC overclaims |
| `InformationGainToStrengthening.v` | DONE | Full sweep 2026-04-17; removed em-dash/trivial-construction artifacts and made the deprecated compatibility theorem explicitly separate from the membership-based B3 result |
| `InsightTaxonomy.v` | DONE | Full sweep 2026-04-17; removed em-dash artifacts, kept the certified-insight/non-cert structural boundary intact, and scoped structural-op lists as examples where the file proves representative lemmas |
| `JacobsonBridgeComponents.v` | DONE | Full sweep 2026-04-17; confirmed the file is already a correctly scoped conditional composition of Clausius and Raychaudhuri components; no changes needed |
| `Kernel.v` | DONE | Full sweep 2026-04-17; narrowed the file to a minimal Turing-machine-shaped data model and removed universality/halting/physical-cost overclaims |
| `KernelBenchmarks.v` | DONE | Full sweep 2026-04-17; scoped benchmark theorems to selected model cost expressions, not wall-clock runtime or every VM operation, and corrected falsification language |
| `KernelNoether.v` | DONE | Full sweep 2026-04-17; rewrote Noether/gauge comments to say Z-indexed μ shifts with positivity guards, clarified monotonicity versus conservation, and removed full-physics overclaims |
| `KernelTM.v` | DONE | Full sweep 2026-04-17; corrected the toy executor comments so ClaimTapeIsZero is described as advance-only here, with no tape erasure or μ charge |
| `KernelThiele.v` | DONE | Full sweep 2026-04-17; scoped step_thiele/run_thiele to costed toy semantics, removed Landauer/hypercomputation physical overclaims, and clarified fuel as a recursion bound |
| `LandauerDerivation.v` | DONE | Full sweep 2026-04-17; narrowed the file from physical Landauer derivation to VM μ-cost/certification bounds and the conservative positive-cost irreversible_bits indicator |
| `LocalInfoLoss.v` | DONE | Full sweep 2026-04-17; narrowed the theorem family to signed module-count loss, removed absolute-value/physical-Landauer overclaims, and clarified FiniteInformation is not instantiated here |
| `LocalMorphismSemantics.v` | DONE | Full sweep 2026-04-17; confirmed split-morphism support semantics and nearest-neighbor boundary-locality wording already matched the proved scope; no changes needed |
| `Locality.v` | DONE | Full sweep 2026-04-17; scoped the theorem to preservation of normalized module-region observations for existing untargeted modules, removing Einstein/superluminal overclaims |
| `LorentzNotForced.v` | DONE | Full sweep 2026-04-17; removed dash artifacts and scoped the file to kernel-level cone underdetermination rather than claiming an emergent Lorentz derivation |
| `LorentzianTensorPipeline.v` | DONE | Full sweep 2026-04-17; confirmed the isotropic mass-gradient sign argument scope and removed remaining Inquisitor-note dash artifacts |
| `MasterSummary.v` | DONE | Full sweep 2026-04-17; removed stale dash artifacts and tightened summary wording around HonestNoFI premises, formal Riemann identity scope, and categorical alias descriptions |
| `MatrixAlgebra4.v` | DONE | Full sweep 2026-04-17; confirmed 4x4 matrix infrastructure scope and removed the remaining em-dash artifact; no proof changes |
| `MetricForcing.v` | DONE | Full sweep 2026-04-17; narrowed forcing claims to the isotropic two-vertex theorem, clarified totalized 0/0 division, removed style artifacts; `make -C coq kernel/MetricForcing.vo` clean |
| `MetricFromMuCosts.v` | DONE | Full sweep 2026-04-17; narrowed metric/spacetime prose to distance-like algebra and local curvature-style definitions, removed style artifacts; `make -C coq kernel/MetricFromMuCosts.vo` clean |
| `MinorConstraints.v` | DONE | Full sweep 2026-04-17; scoped Fine/CHSH prose to finite hidden-variable witnesses, corrected deterministic case count, removed style artifacts; `make -C coq kernel/MinorConstraints.vo` clean |
| `MuChaitin.v` | DONE | Full sweep 2026-04-17; scoped Chaitin/Landauer language to analogy, made cert_priced explicit as policy premise, corrected payload-size prose; `make -C coq kernel/MuChaitin.vo` clean |
| `MuCostDerivation.v` | DONE | Full sweep 2026-04-17; scoped first-principles/physical-cost claims to bridge premises, recast local results as lower-bound interfaces and consistency checks, removed style artifacts; `make -C coq kernel/MuCostDerivation.vo` clean |
| `MuCostModel.v` | DONE | Full sweep 2026-04-17; aligned comments with the simplified operational ledger, removed stale CHSH/physics assertions and LASSERT/LJOIN delta wording; `make -C coq kernel/MuCostModel.vo` clean |
| `MuGeometry.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `MuGravity.v` | DONE | Full sweep 2026-04-17; completed the remaining header cleanup after earlier surgical repair |
| `MuInformation.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `MuInitiality.v` | DONE | Full sweep 2026-04-17; rewrote the universal-initiality framing, cleaned the init_graph/init_csrs commentary, and replaced the old results banner with direct scope language |
| `MuLedgerConservation.v` | DONE | Full sweep 2026-04-16; corrected main theorem references, removed formal-spec boilerplate, and narrowed the gestalt certificate claim to the singleton theorem actually proved |
| `MuLedgerQuantumBridge.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `MuNoFreeInsightQuantitative.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `MuShannonBridge.v` | DONE | Full sweep 2026-04-17; scoped the file to the actual mu/Shannon bridge, clarified feasible-set/log2 commentary, and removed banner-style sales language |
| `MuShannonQuantitative.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `NPAMomentMatrix.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `NoCloning.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `NoFIToEinstein.v` | DONE | Full sweep 2026-04-17; rewrote the bridge framing to keep the calibration/thermodynamic chain explicit and removed the remaining zero-admits slogan from the main theorem note |
| `NoFreeInsight.v` | DONE | Full sweep 2026-04-16; corrected theorem scope, receipt/ledger claims, and predicate-strengthening bridge wording |
| `NonCircularityAudit.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `OCamlExtractionBridge.v` | DONE | Full sweep 2026-04-17; rewrote the extraction-faithfulness header into an explicit trust-boundary statement and kept the axiom-versus-proved split auditably clear |
| `ObserverDerivation.v` | DONE | Full sweep 2026-04-17; rewrote the observer/locality header blocks into direct prose, simplified the observer-equivalence commentary, and fixed a malformed leftover comment during rebuild |
| `PDISCOVERIntegration.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `PNEWTopologyChange.v` | DONE | Full sweep 2026-04-17; rewrote the file header and section intros so the theorem says exactly what fresh PNEW changes do, without overstating Euler-characteristic effects |
| `PartitionSeparation.v` | DONE | Full sweep 2026-04-17; rewrote the feature-separation framing to keep it definitional rather than computability-theoretic, and removed TM/partition sales rhetoric |
| `Persistence.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `PhysicsClosure.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `PrimeAxiom.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ProbabilityImpossibility.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ProperSubsumption.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `Purification.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `PythonBisimulation.v` | DONE | Full sweep 2026-04-17; narrowed the cross-layer claim to the abstract PC/mu correspondence actually proved here and separated it from the executable test harness evidence |
| `QuantitativeNoFI.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `QuantumBound.v` | DONE | Full sweep 2026-04-17; scoped the file to the certification interface and admissibility surface it really proves, and removed legacy end-marker/banner language |
| `QuantumEquivalence.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `QuantumPartitionPSD.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `RaychaudhuriFluxBridge.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ReceiptCore.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ReceiptIntegrity.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `RevelationRequirement.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `RiemannTensor4D.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `SemanticMuCost.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `SemidefiniteProgramming.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ShadowProjection.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `SimulationProof.v` | DONE | Full sweep 2026-04-16; corrected bisimulation/replay scope, replaced formal-spec boilerplate, and documented canonical witness lemmas honestly |
| `SpacetimeEmergence.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `StateSpaceCounting.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `StressEnergyDynamics.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `StructuralAdvantage.v` | DONE | Full sweep 2026-04-17; rewrote the step-count/time-tax commentary into direct prose and kept the theorem tied to the actual blind-versus-sighted comparison |
| `Subsumption.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `TOE.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ThermoEinsteinBridge.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ThieleGenesis.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ThieleTraceProjection.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ThreeLayerIsomorphism.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `TopologyCurvatureBridge.v` | DONE | Full sweep 2026-04-17; rewrote the topology-to-curvature bridge commentary, removed phase/quantization banner voice, and kept the proved bridge scope explicit |
| `TsirelsonFromAlgebra.v` | DONE | Full sweep 2026-04-17; rewrote the archived-versus-non-circular bridge header so the file is clearly the mu-cost bridge to TsirelsonGeneral, not a separate derivation hype block |
| `TsirelsonGeneral.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `TsirelsonQuantumModel.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `TsirelsonUniqueness.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `TsirelsonUpperBound.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `TuringClassicalEmbedding.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `TuringCompletenessISA.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `TuringStrictness.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `Unitarity.v` | DONE | Full sweep 2026-04-17; rewrote the reversible-evolution framing so the file reads as a mu-ledger argument about purity/conservation rather than a manifesto block |
| `UniversalCertificationCost.v` | DONE | Full sweep 2026-04-17; rewrote the substrate-independent certification-cost framing and kept the theorem surface honest about what is parameterized versus proved |
| `VMEncoding.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ValidCorrelation.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `VerilogRTLCorrespondence.v` | DONE | Full sweep 2026-04-17; rewrote the closing correspondence note to separate constructive instantiation from cosimulation evidence and removed the last zero-admits slogan |
| `WitnessPreservationImpossibility.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |

---

### coq/kami_hw/ (22 files)

| File | Status | Notes |
|------|--------|-------|
| `Abstraction.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `CanonicalCPUProof.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `Compatibility.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `EmbedStep.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `EmbedStep_WF.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `FullAbstraction.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `FullEmbedStep.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `FullStep.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `GraphReconstructionBridge.v` | DONE | Full sweep 2026-04-17; completed the bridge-header cleanup after earlier surgical repair |
| `HardwareShadowBridge.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `KamiExtraction.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `LogicEngineEquivalence.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `RTLCorrectnessInstantiation.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `RichStateCommutation.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ShadowDevice.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ShadowDeviceTrace.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ShadowEmbedStep.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ThieleCPUBusTop.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ThieleCPUCore.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ThieleCanonicality.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ThieleTypes.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `VerilogRefinement.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |

---

### coq/nofi/ (5 files)

| File | Status | Notes |
|------|--------|-------|
| `Instance_Kernel.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `MuChaitinTheory_Interface.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `MuChaitinTheory_Theorem.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `NoFreeInsight_Interface.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `NoFreeInsight_Theorem.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |

---

### coq/physics/ (5 files)

| File | Status | Notes |
|------|--------|-------|
| `DiscreteModel.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `DissipativeModel.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `PreregSplit.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `TriangularLattice.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `WaveModel.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |

---

### coq/self_reference/ (9 files)

| File | Status | Notes |
|------|--------|-------|
| `AdversarialChallenge.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `InductiveTrust.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `MuThresholdDisobedience.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `NeuralSymbolicBridge.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `NonInterference.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `RefinementInvariant.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `SelfCertifyingDecider.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `SelfReference.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `TilingChain.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |

---

### coq/spacetime/ (1 file)

| File | Status | Notes |
|------|--------|-------|
| `Spacetime.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |

---

### coq/tests/ (3 files)

| File | Status | Notes |
|------|--------|-------|
| `TestNecessity.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `verify_nofi_load_bearing.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `verify_zero_admits.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |

---

### coq/thermodynamic/ (2 files)

| File | Status | Notes |
|------|--------|-------|
| `LandauerDerived.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ThermodynamicBridge.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |

---

### coq/thiele_manifold/ (4 files)

| File | Status | Notes |
|------|--------|-------|
| `PhysicalConstants.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `PhysicsIsomorphism.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ThieleManifold.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ThieleManifoldBridge.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |

---

### coq/thielemachine/ (2 files)

| File | Status | Notes |
|------|--------|-------|
| `ThieleMachine.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |
| `ThieleProc.v` | DONE | Audit 2026-04-17; acceptable on final pass without further edits |

---

**Total: 188 .v files | Done: 188 | WIP: 0 | Pending: 0 | Skip: 0**

---

## 11. OPEN ISSUES

Things that came up during the sweep that are incomplete, unresolved,
deferred, or need a second pass. Update this table as work proceeds.
Nothing gets dropped silently — if something can't be fixed right now,
it goes here with a reason.

| File | Issue | Status | Notes |
|------|-------|--------|-------|
| `VMStep.v` | File swept but not fully verified — confirm all lemmas after step constructors have Devon-voice comments | CLOSED | Final pass completed 2026-04-16; `make -C coq kernel/VMStep.vo` passes |
| `VMState.v` | First sweep (prior session) produced API-doc voice; full re-sweep completed 2026-04-16 | CLOSED | Confirmed DONE |
| `KernelPhysics.v` | Substrate-level no-signaling theorem (graph_lookup version) is intentionally NOT proven — pmerge legitimately updates super-module axioms | DOCUMENTED | Not a bug; observational_no_signaling is the correct proven theorem |
| All kernel/ files | Kernel tracker backlog closed | CLOSED | Final 2026-04-17 audit/sweep pass cleared the remaining tracker mismatch |
| All kami_hw/ files | Kami tracker backlog closed | CLOSED | Final 2026-04-17 audit/sweep pass cleared the remaining tracker mismatch |
| All nofi/physics/self_reference/spacetime/tests/thermodynamic/thiele_manifold/thielemachine/ | Section backlogs closed | CLOSED | Final 2026-04-17 audit/sweep pass cleared the remaining tracker backlog |
| `Extraction.v` / `ThieleMachineComplete.v` | Root tracker backlog closed | CLOSED | Both root `.v` files are now marked DONE |
