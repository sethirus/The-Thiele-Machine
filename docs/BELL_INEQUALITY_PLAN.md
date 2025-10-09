# Bell Inequality Formalisation Plan

The previous development left `coq/thielemachine/coqproofs/BellInequality.v`
reliant on a long list of axioms.  Eliminating them will require a fairly
substantial refactor of the file and of the "local" interface used throughout
the project.  The high-level plan I captured while installing Coq locally is:

1. **Refine the model of classical strategies.**  The current `local` predicate
   allows arbitrary probability kernels, but the CHSH inequality only depends on
   deterministic strategies.  We need to normalise the probabilistic witnesses
   into convex combinations of deterministic `Bit -> Bit` response functions.

2. **Make the step-by-step bounds computable.**  Once the `local` structure is
   expressed as a finite mixture, we can expand the CHSH expression entirely in
   terms of a handful of rational coefficients.  This opens the door to proving
   the classical Tsirelson bound inside Coq using linear arithmetic (`lra`).

3. **Eliminate the PR-box axioms.**  With the deterministic expansion in place
   we can derive the PR-box properties (`PR_norm`, `PR_nonneg`, `PR_nosig_A`,
   `PR_nosig_B`, `PR_S`, and `PR_not_local`) by direct case analysis instead of
   declaring them as axioms.  ✅ _Completed in Iteration 2L._

4. **Bridge to the runtime receipts.**  After the proof obligations are
   discharged we can connect the Coq witnesses to the Python receipts emitted by
   the simulator so that each recorded CHSH run is accompanied by a machine
   checked certificate.

## Iteration Notes

### Iteration 2F — Local correlator decomposition helpers

- Added `sum_bit_ext`, `sum_bit2_ext`, and `sum_strategies_ext` to transport
  pointwise equalities through the summation operators together with
  `sum_bit2_sum_strategies` for swapping the bitwise and strategy sums.
- Proved `local_E_as_convex` showing that any `local` box decomposes `E B x y`
  into a convex combination of deterministic correlators.
- Introduced helper `sum_bit2_sum_strategies` and recorded the necessary linear
  algebra so that future iterations can reason directly about the convex
  coefficients without resorting to axioms.
- Upcoming task: leverage the new `S` decomposition to push absolute-value
  bounds through the convex mixture.

### Iteration 2I — CHSH convex decomposition

- Added `local_S_decompose` and `local_S_as_convex`, showing that the full
  CHSH expression of any local box is a convex combination of deterministic
  `strategy_S` witnesses.
- With the convex rewrite in place the next step was to turn the classical
  CHSH bound into an explicit convex-inequality argument.

### Iteration 2J — Weighted convexity lemmas

- Introduced `Qmult_le_nonneg_l` plus the `sum_strategies_list_weighted_*`
  lemmas so that convex mixtures over the explicit strategy list can be bounded
  directly in `Q`.
- Attempted to use these lemmas to eliminate `local_CHSH_bound`, but rewriting
  the resulting inequalities (e.g. simplifying `c * 1#1`) exposed a gap in the
  current `Qeq` rewriting support.  The axioms remained in place until a
  `Qeq`-aware normalisation helper or `Q2R` detour could be engineered.
- Next task: build that rational rewriting helper so the constructive convexity
  argument can complete without reintroducing the axioms.

### Iteration 2K — Constructive classical CHSH bound

- Leveraged the weighted convexity lemmas together with `strategy_S_bound` to
  replace the `local_CHSH_bound` axiom by a fully mechanised lemma.
- Used targeted `setoid_rewrite` steps over the `Qeq` relation to normalise the
  convex weights (substituting the `sum_strategies w = 1` witness) without
  resorting to the `ring` tactic.
- Next objective: remove the remaining classical placeholder
  `local_deterministic_CHSH_bound` (now redundant) and begin replacing the
  PR-box axioms with constructive proofs.

### Iteration 2L — PR-box mechanisation

- Replaced the PR-box axioms with explicit lemmas: direct case splits on the
  `PR_p` table establish normalisation, non-negativity, and both no-signalling
  properties.
- Evaluated the correlators explicitly to show `S PR = 4`, then applied the
  constructive `local_CHSH_bound` to refute locality (`PR_not_local`).
- Next objective: formalise the Thiele/Tsirelson advantage (constructive
  Tsirelson bound) and prepare the witnesses needed to bridge Coq proofs with
  the receipt verifier.

### Iteration 2M — Rational Tsirelson witness

- Introduced the rational `TsirelsonApprox` box derived from the generic
  correlator construction and proved it is normalised, non-signalling, and
  achieves `S = (4#1) * gamma` with `gamma = 7071/10000`.
- Established that `Qabs (S TsirelsonApprox)` matches the constructive bound
  and that the box violates locality, giving a fully mechanised classical
  Tsirelson-style advantage.
- Upcoming task: connect the new witness to the receipt verifier so simulated
  CHSH runs emit certificates, and investigate tightening the rational
  approximation toward an exact geometric Thiele strategy.

### Iteration 2N — Receipts bridge skeleton

- Added a parameterised `ReceiptFrame`/`receipts_sound` section to
  `BellInequality.v` capturing the abstract properties required to replay a
  receipt trace against a deterministic step function.
- Proved a general `receipts_sound_single` helper that will instantiate to
  concrete steps (e.g. `PNEW`, `PYEXEC`) once the bridge is specialised to the
  Thiele Machine semantics.
- Upcoming task: instantiate the bridge with the concrete step model and model
  the CHSH/Tsirelson execution trace so that recorded runs can be discharged by
  the Coq checker.

### Iteration 2O — Concrete receipts specialisation

- Imported the concrete machine semantics into `BellInequality.v` and
  specialised the abstract bridge via `concrete_step_frame` and
  `concrete_receipt_frame`.
- Proved `concrete_receipts_sound`, establishing that the deterministically
  generated receipts returned by `concrete_receipts_of` satisfy the abstract
  soundness predicate.

### Iteration 2P — Receipt verifier integration

- Reworked `scripts/verify_truth.sh` so the generated Coq stub defines the
  recorded program and receipt list, proves they coincide with
  `concrete_receipts_of`, and concludes with `concrete_receipts_sound` instead
  of per-step reflexivity lemmas.
- Next step: encode the Tsirelson CHSH program as a concrete receipt trace and
  thread the corresponding witnesses into both the verifier and simulator so the
  recorded runs carry the mechanised certificate end-to-end.

### Iteration 2Q — Tsirelson receipt scaffolding

- Introduced a concrete `tsirelson_program`/`tsirelson_receipts` scaffold inside
  `BellInequality.v`, providing `tsirelson_receipts_sound` and a length lemma to
  reuse the constructive `concrete_receipts_sound` bridge.
- Added `scripts/generate_tsirelson_receipts.py` to emit the canonical receipt
  trace alongside a checked example JSON artefact in `examples/`.
- Extended `scripts/verify_truth.sh` to escape Coq braces correctly, emit
  natural-number literals for `PNEW`, and run `coqc` with the project load path
  so the Tsirelson receipts verify end-to-end.
- Next objective: relate the generated receipts to the rational Tsirelson box
  and thread the resulting witness into the simulator's runtime so the empirical
  CHSH runs align with the formal proof.

### Iteration 2R — Tsirelson receipt characterisation

- Proved that the Coq-level Tsirelson receipts replay the exact instruction
  sequence via `concrete_receipts_instrs`, ensuring the recorded trace mirrors
  the scripted program.
- Exposed the associated observation stream (event tags and zero µ-deltas) as
  explicit lists to ease comparisons with the runtime receipts emitted by the
  Python generator.
- Next objective: map these observed events to the `TsirelsonApprox` correlator
  and show that the recorded run realises the constructive violation witnessed
  earlier in the development.

### Iteration 2S — Tsirelson state alignment

- Characterised the Coq-level Tsirelson receipt states by fixing the pre/post
  sequences to the deterministic program-counter progression from 0 to 5 with
  zero status or µ drift.
- This establishes the concrete-state backbone that the future correlator proof
  will reference when relating the recorded execution to the rational
  `TsirelsonApprox` witness.
- Next objective: use these state invariants to interpret the recorded receipts
  as CHSH trials and connect them to the constructive Tsirelson correlators.

### Iteration 2T — Tsirelson step indexing helpers

- Added `nth_error` lemmas that pin each Tsirelson program instruction and
  recorded event to its concrete index, giving a precise handle on the
  `alice_measurement`/`bob_measurement` steps for later correlator reasoning.
- The new lemmas ensure future proofs can directly reference the measurement
  receipts when extracting CHSH outcomes from the trace.
- Next objective: interpret those measurement receipts as explicit CHSH trials
  and relate them to the rational Tsirelson witness.

### Iteration 2U — Tsirelson measurement receipt shapes

- Captured the full `alice_measurement` and `bob_measurement` receipts (including
  instruction, pre/post states, and observations) so the Coq development can
  work with concrete witnesses rather than just their events.
- These lemmas set up the next step of extracting the CHSH outcome bits from the
  recorded trace and comparing them against the `TsirelsonApprox` correlator.
- Next action: formalise the extraction of those bits and show they coincide
  with the rational Tsirelson correlator table.

### Iteration 2V — Measurement frames and soundness

- Introduced explicit `tsirelson_alice_receipt`/`tsirelson_bob_receipt`
  definitions together with their mapped receipt frames, making the
  measurement steps reusable without re-expanding the full trace.
- Proved `tsirelson_measurements_sound`, a specialised `receipts_sound`
  witness for the two-step measurement subtrace, giving a clean handle for the
  upcoming CHSH outcome extraction.
- Next objective: attach concrete outcome bits to these frames and relate the
  resulting trial to the rational `TsirelsonApprox` box.

### Iteration 2W — Measurement frame component lemmas

- Proved field-level lemmas for each Tsirelson measurement frame, exposing the
  concrete instruction, pre/post state, and observation metadata directly from
  `tsirelson_alice_frame` and `tsirelson_bob_frame`.
- These witnesses avoid repeated unfolding of the concrete receipt records and
  prepare the ground for introducing explicit CHSH outcome bits derived from
  the recorded trace.
- Next objective: define the outcome bits and compare them against the
  `TsirelsonApprox` correlator entries.

### Iteration 2X — CHSH trial scaffolding

- Added a `CHSHTrial` record plus helper lemmas (`trial_S_cases`,
  `trial_S_Qabs`, `trials_S_app`) capturing the ±1 contributions of individual
  measurement outcomes and the additive structure for aggregating trials.
- This scaffolding will let future iterations map the concrete Tsirelson
  measurement frames to explicit CHSH outcome bits and relate the resulting
  trials to the constructive `TsirelsonApprox` witness.
- Next objective: instantiate the trial structure with bits extracted from the
  receipts and prove that the resulting sample realises the Tsirelson correlator.

### Iteration 2Y — Frame interpreter scaffolding

- Introduced a `FrameTrialInterpreter` abstraction for translating pairs of
  receipt frames into `CHSHTrial` witnesses, and specialised it to the
  Tsirelson measurement frames.
- Proved singleton helper lemmas (`interpret_trials_singleton`,
  `tsirelson_trials_S_of`) so the measurement slice rewrites directly to a
  trial contribution while reusing the existing receipt soundness witness.
- Next objective: supply concrete bit interpretations for the Tsirelson
  measurement receipts and compare the resulting trials with the
  `TsirelsonApprox` correlator table.

### Iteration 2Z — Measurement bit encoding and interpreter

- Added canonical setting/outcome bits to the Tsirelson certificates, taught
  both the Coq concrete semantics and the Python receipt generator to emit the
  same metadata, and regenerated the example JSON artefact.
- Defined helper functions that extract the timestamp/sequence bits from
  receipt frames, instantiated them for the Tsirelson measurement steps, and
  packaged them into a concrete `tsirelson_frame_interpreter`.
- Next objective: relate the interpreted Tsirelson trial to the constructive
  `TsirelsonApprox` correlator to start comparing recorded CHSH samples with
  the formal probability box.

### Iteration 2AA — Pointwise Tsirelson trial alignment

- Proved that the interpreted Tsirelson measurement trial contributes `+1` to
  the CHSH sum and that its recorded settings/outcomes appear with strictly
  positive probability in `TsirelsonApprox`.
- Established that the recorded settings pair `(x = B0, y = B1)` matches the
  constructive correlator value `tsirelson_gamma`, giving pointwise agreement
  between the receipts and the rational Tsirelson box.
- Next objective: generalise these pointwise facts to aggregates of
  `CHSHTrial`s so that entire receipt traces can be compared to the
  Tsirelson correlator table.

### Iteration 2AB — Aggregated trial probabilities

- Defined `trial_probability` and `trials_probability` to sum the recorded
  CHSH trials against a candidate box, providing lemmas that specialise the
  construction to the Tsirelson interpreter.
- Proved that the singleton Tsirelson receipt slice has positive aggregated
  probability mass, extending the pointwise witnesses to small finite traces.
- Next objective: connect `trials_S` with `trials_probability` so batches of
  receipts can be compared directly against the constructive Tsirelson
  correlator table.

### Iteration 2AC — Weighted CHSH sums

- Introduced the weighted CHSH aggregator `trials_weighted_S`, proved
  non-negativity bounds via `Qabs`, and established that Tsirelson singleton
  receipts equate the weighted and unweighted probability sums.
- Next objective: extend the weighted-sum machinery to finite batches of
  receipt-derived trials so that their CHSH contributions can be compared with
  the Tsirelson correlator table entry-wise.
- **Iteration 2AD — Repeated Tsirelson batches**

- Proved `tsirelson_trials_weighted_S_repeat_probability`, showing that any
  finite batch of repeated Tsirelson measurement pairs has identical weighted
  `S` and probability aggregates.  This provides the reusable building block
  for scaling the receipt analysis from a single trial to arbitrary finite
  samples.
- Next objective: define the receipt-frame chunking operation that groups
  execution traces into repeated Tsirelson measurement pairs and relate those
  batches directly to the constructive correlator witnesses.

### Iteration 2AE — Measurement frame chunking

- Defined `chunk_pairs` to group receipt frames into ordered pairs and
  specialised it to the Tsirelson measurement frames.
- Proved that concatenating repeated `[alice; bob]` frame lists and chunking
  them recovers `List.repeat tsirelson_measurement_pair n`, establishing the
  combinatorial bridge needed for multi-trial receipt reasoning.
- Next objective: apply the chunking helper to concrete receipt slices (e.g.
  prefixes of repeated runs) so that the interpreter lemmas can manipulate
  multi-trial traces when comparing them against the constructive Tsirelson box.

### Iteration 2AF — Chunked trial interpretation

- Applied `chunk_pairs` to the Tsirelson measurement frames and proved that
  interpreting the resulting chunked lists produces `List.repeat` copies of the
  canonical `tsirelson_trial` witness.
- Combined the chunking lemma with the weighted CHSH bounds to show that the
  aggregated sums and probabilities remain equal after chunking, aligning the
  combinatorial and probabilistic viewpoints.
- Next objective: generalise these chunked-trial equalities to arbitrary
  receipt prefixes emitted by the verifier so that multi-run traces can be
  compared directly with the constructive Tsirelson correlator.

### Iteration 2AG — Prefix interpreter scaffolding (partial)

- Added the commuting lemma `interpret_trials_firstn`, ensuring that applying
  `firstn` before or after `interpret_trials` yields the same truncated list of
  `CHSHTrial`s.
- This helper prepares the way for chunked-prefix reasoning, but the explicit
  equality relating `chunk_pairs (firstn ...)` to `firstn` of the chunked list
  is still outstanding and remains the next objective.

### Iteration 2AH — Prefix chunking attempt (incomplete)

- Explored proving a helper lemma that would show `chunk_pairs` commutes with
  even-length prefixes and applying it to the repeated Tsirelson measurement
  frames, but the naive induction ran into stubborn `firstn`/`concat`
  simplification problems inside Coq.
- Rolled the experimental Coq changes back after confirming the approach did
  not close easily and captured the failure mode so the next iteration can try a
  different angle (e.g. expanding the repeated concatenation before induction).
- Next objective: craft a prefix lemma that avoids the `firstn` arithmetic trap
  so the weighted `S`/probability aggregators can be transported to partial
  Tsirelson receipt batches.

### Iteration 2AI — Prefix chunking attempt (rolled back)

- Explored proving a general lemma `chunk_pairs_firstn` to commute with even
  prefixes and wiring it into `interpret_trials_firstn`, but the Coq proof got
  stuck while rewriting the measurement traces and the experiment was rolled
  back.
- The obstacle mirrors the Iteration 2AH arithmetic issues, suggesting the next
  iteration needs a different proof structure (e.g. app-based reasoning) before
  tackling the receipt integration again.
- Next objective: revisit the chunk-prefix lemma with a new approach that avoids
  the `firstn` simplification pitfall, enabling future iterations to relate
  partial receipt batches to the Tsirelson witnesses.

### Iteration 2AJ — Prefix chunking breakthrough

- Proved the general helper `chunk_pairs_firstn_repeat`, showing that even-length
  prefixes of repeated `[alice; bob]` lists chunk into the corresponding prefix
  of deterministic strategy pairs.
- Specialised the helper to the Tsirelson measurement frames and combined it
  with `firstn`/`repeat` algebra to obtain `chunk_measurement_frames_firstn` and
  `tsirelson_trials_weighted_S_chunk_measurement_frames_firstn`, establishing
  that every even-length prefix of the canonical receipt trace preserves the
  weighted CHSH/probability equality.
- Next objective: extend the new lemma to streamed verifier outputs beyond the
  repeated baseline (e.g. mixed prefixes coming from `firstn` over interpreter
  outputs) so the final chunk-prefix comparison can support arbitrary receipt
  batches.

### Iteration 2AK — Streamed prefix generalisation

- Strengthened the chunk-prefix machinery with `chunk_pairs_firstn_repeat_general`
  so arbitrary prefixes (even or odd length) of repeated measurement frames map
  to the expected deterministic strategy prefixes.
- Specialised the general lemma to the Tsirelson measurement frames and lifted
  it through `interpret_trials`, yielding `tsirelson_trials_weighted_S_*`
  equalities for every streamed prefix regardless of parity.
- Next objective: push the streamed-prefix identities through the interpreter
  outputs to relate arbitrary verifier logs to the constructive Tsirelson trial
  witnesses.

### Iteration 2AL — Measurement frame filtering scaffolding

- Added a boolean filter that recognises Tsirelson measurement frames and proved
  it extracts the canonical `[alice; bob]` slice from a single execution trace.
- Lifted the filter across repeated traces so any concatenation of Tsirelson
  runs reduces to the repeated measurement-frame sequence required by the
  chunking lemmas.
- Next objective: combine the filter with prefix reasoning (`firstn`) so partial
  verifier logs can be normalised before invoking the streamed-prefix equalities.

### Iteration 2AN — Single-run measurement prefix normalisation

- Established `filter_measurement_frames_firstn_tsirelson_frames` by explicitly
  analysing the five-instruction Tsirelson prefix, yielding a closed-form
  expression `firstn (Nat.min (Nat.sub k 2) 2) tsirelson_measurement_frames`
  for every prefix length `k`.
- This resolves the outstanding base case for measurement-frame filtering and
  sets the stage for lifting the argument to repeated traces in the next
  iteration.
- Next objective: compose the prefix lemma with the repetition/concatenation
  helpers so filtered prefixes of multi-run traces reduce to canonical
  measurement-frame prefixes before applying the chunking machinery.

## Iteration Log

- **Iteration 2B:** added deterministic correlator helpers `strategy_E` and
  `strategy_S` together with a direct bound `strategy_S_bound` (|S| ≤ 2) to
  expose the classical extremal values without relying on the axioms.  The next
  step is to push the `local` mixture through `E`/`S` using these helpers so
  that the convex CHSH bound can be proved constructively.
- **Iteration 2C:** attempted to push the convex decomposition through `E`/`S`
  but ran into Coq simplification issues over rationals (linearity over `Q`
  requires an explicit ring instance).  The next iteration needs to factor out
  reusable `sum_strategies` lemmas (linearity, scaling, monotonicity) and set up
  the ring automation so the CHSH bound can be expressed without axioms.
- **Iteration 2D:** proved `strategy_E_from_indicators`, showing that the
  correlator `E` collapses to the deterministic sign product for each response
  table.  This verifies the indicator calculus for single strategies before
  addressing the convex linearity lemmas.
- **Iteration 2E:** attempted to formalise the linearity lemmas for
  `sum_bit`/`sum_bit2`/`sum_strategies`, but rewriting with `ring` ran into the
  mismatch between definitional equality on `Q` and the `Qeq` relation used by
  the arithmetic libraries.  The next coding session needs to decide whether to
  restate the lemmas using `Qeq` (and adjust downstream proofs accordingly) or
  to detour through `Q2R` so that `ring`/`lra` can be applied over the reals.
- **Iteration 2F:** established foundational `Qabs` lemmas (non-negativity and
  upper/lower bounds) that will be required when converting the convex
  combination over deterministic strategies into an absolute-value bound.  The
  follow-up task is to finish the linearity lemmas so these inequalities can be
  applied to `sum_strategies` witnesses directly.
- **Iteration 2G:** rewrote `sum_strategies` using an explicit list recursion
  and proved addition/scaling lemmas with `Qeq` corollaries, clearing the path
  to push the convex decomposition through `E` and `S` in the constructive
  CHSH bound proof.
- **Iteration 2H:** established summation extensionality lemmas and derived the
  `local_E_as_convex` result so that each `E B x y` is now expressed as a convex
  combination over deterministic correlators.  This cleared the path for the
  subsequent iterations that rewrote `S` and ultimately eliminated
  `local_CHSH_bound` constructively.
- **Iteration 2I:** completed the convex rewrite for the CHSH correlator by
  proving `local_S_decompose`/`local_S_as_convex`.  Upcoming work will apply the
  deterministic `strategy_S_bound` lemma to replace the classical CHSH axiom
  with a constructive convexity argument.
- **Iteration 2AE:** implemented receipt-frame chunking via `chunk_pairs` and
  proved it reconstructs repeated Tsirelson measurement pairs after flattening
  the `[alice; bob]` frame lists.  The next step is to connect this helper to
  concrete receipt slices so multi-trial traces align with the interpreter
  machinery.
- **Iteration 2AM:** investigated how `filter_measurement_frames` interacts
  with `firstn` on the concrete Tsirelson trace.  Arithmetic rewrites over
  `Nat.div`/`Nat.modulo` proved fragile under the project’s mixed scopes, so
  the upcoming pass will pivot to a direct case analysis over the five-frame
  program prefix.
- **Iteration 2AN:** added the base helper `filter_measurement_frames_nil` and
  discharged the explicit `m ≤ 4` prefixes of the measurement-frame lemma,
  setting up the next iteration to tackle the remaining multi-frame cases.
- **Iteration 2AN:** proved `filter_measurement_frames_firstn_tsirelson_frames`
  by enumerating the five-step Tsirelson prefix, providing a closed-form
  description of the filtered measurement frames for every prefix length and
  clearing the way to lift the argument to repeated traces in the next
  iteration.
- **Iteration 2AO:** tried to lift the measurement-frame filter to repeated
  traces but the `firstn`/`List.concat` rewrites became unwieldy inside Coq;
  the code was rolled back to keep the build stable.  Next step: craft a more
  controlled proof strategy (likely via helper lemmas for `firstn` over
  concatenated lists) before reattempting the repeated-trace specialisation.
- **Iteration 2AP:** attempted to package the repeated-trace prefixes via a
  recursive `filter_measurement_frames_prefix` helper and a companion lemma for
  expanding `List.concat (List.repeat tsirelson_frames (S n))`.  Scope clashes
  between list append and `string_scope`’s `++` notation derailed the proof,
  so the Coq experiment was rolled back to keep the build green.  The follow-up
  task is to restate the helper entirely with `List.app` (or another unambiguous
  combinator) before reattempting the constructive repeated-prefix lemma.
- **Iteration 2AQ:** added supporting lemmas capturing the two-frame length of
  `tsirelson_measurement_frames` and a general `firstn`-over-append rewrite.
  These helper facts set up the forthcoming proof that repeated Tsirelson
  traces truncate cleanly along whole trials.  The next milestone is to use
  them to derive the explicit whole-trial prefix lemma needed by the
  chunking/interpreter machinery before tackling arbitrary streamed prefixes.
- **Iteration 2AR:** attempted to prove the whole-trial filtering lemma via a
  straightforward induction but repeatedly hit rewriting obstacles around
  `firstn` and `Nat.min`.  The proof was rolled back to keep the file
  compiling; the next pass will revisit the lemma with a better-structured
  induction (likely by recursing on the trace length first).
- **Iteration 2AR:** proved `filter_measurement_frames_firstn_repeat_whole_trials`,
  establishing that truncating repeated Tsirelson traces at multiples of the
  program length yields the expected concatenation of measurement frames.  Next
  step: feed this lemma into the chunking/interpretation pipeline so batches of
  whole trials can inherit the previously proved weighted-`S` equalities.
- **Iteration 2AS:** introduced the general `repeat_app` lemma in the Bell
  inequality development so repeated `[alice; bob]` frame lists can be split and
  normalised algebraically before applying chunking or prefix reasoning.
- **Iteration 2AS:** threaded the whole-trial filtering lemma through the
  chunking and interpreter machinery, proving that filtered receipt prefixes
  covering an integral number of Tsirelson trials map to repeated CHSH witnesses
  with matching weighted-`S`/probability sums.  The follow-up task is to extend
  the certification to non-multiple prefixes so streaming verifiers can handle
  measurement slices that end partway through a trial.
- **Iteration 2AT:** added a `chunk_pairs_measurement_frames_app` helper and a
  single-run lemma showing that any prefix of the five-instruction Tsirelson
  program already satisfies the weighted-`S`/probability equality once the
  measurement frames are filtered.  The next step is to propagate this result to
  repeated traces while avoiding the failed whole-trace induction attempted in
  earlier iterations.

With Coq (`coqc`) now installed in the container, the first concrete change is
to rework the `local` predicate as described in step (1) and then incrementally
port the existing axioms to lemmas.

## Audit Notes (Iteration 2)

- `Box` packages the CHSH probability table together with normalization and
  no-signaling equalities that must be preserved by any refactoring.
- `local` currently quantifies over arbitrary kernels `p_A` and `p_B` indexed by
  `Bit`-valued hidden variables, while `local_deterministic` hardcodes
  deterministic witnesses via total response functions `A : Bit -> Bit` and
  `C : Bit -> Bit`.
- The outstanding classical placeholder `local_deterministic_CHSH_bound` and the
  PR-box facts (`PR_norm`, `PR_nonneg`, `PR_nosig_A`, `PR_nosig_B`, `PR_S`,
  `PR_not_local`) are axioms that must be replaced with constructive proofs once
  the deterministic decomposition is available.  ✅ _Resolved in Iteration 2L._
- Completed step (1) by introducing explicit response-table records and
  rewriting `local` as a convex combination over the 16 deterministic strategy
  tables.
- Next design task: leverage the now fully constructive Bell development to
  formalise the Thiele/Tsirelson entangled strategy and integrate its receipts
  with the unified verifier.
