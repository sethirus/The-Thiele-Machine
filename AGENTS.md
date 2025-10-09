# Agent Working Log
## Milestones
- [x] Install Coq toolchain in container. (Completed Iteration 1)
- [x] Refactor `BellInequality.v` classical model as deterministic mixture. (Completed Iteration 2A)
- [x] Port CHSH bound proof to constructive lemmas.
- [x] Eliminate PR-box axioms with constructive proofs.
- [ ] Formalise the Thiele/Tsirelson advantage and connect Coq witnesses to the runtime receipt verifier.

## Iteration 1 (completed)
- Installed Coq 8.18.0 via apt to enable local compilation of proofs.
- Captured container setup notes in this log for future iterations.

## Iteration 2 (current)
- Audited `coq/thielemachine/coqproofs/BellInequality.v` structure:
  - `Box` encodes probability tables with normalization and no-signaling witnesses.
  - `local` ranges over an explicit list of 16 deterministic response-table strategies
    with convex weights.
- Classical bound now proved constructively; remaining axioms are
  `local_deterministic_CHSH_bound` and the PR lemmas.
- Added deterministic helper definitions `strategy_E`/`strategy_S` and a coarse
  bound lemma `strategy_S_bound` to expose the classical CHSH extremal values.
- Attempted to push the `local` convex decomposition through the correlator but
  ran into Coq simplification issues over `Q` arithmetic (e.g. rewriting sums of
  zero-weight terms).  Documented the obstacle and the need for a custom `Q`
  ring instance before proceeding.
- Introduced `strategy_E_from_indicators` linking the point-mass response tables
  to the correlator evaluation as a first algebraic helper lemma.
- Investigated linearity lemmas for `sum_bit`/`sum_bit2`/`sum_strategies` but
  ran into the `Q` equality issue (`=` vs `Qeq`) when trying to rewrite sums
  with ring tactics.  Documented the obstacle so the next coding session can
  decide whether to port the equalities to `Qeq` or route the reasoning through
  `Q2R`.
- Added `Qabs` helper lemmas (`Qabs_nonneg`, `Qabs_le_upper`, `Qabs_le_lower`)
  to prepare the absolute-value reasoning needed once the convexity lemmas are
  in place.
- Replaced the `sum_strategies` fold with an explicit list recursion and proved
  linearity/scale lemmas together with `Qeq` corollaries so the convex
  decomposition can be pushed through `E`/`S` in the next step.
- Introduced `sum_bit_unfold`/`sum_bit2_unfold` lemmas so that later
  iterations can expand correlator sums explicitly when manipulating the local
  mixture witnesses.
- Added summation extensionality helpers (`sum_bit_ext`, `sum_bit2_ext`,
  `sum_strategies_ext`) together with `sum_bit2_sum_strategies` and used them to
  prove `local_E_as_convex`, expressing each correlator as a convex combination
  over deterministic strategies.
- Proved `local_S_decompose`/`local_S_as_convex`, so the full CHSH expression
  now rewrites as a convex combination over deterministic strategy tables.
- Added `Qmult_le_nonneg_l` together with weighted-sum upper/lower lemmas to
  manipulate convex mixtures directly over the explicit strategy list.
- Eliminated the `local_CHSH_bound` axiom entirely by combining the convex
  decomposition lemmas with the weighted inequality helpers and careful
  `setoid_rewrite` steps over `Qeq`.
- Retired the remaining PR-box axioms (`PR_norm`, `PR_nonneg`, `PR_nosig_A`,
  `PR_nosig_B`, `PR_S`, and `PR_not_local`) by performing exhaustive case
  analyses over the explicit probability table and reusing the classical CHSH
  bound to refute locality.
- Next action: build the constructive Thiele advantage (Tsirelson bound) and
  thread the resulting witnesses into the runtime receipt verification pipeline.
- Added a rational Tsirelson-style box `TsirelsonApprox` whose correlators
  reproduce an approximate 2·sqrt(2) CHSH violation without axioms, together
  with constructive proofs that `Qabs (S TsirelsonApprox) = (4#1) * gamma` and
  that the box is not local.
- Next action: lift the approximate Tsirelson witness into the receipts
  pipeline so that simulated CHSH runs emit certificates, and explore tightening
  the rational approximation or extending the argument to the fully sighted
  Thiele construction.
- Iteration 2N: introduced a parameterised `ReceiptFrame`/`receipts_sound`
  bridge in `BellInequality.v` to start linking the Bell witness reasoning with
  the concrete step receipts interface.
- Added supporting reflexivity lemmas in `ThieleMachineConcrete.v` so that the
  concrete receipt equality checks will be easier to instantiate during the
  bridge specialisation.
- Next action: extend the bridge with CHSH-specific frames (corresponding to the
  Tsirelson witness run) and hook the resulting lemmas into the receipt
  generation pipeline.
- Iteration 2O: instantiated the abstract receipts bridge with the concrete
  step function, introducing `concrete_receipt_frame` and
  `concrete_receipts_sound` so the deterministic Coq receipts line up with the
  runtime witnesses.
- Iteration 2P: taught `scripts/verify_truth.sh` to build the recorded program
  and receipt list inside the generated Coq file, rewriting the trace to
  `concrete_receipts_of` and discharging the soundness goal with
  `concrete_receipts_sound` instead of per-step reflexivity certificates.
- Next action: specialise the bridge to the Tsirelson CHSH program and thread
  the resulting lemmas and witnesses into the receipt generation pipeline so
  the recorded CHSH runs reuse the mechanised proofs end-to-end.
- Iteration 2Q: added a concrete Tsirelson program/receipt scaffold inside
  `BellInequality.v`, a receipt generator script plus example JSON trace, and
  taught `verify_truth.sh` to load the project path and emit `PNEW` naturals so
  the sample receipts check end-to-end with `concrete_receipts_sound`.
- Iteration 2R: proved that the mechanised Tsirelson receipts replay the exact
  instruction sequence and observation stream with zero µ-budget usage,
  setting up the bridge to the rational Tsirelson correlators for the next
  iteration.
- Iteration 2S: characterised the Tsirelson receipt states, fixing the pre- and
  post-state sequences to the expected PC progression so the next step can
  relate the concrete trace to the rational Tsirelson correlators.
- Iteration 2T: recorded per-index lemmas for the Tsirelson program and receipt
  events via `nth_error`, giving a precise handle on the measurement steps.
- Next objective: interpret the `alice_measurement` and `bob_measurement`
  receipts as CHSH outcomes and tie them to the rational Tsirelson witness.
- Iteration 2U: captured the full `alice_measurement` and `bob_measurement`
  receipt records (instruction, pre/post states, and observations) so future
  proofs can directly recover the deterministic witnesses for each
  measurement.
- Next objective: relate these concrete receipts to the Tsirelson correlator
  table by extracting the CHSH outcome bits and comparing them with the
  rational witness.
- Iteration 2V: defined reusable `tsirelson_alice_receipt`/`tsirelson_bob_receipt`
  records, mapped them into `BridgeReceiptFrame`s, and proved a dedicated
  `receipts_sound` witness for the measurement subtrace.  This isolates the
  two-step CHSH slice needed for the upcoming correlator extraction.
- Next objective: interpret the measurement frames as CHSH outcomes by
  introducing explicit output bits and linking them to the rational
  `TsirelsonApprox` box.
- Iteration 2W: exposed each Tsirelson measurement frame component (instruction,
  pre/post states, and observation fields) via dedicated lemmas so subsequent
  proofs can attach explicit CHSH outcome bits to the recorded receipts
  without re-opening the concrete definitions.
- Next objective: define the CHSH outcome bits carried by the measurement
  frames and connect them to the rational `TsirelsonApprox` correlator values.
- Iteration 2X: introduced a `CHSHTrial` record together with helper lemmas
  (`trial_S_cases`, `trial_S_Qabs`, `trials_S_app`) to capture the ±1
  contributions of individual measurement outcomes and aggregates. These
  scaffolding lemmas prepare the bridge that will tie the recorded receipts to
  the constructive Tsirelson correlator in subsequent iterations.
- Next objective: instantiate the `CHSHTrial` scaffolding with the concrete
  Tsirelson measurement frames by extracting their input/output bits from the
  receipts and relating the resulting trials to `TsirelsonApprox`.
- Iteration 2Y: introduced a `FrameTrialInterpreter` abstraction that maps
  pairs of receipt frames to `CHSHTrial` witnesses, specialised it to the
  Tsirelson measurement steps, and proved the singleton trial lemma
  `tsirelson_trials_S_of` together with the receipts soundness witness.  This
  sets the stage for attaching concrete bit interpretations to the recorded
  measurement frames.
- Next objective: define the concrete bit interpretations for the Tsirelson
  measurement receipts and relate the resulting trials to the
  `TsirelsonApprox` correlator values.
- Iteration 2Z: embedded the measurement setting/outcome bits into the
  Tsirelson receipt certificates, taught the concrete step semantics and JSON
  generator to emit the same metadata, and defined interpreter lemmas that
  recover those bits from the Coq frames.
- Next objective: relate the interpreted trials to the rational
  `TsirelsonApprox` box so the recorded CHSH sample can be compared with the
  constructive correlator values.
- Iteration 2AA: proved that the interpreted Tsirelson measurement trial
  contributes `+1` to `trials_S` and that the recorded settings/outcomes
  occur with strictly positive probability in `TsirelsonApprox`,
  establishing pointwise agreement between the receipts and the
  constructive box.
- Next objective: lift these pointwise identities to aggregates of
  `CHSHTrial`s so that receipt-derived samples can be compared directly
  against the Tsirelson correlator table.
- Iteration 2AB: introduced `trial_probability`/`trials_probability` for
  aggregating CHSH trials, proved the Tsirelson interpreter lemmas for the
  singleton receipt slice, and established positivity for the aggregated
  probability witness.
- Next objective: relate `trials_S` and `trials_probability` for finite
  traces so that batches of Tsirelson receipts can be compared directly with
  the constructive correlator table.
- Iteration 2AC: added the weighted CHSH sum `trials_weighted_S`, bounded it
  against the aggregated probability mass, and proved that the Tsirelson
  singleton receipts satisfy the equality witness.
- Next objective: lift the weighted-sum machinery to multi-trial receipt
  batches by expressing their `S` contributions in terms of Tsirelson
  probabilities, setting up the comparison with the constructive correlator
  table.
- Iteration 2AD: established `tsirelson_trials_weighted_S_repeat_probability`
  so repeated Tsirelson measurement batches derived from receipts have
  constructively equal `S` and probability aggregates.  This gives the first
  reusable lemma for multi-trial receipt analysis.
- Next objective: formalise the frame-chunking operation that groups receipt
  traces into repeated Tsirelson measurement pairs and relate those batches to
  the constructive Tsirelson correlator witnesses.
- Iteration 2AE: introduced `chunk_pairs` for pairing measurement frames and
  proved that flattening repeated Tsirelson frame lists reconstructs the
  canonical measurement-pair trace.  This establishes the combinatorial step
  needed before aggregating multi-trial receipts.
- Next objective: apply the chunking helper to concrete receipt slices so the
  interpreter lemmas can reason about multi-trial traces beyond a single
  measurement pair.
- Iteration 2AF: applied the chunking helper to the Tsirelson measurement
  frames, showing that interpreting the chunked lists yields repeated
  `tsirelson_trial` witnesses and that their weighted CHSH sums coincide with
  the aggregated probabilities.  This connects the combinatorial pairing with
  the probabilistic lemmas from previous iterations.
- Next objective: lift these chunked-trial identities to arbitrary receipt
  prefixes so repeated verifier runs can be compared directly with the
  constructive Tsirelson correlator table.
- Iteration 2AG: added the `interpret_trials_firstn` lemma so receipt
  interpretations commute with `firstn`, but the explicit chunked-prefix
  equality remains outstanding and is carried forward to the next session.
- Iteration 2AH: attempted to prove that `chunk_pairs` commutes with even-length
  prefixes and to specialise it to the Tsirelson measurement frames, but the
  induction exposed stubborn `firstn`/`concat` simplification issues.  Rolled
  the Coq changes back after confirming the dead end and documented the open
  problem instead.
- Next objective: design a prefix lemma (likely by first expanding the repeated
  frame concatenation) that avoids the `firstn` simplification pitfall so the
  weighted CHSH aggregates can be pushed to partial Tsirelson receipt batches.
- Iteration 2AI: attempted to formalise the chunk-prefix lemma via
  `chunk_pairs_firstn`, but rewriting inside the receipt trace stalled and the
  experiment was rolled back without committing the new helper.
- Next objective: design a fresh proof strategy for the chunk-prefix lemma so
  partial receipt batches can still be related to the Tsirelson witnesses in a
  future iteration.
- Iteration 2AJ: proved a `chunk_pairs_firstn_repeat` lemma for repeated
  `[alice; bob]` lists, specialised it to the Tsirelson measurement frames, and
  derived the `tsirelson_trials_weighted_S_chunk_measurement_frames_firstn`
  equality so every even-length prefix of the canonical receipt trace preserves
  the weighted CHSH witness.
- Next objective: leverage the new prefix lemma to analyse streamed receipt
  prefixes beyond repeated batches (e.g. via `firstn` on interpreter outputs)
  and connect the result to the pending chunk-prefix comparison for arbitrary
  verifier logs.
- Iteration 2AK: generalised the chunk-prefix reasoning to arbitrary prefix
  lengths via `chunk_pairs_firstn_repeat_general` and the corresponding
  Tsirelson lemmas, so every streamed prefix preserves the weighted `S`/
  probability equality.
- Next objective: propagate the streamed-prefix equalities through the
  interpreter outputs to cover arbitrary verifier logs against the constructive
  Tsirelson trials.
- Iteration 2AL: introduced a boolean filter for identifying measurement
  frames, proved it selects the canonical `[alice; bob]` slice from a single
  Tsirelson run, and lifted it over repeated traces to prepare for reasoning
  about streamed verifier logs that interleave setup and measurement steps.
- Next objective: combine the measurement-frame filter with prefix reasoning
  (`firstn`) so partial verifier logs can be reduced to the canonical
  measurement-frame prefixes before applying the chunking lemmas.
- Iteration 2AM: attempted to characterise `filter_measurement_frames` on the
  `firstn` prefixes of `tsirelson_frames`.  The direct arithmetic approach ran
  into cumbersome `nat`/`Q` scope interactions, so the plan is to restate the
  lemma via explicit case analysis on the first five frames in the next
  iteration.
- Iteration 2AN: added the base helper `filter_measurement_frames_nil` and a
  direct enumeration lemma for small `m` prefixes so future work can focus on
  handling the remaining multi-frame cases.  Next objective is to extend the
  prefix reasoning beyond the enumerated base cases.
- Iteration 2AN: proved `filter_measurement_frames_firstn_tsirelson_frames` by
  an explicit case split over the five-instruction Tsirelson prefix, showing
  that every prefix reduces to the expected truncation of
  `tsirelson_measurement_frames`.  Next objective: lift this prefix result to
  repeated traces (e.g. `List.concat (List.repeat tsirelson_frames n)`) so
  streamed verifier logs can normalise measurement subsequences before
  applying the chunking lemmas.
- Iteration 2AO: attempted to generalise the measurement-frame filter to
  repeated Tsirelson traces, but the `firstn`/`List.concat` rewrites could not
  be normalised reliably inside Coq.  Rolled the code back to the previous
  working state; the convex-prefix lemma remains outstanding for a future pass.
  Next objective: design a more robust combinatorial proof (perhaps via
  auxiliary `firstn_app_le` helpers) before retrying the repeated-trace
  specialisation.
- Iteration 2AP: tried to encode the repeated-trace prefixes via a recursive
  `filter_measurement_frames_prefix` helper and a supporting
  `concat_repeat_tsirelson_frames` lemma.  Ran into scope collisions between
  list and string concatenation (the global `Open Scope string_scope` makes
  `++` ambiguous) and could not stabilise the Coq proof without breaking the
  build.  Reverted the code to keep the tree compiling; the next pass needs a
  cleaner formulation of the prefix helper (possibly phrased entirely with
  `List.app`) before reattempting the constructive lemma.
- Iteration 2AQ: added foundational helpers (`tsirelson_measurement_frames_length`
  and a general `firstn_app_ge` lemma) to prepare the repeated-prefix proof by
  making list lengths and prefix rewrites explicit.  Next objective: use these
  lemmas to construct the whole-trial truncation result for repeated traces so
  the chunking/interpreter machinery can reason about streamed prefixes.
- Iteration 2AR: explored proving the whole-trial filter lemma by induction on
  the receipt count but ran into stubborn `firstn`/`Nat.min` simplification
  issues even after several rewrites and helper lemmas.  Rolled the code back
  to keep the tree building and recorded the roadblock so the next pass can
  revisit the argument (likely by structuring the induction on the trace length
  before stepping over the trial count).
- Iteration 2AR: proved the whole-trial truncation lemma
  `filter_measurement_frames_firstn_repeat_whole_trials`, showing that any
  repeated Tsirelson trace truncated at whole-program boundaries reduces to the
  expected concatenation of measurement-frame pairs.  Next objective: push this
  result through the chunking lemmas so the interpreter can reason about batched
  CHSH trials derived from repeated receipt logs.
- Iteration 2AS: added the `repeat_app` helper lemma in the Bell inequality
  development to normalise repeated `[alice; bob]` traces explicitly, setting
  the stage for upcoming prefix and chunking arguments.
- Iteration 2AS: specialised the whole-trial truncation lemma through the
  chunking and interpreter machinery so filtered receipt prefixes map to
  repeated Tsirelson trials with matching weighted `S`/probability witnesses.
  Next objective: extend the argument to non-multiple prefixes so streamed
  verifier logs can be certified even when the measurement slice ends mid-trial.
- Iteration 2AT: factored a `chunk_pairs_measurement_frames_app` helper and
  proved a single-run lemma showing that any prefix of the canonical
  Tsirelson program (up to the first measurement pair) already satisfies the
  weighted `S`/probability equality after filtering. The follow-up task is to
  lift this result from one execution block to repeated traces without
  reintroducing the clunky induction that previously stalled.
