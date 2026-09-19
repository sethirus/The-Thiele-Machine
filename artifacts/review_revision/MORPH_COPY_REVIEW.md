# Independent review of the physical copy-rule proof

Reviewed the staged `MorphCopy.v` from `/tmp/thiele-resume/MorphCopy.v` for
integration as `coq/kami_hw/MorphCopy.v`, against the actual `mc_copy_loop`
rule in `ThieleCPUCore.v` and the imported normalization/commit contract.
This is a same-workspace source review, separate from compilation, theorem
probes, and compiled-library checking.

No concrete mismatch was found in the scoped actual-copy execution and
normalization-composition conclusions.

## Actual action and control behavior

`copy_actual_action` supplies all thirteen typed reads of the actual phase-4
rule and specifies its nine writes and empty method-call map. The supplied
index, done, full, blocked, and overflow definitions match the real rule.
The action prioritizes the first range while its cursor remains below its
count, then copies the second range. It does not alternate or interleave the
two lists.

The terminal firing occurs after both cursors have reached their counts.
It preserves the pair source, destination, and valid vectors, output pointer,
error latch, and error code, and changes phase to 5. It nevertheless leaves
`mc_i = c1` and writes `mc_j = S c2`, exactly as the actual unconditional
cursor update requires. The proof includes this terminal extra firing rather
than stopping the trace immediately after the last copied pair. Empty ranges
are handled by the same terminal behavior.

`copy_capacity_failure` proves that a not-done action at output pointer 16
sets error and `ERR_COUPLING_INVALID`, returns phase to zero, and preserves
the output pointer and all three pair-vector values. This is value
preservation, not absence of register writes: the real rule writes the
unchanged vectors. The cursors still advance according to which range is
selected, as separately stated in `copy_cursor_updates_even_when_blocked`.
The result does not assert rollback of earlier copies or earlier dispatch.

The actual full guard tests equality with 16, not every unsigned value above
16. The admitted-loop theorem excludes those larger pointers through its
natural-number bounds; it does not generalize this fault lemma to arbitrary
malformed pointer values.

## Source/output aliasing and raw-list order

The loop uses an explicit source-before-output condition:
`a1 + c1 <= b`, `a2 + c2 <= b`, `b <= out`, and `out + remaining <= 16`.
Every effective source index is therefore strictly below `b`, while every
append target is at least `b`. `low_agrees` and
`append_pair_preserves_low` show that successive actual writes preserve the
source observations. The four-bit source-base additions and truncated cursor
indices match the intended natural indices under these bounds.

The two input ranges may overlap each other. This is consistent with the
claim: the raw result is their concatenation, including repetitions, rather
than a disjoint union. The proof does not silently assume that a source can
be overwritten safely when it aliases the append workspace.

`store_pairs` is connected to the exact table writes of the actual execution.
Its slice theorem establishes the complete raw appended list. The admitted
copy result also proves that all pair-table positions below `b` retain their
original values. Its loop frame retains other registers outside the named
nine-write footprint, including the source descriptors and write base needed
for subsequent normalization.

## Normalization composition and its limits

`copy_retirement` composes that actual copy trace with the actual
normalization trace and commit. The final appended range is exactly the
ordered, last-occurrence `nodup` of the first input slice followed by the
second input slice. The final state explicitly uses the actual descriptor
commit map; pair-table reads are stated at precommit and survive that commit
by the imported frame result.

The copy-stage `low_agrees` results are not included in the conclusion of
`copy_retirement`. The imported normalization theorem's register frame
excludes the entire pair-vector registers and does not by itself establish
an elementwise prefix frame through normalization. Consequently this
composed theorem must not be cited as already proving preservation of every
old allocated pair below `b`, despite the copy-stage result and the shape of
the actual compaction algorithm. A further preservation lemma can close
that explicit remaining output-contract obligation.

The copy routine can serve identity-COMPOSE and MORPH_TENSOR paths only after
a dispatch/representation theorem establishes these phase-4 inputs and their
meaning. The present theorem does not itself prove which operand is an
identity, tensor endpoint renaming, labels, region membership, valid input
slots, descriptor freshness, or graph allocation. Descriptor truncation and
modular increment remain visible in the inherited commit map. Valid bits
written during raw copy are not cleared merely because normalization reduces
the descriptor count.

## Selected firing counts

Copying `n = c1 + c2` pairs uses exactly `n + 1` selected copy-rule firings,
including the terminal check, and at most 17 under the stated capacity
bound. Adding normalization start, scan/emit iterations, and commit gives
exactly `n + 3 + outer_firings n` selected rule firings and the conservative
upper bound 171. These formulas include the all-empty case, which takes one
copy terminal firing and two normalization/commit firings.

The traces use Kami's reverse label-list convention consistently. Their
existence does not imply arbitrary-scheduler termination, whole-module
exclusivity, physical clock timing, or extraction/generated-RTL refinement.
No local axiom, admission, or checker bypass appears in the reviewed source;
inherited assumptions remain part of the direct probe contract.

## Addendum: integrated prefix strengthening

The integrated 31-result version strengthens `copy_retirement` with old-prefix agreement in the same execution. It invokes `normalization_retirement_with_prefix` and composes that agreement with the copy-stage `low_agrees` premises. The earlier paragraph identifying the missing final-prefix conclusion applies to the reviewed 30-result version and is superseded for this specific obligation. `NORMALIZATION_FRAME_REVIEW.md` independently reviews the strengthened source and records its hash. Dispatch, descriptor freshness, full representation and scheduling obligations remain.
