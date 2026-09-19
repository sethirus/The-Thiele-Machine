# Independent review of the actual relational join

Reviewed integrated `coq/kami_hw/MorphJoin.v` against the phase-7
`mc_join_loop` rule in `ThieleCPUCore.v`, the actual Kami execution helpers,
and the strengthened normalization-prefix contract. Reviewed source SHA-256:
`8dc02bace3cbd441fa3269b2abe5f9dbb6136bce523b3b52d715b7ba6ede58f5`.
This is a source review in the current workspace, separate from the frozen
container build, theorem probes, and compiled-library checks.

No concrete mismatch was found in the scoped join and retirement conclusions.
The result covers an explicitly chosen execution of the actual join rule,
followed by actual normalization and commit, from supplied phase-7 premises.

## Actual rule, matching, and cursor behavior

`join_actual_action` supplies all thirteen typed reads, all nine writes, and
the empty method-call map of the real rule. Its match condition compares the
first pair's destination word with the second pair's source word. A match
appends the first source and second destination. The `wordToNat` conversion
used by `append_pair` in the update wrapper is converted back to the same
five-bit word by `natToWord_wordToNat` in the actual-action proof; it does not
replace the hardware's truncated output index with an unbounded index.

The candidate traversal is row-major: the second cursor advances fastest,
wraps to zero at its count, and then advances the first cursor. For two
nonempty ranges the final candidate itself changes phase to 5. There is no
additional nonempty terminal-check firing. If either count is zero, one
actual firing changes phase to 5 without appending or raising overflow.
Cursor updates still occur on the empty or failure firing according to the
actual wrap expression; they are not treated as an implicit rollback.

An output pointer at capacity is allowed to pass a nonmatching candidate.
Overflow occurs only for a nonempty, matching candidate without room. Unlike
the copy rule's equality test, this rule tests unsigned `out < 16` for room.
The failure theorem covers `16 <= out < 32`, preserves all pair-vector values
and the output pointer, sets the error/code, and returns phase to zero.
These vectors are written with unchanged values; the theorem does not claim
that the action performs no register writes. The separate cursor theorem
records the updates that still occur on failure. Earlier partial output and
dispatch effects are not rolled back.

## Bounds, source aliasing, and relational order

The successful loop requires each complete input range to end at or before
append base `b`, with the current output at or above `b`. Every effective
source read is therefore below the append workspace. The low-prefix
invariant establishes that actual append writes preserve all subsequent
match decisions and output payloads. Input ranges may overlap each other;
that is compatible with the stated list-join result.

The capacity premise bounds the number of raw matching candidate outputs,
including duplicates: `b + length raw_join <= 16`. It does not assert that
admission depends on the eventual normalized length. Thus a duplicate-heavy
join whose normalized output would fit can still lie outside this successful
contract. This matches the implemented raw-intermediate capacity policy.

`candidate_indices`, `remaining_join`, and `store_pairs` are connected to the
proved actual substep and cursor induction. They are proof summaries of that
execution, not a separate executable FSM asserted to refine the physical
one. `raw_join_relational` identifies the row-major output with the explicitly
defined nested-list `relational_word_join`. Duplicates occur once per matching
candidate before normalization. The final list is exactly last-occurrence
`nodup` in that order, rather than only an equal set of pairs.

This algebraic list join is not yet a theorem identifying the entire kernel
COMPOSE operation: source module endpoints, region membership, identities,
labels, and finite-word representation need their own applicable bridge.
No pair-valid flags or descriptor-valid predicates are used as input checks
inside this rule.

## Same-execution normalization and prefix frame

`join_retirement` composes the actual loading trace with
`normalization_retirement_with_prefix`. The same final witness carries both
the ordered normalized output and `table_prefix_agrees` below `b`. Its proof
combines the join-stage low-prefix facts with the strengthened normalization
induction; it does not infer prefix preservation from an unrelated or weaker
existential execution.

The theorem states pair-table reads at precommit and the exact final commit
update map. Imported commit-frame/readout lemmas preserve those pair tables
and their old-prefix readouts through commit. Existing interval payloads
wholly below `b` therefore retain their pair content. This does not by itself
prove that every old descriptor retains its metadata: `d` is an arbitrary
five-bit word, and the actual commit truncates it to a descriptor slot and
increments it modularly. Freshness and nonaliasing of that descriptor slot
remain separate requirements.

The explicit join/normalization register frame is a precommit frame. A final
register frame must additionally account for the descriptor tables and
allocator pointers written by commit. Error and error code lie in the join
footprint; admitted join execution separately preserves their existing
values. Preserved PC and ledger values refer to the supplied phase-7 state,
not to an unproved state before instruction dispatch. Raw-output valid bits
are not cleared merely because normalization shortens the descriptor range.

## Firing counts and remaining full-refinement obligations

For nonempty ranges, join uses exactly `c1 * c2` selected rule firings. The
empty case uses one. With `n` raw matching outputs, the composed count is
`join_firings c1 c2 + 2 + outer_firings n`. The proved bound 410 follows from
separate bounds `c1,c2,n <= 16`; it is a conservative bound, not a claim that
all extreme values are jointly attainable under every source/capacity
premise. Kami's reverse label-list convention is used consistently.

The existence trace and its firing count do not establish progress under an
arbitrary scheduler, whole-module exclusivity, cycle timing, or generated-RTL
refinement. Remaining C obligations include deriving phase-7 inputs from
COMPOSE dispatch and identity routing, full descriptor/endpoint/region/label
representation, all instruction-wide capacity and failure paths, allocation
freshness, complete retirement observation including dispatch PC/mu effects,
and extraction/toolchain correspondence. No local axiom, admission, or
checker bypass appears in the reviewed source. Inherited global assumptions
remain part of the direct theorem-probe contract.
