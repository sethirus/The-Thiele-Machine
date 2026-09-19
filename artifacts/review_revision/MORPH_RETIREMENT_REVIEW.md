# Independent review of MORPH loading and retirement

Reviewed `coq/kami_hw/MorphLoading.v` and `MorphRetirement.v` against the actual
`mc_morph_header` and `mc_morph_loop` rules in `ThieleCPUCore.v`, and the
normalization execution, list-content, and commit dependencies. This is a
source review in the current workspace. The integrated build, direct
assumption probes, and compiled-library checks provide separate validation.

No concrete mismatch was found between the scoped theorem conclusions and
the reviewed actual-rule semantics. The main result gives a selected actual
Kami execution from phase 1 through header, raw loading, normalization, and
commit to phase 0. Its observation is an ordered list of raw memory pairs,
not the full kernel MORPH result.

## Header and failure behavior

The six typed reads and six writes of `morph_header_actual_action` match the
real header rule. `morph_fits` retains the actual finite-word subtraction,
zero extension, right shift, and unsigned comparisons. Raw count is read
through the seven-bit memory index and is truncated to five bits only for
the subsequent loop register.

`morph_header_failure` states properties of the actual header update map:
error becomes true, error code becomes `ERR_COUPLING_INVALID`, and phase
becomes zero. The corresponding header action/substep theorem supplies the
execution when its typed-read premises hold. Failure also writes the pair
count, read pointer, and loop index. It does not roll back any effects from
an earlier instruction dispatch. The header frame preserves the pair tables
and unrelated registers; no claim of transaction-wide rollback is made.

On admitted input the header preserves the existing error latch and error
code, including an already true error flag. Neither the actual header nor
the load rule requires that flag to be clear. The proof therefore cannot be
read as guaranteeing that the subsequent instruction-fetch rule is enabled.
An admitted zero raw count goes directly to normalization phase 5 and
executes no load iterations.

## Raw load loop and bounds

The actual load action reads two consecutive memory words, writes one source
and destination entry plus a true valid bit, advances the read pointer by
two and the output/index pointers by one, and selects phase 5 exactly on the
last pair. The loop proof reestablishes these typed reads after each real
substep. `loaded_table` summarizes that proven execution; it is not supplied
as an alternative implementation in place of the Kami rule.

The generic loop theorem records the exact finite-word behavior even without
a bound on the starting output pointer. The raw-slice and admitted-loading
theorems add `out + count <= 16`, which prevents aliasing of pair slots and
supports the inside/outside table lemmas. The header count is explicitly
identified with `natToWord 32 count`, with `count <= 16`; this justifies its
five-bit truncation in the applicable composed theorem.

The memory observation deliberately retains `wplus` on 32-bit addresses and
`mem_index` truncation to seven bits. There is no theorem here that all source
addresses are ordinary, nonwrapping natural addresses. In particular,
`morph_fits = true` alone should not be substituted for a proof that
`base <= 127`: the actual subtraction `127 - base` is modular. The composed
result remains correct at such values because its right-hand side uses the
same word arithmetic. An ISA dispatch bridge can supply the narrower
seven-bit operand contract where required.

## Composition, content, and frames

`morph_retirement` explicitly requires phase 1, matching initial write base,
write pointer, and pair-next pointer `b`, the admitted header/count conditions,
`b + count <= 16`, and the typed memory, pair, valid, and descriptor registers.
It composes the header/loading trace with the actual bounded normalization
trace, then commits using the real six-write descriptor update map. This is
a selected `Multistep thieleCore`, with Kami's reverse label-list convention
handled correctly by the composition theorem.

The resulting list is exactly last-occurrence `nodup` of
`raw_memory_pairs mem base count`. No source/destination module-region
membership filter, arbitrary coupling label, or semantic property checker is
inserted into that observation. The source headers explicitly exclude those
identifications. Pair-table reads are stated at precommit and survive commit
by the imported commit-frame theorem.

The combined frame includes header, load, and normalization writes, then
adds descriptor tables and allocator pointers for the final state. It
preserves memory, PC, ledger, and other registers outside that footprint from
the phase-1 state. Error and error code are in the header footprint; their
admitted-case preservation is separately available. Valid bits written by raw
loading are not cleared merely because normalization shortens the descriptor
range. The main result does not assert that exactly the compacted range is
marked valid.

Descriptor index `d` remains an arbitrary five-bit word. Commit uses its real
four-bit truncation and modular increment. Descriptor freshness, reservation
of slot zero, and absence of pointer wrap are not inferred from this theorem.
Those allocation conditions still require the dispatch/representation
contract.

## Firing count and remaining scope

The selected execution has `count + 3 + outer_firings count` rule firings:
one header, `count` loads, normalization start, the complete scan/emit loop,
and commit. This gives three firings for count zero and at most 171 for
count at most 16. It is a count of the constructed rule schedule, not a
physical-clock bound under arbitrary scheduling.

Remaining full-refinement obligations include establishing the phase-1
premises from ISA dispatch, capacity and failure behavior across the entire
instruction, descriptor freshness, region/endpoint/label representation,
COMPOSE and MORPH_TENSOR execution, scheduling assumptions or stronger
progress/determinism results, and the extraction/generated-RTL connection.
The reviewed source does not claim those conclusions. No local axiom,
admission, or checker bypass appears in these new files; inherited global
assumptions must be preserved in the direct probe reports.
