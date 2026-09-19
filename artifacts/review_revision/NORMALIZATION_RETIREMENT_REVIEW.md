# Independent review of normalization retirement

Reviewed `coq/kami_hw/NormalizationRetirement.v` against the four actual
normalization rules in `ThieleCPUCore.v` and their `NormalizationStart`,
`NormalizationSteps`, `NormalizationExecution`, `NormalizationScanExecution`,
`NormalizationLoop`, and `NormalizationPrefix` dependencies. This is source
review in the current workspace. Integrated compilation, assumption probes,
and compiled-library checking are separate evidence.

No concrete mismatch was found in the claimed bounded normalization result.
The file establishes a selected finite execution of the real Kami rule bodies,
including the complete outer loop and commit. It does not establish full
instruction dispatch-to-retirement refinement or arbitrary-scheduler progress.

## Actual execution and loop connection

The outer loop uses `scan_complete_state` only through a theorem that supplies
its actual `Multistep thieleCore` execution. That trace includes the terminal
scan firing at `j = e`. Each following emit is the imported actual
`normalization_emit_actual_substep`, with all seven typed register reads
reestablished after scanning. The induction reestablishes the next candidate's
phase, pointers, cleared duplicate flag, and physical source/destination
vectors. It therefore does not assume that an unrelated Gallina normalizer
implements the FSM.

`normalization_multistep_trans` concatenates labels in the order required by
Kami's `Multi` constructor: later execution labels precede earlier labels.
The constructed final trace contains start, each complete scan and emit, and
commit in execution order, with labels stored in reverse order. The imported
step lifting uses singleton, no-call actual rule substeps. It neither omits a
method call nor assumes a hidden environment response.

The nonempty case inducts on the strictly decreasing natural `e - i`. The
empty case reuses the actual two-firing start/commit theorem. The final
`normalization_retirement` theorem covers both cases under `b <= e <= 16`
and nine typed old-register premises, starting at normalization phase 5.
It is an existence theorem for a chosen schedule from those states. It is not
an assertion about all schedules, reset reachability, or all states reachable
from an admitted opcode.

## Ordered list result and frame

The emitted-prefix/raw-suffix invariant is connected to each actual table
update. Its bounds ensure compaction writes at or before the current input
candidate, retaining the unread raw suffix. The scanner tests for a later
matching pair, so retaining only candidates without a later match implements
Coq's last-occurrence `nodup`, with the surviving pairs in original order.
For example, raw `[a; b; a]` selects `[b; a]`, rather than first-occurrence
order `[a; b]`.

The terminal theorem states exact list equality, not only set membership or
absence of duplicates. It records the physical pair-table reads in
`precommit`; `normalization_commit_pair_tables` proves those tables survive
the commit. The explicit final state is the actual commit update map unioned
with that precommit state, so the list result refers to the final physical
table content as well.

`outer_frame` correctly includes the eight possible outer-loop register
writes. It preserves all other registers through start and the complete
scan/emit loop. `normalization_committed_frame` adds the five descriptor and
allocator table/pointer registers written at commit; phase was already in
the outer footprint. The resulting frame preserves PC, ledger, error,
ordinary data, and all other register names outside the stated footprint.
It does not mean those fields equal their values before opcode dispatch.
The whole source/destination vector registers are in the footprint; this
frame alone is not an elementwise preservation theorem for every table slot
outside the admitted workspace.

## Finite-width contract and descriptor limitations

All list candidates and effective table writes lie below 16. Natural bounds
also keep the five-bit scan, candidate, endpoint, and compacted-output values
from wrapping: the terminal scan or reset next-scan pointer may reach 17,
which still fits five bits. The terminal scan at endpoint 16 computes a
truncated vector index but gates its equality contribution with the false
in-range flag, matching the actual rule.

The committed count is exactly `out - b` under `b <= out <= 16`, established
by `normalization_descriptor_count_exact`. The committed maps retain the
real four-bit truncations `pair_index d` and `pair_index b`, and the real
five-bit increment of descriptor pointer `d`.

There is deliberately no descriptor-admission or freshness premise on `d`.
Consequently this theorem permits truncation to an existing descriptor slot
and modular descriptor-pointer wrap, and proves their exact effect rather
than ruling them out. Likewise, the empty case permits `b = e = 16`: its
stored four-bit descriptor base is zero and its count is zero. This is an
exact representation fact, not a proof that a positive-length range beginning
at 16 is admissible. Pair-valid flags and coupling labels are not checked by
these normalization rules; the theorem normalizes the supplied table pairs
without adding those missing representation contracts.

## Firing count and remaining physical obligations

For a candidate with `k = e - i` raw positions remaining, the selected trace
uses `k - 1` in-range scans, one terminal scan, and one emit, totaling `k + 1`.
Thus `outer_firings n` satisfies `2 * outer_firings n = n * (n + 3)`.
Adding start and commit gives at most 154 selected rule firings when
`n <= 16`; the empty case uses two. This is not a clock bound in the presence
of scheduler stuttering or unrelated rule firings.

Remaining obligations for the requested full physical refinement include
establishing these phase-5 premises from admitted MORPH/COMPOSE/MORPH_TENSOR
dispatch and data-loading/joining runs; endpoint, region, label, and valid-slot
representation; descriptor freshness and all capacity/error paths; a complete
instruction retirement observation with PC/mu behavior; scheduling/progress
conditions as appropriate; and the extraction/RTL/toolchain connection. None
of these follows merely from the new normalization theorem. The source
header preserves the existence-schedule scope. No new local axiom,
admission, or proof-checking bypass appears in the reviewed file; inherited
global assumptions remain an obligation of the direct probe reports.
