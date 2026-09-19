# Source review of normalization scan and selection lemmas

Source review: NormalizationLoop.v against NormalizationSteps.v and its update maps. This is a review in the same environment; it is not a separate-environment reproduction.

The scan invariant `scan_seen src dst i lo count` is an existential Boolean test over the half-open natural index interval [lo,lo+count). Its extension adds exactly the next comparison. At j=end, the actual guarded comparison contributes false and leaves the accumulated duplicate flag unchanged. Separate update-map equations identify phase 8 during scanning, phase 9 at the terminal comparison, and the next scan pointer. These equations use `M.union updates old` and the exact maps from the earlier actual-action proofs.

The final `normalization_terminal_emit_selection` also identifies the terminal duplicate Boolean with the head contribution in the nodup recurrence. Its two cases use the established scanned-slice membership equivalence.

The selection theorem proves equality with Coq's last-occurrence nodup, including order, rather than only membership or NoDup. It is a theorem about the selected original table slice. It does not prove that a sequence of actual emits has already materialized that slice in the output table. The slice theorems are valid even for aliased indices outside the admitted physical range because they refer to the same truncated table function on both sides; interpreting them as distinct physical cells needs the separate bounds.

The emitted-table wrappers match the source and destination entries of the real emit update map. Under out<=i<candidate<16 and a later scan interval within the table, the unread cells and the candidate cell retain their previous values. Extensional agreement over those cells then preserves scan_seen. These are the relevant ingredients for relating later scans to the immutable raw slice after compaction.

No concrete mismatch was found in these statements. The source does not assert an arbitrary SemAction inversion theorem, Step/Multistep composition, scheduling fairness, or completed retirement. The next load-bearing invariant must join the selected output prefix, unchanged raw suffix, duplicate interval, and pointer bounds throughout the actual rule sequence. Dispatch initialization, commit allocation, failure behavior and the wider representation contract remain additional obligations.

Compilation, theorem assumption reports and compiled-library checking are recorded separately in STATUS.md and the raw checkpoint evidence.
