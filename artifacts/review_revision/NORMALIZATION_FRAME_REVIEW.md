# Normalization prefix and descriptor readout review

Result: no concrete proof-contract mismatch found in this bounded source review.

The reviewer examined the nine results in `NormalizationFrame.v` and the strengthened prefix conclusions in `MorphLoading.v`, `MorphRetirement.v`, and `MorphCopy.v`, against the actual normalization/loading/copy/commit rules in `ThieleCPUCore.v`. Scope: source inspection in the development workspace; no independent rebuild.

## Findings

1. `normalization_emit_preserves_low_prefix` uses the actual emitted-table function and the established prefix invariant. Its bounds imply `k < b <= out <= i < e <= 16`, so a write at truncated `out` cannot alias a retained index `k`. This is the necessary finite-index premise; the proof does not assume non-aliasing without establishing it.
2. `normalization_outer_execution_with_prefix` carries the extra prefix equality through the actual scan/emit induction. It constructs the same selected actual-rule schedule while preserving the emitted-prefix invariant, terminal phase/end, exact output tables, register frame, and firing count. It does not infer the stronger prefix conclusion from the old weaker existential theorem.
3. The nonempty and uniform retirement theorems start this strengthened induction from identical source tables. The empty case uses the actual start and commit execution and reflexive prefix equality. Both endpoints remain actual commit-update maps; their prefix statements initially describe the supplied precommit pair-table functions.
4. `normalization_commit_preserves_prefix_reads` explicitly bridges those precommit functions to final register values. This matches the actual commit rule, whose six writes update descriptor metadata, allocator pointers, and phase, but do not write either pair table.
5. `normalization_prefix_preserves_range_readout` correctly restricts the requested interval to `a + count <= bound`. It expands the table slice and applies the pointwise prefix relation to each indexed entry. The standalone lemma is an implication under the supplied prefix relation; physical index/range interpretation comes from the bounded retirement instance.
6. `normalization_commit_other_descriptor` uses inequality against the actual truncated slot `pair_index d`. Merely requiring a different natural descriptor ID would have been insufficient because truncation can alias. The theorem does not infer descriptor freshness.
7. `normalization_commit_old_descriptor_readout` requires both the non-aliasing slot premise and that the old descriptor's base/count interval lies wholly below the preserved bound. It preserves the old pair-list readout under those hypotheses. Its readout definition deliberately ignores the valid flag, labels, endpoint semantics, and module membership. Separate validity preservation follows from `normalization_commit_other_descriptor` for the same non-target slot; semantic interpretation still needs the representation contract.
8. `morph_admitted_loading` derives prefix preservation from the actual recursively loaded tables using `loaded_table_outside` and the admitted `out + count <= 16` bound. The header has no pair-table writes. The strengthened MORPH retirement theorem composes this loading prefix relation with normalization's prefix relation. The zero-count case preserves the original pair tables through the header and empty normalization schedule.
9. `copy_retirement` composes the loader's independently proved source/destination `low_agrees` facts with normalization's pairwise prefix relation. `copy_retirement_prefix_components` extracts the two word components by `fst`/`snd`. The resulting prefix statement therefore extends through normalization, rather than remaining scoped only to raw copying. The existing source-ranges-before-append-base and raw-capacity premises are retained.

## Limits that remain load-bearing

- These are existence theorems for selected actual Kami rule schedules. They do not establish every possible schedule, fairness, arbitrary clock-time progress, or refinement of generated physical RTL.
- The statements begin at typed construction/normalization entry states. They do not prove dispatch reaches those states with the specified descriptor identities, endpoint relations, ranges, and capacity conditions.
- Old descriptor preservation applies only to slots distinct from the committed truncated slot and intervals wholly below the append base. A freshness/allocation invariant is still needed to say that all previously allocated descriptors satisfy these conditions.
- Prefix preservation concerns pair content. It does not itself establish validity-table ownership, remove stale valid bits above the final allocator pointer, supply missing labels, enforce a region-membership filter, or prove tensor/category laws.
- The admission policy still uses raw intermediate capacity. The stronger frame does not make rejected raw constructions admissible merely because normalization would shrink their mathematical output.
- Partial state changes on failure remain governed by the explicit construction error contracts. None of these successful-prefix statements implies rollback.

## Reviewed source identities

| File | SHA-256 |
| --- | --- |
| `coq/kami_hw/NormalizationFrame.v` | `c244e89c0c52531e65dfd3fc7e8ae8aae81aa6ff49102720648e016b15f1d527` |
| `coq/kami_hw/MorphLoading.v` | `22a0cc637111f4a2c64a4bb73bb2d7c7e35620234bda987b3f9543b83b1e4a5f` |
| `coq/kami_hw/MorphRetirement.v` | `5c882bdd49f332942d34dea4a27f522b5bd5bef4ead82d352e1707bfed47ba6e` |
| `coq/kami_hw/MorphCopy.v` | `164f3e13513da990ecb0702c1cdcc296c396082f6fd0732a74849dd259739ca3` |
| `coq/kami_hw/ThieleCPUCore.v` | `185c23f622fbeda4cb0a582079fe34f44ddfbca93f5f489bf280a587b588a6b3` |

Review timestamp (UTC): 2026-09-12T22:32:31.199979+00:00
