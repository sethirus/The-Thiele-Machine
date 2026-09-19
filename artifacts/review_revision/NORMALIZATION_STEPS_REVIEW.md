# Independent review of NormalizationSteps.v

Reviewed source: `coq/kami_hw/NormalizationSteps.v`, `NormalizationStart.v`, actual rules in `ThieleCPUCore.v:2027-2106`, widths in `ThieleTypes.v`, and Kami `Semantics.v` definitions. This is source review only; compilation and assumption reports are separate evidence. No source was edited and no tests were run for this review.

## Finding

No concrete mismatch found between the three defined update maps and the actual selected actions. The helper lemmas have appropriately local statements. They provide meaningful additional dependencies toward Gate C2; they do not close C2 or the normalization suffix retirement theorem.

## Actual action selection and updates

The core has 12 rules in the inspected order. Indices 8, 9, 10 select `mc_normalize_scan`, `mc_normalize_emit`, `mc_commit`. The separate name equalities and `nth_In` membership proofs bind the wrappers to the real `getRules thieleCore` actions; a changed list order cannot silently preserve the checked name claims. The action proofs unfold the actual selected action and construct Kami `SemAction`, so they are not just proofs of an unrelated Gallina transcription.

Widths agree: pointers/counts are 5 bits, pair and descriptor indices are 4 bits, pair coordinates are 32 bits. Reusing `pair_index` for descriptor indexing is valid at the current equal index widths, although the name is narrower than its use.

- Scan reads exactly phase=8, i, j, end, duplicate, src and dst vectors. It writes duplicate OR (j<end AND pair equality), j+1, phase8 or9. Its out-of-range terminal scan still reads the truncated j index but excludes that equality from the duplicate flag. The update map preserves that exact behavior, including modulo-32 increment.
- Emit reads exactly phase=9, i, end, out, duplicate, src/dst. It copies each source coordinate at i to out iff duplicate=false; updates out, conditionally replaces end on the final candidate, advances i and j, clears duplicate, and selects phase11 or8. The map has exactly these eight writes. Vector writes are functional updates of old vectors, matching Kami's old-register read semantics.
- Commit reads exactly phase=11, base, end, descriptor-next, descriptor bases/counts/validity. It writes descriptor metadata at truncated descriptor-next, modulo-32 end-base count, next descriptor, next pair, and phase0. The six writes match the CPU exactly.

The typed lookup premises cover every actual read. They do not claim reset reachability, global register-map well-formedness, admissible raw ranges, or fresh descriptors. That is acceptable for local action semantics, but those obligations must be supplied before interpreting the bitvector equations as abstract allocation.

## Frames and word helpers

The frame lemmas use `M.union updates old`, the same direction used by Kami `Multistep.Multi`. Their excluded key lists match each map's exact write footprint, including unchanged-value table writes on duplicate emit. PC, mu, err and ordinary registers lie outside these maps and are therefore preserved for these isolated updates.

`normalization_pointer_increment_no_wrap` correctly covers inputs through16, giving17 on the terminal scan. `normalization_pair_index_exact` deliberately requires n<16; it does not misidentify index16 with a distinct physical slot.

`normalization_emit_preserves_other_pair` uses both range assumptions to exclude truncated-index aliasing. The unread-suffix corollary's out<=i<k<16 implies out<16 and k<>out, so its use of the pointwise lemma is sound. It proves preservation of future table entries for the emit expression. It does not yet prove that those entries represent an immutable raw-list suffix, nor that earlier descriptors are preserved, until embedded in a range/list invariant. The source and destination tables must each be instantiated and related to the updated register lookups.

## Exact assurance scope

`SemAction` and `Substep.SingleRule` establish that the actual action can produce the specified update map, no calls, and void return from every old map satisfying the typed read premises. These rules contain no nondeterministic reads or calls; nonetheless the current theorem statements do not establish uniqueness of every possible `SemAction` derivation, inversion of arbitrary substeps, or global execution refinement.

The following remain necessary for Gate C2:

1. Lift the singleton substeps into actual `Step` and `Multistep`, or use a checked existing lifting theorem. `Step` also has combination/hiding obligations.
2. Define the shared list/range invariant with immutable raw list, output prefix order, untouched suffix, and exact meaning of duplicate during/after scanning. Prove invariant establishment, preservation, and exact last-occurrence `nodup` result.
3. Preserve prior allocated descriptors and pair ranges through the composed suffix; handle empty base=end=16 separately as an empty descriptor with truncated base0.
4. Prove finite rule-firing progress and integrate scheduling assumptions. Kami admits empty/stuttering substeps; existence of one enabled action does not force a scheduler to select it. No universal clock bound follows from these lemmas.
5. Establish the suffix preconditions from actual dispatch/loading/copying/joining, including raw admission, capacity boundaries, identity/descriptor-zero handling and failure outcomes. Commit's unconstrained word subtraction is not yet a natural-length theorem.
6. Define and prove the abstract-to-hardware instruction-boundary relation, reset/init, successful retirement, and faults with exact PC/error/accounting/allocation behavior. The normalization suffix frames cannot substitute for the earlier dispatch changes.
7. Finish the promised labels, regions, tensor endpoints and downstream extraction/compiler/RTL assurance boundaries. These action lemmas cannot create data absent from the representation.

The existing file comments correctly call range, list and scheduling properties additional retirement obligations. Any status wording should similarly say “exact scan/emit/commit action/substep maps and local frame/index lemmas proved,” rather than “normalization refinement/progress proved.”
