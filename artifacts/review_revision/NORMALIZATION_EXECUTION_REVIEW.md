# Independent review of normalization execution composition

Reviewed `coq/kami_hw/NormalizationExecution.v` against the actual definitions in
`vendor/kami/Kami/Semantics.v`, plus the imported normalization start, scan,
emit, and commit substep statements. This is a source review in the same
workspace, not separate-environment reproduction or a replacement for the
compiled-library checker.

No concrete mismatch was found between the new theorem statements and the
reviewed Kami execution semantics.

## Step construction and labels

`no_call_rule_substep_is_step` constructs a singleton `SubstepRec` list from an
actual `Substep m old u (Rle (Some name)) (M.empty _)`. The singleton satisfies
`substepsComb`: there are no other substeps with which it must satisfy the
pairwise disjointness conditions. Its folded update map is exactly `u`.

`getLabel` gives a rule no method-definition entry. The premise also supplies
an empty method-call map, so both maps remain empty after folding and hiding.
The two `wellHidden` key-disjointness requirements therefore hold for arbitrary
module call and definition inventories. No external call is dropped by this
construction. This lemma cannot be applied to a substep with a nonempty call
map without separately proving that premise.

The resulting annotation is `Some (Some name)`, matching the distinction
between a named rule, an unnamed rule, and a method-only label. Kami's `Multi`
constructor prepends the newly executed label, so
`[mc_commit; mc_normalize_start]` correctly denotes start followed by commit.
The file header explicitly records this reverse execution order.

## Empty normalization trace

`normalization_empty_execution` supplies seven typed read premises: phase 5;
matching five-bit workspace base and end `b`; five-bit descriptor-next `d`;
and the descriptor base, count, and valid vectors. These are sufficient for
the two imported actual rule substeps. The start update changes only
`mc_i`, `mc_j`, `mc_norm_ptr`, `mc_duplicate`, and `mc_phase`, so all descriptor
and workspace reads needed by commit are retained. Equality of base and end
selects phase 11. The second substep is the actual `mc_commit` rule.

The final state is the correctly ordered left-biased union of commit updates,
start updates, and the original registers. `normalization_commit_phase_zero`
establishes phase zero after this commit. The imported commit map stores the
base at `pair_index b`, zero count at `pair_index d`, validity true, the
incremented descriptor pointer, and the pair-next pointer `b`.
`normalization_empty_descriptor_count` separately proves the zero-count
arithmetic at the selected descriptor slot.

Here "empty" means the raw workspace interval has equal endpoints. It does
not mean the whole physical pair table is empty. The theorem quantifies over
arbitrary five-bit base and descriptor values; it does not require fresh
allocation, capacity admission, valid dispatch, or a reachable reset state.
Consequently it establishes the exact two-rule existence trace, including
finite-width truncation and arithmetic, rather than correctness of the
allocator protocol at arbitrary values. The source describes this scope
explicitly and does not use this result to assert fresh allocation or
unbounded capacity.

## Remaining obligations

The four `*_actual_step` results lift the existing concrete substeps into
`Step`. `normalization_step_extends_execution` composes one such step with an
existing `Multistep`. These prove available execution paths, not uniqueness of
all possible paths, fair scheduling, or eventual progress under arbitrary
scheduling.

The nonempty scan/emit loop induction, list-data invariant across that loop,
dispatch and failure contracts, full retirement relation, reset reachability,
and generated RTL/toolchain correspondence are not proved by this file. No
statement in the reviewed source claims those conclusions. No local axioms,
admissions, or proof-bypass commands appear in the new file. Global
assumptions inherited from its dependencies must be read from the integrated
probe and checker reports; source inspection alone does not establish that
those reports are empty.
