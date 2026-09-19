# Boundary proof development

The first whole-reset `vm_compute` attempt was terminated by the 1.8 GB
per-process guard: exit 143 after 24 seconds, sampled RSS 1,844,280 KB.
That proof was removed. The final completeness proof uses a checked register-name
list and Kami's `makeMap_KeysSubset` / `find_KeysSubset` facts to exclude unknown
keys without evaluating every reset payload. No resource ceiling was raised.

The total field reader returns a default on a malformed map, but its correctness
lemma requires the actual CoreTyping schema. The completeness theorem has that
schema premise and proves exact map equality, so defaults do not conceal missing
or mistyped registers in the admitted theorem domain.

`prior-rebuild.log` preserves the pre-task successful rebuild log. Final checks,
commands, exit codes, limits and measured peaks are in `validation.json`.

A subsequent validation build was deliberately stopped while a broad `subst` /
`contradiction` tactic processed the 138 exclusions (integration exit 2 after
138.7 seconds, sampled peak 1,244 MB). The final proof uses each named inequality
directly, avoiding repeated substitution through the CPU context.
